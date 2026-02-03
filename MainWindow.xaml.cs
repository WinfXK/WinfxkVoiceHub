/*
* Copyright Notice
* © [2024 - 2026] Winfxk. All rights reserved.
* The software, its source code, and all related documentation are the intellectual property of Winfxk. Any reproduction or distribution of this software or any part thereof must be clearly attributed to Winfxk and the original author. Unauthorized copying, reproduction, or distribution without proper attribution is strictly prohibited.
* For inquiries, support, or to request permission for use, please contact us at:
* Email: admin@winfxk.cn
* QQ: 2508543202
* Visit our homepage for more information: http://Winfxk.cn
*
* --------- Create message ---------
* Created by IntelliJ IDEA
* Author： Winfxk
* Web: http://winfxk.com
* Created Date: 2026/02/04 14:15 
*/

using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Speech.Synthesis;
using System.Speech.AudioFormat;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Media.Animation;
using NAudio.Wave;
using Whisper.net;
using Microsoft.Win32;
using System.Text.Json;
using System.ComponentModel;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Threading;

namespace WinfxkVoiceHub
{
    /// <summary>
    /// Winfxk Voice Hub - 智能有声书阅读器主窗口
    /// </summary>
    public partial class MainWindow : Window
    {
        private System.Speech.Synthesis.SpeechSynthesizer ttsEngine;
        private IWaveIn captureDevice;
        private WaveOutEvent virtualOutput;
        private BufferedWaveProvider globalAudioBuffer; 
        private WhisperFactory whisperFactory;
        private WhisperProcessor whisperProcessor;
        private System.Windows.Forms.NotifyIcon trayIcon;
        private readonly string baseDir = AppDomain.CurrentDomain.BaseDirectory;
        private readonly string configDir;
        private readonly string configFilePath;
        private readonly string progressFilePath;
        private readonly string cacheDir;
        private SynchronizationContext uiContext;
        private bool _isInitializing = true;
        private bool isListening = false;
        private bool isReading = false;
        private bool isTtsSpeaking = false;
        private string _currentFilePath = "";
        private string _currentFileHash = "";
        private long _currentSessionId = 0;
        private string _selectedVoiceName = "";
        private List<string> _currentChapterTasks = new List<string>();
        private int _currentIndex = 0;
        private int _producerIndex = 0;
        private int _currentChapterIdx = -1;
        private Dictionary<string, int> _historyProgress = new Dictionary<string, int>();
        private DispatcherTimer visualizerTimer;
        private double wavePhase = 0;
        private readonly object bufferLock = new object();
        private List<float> audioBuffer = new List<float>();
        private const float volumeThreshold = 0.015f;
        private int silenceCounter = 0;

        public class ChapterInfo : INotifyPropertyChanged
        {
            public int StartIndex { get; set; }
            public int EndIndex { get; set; }
            public int TaskCount { get; set; }
            public string Title { get; set; }
            public string Name { get; set; }
            public string FullTitle
            {
                get
                {
                    if (string.IsNullOrWhiteSpace(Name)) return Title;
                    return $"{Title} {Name}";
                }
            }

            private bool _isActive;
            public bool IsActive
            {
                get => _isActive;
                set { _isActive = value; OnPropertyChanged(nameof(IsActive)); }
            }

            public event PropertyChangedEventHandler PropertyChanged;
            protected void OnPropertyChanged(string name) => PropertyChanged?.Invoke(this, new PropertyChangedEventArgs(name));
        }

        public class BookMeta
        {
            public string Hash { get; set; }
            public string FileName { get; set; }
            public int TotalTasks { get; set; }
            public List<ChapterInfo> Chapters { get; set; }
        }
        private List<ChapterInfo> _chapters = new List<ChapterInfo>();
        private List<ChapterInfo> _displayChapters = new List<ChapterInfo>();
        private ConcurrentQueue<(int Index, string Text, byte[] AudioData, double Duration, long SessionId)> _ttsBufferQueue = new ConcurrentQueue<(int, string, byte[], double, long)>();
        private CancellationTokenSource _searchCts;

        public MainWindow()
        {
            Encoding.RegisterProvider(CodePagesEncodingProvider.Instance);
            InitializeComponent();
            uiContext = SynchronizationContext.Current;
            configDir = Path.Combine(baseDir, "config");
            if (!Directory.Exists(configDir)) Directory.CreateDirectory(configDir);
            configFilePath = Path.Combine(configDir, "config.ini");
            progressFilePath = Path.Combine(configDir, "progress.json");
            cacheDir = Path.Combine(baseDir, "cache");
            if (!Directory.Exists(cacheDir)) Directory.CreateDirectory(cacheDir);
            InitializeTray();
            InitializeVisualizer();
            RefreshDevices();
            LoadGlobalSettings();
            LoadProgressHistory();
            InitializeEngines();
            Task.Run(() => StartPermanentProducer());
            Task.Run(() => StartPermanentConsumer());
            _isInitializing = false;
        }

        #region 系统底层支持 (托盘、动画绘制)

        private void InitializeTray()
        {
            trayIcon = new System.Windows.Forms.NotifyIcon();
            try
            {
                var iconUri = new Uri("pack://application:,,,/保龄球.ico");
                var iconStream = Application.GetResourceStream(iconUri).Stream;
                trayIcon.Icon = new System.Drawing.Icon(iconStream);
            }
            catch
            {
                trayIcon.Icon = System.Drawing.SystemIcons.Information;
            }
            trayIcon.Text = "Winfxk Voice Hub";
            trayIcon.Visible = true;
            trayIcon.DoubleClick += (s, e) => { this.Show(); this.WindowState = WindowState.Normal; this.Activate(); };
            var menu = new System.Windows.Forms.ContextMenuStrip();
            menu.Items.Add("主界面", null, (s, e) => { this.Show(); this.WindowState = WindowState.Normal; });
            menu.Items.Add("退出", null, (s, e) => { Application.Current.Shutdown(); });
            trayIcon.ContextMenuStrip = menu;
        }

        private void Window_Closing(object sender, CancelEventArgs e)
        {
            e.Cancel = true;
            this.Hide();
            AppendLog("[SYS] 程序切入后台模式。");
        }

        private void Window_StateChanged(object sender, EventArgs e)
        {
            if (this.WindowState == WindowState.Minimized) this.Hide();
        }

        private void InitializeVisualizer()
        {
            visualizerTimer = new DispatcherTimer(DispatcherPriority.Render);
            visualizerTimer.Interval = TimeSpan.FromMilliseconds(30);
            visualizerTimer.Tick += (s, e) => DrawWaves();
        }

        private void DrawWaves()
        {
            if (!isReading && !isTtsSpeaking)
            {
                VisualizerCanvas.Visibility = Visibility.Collapsed;
                return;
            }
            VisualizerCanvas.Visibility = Visibility.Visible;
            wavePhase += 0.25;
            double width = VisualizerCanvas.ActualWidth;
            double height = VisualizerCanvas.ActualHeight;
            if (width <= 0 || height <= 0) return;
            UpdatePath(WavePath1, width, height, 45, 0.015, wavePhase);
            UpdatePath(WavePath2, width, height, 30, 0.025, wavePhase * 1.3);
            UpdatePath(WavePath3, width, height, 15, 0.045, wavePhase * 0.7);
        }

        private void UpdatePath(System.Windows.Shapes.Path path, double width, double height, double amplitude, double frequency, double phase)
        {
            var points = new PointCollection();
            double centerY = height / 2;
            double dynamicAmp = amplitude * (0.8 + new Random().NextDouble() * 0.5);

            for (double x = 0; x <= width; x += 15)
            {
                double y = centerY + Math.Sin(x * frequency + phase) * dynamicAmp;
                points.Add(new Point(x, y));
            }

            var geometry = new StreamGeometry();
            using (StreamGeometryContext ctx = geometry.Open())
            {
                ctx.BeginFigure(points[0], false, false);
                ctx.PolyLineTo(points.Skip(1).ToList(), true, true);
            }
            path.Data = geometry;
        }

        #endregion

        #region 基础交互逻辑
        private async void Window_KeyDown(object sender, KeyEventArgs e)
        {
            switch (e.Key)
            {
                case Key.MediaPlayPause:
                case Key.Play:
                case Key.Pause:
                    BtnStartRead_Click(null, null);
                    e.Handled = true;
                    break;
                case Key.MediaNextTrack:
                    await JumpToNextChapter();
                    e.Handled = true;
                    break;
                case Key.MediaPreviousTrack:
                    await JumpToPreviousChapter();
                    e.Handled = true;
                    break;
                case Key.Space:
                    if (!TextInputField.IsFocused && !TxtChapterSearch.IsFocused)
                    {
                        BtnStartRead_Click(null, null);
                        e.Handled = true;
                    }
                    break;
            }
        }

        private async Task JumpToNextChapter()
        {
            if (_chapters.Count == 0) return;
            int n = _currentChapterIdx + 1;
            if (n < _chapters.Count) await JumpToAsync(_chapters[n].StartIndex, isReading);
        }

        private async Task JumpToPreviousChapter()
        {
            if (_chapters.Count == 0) return;
            int p = _currentChapterIdx - 1;
            if (p >= 0) await JumpToAsync(_chapters[p].StartIndex, isReading);
        }

        private void BtnAbout_Click(object sender, RoutedEventArgs e)
        {
            string msg = "🌌 Voice Hub - v1.0 (Starline)\n\n" +
                         "作者：冰月 (Winfxk)\n" +
                         "站点：http://Winfxk.cn\n" +
                         "QQ：2508543202\n" +
                         "Email：Winfxk@gmail.com\n";
            MessageBox.Show(this, msg, "冰月", MessageBoxButton.OK, MessageBoxImage.Information);
        }

        private void BtnClear_Click(object sender, RoutedEventArgs e)
        {
            isReading = false;
            Interlocked.Increment(ref _currentSessionId);
            if (globalAudioBuffer != null) globalAudioBuffer.ClearBuffer();
            _currentIndex = 0;
            _producerIndex = 0;
            _currentChapterIdx = -1;
            _chapters.Clear();
            _currentChapterTasks.Clear();
            TextInputField.IsReadOnly = false;
            TextInputField.Text = "";
            TxtFileInfo.Text = "环境已就绪。";
            TxtNowReading.Text = "就绪";
            TxtProgressLabel.Text = "进度: 0/0";
            SliderProgress.Value = 0;
            ChapterListBox.ItemsSource = null;
            SaveSettings();
        }

        private async void BtnImportTxt_Click(object sender, RoutedEventArgs e)
        {
            var ofd = new OpenFileDialog { Filter = "文本文件 (*.txt)|*.txt", Title = "载入书籍数据" };
            if (ofd.ShowDialog() == true) await InternalImportBookAsync(ofd.FileName);
        }

        private async void SliderProgress_PreviewMouseLeftButtonUp(object sender, MouseButtonEventArgs e)
        {
            await JumpToAsync((int)SliderProgress.Value, isReading);
        }

        #endregion

        #region Whisper STT 支持

        private void BtnToggleListen_Click(object sender, RoutedEventArgs e)
        {
            if (!isListening)
            {
                if (whisperProcessor == null) { AppendLog("错误：识别引擎未就绪。"); return; }
                if (isReading || _chapters.Count > 0 || !string.IsNullOrWhiteSpace(TextInputField.Text)) BtnClear_Click(null, null);

                StartListeningMode();
                BtnListen.Content = "⏹ 停止对话";
                BtnListen.Background = System.Windows.Media.Brushes.IndianRed;
                isListening = true;
                Task.Run(() => ProcessingLoop());
            }
            else
            {
                StopListeningMode();
                BtnListen.Content = "🎙️ 实时识别";
                BtnListen.Background = (Brush)new BrushConverter().ConvertFrom("#409EFF");
                isListening = false;
            }
        }

        private void StartListeningMode()
        {
            try
            {
                bool isSystem = RadioSystem.IsChecked ?? false;
                lock (bufferLock) { audioBuffer.Clear(); }
                silenceCounter = 0;

                if (isSystem) captureDevice = new WasapiLoopbackCapture();
                else captureDevice = new WaveInEvent { DeviceNumber = InputDeviceCombo.SelectedIndex, WaveFormat = new WaveFormat(16000, 1) };

                captureDevice.DataAvailable += (s, e) =>
                {
                    if (isTtsSpeaking) return;
                    float[] samples = ConvertToStandardSamples(e.Buffer, e.BytesRecorded, captureDevice.WaveFormat);
                    float rms = CalculateRMS(samples);
                    lock (bufferLock)
                    {
                        if (rms > volumeThreshold) { audioBuffer.AddRange(samples); silenceCounter = 0; }
                        else if (audioBuffer.Count > 0) silenceCounter++;
                    }
                };
                captureDevice.StartRecording();
                AppendLog("[STT] 监听模式已挂载。");
            }
            catch (Exception ex) { AppendLog($"[ERROR] 录音失败 -> {ex.Message}"); }
        }

        private void StopListeningMode()
        {
            if (captureDevice != null)
            {
                captureDevice.StopRecording();
                (captureDevice as IDisposable)?.Dispose();
                captureDevice = null;
            }
            AppendLog("[STT] 监听模式关闭。");
        }

        private async Task ProcessingLoop()
        {
            while (isListening)
            {
                float[] dataToProcess = null;
                lock (bufferLock)
                {
                    if (audioBuffer.Count > 16000 && (silenceCounter > 15 || audioBuffer.Count > 240000))
                    {
                        dataToProcess = audioBuffer.ToArray();
                        audioBuffer.Clear();
                        silenceCounter = 0;
                    }
                }

                if (dataToProcess != null)
                {
                    try
                    {
                        string rawResult = "";
                        await foreach (var result in whisperProcessor.ProcessAsync(dataToProcess)) rawResult += result.Text;
                        string cleaned = CleanWhisperHallucinations(rawResult);
                        if (!string.IsNullOrWhiteSpace(cleaned))
                        {
                            uiContext.Post(_ => { TextInputField.AppendText($"[识别] {cleaned}\n"); TextInputField.ScrollToEnd(); }, null);
                            await SpeakToDeviceAsync(cleaned);
                        }
                    }
                    catch { }
                }
                await Task.Delay(150);
            }
        }

        private float[] ConvertToStandardSamples(byte[] buffer, int length, WaveFormat format)
        {
            int bytesPerSample = format.BitsPerSample / 8;
            int sampleCount = length / bytesPerSample;
            float[] inputFloats = new float[sampleCount];
            for (int i = 0; i < sampleCount; i++)
            {
                if (format.Encoding == WaveFormatEncoding.IeeeFloat) inputFloats[i] = BitConverter.ToSingle(buffer, i * 4);
                else if (format.BitsPerSample == 16) inputFloats[i] = BitConverter.ToInt16(buffer, i * 2) / 32768f;
            }
            int channels = format.Channels;
            int monoCount = sampleCount / channels;
            float[] monoFloats = new float[monoCount];
            for (int i = 0; i < monoCount; i++)
            {
                float sum = 0;
                for (int c = 0; c < channels; c++) sum += inputFloats[i * channels + c];
                monoFloats[i] = sum / channels;
            }
            if (format.SampleRate == 16000) return monoFloats;
            double ratio = (double)format.SampleRate / 16000;
            int outCount = (int)(monoCount / ratio);
            float[] result = new float[outCount];
            for (int i = 0; i < outCount; i++) result[i] = monoFloats[(int)(i * ratio)];
            return result;
        }

        private float CalculateRMS(float[] samples)
        {
            if (samples.Length == 0) return 0;
            float sum = 0;
            foreach (var s in samples) sum += s * s;
            return (float)Math.Sqrt(sum / samples.Length);
        }

        private string CleanWhisperHallucinations(string input)
        {
            if (string.IsNullOrWhiteSpace(input)) return "";
            string cleaned = Regex.Replace(input, @"\([^\)]*\)|\[[^\]]*\]|（[^）]*）", "");
            string[] blackList = { "字幕", "谢谢观看", "音乐", "声音", "繁體", "廣告", "无法解释" };
            foreach (var word in blackList) cleaned = cleaned.Replace(word, "");
            cleaned = cleaned.Trim();
            if (cleaned.Length <= 1 || Regex.IsMatch(cleaned, @"^[^\w\s\u4e00-\u9fa5]+$")) return "";
            return cleaned;
        }

        private async Task SpeakToDeviceAsync(string text)
        {
            if (string.IsNullOrWhiteSpace(text) || ttsEngine == null) return;
            int rate = 0;
            string voice = _selectedVoiceName;
            uiContext.Send(_ => rate = (int)SliderSpeed.Value, null);

            await Task.Run(async () =>
            {
                try
                {
                    isTtsSpeaking = true;
                    PrepareAudioHardware();
                    using (var ms = new MemoryStream())
                    {
                        lock (ttsEngine)
                        {
                            if (!string.IsNullOrEmpty(voice)) ttsEngine.SelectVoice(voice);
                            ttsEngine.Rate = rate;
                            ttsEngine.SetOutputToAudioStream(ms, new SpeechAudioFormatInfo(22050, AudioBitsPerSample.Sixteen, AudioChannel.Mono));
                            ttsEngine.Speak(text);
                        }
                        ms.Position = 0;
                        byte[] buffer = ms.ToArray();
                        if (buffer.Length > 0)
                        {
                            byte[] padding = new byte[globalAudioBuffer.WaveFormat.AverageBytesPerSecond / 2];
                            globalAudioBuffer.AddSamples(padding, 0, padding.Length);
                            globalAudioBuffer.AddSamples(buffer, 0, buffer.Length);
                        }
                        if (virtualOutput.PlaybackState != PlaybackState.Playing) virtualOutput.Play();
                        double duration = buffer.Length / (double)globalAudioBuffer.WaveFormat.AverageBytesPerSecond;
                        await Task.Delay((int)(duration * 1000) + 400);
                    }
                }
                finally { isTtsSpeaking = false; }
            });
        }

        #endregion

        #region 书籍解析 
        private async Task InternalImportBookAsync(string filePath)
        {
            _currentFilePath = filePath;
            SaveSettings();

            LoadingOverlay.Visibility = Visibility.Visible;
            TxtParseStatus.Text = "扫描章节数据...";
            TextInputField.Text = "";
            _chapters.Clear();
            try
            {
                await Task.Run(async () =>
                {
                    _currentFileHash = GetFileHash(filePath);
                    string metaPath = Path.Combine(cacheDir, _currentFileHash, "meta.json");
                    string chapterDir = Path.Combine(cacheDir, _currentFileHash, "chapters");

                    if (File.Exists(metaPath))
                    {
                        _chapters = JsonSerializer.Deserialize<BookMeta>(File.ReadAllText(metaPath)).Chapters;
                    }
                    else
                    {
                        if (!Directory.Exists(chapterDir)) Directory.CreateDirectory(chapterDir);
                        using (var reader = new StreamReader(filePath, Encoding.Default))
                        {
                            var chapters = new List<ChapterInfo>();
                            var reg = new Regex(@"^\s*((?:第?\s*[0-9一二三四五六七八九十百千万零]+\s*[部篇卷章节回幕节]\s*)+|楔子|序言|序章|内容简介|前言|Chapter\s*[0-9]+)\s*(.*)$", RegexOptions.Compiled | RegexOptions.IgnoreCase);
                            List<string> buffer = new List<string>();
                            string cT = "开始"; string cN = "";
                            int gIdx = 0; long cCount = 0; string line;
                            while ((line = await reader.ReadLineAsync()) != null)
                            {
                                string t = line.Trim();
                                if (string.IsNullOrWhiteSpace(t)) continue;
                                bool isH = t.Length < 80 && reg.IsMatch(t);
                                if ((isH || cCount > 250000) && buffer.Count > 0)
                                {
                                    File.WriteAllLines(Path.Combine(chapterDir, $"{chapters.Count}.dat"), buffer);
                                    chapters.Add(new ChapterInfo { StartIndex = gIdx - buffer.Count, EndIndex = gIdx - 1, TaskCount = buffer.Count, Title = cT, Name = cN });
                                    buffer.Clear(); cCount = 0;
                                    if (isH) { var m = reg.Match(t); cT = m.Groups[1].Value.Trim(); cN = m.Groups[2].Value.Trim(); }
                                    else if (!cT.EndsWith("(续)")) cT += " (续)";
                                }
                                var frags = SmartSplit(t);
                                foreach (var f in frags) { buffer.Add(f); cCount += f.Length; }
                                gIdx += frags.Count;
                            }
                            if (buffer.Count > 0)
                            {
                                File.WriteAllLines(Path.Combine(chapterDir, $"{chapters.Count}.dat"), buffer);
                                chapters.Add(new ChapterInfo { StartIndex = gIdx - buffer.Count, EndIndex = gIdx - 1, TaskCount = buffer.Count, Title = cT, Name = cN });
                            }
                            _chapters = chapters;
                            File.WriteAllText(metaPath, JsonSerializer.Serialize(new BookMeta { Hash = _currentFileHash, Chapters = _chapters }));
                        }
                    }
                    _currentIndex = _historyProgress.ContainsKey(_currentFilePath) ? _historyProgress[_currentFilePath] : 0;
                });
                await JumpToAsync(_currentIndex, false);
                SliderProgress.Maximum = _chapters.Count > 0 ? _chapters.Last().EndIndex : 0;
                SliderProgress.Value = _currentIndex;
                _displayChapters = _chapters.ToList();
                ChapterListBox.ItemsSource = _displayChapters;
                TxtFileInfo.Text = $"{Path.GetFileName(filePath)} (锚点: {_chapters.Count})";
                AppendLog("[SYS] 书籍载入完成。");
            }
            catch (Exception ex) { AppendLog($"[ERROR] 载入书籍失败 -> {ex.Message}"); }
            finally { LoadingOverlay.Visibility = Visibility.Collapsed; }
        }

        private string GetFileHash(string path)
        {
            using (var sha = SHA256.Create())
            using (var fs = File.OpenRead(path)) return BitConverter.ToString(sha.ComputeHash(fs)).Replace("-", "").ToLower();
        }

        private List<string> SmartSplit(string text)
        {
            var parts = Regex.Split(text, @"(?<=[。！？；\n\r])");
            var res = new List<string>();
            foreach (var p in parts) { string s = p.Trim(); if (!string.IsNullOrEmpty(s)) res.Add(s); }
            return res;
        }

        #endregion

        #region 朗读流水线核心控制  
        private void BtnStartRead_Click(object sender, RoutedEventArgs e)
        {
            if (isReading)
            {
                isReading = false;
                visualizerTimer.Stop();
                BtnStartRead.Content = "▶ 开始播放";
                BtnStartRead.Background = (Brush)new BrushConverter().ConvertFrom("#67C23A");
            }
            else
            {
                isReading = true;
                _producerIndex = _currentIndex;  
                PrepareAudioHardware();
                Interlocked.Increment(ref _currentSessionId); 
                visualizerTimer.Start();
                BtnStartRead.Content = "⏹ 停止播放";
                BtnStartRead.Background = System.Windows.Media.Brushes.IndianRed;

                if (virtualOutput.PlaybackState != PlaybackState.Playing) virtualOutput.Play();
            }
        }

        private void PrepareAudioHardware()
        {
            if (virtualOutput != null) return;
            int devIdx = 0;
            uiContext.Send(_ => devIdx = OutputDeviceCombo.SelectedIndex, null);
            virtualOutput = new WaveOutEvent { DeviceNumber = devIdx };
            globalAudioBuffer = new BufferedWaveProvider(new WaveFormat(22050, 16, 1)) { BufferLength = 1024 * 1024 * 5, DiscardOnBufferOverflow = true };
            byte[] silence = new byte[globalAudioBuffer.WaveFormat.AverageBytesPerSecond / 2];
            globalAudioBuffer.AddSamples(silence, 0, silence.Length);
            virtualOutput.Init(globalAudioBuffer);
        }

        private async Task StartPermanentProducer()
        {
            while (true)
            {
                try
                {
                    if (_chapters.Count == 0 || _ttsBufferQueue.Count >= 8) { await Task.Delay(200); continue; }
                    long sid = _currentSessionId;
                    int pIdx = _producerIndex;
                    string text = await GetTaskTextAsync(pIdx);
                    if (text == null) { await Task.Delay(500); continue; }
                    var ms = new MemoryStream();
                    lock (ttsEngine)
                    {
                        if (!string.IsNullOrEmpty(_selectedVoiceName)) ttsEngine.SelectVoice(_selectedVoiceName);
                        int rate = 0;
                        uiContext.Send(_ => rate = (int)SliderSpeed.Value, null);
                        ttsEngine.Rate = rate;
                        ttsEngine.SetOutputToAudioStream(ms, new SpeechAudioFormatInfo(22050, AudioBitsPerSample.Sixteen, AudioChannel.Mono));
                        ttsEngine.Speak(text + " ");
                    }
                    if (sid == _currentSessionId)
                    {
                        _ttsBufferQueue.Enqueue((pIdx, text, ms.ToArray(), ms.Length / (double)22050 / 2, sid));
                        _producerIndex++;
                    }
                    else await Task.Yield();
                }
                catch { await Task.Delay(1000); }
            }
        }

        private async Task StartPermanentConsumer()
        {
            while (true)
            {
                try
                {
                    if (!isReading || !_ttsBufferQueue.TryPeek(out var item)) { await Task.Delay(50); continue; }
                    if (item.SessionId != _currentSessionId || item.Index < _currentIndex) { _ttsBufferQueue.TryDequeue(out _); continue; }
                    if (globalAudioBuffer != null && globalAudioBuffer.BufferedDuration.TotalMilliseconds > 200) { await Task.Delay(30); continue; }
                    if (_ttsBufferQueue.TryDequeue(out var task))
                    {
                        _ = Task.Run(() => LoadChapterToUIAsync(task.Index));
                        uiContext.Post(_ =>
                        {
                            TxtNowReading.Text = task.Text;
                            SliderProgress.Value = task.Index;
                            UpdateProgressUI();
                            HighlightText(task.Text);
                        }, null);
                        if (task.AudioData != null) globalAudioBuffer.AddSamples(task.AudioData, 0, task.AudioData.Length);
                        _currentIndex = task.Index + 1;
                        SaveProgress(_currentFilePath, _currentIndex);
                    }
                }
                catch { await Task.Delay(1000); }
            }
        }

        private async Task JumpToAsync(int index, bool autoResume = false)
        {
            long sid = Interlocked.Increment(ref _currentSessionId);
            if (globalAudioBuffer != null) globalAudioBuffer.ClearBuffer();
            while (_ttsBufferQueue.TryDequeue(out _)) { }
            _currentIndex = index;
            _producerIndex = index;
            await LoadChapterToUIAsync(_currentIndex);
            UpdateProgressUI();
            if (autoResume)
            {
                isReading = true;  
                PrepareAudioHardware();
                if (virtualOutput.PlaybackState != PlaybackState.Playing) virtualOutput.Play();

                uiContext.Post(_ => {
                    BtnStartRead.Content = "⏹ 停止播放";
                    BtnStartRead.Background = System.Windows.Media.Brushes.IndianRed;
                }, null);
            }
            else
            {
                isReading = false;
                uiContext.Post(_ => {
                    BtnStartRead.Content = "▶ 开始播放";
                    BtnStartRead.Background = (Brush)new BrushConverter().ConvertFrom("#67C23A");
                }, null);
            }
            await Task.Delay(50);
        }

        private async Task<string> GetTaskTextAsync(int idx)
        {
            if (_chapters.Count == 0) return (idx >= 0 && idx < _currentChapterTasks.Count) ? _currentChapterTasks[idx] : null;
            var c = _chapters.LastOrDefault(ch => ch.StartIndex <= idx);
            if (c == null) return null;
            int rel = idx - c.StartIndex;
            string path = Path.Combine(cacheDir, _currentFileHash, "chapters", $"{_chapters.IndexOf(c)}.dat");
            if (!File.Exists(path)) return null;
            try
            {
                var lines = File.ReadAllLines(path);
                return (rel >= 0 && rel < lines.Length) ? lines[rel] : null;
            }
            catch { return null; }
        }

        private async Task LoadChapterToUIAsync(int idx)
        {
            if (_chapters.Count == 0) return;
            var c = _chapters.LastOrDefault(ch => ch.StartIndex <= idx) ?? _chapters[0];
            int cIdx = _chapters.IndexOf(c);

            uiContext.Post(_ =>
            {
                foreach (var chapter in _chapters) chapter.IsActive = false;
                if (cIdx >= 0 && cIdx < _chapters.Count)
                {
                    var target = _chapters[cIdx];
                    target.IsActive = true;
                    ChapterListBox.SelectedItem = target;
                    ChapterListBox.ScrollIntoView(target);
                }
            }, null);

            if (_currentChapterIdx == cIdx) return;

            try
            {
                string p = Path.Combine(cacheDir, _currentFileHash, "chapters", $"{cIdx}.dat");
                if (File.Exists(p))
                {
                    var lines = await File.ReadAllLinesAsync(p);
                    _currentChapterTasks = lines.ToList();
                    _currentChapterIdx = cIdx;
                    uiContext.Post(_ => { TextInputField.IsReadOnly = false; TextInputField.Text = string.Join(Environment.NewLine, lines); TextInputField.IsReadOnly = true; }, null);
                }
            }
            catch { }
        }

        #endregion

        #region 引擎与辅助模块
        private void InitializeEngines()
        {
            try
            {
                if (ttsEngine != null) ttsEngine.Dispose();
                ttsEngine = new System.Speech.Synthesis.SpeechSynthesizer();
                var voices = ttsEngine.GetInstalledVoices();
                VoiceCombo.Items.Clear();
                foreach (var v in voices) VoiceCombo.Items.Add(v.VoiceInfo.Name);
                string pref = voices.FirstOrDefault(v => v.VoiceInfo.Name.Contains("Xiaoxiao"))?.VoiceInfo.Name ?? (voices.Count > 0 ? voices[0].VoiceInfo.Name : null);
                if (pref != null) { VoiceCombo.SelectedItem = pref; _selectedVoiceName = pref; }
                string modelPath = Path.Combine(baseDir, "ggml-base-q5_1.bin");
                if (File.Exists(modelPath))
                {
                    Task.Run(() => {
                        whisperFactory = WhisperFactory.FromPath(modelPath);
                        whisperProcessor = whisperFactory.CreateBuilder().WithLanguage("zh").Build();
                        AppendLog("[SYS] Whisper 系统已载入。");
                    });
                }
            }
            catch (Exception ex) { AppendLog($"[ERROR] 引擎引导失败 -> {ex.Message}"); }
        }

        private void LoadGlobalSettings()
        {
            if (!File.Exists(configFilePath)) return;
            try
            {
                string[] lines = File.ReadAllLines(configFilePath);
                if (lines.Length >= 1 && int.TryParse(lines[0], out int rate)) SliderSpeed.Value = rate;
                if (lines.Length >= 2) { VoiceCombo.SelectedItem = lines[1]; _selectedVoiceName = lines[1]; }
                if (lines.Length >= 3) OutputDeviceCombo.SelectedItem = lines[2];
                if (lines.Length >= 4 && File.Exists(lines[3])) uiContext.Post(async _ => await InternalImportBookAsync(lines[3]), null);
            }
            catch { }
        }

        private void SaveSettings()
        {
            if (_isInitializing) return;
            try
            {
                var sb = new StringBuilder();
                sb.AppendLine(((int)SliderSpeed.Value).ToString());
                sb.AppendLine(VoiceCombo.SelectedItem?.ToString() ?? "");
                sb.AppendLine(OutputDeviceCombo.SelectedItem?.ToString() ?? "");
                sb.AppendLine(_currentFilePath);
                File.WriteAllText(configFilePath, sb.ToString());
            }
            catch { }
        }

        private void OnSettingChanged(object sender, EventArgs e)
        {
            if (sender == VoiceCombo) _selectedVoiceName = VoiceCombo.SelectedItem?.ToString() ?? "";
            SaveSettings();
        }

        private void OnSettingChanged(object sender, RoutedPropertyChangedEventArgs<double> e) => SaveSettings();

        private void LoadProgressHistory()
        {
            if (File.Exists(progressFilePath))
            {
                try { _historyProgress = JsonSerializer.Deserialize<Dictionary<string, int>>(File.ReadAllText(progressFilePath)); } catch { }
            }
        }

        private void SaveProgress(string path, int idx)
        {
            if (string.IsNullOrEmpty(path)) return;
            _historyProgress[path] = idx;
            try { File.WriteAllText(progressFilePath, JsonSerializer.Serialize(_historyProgress)); } catch { }
        }

        private void UpdateProgressUI()
        {
            int tot = _chapters.Count > 0 ? (_chapters.Last().EndIndex + 1) : 0;
            TxtProgressLabel.Text = $"阅读进度: {_currentIndex}/{tot}";
        }

        private void HighlightText(string text)
        {
            try
            {
                int idx = TextInputField.Text.IndexOf(text);
                if (idx >= 0)
                {
                    TextInputField.Focus();
                    TextInputField.Select(idx, text.Length);
                    TextInputField.ScrollToLine(TextInputField.GetLineIndexFromCharacterIndex(idx));
                }
            }
            catch { }
        }

        private void RefreshDevices()
        {
            InputDeviceCombo.Items.Clear(); OutputDeviceCombo.Items.Clear();
            for (int i = 0; i < WaveIn.DeviceCount; i++) InputDeviceCombo.Items.Add(WaveIn.GetCapabilities(i).ProductName);
            for (int i = 0; i < WaveOut.DeviceCount; i++) OutputDeviceCombo.Items.Add(WaveOut.GetCapabilities(i).ProductName);
            if (InputDeviceCombo.Items.Count > 0) InputDeviceCombo.SelectedIndex = 0;
            if (OutputDeviceCombo.Items.Count > 0) OutputDeviceCombo.SelectedIndex = 0;
        }

        private void BtnOpenChapterSelector_Click(object sender, RoutedEventArgs e)
        {
            ChapterOverlay.Visibility = Visibility.Visible;
            _displayChapters = _chapters.ToList();
            ChapterListBox.ItemsSource = _displayChapters;
            if (_currentChapterIdx >= 0 && _currentChapterIdx < _displayChapters.Count)
            {
                ChapterListBox.ScrollIntoView(_displayChapters[_currentChapterIdx]);
                ChapterListBox.SelectedItem = _displayChapters[_currentChapterIdx];
            }
        }

        private void BtnCloseChapter_Click(object sender, RoutedEventArgs e) => ChapterOverlay.Visibility = Visibility.Collapsed;

        private async void TxtChapterSearch_TextChanged(object sender, TextChangedEventArgs e)
        {
            _searchCts?.Cancel();
            _searchCts = new CancellationTokenSource();
            try
            {
                await Task.Delay(300, _searchCts.Token);
                string filter = TxtChapterSearch.Text.Trim().ToLower();
                _displayChapters = string.IsNullOrEmpty(filter) ? _chapters : _chapters.Where(c => c.FullTitle.ToLower().Contains(filter)).ToList();
                ChapterListBox.ItemsSource = _displayChapters;
            }
            catch { }
        }

        private async void ChapterListBox_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            if (ChapterListBox.SelectedItem is ChapterInfo c)
            {
                ChapterOverlay.Visibility = Visibility.Collapsed;
                await JumpToAsync(c.StartIndex, isReading);
            }
        }

        private void AppendLog(string msg)
        {
            uiContext.Post(_ => { LogConsole.AppendText($"[{DateTime.Now:HH:mm:ss}] {msg}\r\n"); LogConsole.ScrollToEnd(); }, null);
        }

        #endregion
    }
}