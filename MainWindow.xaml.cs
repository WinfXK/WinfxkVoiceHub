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
* Created Date: 2026/02/02 18:20
*/

using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Security.Cryptography;
using System.Speech.Synthesis;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using System.Windows;
using System.Windows.Controls;
using NAudio.Wave;
using Whisper.net;
using Microsoft.Win32;
using System.Text.Json;

namespace WinfxkVoiceHub
{
    public partial class MainWindow : Window
    {
        private System.Speech.Synthesis.SpeechSynthesizer ttsEngine;
        private IWaveIn captureDevice;
        private WaveOutEvent virtualOutput;
        private WhisperFactory whisperFactory;
        private WhisperProcessor whisperProcessor;

        private readonly string baseDir = AppDomain.CurrentDomain.BaseDirectory;
        private readonly string configFilePath;
        private readonly string progressFilePath;
        private readonly string cacheDir;
        private SynchronizationContext uiContext;

        // 状态与记忆数据
        private bool _isInitializing = true; // 防止启动加载时重复保存配置
        private bool isListening = false;
        private bool isReading = false;
        private bool isTtsSpeaking = false;
        private string _currentFilePath = "";
        private string _currentFileHash = "";

        private List<string> _currentChapterTasks = new List<string>();
        private int _currentIndex = 0;
        private int _currentChapterIdx = -1;

        private Dictionary<string, int> _historyProgress = new Dictionary<string, int>();

        public class ChapterInfo
        {
            public int StartIndex { get; set; }
            public int EndIndex { get; set; }
            public int TaskCount { get; set; }
            public string Title { get; set; }
            public string Name { get; set; }
            public string FullTitle => string.IsNullOrWhiteSpace(Name) ? Title : $"{Title} {Name}";
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
        private ConcurrentQueue<(int Index, string Text, MemoryStream Stream)> _ttsBufferQueue = new ConcurrentQueue<(int, string, MemoryStream)>();
        private CancellationTokenSource _readCts;

        private readonly object bufferLock = new object();
        private List<float> audioBuffer = new List<float>();
        private const float volumeThreshold = 0.015f;
        private int silenceCounter = 0;

        public MainWindow()
        {
            Encoding.RegisterProvider(CodePagesEncodingProvider.Instance);
            InitializeComponent();
            uiContext = SynchronizationContext.Current;

            configFilePath = Path.Combine(baseDir, "config.ini");
            progressFilePath = Path.Combine(baseDir, "progress.json");
            cacheDir = Path.Combine(baseDir, "cache");
            if (!Directory.Exists(cacheDir)) Directory.CreateDirectory(cacheDir);

            RefreshDevices();
            LoadGlobalSettings();
            LoadProgressHistory();
            InitializeEngines();

            _isInitializing = false; // 加载完成，开启实时保存
        }

        #region 配置与自动加载

        private void LoadGlobalSettings()
        {
            if (!File.Exists(configFilePath)) return;
            try
            {
                string[] lines = File.ReadAllLines(configFilePath);
                if (lines.Length >= 1 && int.TryParse(lines[0], out int rate)) SliderSpeed.Value = rate;
                if (lines.Length >= 2) SetComboByText(InputDeviceCombo, lines[1]);
                if (lines.Length >= 3) SetComboByText(OutputDeviceCombo, lines[2]);

                // 自动打开上次的书籍
                if (lines.Length >= 4)
                {
                    string lastPath = lines[3].Trim();
                    if (File.Exists(lastPath))
                    {
                        uiContext.Post(async _ => await InternalImportBookAsync(lastPath), null);
                    }
                }
            }
            catch { }
        }

        private void SaveSettings()
        {
            if (_isInitializing) return; // 初始化过程中不执行保存
            try
            {
                var sb = new StringBuilder();
                sb.AppendLine(((int)SliderSpeed.Value).ToString());
                sb.AppendLine(InputDeviceCombo.SelectedItem?.ToString() ?? "");
                sb.AppendLine(OutputDeviceCombo.SelectedItem?.ToString() ?? "");
                sb.AppendLine(_currentFilePath); // 记录关闭前打开的书籍路径
                File.WriteAllText(configFilePath, sb.ToString());
            }
            catch { }
        }

        private void LoadProgressHistory()
        {
            if (!File.Exists(progressFilePath)) return;
            try
            {
                string json = File.ReadAllText(progressFilePath);
                _historyProgress = JsonSerializer.Deserialize<Dictionary<string, int>>(json) ?? new Dictionary<string, int>();
            }
            catch { }
        }

        private void SaveProgress(string filePath, int index)
        {
            if (string.IsNullOrEmpty(filePath)) return;
            try
            {
                _historyProgress[filePath] = index;
                File.WriteAllText(progressFilePath, JsonSerializer.Serialize(_historyProgress));
            }
            catch { }
        }

        private void SetComboByText(ComboBox combo, string text)
        {
            foreach (var item in combo.Items) if (item.ToString() == text) { combo.SelectedItem = item; return; }
            if (combo.Items.Count > 0) combo.SelectedIndex = 0;
        }

        private void OnSettingChanged(object sender, EventArgs e)
        {
            SaveSettings(); // 实时触发保存
        }

        #endregion

        #region 高性能书籍导入与分片 (复用逻辑)

        private async void BtnImportTxt_Click(object sender, RoutedEventArgs e)
        {
            var ofd = new OpenFileDialog { Filter = "书籍文件 (*.txt)|*.txt" };
            if (ofd.ShowDialog() == true) await InternalImportBookAsync(ofd.FileName);
        }

        /// <summary>
        /// 内部书籍载入核心：支持手动与自动回载
        /// </summary>
        private async Task InternalImportBookAsync(string filePath)
        {
            _currentFilePath = filePath;
            SaveSettings(); // 记录当前书籍路径

            LoadingOverlay.Visibility = Visibility.Visible;
            TxtParseStatus.Text = "正在智能挂载书籍资源...";
            TextInputField.Text = "";
            _chapters.Clear();
            _currentChapterIdx = -1;

            try
            {
                await Task.Run(async () => {
                    _currentFileHash = GetFileHash(filePath);
                    string bookCacheDir = Path.Combine(cacheDir, _currentFileHash);
                    string metaPath = Path.Combine(bookCacheDir, "meta.json");
                    string chapterDir = Path.Combine(bookCacheDir, "chapters");

                    if (File.Exists(metaPath))
                    {
                        uiContext.Post(_ => TxtParseStatus.Text = "命中分片缓存，极速加载中...", null);
                        string json = File.ReadAllText(metaPath);
                        var meta = JsonSerializer.Deserialize<BookMeta>(json);
                        _chapters = meta.Chapters;
                    }
                    else
                    {
                        uiContext.Post(_ => TxtParseStatus.Text = "首次导入：正在执行流式预处理...", null);
                        if (!Directory.Exists(chapterDir)) Directory.CreateDirectory(chapterDir);

                        using (var reader = new StreamReader(filePath, Encoding.Default))
                        {
                            var chapters = new List<ChapterInfo>();
                            var reg = new Regex(@"^\s*(第\s*[0-9一二三四五六七八九十百千万零]+\s*[章节回卷篇幕])\s*(.*)$");

                            List<string> currentBuffer = new List<string>();
                            string cTitle = "序章"; string cName = "";
                            int globalIndex = 0; int lineCount = 0; long currentChapterCharCount = 0;

                            string line;
                            while ((line = await reader.ReadLineAsync()) != null)
                            {
                                lineCount++; string trimmed = line.Trim();
                                if (string.IsNullOrWhiteSpace(trimmed)) continue;

                                bool isHeader = false;
                                if (trimmed.Length < 45)
                                {
                                    var match = reg.Match(trimmed);
                                    if (match.Success)
                                    {
                                        string suffix = match.Groups[2].Value.Trim();
                                        if (!suffix.StartsWith("课") && !suffix.StartsWith("级")) isHeader = true;
                                    }
                                }

                                if ((isHeader || (currentBuffer.Count >= 500 && currentChapterCharCount > 50000)) && currentBuffer.Count > 0)
                                {
                                    SaveChapterToDisk(chapterDir, chapters.Count, currentBuffer);
                                    chapters.Add(new ChapterInfo { StartIndex = globalIndex - currentBuffer.Count, EndIndex = globalIndex - 1, TaskCount = currentBuffer.Count, Title = cTitle, Name = cName });
                                    currentBuffer.Clear(); currentChapterCharCount = 0;
                                    if (isHeader)
                                    {
                                        var m = reg.Match(trimmed);
                                        cTitle = m.Groups[1].Value.Trim(); cName = m.Groups[2].Value.Trim();
                                    }
                                    else
                                    {
                                        cTitle = cTitle.StartsWith("[续]") ? cTitle : $"[续] {cTitle}";
                                    }
                                }

                                var frags = SmartSplit(trimmed);
                                foreach (var f in frags) { currentBuffer.Add(f); currentChapterCharCount += f.Length; }
                                globalIndex += frags.Count;
                                if (lineCount % 3000 == 0) uiContext.Post(_ => TxtParseProgress.Text = $"已扫描 {lineCount} 行...", null);
                            }
                            if (currentBuffer.Count > 0)
                            {
                                SaveChapterToDisk(chapterDir, chapters.Count, currentBuffer);
                                chapters.Add(new ChapterInfo { StartIndex = globalIndex - currentBuffer.Count, EndIndex = globalIndex - 1, TaskCount = currentBuffer.Count, Title = cTitle, Name = cName });
                            }
                            _chapters = chapters;
                            var meta = new BookMeta { Hash = _currentFileHash, FileName = Path.GetFileName(filePath), TotalTasks = globalIndex, Chapters = _chapters };
                            File.WriteAllText(metaPath, JsonSerializer.Serialize(meta));
                        }
                    }
                    _currentIndex = _historyProgress.ContainsKey(_currentFilePath) ? _historyProgress[_currentFilePath] : 0;
                });

                await LoadChapterToUIAsync(_currentIndex);
                SliderProgress.Maximum = _chapters.Count > 0 ? _chapters.Last().EndIndex : 0;
                SliderProgress.Value = _currentIndex;
                _displayChapters = _chapters.ToList();
                ChapterListBox.ItemsSource = _displayChapters;
                TxtFileInfo.Text = $"书籍：{Path.GetFileName(filePath)}\n共 {_chapters.Count} 章 / {_chapters.Sum(c => c.TaskCount)} 段";
                UpdateProgressUI();
                AppendLog($"系统：书籍载入成功。上次进度：第 {_currentIndex + 1} 段。");

            }
            catch (Exception ex) { AppendLog($"错误：加载书籍失败 -> {ex.Message}"); }
            finally { LoadingOverlay.Visibility = Visibility.Collapsed; }
        }

        private string GetFileHash(string filePath)
        {
            using (var sha = SHA256.Create())
            using (var stream = File.OpenRead(filePath))
            {
                if (stream.Length > 10 * 1024 * 1024)
                {
                    byte[] buffer = new byte[1024 * 1024]; stream.Read(buffer, 0, buffer.Length);
                    return BitConverter.ToString(sha.ComputeHash(buffer)).Replace("-", "").ToLower();
                }
                return BitConverter.ToString(sha.ComputeHash(stream)).Replace("-", "").ToLower();
            }
        }

        private void SaveChapterToDisk(string dir, int index, List<string> tasks)
        {
            File.WriteAllLines(Path.Combine(dir, $"{index}.dat"), tasks);
        }

        private async Task LoadChapterToUIAsync(int taskIndex)
        {
            if (_chapters.Count == 0) return;
            var chapter = _chapters.LastOrDefault(c => c.StartIndex <= taskIndex) ?? _chapters[0];
            int idx = _chapters.IndexOf(chapter);
            if (_currentChapterIdx == idx) return;

            try
            {
                string path = Path.Combine(cacheDir, _currentFileHash, "chapters", $"{idx}.dat");
                if (File.Exists(path))
                {
                    var lines = await File.ReadAllLinesAsync(path);
                    _currentChapterTasks = lines.ToList();
                    _currentChapterIdx = idx;
                    uiContext.Post(_ => {
                        TextInputField.IsReadOnly = false;
                        TextInputField.Text = string.Join(Environment.NewLine, lines);
                        TextInputField.IsReadOnly = true;
                    }, null);
                }
            }
            catch { }
        }

        private List<string> SmartSplit(string text)
        {
            if (string.IsNullOrWhiteSpace(text)) return new List<string>();
            var parts = Regex.Split(text, @"(?<=[。！？；\n\r])");
            var result = new List<string>();
            foreach (var p in parts)
            {
                string s = p.Trim();
                if (string.IsNullOrWhiteSpace(s)) continue;
                if (s.Length > 120)
                {
                    var subs = Regex.Split(s, @"(?<=[，、,])");
                    foreach (var sub in subs) if (!string.IsNullOrWhiteSpace(sub)) result.Add(sub.Trim());
                }
                else result.Add(s);
            }
            return result;
        }

        #endregion

        #region 朗读与跳转 (预读逻辑)

        private async void BtnStartRead_Click(object sender, RoutedEventArgs e)
        {
            if (isReading) { StopReading(); return; }
            if (_chapters.Count > 0 && (_currentChapterTasks == null || _currentChapterTasks.Count == 0))
                await LoadChapterToUIAsync(_currentIndex);
            else if (_chapters.Count == 0 && !string.IsNullOrEmpty(TextInputField.Text))
                _currentChapterTasks = SmartSplit(TextInputField.Text);

            if (_currentChapterTasks == null || _currentChapterTasks.Count == 0) return;

            isReading = true;
            _readCts = new CancellationTokenSource();
            BtnStartRead.Content = "⏹ 停止播放";
            BtnStartRead.Background = System.Windows.Media.Brushes.IndianRed;
            _ = StartProducer(_readCts.Token);
            await StartConsumer(_readCts.Token);
        }

        private void StopReading()
        {
            isReading = false; _readCts?.Cancel(); virtualOutput?.Stop();
            BtnStartRead.Content = "▶ 开始全文朗读";
            BtnStartRead.Background = System.Windows.Media.Brushes.DarkSeaGreen;
            while (_ttsBufferQueue.TryDequeue(out var leftover)) leftover.Stream.Dispose();
        }

        private async Task StartProducer(CancellationToken token)
        {
            int rate = 0; uiContext.Send(_ => rate = (int)SliderSpeed.Value, null);
            int taskPointer = _currentIndex;
            int total = _chapters.Count > 0 ? (_chapters.Last().EndIndex + 1) : _currentChapterTasks.Count;
            while (taskPointer < total && !token.IsCancellationRequested)
            {
                while (_ttsBufferQueue.Count >= 5 && !token.IsCancellationRequested) await Task.Delay(100);
                if (token.IsCancellationRequested) break;
                string text = await GetTaskTextFromCacheAsync(taskPointer);
                if (string.IsNullOrEmpty(text)) { taskPointer++; continue; }
                var ms = new MemoryStream();
                lock (ttsEngine) { ttsEngine.Rate = rate; ttsEngine.SetOutputToWaveStream(ms); ttsEngine.Speak(text); }
                ms.Position = 0; _ttsBufferQueue.Enqueue((taskPointer, text, ms)); taskPointer++;
            }
        }

        private async Task<string> GetTaskTextFromCacheAsync(int index)
        {
            if (_chapters.Count == 0)
                return (index >= 0 && index < _currentChapterTasks.Count) ? _currentChapterTasks[index] : null;
            var chapter = _chapters.LastOrDefault(c => c.StartIndex <= index);
            if (chapter == null) return null;
            int cIdx = _chapters.IndexOf(chapter);
            int relIdx = index - chapter.StartIndex;
            string path = Path.Combine(cacheDir, _currentFileHash, "chapters", $"{cIdx}.dat");
            if (!File.Exists(path)) return null;
            try
            {
                var lines = File.ReadAllLines(path);
                if (relIdx >= 0 && relIdx < lines.Length) return lines[relIdx];
            }
            catch { }
            return null;
        }

        private async Task StartConsumer(CancellationToken token)
        {
            try
            {
                while (isReading && !token.IsCancellationRequested)
                {
                    while (_ttsBufferQueue.IsEmpty && !token.IsCancellationRequested) await Task.Delay(50);
                    if (token.IsCancellationRequested) break;
                    if (_ttsBufferQueue.TryDequeue(out var item))
                    {
                        if (item.Index != _currentIndex) { item.Stream.Dispose(); continue; }
                        await LoadChapterToUIAsync(item.Index);
                        uiContext.Post(_ => {
                            _currentIndex = item.Index;
                            TxtNowReading.Text = item.Text;
                            SliderProgress.Value = _currentIndex;
                            UpdateProgressUI();
                            HighlightText(item.Text);
                        }, null);
                        await PlayStreamAsync(item.Stream);
                        item.Stream.Dispose(); _currentIndex++;
                        if (_currentIndex % 10 == 0) SaveProgress(_currentFilePath, _currentIndex);
                    }
                }
            }
            finally { if (isReading) StopReading(); SaveProgress(_currentFilePath, _currentIndex); }
        }

        private void HighlightText(string text)
        {
            if (string.IsNullOrEmpty(TextInputField.Text)) return;
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

        private async Task PlayStreamAsync(MemoryStream ms)
        {
            int devIdx = 0; uiContext.Send(_ => devIdx = OutputDeviceCombo.SelectedIndex, null);
            await Task.Run(() => {
                try
                {
                    isTtsSpeaking = true;
                    using (var reader = new WaveFileReader(ms))
                    {
                        var output = new WaveOutEvent { DeviceNumber = devIdx };
                        virtualOutput = output; output.Init(reader); output.Play();
                        while (output.PlaybackState == PlaybackState.Playing && isReading) Thread.Sleep(50);
                        output.Dispose();
                    }
                }
                catch { }
                finally { Thread.Sleep(100); isTtsSpeaking = false; }
            });
        }

        #endregion

        #region UI 交互与章节选择

        private async void SliderProgress_PreviewMouseLeftButtonUp(object sender, System.Windows.Input.MouseButtonEventArgs e)
        {
            await JumpToAsync((int)SliderProgress.Value);
        }

        private async Task JumpToAsync(int index)
        {
            _currentIndex = index;
            await LoadChapterToUIAsync(_currentIndex);
            UpdateProgressUI();
            if (isReading) { StopReading(); BtnStartRead_Click(null, null); }
        }

        private void UpdateProgressUI()
        {
            int total = _chapters.Count > 0 ? (_chapters.Last().EndIndex + 1) : _currentChapterTasks.Count;
            TxtProgressLabel.Text = $"段落: {_currentIndex + 1}/{total}";
        }

        private void BtnOpenChapterSelector_Click(object sender, RoutedEventArgs e)
        {
            ChapterOverlay.Visibility = Visibility.Visible;
            TxtChapterSearch.Text = "";
            _displayChapters = _chapters.ToList();
            ChapterListBox.ItemsSource = _displayChapters;
            if (_currentChapterIdx >= 0 && _currentChapterIdx < _displayChapters.Count)
                ChapterListBox.ScrollIntoView(_displayChapters[_currentChapterIdx]);
        }

        private void TxtChapterSearch_TextChanged(object sender, TextChangedEventArgs e)
        {
            string filter = TxtChapterSearch.Text.Trim().ToLower();
            _displayChapters = string.IsNullOrEmpty(filter) ? _chapters.ToList() : _chapters.Where(c => c.FullTitle.ToLower().Contains(filter)).ToList();
            ChapterListBox.ItemsSource = _displayChapters;
        }

        private async void ChapterListBox_SelectionChanged(object sender, SelectionChangedEventArgs e)
        {
            if (ChapterListBox.SelectedItem is ChapterInfo chapter)
            {
                ChapterOverlay.Visibility = Visibility.Collapsed;
                await JumpToAsync(chapter.StartIndex);
            }
        }

        private void BtnCloseChapter_Click(object sender, RoutedEventArgs e) { ChapterOverlay.Visibility = Visibility.Collapsed; }

        #endregion

        #region 语音与引擎

        private async void InitializeEngines()
        {
            try
            {
                AppendLog("系统：初始化 SAPI5 核心驱动...");
                await Task.Run(() => {
                    if (ttsEngine != null) ttsEngine.Dispose();
                    ttsEngine = new System.Speech.Synthesis.SpeechSynthesizer();
                    var xiaoxiao = ttsEngine.GetInstalledVoices().FirstOrDefault(v => v.VoiceInfo.Name.Contains("Xiaoxiao"));
                    if (xiaoxiao != null) ttsEngine.SelectVoice(xiaoxiao.VoiceInfo.Name);
                });
                if (File.Exists("ggml-base-q5_1.bin"))
                {
                    await Task.Run(() => {
                        whisperFactory = WhisperFactory.FromPath("ggml-base-q5_1.bin");
                        whisperProcessor = whisperFactory.CreateBuilder().WithLanguage("zh").Build();
                    });
                    AppendLog("系统：实时 Whisper 引擎已就绪。");
                }
            }
            catch (Exception ex) { AppendLog($"错误：核心引导失败: {ex.Message}"); }
        }

        private void RefreshDevices()
        {
            InputDeviceCombo.Items.Clear(); OutputDeviceCombo.Items.Clear();
            for (int n = 0; n < WaveIn.DeviceCount; n++) InputDeviceCombo.Items.Add(WaveIn.GetCapabilities(n).ProductName);
            for (int n = 0; n < WaveOut.DeviceCount; n++) OutputDeviceCombo.Items.Add(WaveOut.GetCapabilities(n).ProductName);
            if (InputDeviceCombo.Items.Count > 0) InputDeviceCombo.SelectedIndex = 0;
            if (OutputDeviceCombo.Items.Count > 0) OutputDeviceCombo.SelectedIndex = 0;
        }

        private void BtnToggleListen_Click(object sender, RoutedEventArgs e)
        {
            if (!isListening)
            {
                StartListeningMode(); BtnListen.Content = "⏹ 停止对话";
                BtnListen.Background = System.Windows.Media.Brushes.IndianRed;
                isListening = true; Task.Run(() => ProcessingLoop());
            }
            else
            {
                StopListeningMode(); BtnListen.Content = "🎙️ 开启实时模式";
                BtnListen.Background = (System.Windows.Media.Brush)new System.Windows.Media.BrushConverter().ConvertFrom("#409EFF");
                isListening = false;
            }
        }

        private void StartListeningMode()
        {
            try
            {
                bool isSystem = RadioSystem.IsChecked ?? false;
                lock (bufferLock) audioBuffer.Clear();
                silenceCounter = 0;
                captureDevice = isSystem ? (IWaveIn)new WasapiLoopbackCapture() : new WaveInEvent { DeviceNumber = InputDeviceCombo.SelectedIndex, WaveFormat = new WaveFormat(16000, 1) };
                captureDevice.DataAvailable += (s, e) => {
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
            }
            catch (Exception ex) { AppendLog($"错误：录音开启失败 -> {ex.Message}"); }
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
                float sum = 0; for (int c = 0; c < channels; c++) sum += inputFloats[i * channels + c];
                monoFloats[i] = sum / channels;
            }
            if (format.SampleRate == 16000) return monoFloats;
            double ratio = (double)format.SampleRate / 16000;
            int outCount = (int)(monoCount / ratio);
            float[] result = new float[outCount];
            for (int i = 0; i < outCount; i++)
            {
                double srcIndex = i * ratio; int index1 = (int)srcIndex; int index2 = Math.Min(index1 + 1, monoCount - 1);
                double factor = srcIndex - index1; result[i] = (float)(monoFloats[index1] * (1 - factor) + monoFloats[index2] * factor);
            }
            return result;
        }

        private float CalculateRMS(float[] samples)
        {
            if (samples.Length == 0) return 0;
            float sum = 0; foreach (var s in samples) sum += s * s;
            return (float)Math.Sqrt(sum / samples.Length);
        }

        private async Task ProcessingLoop()
        {
            while (isListening)
            {
                float[] dataToProcess = null;
                lock (bufferLock)
                {
                    if (audioBuffer.Count > 16000 && (silenceCounter > 16 || audioBuffer.Count > 240000))
                    {
                        dataToProcess = audioBuffer.ToArray(); audioBuffer.Clear(); silenceCounter = 0;
                    }
                }
                if (dataToProcess != null)
                {
                    try
                    {
                        string rawResult = "";
                        var enumerator = whisperProcessor.ProcessAsync(dataToProcess).GetAsyncEnumerator();
                        try { while (await enumerator.MoveNextAsync()) rawResult += enumerator.Current.Text; }
                        finally { await enumerator.DisposeAsync(); }
                        string cleanedResult = CleanWhisperHallucinations(rawResult);
                        if (!string.IsNullOrWhiteSpace(cleanedResult))
                        {
                            uiContext.Post(_ => { TextInputField.AppendText(cleanedResult + " "); TextInputField.ScrollToEnd(); }, null);
                            await SpeakToDeviceAsync(cleanedResult);
                        }
                    }
                    catch { }
                }
                await Task.Delay(100);
            }
        }

        private async Task SpeakToDeviceAsync(string text)
        {
            if (string.IsNullOrWhiteSpace(text) || ttsEngine == null) return;
            int devIdx = 0; int rate = 0;
            uiContext.Send(_ => { devIdx = OutputDeviceCombo.SelectedIndex; rate = (int)SliderSpeed.Value; }, null);
            await Task.Run(() => {
                try
                {
                    isTtsSpeaking = true;
                    using (var ms = new MemoryStream())
                    {
                        lock (ttsEngine) { ttsEngine.Rate = rate; ttsEngine.SetOutputToWaveStream(ms); ttsEngine.Speak(text); }
                        ms.Position = 0;
                        using (var reader = new WaveFileReader(ms))
                        {
                            var output = new WaveOutEvent { DeviceNumber = devIdx };
                            virtualOutput = output; output.Init(reader); output.Play();
                            while (output.PlaybackState == PlaybackState.Playing) Thread.Sleep(50);
                            output.Dispose();
                        }
                    }
                }
                catch { }
                finally { Thread.Sleep(200); isTtsSpeaking = false; }
            });
        }

        private string CleanWhisperHallucinations(string input)
        {
            if (string.IsNullOrWhiteSpace(input)) return "";
            string cleaned = Regex.Replace(input, @"\([^\)]*\)|\[[^\]]*\]|（[^）]*）", "");
            string[] blackList = { "字幕", "谢谢", "无法解释", "音乐", "声音", "Thank", "Watching", "繁體", "廣告" };
            foreach (var word in blackList) cleaned = cleaned.Replace(word, "");
            cleaned = cleaned.Trim();
            if (cleaned.Length <= 1 || Regex.IsMatch(cleaned, @"^[^\w\s\u4e00-\u9fa5]+$")) return "";
            return cleaned;
        }

        private void StopListeningMode()
        {
            if (captureDevice != null) { captureDevice.StopRecording(); if (captureDevice is IDisposable d) d.Dispose(); captureDevice = null; }
            AppendLog("系统：实时监听停止。");
        }

        #endregion

        private void AppendLog(string message)
        {
            uiContext.Post(_ => {
                LogConsole.AppendText($"[{DateTime.Now:HH:mm:ss}] {message}\r\n");
                LogConsole.ScrollToEnd();
            }, null);
        }
    }
}