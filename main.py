import tkinter as tk
from tkinter import ttk, filedialog, messagebox
try:
    import windnd  # 导入 windnd
    DRAG_DROP_SUPPORTED = True
except ImportError:
    DRAG_DROP_SUPPORTED = False
import os
import sys
import time
import logging
import subprocess
from pathlib import Path
import threading
from PIL import Image, ImageTk
import cv2
import shutil
from datetime import datetime
import re
import random

VIDEO_EXTENSIONS = {'.mp4', '.avi', '.mkv', '.mov', '.wmv', '.flv'}

def setup_logging():
    logs_dir = "logs"
    if not os.path.exists(logs_dir):
        os.makedirs(logs_dir)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = os.path.join(logs_dir, f"process_log_{timestamp}.txt")
    
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(message)s',
        handlers=[
            logging.FileHandler(log_file, encoding='utf-8'),
            logging.StreamHandler()
        ]
    )
    return log_file

def sanitize_filename(filename):
    filename = re.sub(r'[<>:"/\\|?*]', '_', filename)
    base, ext = os.path.splitext(filename)
    if len(filename) > 255:
        return base[:255-len(ext)] + ext
    return filename

def get_video_duration(video_path, ffmpeg_path=None):
    """使用OpenCV获取视频时长"""
    try:
        cap = cv2.VideoCapture(video_path)
        if not cap.isOpened():
            logging.error(f"无法打开视频文件: {video_path}")
            return 0
            
        fps = cap.get(cv2.CAP_PROP_FPS)
        frame_count = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
        
        if fps <= 0 or frame_count <= 0:
            logging.error(f"无效的视频参数: fps={fps}, frames={frame_count}")
            return 0
            
        duration = frame_count / fps
        cap.release()
        
        if duration > 0:
            return duration
        else:
            logging.error(f"计算得到的视频时长无效: {duration}")
            return 0
            
    except Exception as e:
        logging.error(f"获取视频时长失败: {str(e)}")
        return 0

def is_video_file(file_path):
    return Path(file_path).suffix.lower() in VIDEO_EXTENSIONS

def get_ffmpeg_path():
    current_dir = os.path.dirname(os.path.abspath(__file__))
    ffmpeg_path = os.path.join(current_dir, "ffmpeg.exe")
    
    if os.path.exists(ffmpeg_path):
        return ffmpeg_path
        
    for path in os.environ["PATH"].split(os.pathsep):
        ffmpeg_path = os.path.join(path, "ffmpeg.exe")
        if os.path.exists(ffmpeg_path):
            return ffmpeg_path
            
    return "ffmpeg"

def normalize_path(path):
    """规范化路径，处理中文和特殊字符"""
    try:
        # 确保路径是字符串类型
        if isinstance(path, bytes):
            try:
                path = path.decode('utf-8')
            except UnicodeDecodeError:
                try:
                    path = path.decode('gbk')
                except UnicodeDecodeError:
                    path = path.decode('utf-8', errors='replace')
        
        # 规范化路径分隔符
        path = os.path.normpath(path)
        
        # 处理 Windows 路径中的反斜杠
        path = path.replace('\\', '/')
        
        return path
    except Exception as e:
        logging.error(f"规范化路径失败: {str(e)}")
        return path

def ensure_directory(path):
    """确保目录存在，支持中文路径"""
    try:
        directory = os.path.dirname(path)
        if directory and not os.path.exists(directory):
            os.makedirs(directory, exist_ok=True)
        return True
    except Exception as e:
        logging.error(f"创建目录失败: {str(e)}")
        return False

def prepare_path(path, is_output=False):
    """准备路径，确保正确处理中文字符"""
    try:
        # 将路径转换为绝对路径并规范化
        abs_path = os.path.abspath(os.path.normpath(path))
        
        # 如果是输出路径，确保目录存在
        if is_output:
            output_dir = os.path.dirname(abs_path)
            os.makedirs(output_dir, exist_ok=True)
        
        # 处理中文路径
        try:
            # 对于包含中文的路径，直接使用原始路径，但确保使用正斜杠
            safe_path = abs_path.replace('\\', '/')
            
            # 检查路径是否存在
            if not os.path.exists(os.path.dirname(safe_path)):
                raise Exception(f"目录不存在: {os.path.dirname(safe_path)}")
            
            # 如果是输出路径，不检查文件是否存在
            if not is_output and not os.path.exists(safe_path):
                raise Exception(f"文件不存在: {safe_path}")
            
            # 对于包含中文的路径，不使用引号包裹
            if any(ord(c) > 127 for c in safe_path):
                return safe_path
            else:
                return f'"{safe_path}"'
            
        except Exception as e:
            logging.warning(f"处理路径失败: {str(e)}")
            # 如果处理失败，尝试使用短路径名
            try:
                import win32api
                short_path = win32api.GetShortPathName(abs_path)
                if short_path and short_path != abs_path:
                    return f'"{short_path}"'
            except Exception as e:
                logging.debug(f"获取短路径失败: {str(e)}")
            
            # 如果所有方法都失败，返回原始路径
            return f'"{path}"'
            
    except Exception as e:
        logging.error(f"处理路径出错: {str(e)}")
        return f'"{path}"'

class VideoOverlayApp:
    def __init__(self, root):
        self.root = root
        self.root.title("视频隐写工具")
        
        # 设置日志
        self.current_log_file = setup_logging()
        
        # 初始化变量
        self.main_video_paths = []  # A组视频列表
        self.overlay_video_paths = []  # B组视频列表
        self.main_video_durations = {}  # 存储A组视频时长
        self.overlay_video_durations = {}  # 存储B组视频时长
        self.output_directory = None
        self.opacity_var = tk.DoubleVar(value=2)
        self.processing = False
        self.paused = False
        self.current_processes = {}
        self.start_time = 0
        self.max_concurrent_processes = 3
        self.processing_semaphore = threading.Semaphore(self.max_concurrent_processes)
        self.use_gpu = tk.BooleanVar(value=True)  # 默认启用GPU
        
        # 获取ffmpeg路径
        self.ffmpeg_path = get_ffmpeg_path()
        
        # 创建UI布局
        self.setup_ui()
        
        # 设置文件选择功能
        self.setup_file_handlers()
        
        # 设置拖放功能
        if DRAG_DROP_SUPPORTED:
            self.setup_drag_drop()
        else:
            logging.warning("windnd 未安装，拖放功能不可用")

    def setup_file_handlers(self):
        """设置文件选择处理"""
        # 为列表框添加双击事件
        self.video_listbox.bind('<Double-Button-1>', 
                               lambda e: self.show_file_dialog(target="main"))
        self.overlay_listbox.bind('<Double-Button-1>', 
                                lambda e: self.show_file_dialog(target="overlay"))

    def show_file_dialog(self, event=None, target=None):
        """显示文件选择对话框"""
        if target is None:
            # 判断点击的是哪个列表框
            clicked_widget = event.widget if event else None
            target = None
            
            if clicked_widget == self.video_listbox:
                target = "main"
            elif clicked_widget == self.overlay_listbox:
                target = "overlay"
                
            if target is None:
                # 如果点击在其他区域，弹出选择对话框
                choice = messagebox.askquestion(
                    title="选择目标",
                    message='是否添加到主视频组(A组)？\n选择"否"则添加到覆盖视频组(B组)'
                )
                target = "main" if choice == 'yes' else "overlay"
        
        # 支持选择文件和文件夹
        choice = messagebox.askquestion(
            title="选择类型",
            message='是否选择文件夹？\n选择"否"则选择文件'
        )
        
        if choice == 'yes':
            # 选择文件夹
            folder = filedialog.askdirectory(title="选择文件夹")
            if folder:
                self.import_folder(folder, target)
        else:
            # 选择文件
            files = filedialog.askopenfilenames(
                title="选择视频文件",
                filetypes=[("视频文件", "*.mp4 *.avi *.mkv *.mov *.wmv *.flv")]
            )
            if files:
                for file in files:
                    self.add_video(file, target)

    def import_folder(self, folder_path, target):
        """导入文件夹中的视频"""
        for root, _, files in os.walk(folder_path):
            for file in files:
                file_path = os.path.join(root, file)
                if is_video_file(file_path):
                    self.add_video(file_path, target)

    def add_video(self, video_path, target):
        """添加视频到列表"""
        duration = get_video_duration(video_path, self.ffmpeg_path)
        if duration == 0:
            messagebox.showerror("错误", f"无法读取视频: {video_path}")
            return

        if target == "main":
            if video_path not in self.main_video_paths:
                self.main_video_paths.append(video_path)
                self.main_video_durations[video_path] = duration
                self.update_main_video_list()
        else:
            if video_path not in self.overlay_video_paths:
                self.overlay_video_paths.append(video_path)
                self.overlay_video_durations[video_path] = duration
                self.update_overlay_video_list()

    def get_suitable_overlay_videos(self, main_video_path):
        """获取适合的叠加视频"""
        try:
            main_duration = get_video_duration(main_video_path)
            if main_duration <= 0:
                logging.warning(f"无法获取主视频时长: {main_video_path}")
                return []
            
            logging.info(f"主视频 {os.path.basename(main_video_path)} 时长: {main_duration:.2f}秒")
            suitable_videos = []
            
            for overlay_path in self.overlay_video_paths:
                overlay_duration = get_video_duration(overlay_path)
                if overlay_duration <= 0:
                    logging.warning(f"无法获取叠加视频时长: {overlay_path}")
                    continue
                
                # 确保叠加视频时长大于主视频时长
                # 允许叠加视频最长为主视频的3倍，以避免文件过大
                min_duration = main_duration
                max_duration = main_duration * 3.0
                
                logging.debug(f"检查叠加视频 {os.path.basename(overlay_path)}: "
                             f"时长 {overlay_duration:.2f}秒, "
                             f"需要 >= {min_duration:.2f}秒")
                
                if min_duration <= overlay_duration <= max_duration:
                    suitable_videos.append(overlay_path)
                    logging.info(f"找到合适的叠加视频: {os.path.basename(overlay_path)} "
                               f"({overlay_duration:.2f}秒)")
            
            if not suitable_videos:
                logging.warning(
                    f"未找到合适的叠加视频，共检查了 {len(self.overlay_video_paths)} 个视频。"
                    f"需要时长大于 {main_duration:.2f}秒 的视频"
                )
            else:
                logging.info(f"共找到 {len(suitable_videos)} 个合适的叠加视频")
            
            return suitable_videos
            
        except Exception as e:
            logging.error(f"查找合适的叠加视频时出错: {str(e)}")
            return []

    def select_random_overlay_video(self, main_video_path):
        suitable_videos = self.get_suitable_overlay_videos(main_video_path)
        if not suitable_videos:
            return None
        return random.choice(suitable_videos)

    def setup_ui(self):
        # 创建主视频区域框架
        main_frame = ttk.LabelFrame(self.root, text="主视频")
        main_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)

        # 主视频区域按钮
        main_button_frame = ttk.Frame(main_frame)
        main_button_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 创建并存储按钮引用
        self.add_main_button = ttk.Button(main_button_frame, text="添加视频", 
                                        command=lambda: self.show_file_dialog(target="main"))
        self.add_main_button.pack(side=tk.LEFT, padx=2)
        
        self.clear_main_button = ttk.Button(main_button_frame, text="清除所选", 
                                          command=self.remove_selected_video)
        self.clear_main_button.pack(side=tk.LEFT, padx=2)
        
        self.rename_main_button = ttk.Button(main_button_frame, text="重命名选中", 
                                           command=lambda: self.rename_selected_files("main"))
        self.rename_main_button.pack(side=tk.LEFT, padx=2)
        
        self.select_all_main_button = ttk.Button(main_button_frame, text="全选", 
                                               command=lambda: self.select_all_files("main"))
        self.select_all_main_button.pack(side=tk.LEFT, padx=2)

        # 主视频列表框
        self.video_listbox = tk.Listbox(main_frame, selectmode=tk.EXTENDED)
        self.video_listbox.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # 为列表框添加文件选择功能
        self.video_listbox.bind('<Double-Button-1>', 
                               lambda e: self.show_file_dialog(target="main"))
        
        # 创建覆盖视频区域框架
        overlay_frame = ttk.LabelFrame(self.root, text="叠加视频")
        overlay_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)

        # 覆盖视频区域按钮
        overlay_button_frame = ttk.Frame(overlay_frame)
        overlay_button_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(overlay_button_frame, text="添加视频", command=lambda: self.show_file_dialog(target="overlay")).pack(side=tk.LEFT, padx=2)
        ttk.Button(overlay_button_frame, text="清除所选", command=lambda: self.remove_selected_overlay()).pack(side=tk.LEFT, padx=2)
        ttk.Button(overlay_button_frame, text="重命名选中", command=lambda: self.rename_selected_files("overlay")).pack(side=tk.LEFT, padx=2)
        ttk.Button(overlay_button_frame, text="全选", command=lambda: self.select_all_files("overlay")).pack(side=tk.LEFT, padx=2)

        # 覆盖视频列表框
        self.overlay_listbox = tk.Listbox(overlay_frame, selectmode=tk.EXTENDED)
        self.overlay_listbox.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # 为列表框添加文件选择功能
        self.overlay_listbox.bind('<Double-Button-1>', 
                                lambda e: self.show_file_dialog(target="overlay"))

        # 创建控制区域框架
        control_frame = ttk.LabelFrame(self.root, text="控制")
        control_frame.pack(side=tk.LEFT, fill=tk.BOTH, padx=5, pady=5)

        # 控制区域按钮
        control_button_frame = ttk.Frame(control_frame)
        control_button_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 存储控制按钮引用
        self.start_button = ttk.Button(control_button_frame, text="开始处理", 
                                     command=self.start_processing)
        self.start_button.pack(side=tk.LEFT, padx=2)
        
        self.pause_button = ttk.Button(control_button_frame, text="暂停", 
                                     command=self.toggle_pause)
        self.pause_button.pack(side=tk.LEFT, padx=2)
        
        self.stop_button = ttk.Button(control_button_frame, text="停止", 
                                    command=self.stop_processing)
        self.stop_button.pack(side=tk.LEFT, padx=2)
        
        # 设置按钮初始状态
        self.pause_button.configure(state="disabled")
        self.stop_button.configure(state="disabled")

        # 进度条
        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(control_frame, variable=self.progress_var, maximum=100)
        self.progress_bar.pack(fill=tk.X, padx=5, pady=5)

        # 状态标签
        self.status_label = ttk.Label(control_frame, text="就绪")
        self.status_label.pack(padx=5, pady=5)

        # 时间标签
        self.time_label = ttk.Label(control_frame, text="预计剩余时间: --:--")
        self.time_label.pack(padx=5, pady=5)

        # 添加不透明度控制
        opacity_frame = ttk.Frame(control_frame)
        opacity_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(opacity_frame, text="不透明度:").pack(side=tk.LEFT)
        self.opacity_scale = ttk.Scale(opacity_frame, 
                                     from_=1, 
                                     to=15,
                                     orient="horizontal",
                                     variable=self.opacity_var,
                                     command=self.update_opacity_label)
        self.opacity_scale.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.opacity_label = ttk.Label(opacity_frame, text="2%")
        self.opacity_label.pack(side=tk.LEFT)
        
        # 添加输出目录选择
        output_frame = ttk.Frame(control_frame)
        output_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(output_frame, text="选择输出目录", 
                  command=self.select_output_directory).pack(side=tk.LEFT, padx=5)
        self.output_dir_label = ttk.Label(output_frame, text="默认: 主视频目录/output")
        self.output_dir_label.pack(side=tk.LEFT, padx=5)

        # 在控制面板添加GPU选项
        gpu_frame = ttk.Frame(control_frame)
        gpu_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Checkbutton(gpu_frame, 
                        text="使用GPU加速", 
                        variable=self.use_gpu).pack(side=tk.LEFT)

        # 设置样式
        style = ttk.Style()
        style.theme_use('clam')

    def select_all_files(self, target):
        if target == "main":
            listbox = self.video_listbox
        else:
            listbox = self.overlay_listbox
        listbox.select_set(0, tk.END)

    def rename_selected_files(self, target):
        if target == "main":
            listbox = self.video_listbox
            paths = self.main_video_paths
            durations = self.main_video_durations
            prefix = "Main"  
        else:
            listbox = self.overlay_listbox
            paths = self.overlay_video_paths
            durations = self.overlay_video_durations
            prefix = f"video_{target}"
            
        selected = listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择要重命名的文件")
            return
            
        try:
            first_file = paths[selected[0]]
            target_dir = os.path.dirname(first_file)
            
            renamed_paths = {}  
            for i, index in enumerate(selected):
                old_path = paths[index]
                ext = os.path.splitext(old_path)[1]
                new_filename = f"{prefix}_{i+1:03d}{ext}"
                new_path = os.path.normpath(os.path.join(target_dir, new_filename))
                
                base_path = new_path
                counter = 1
                while os.path.exists(new_path):
                    base_name = os.path.splitext(base_path)[0]
                    new_path = os.path.normpath(f"{base_name}_{counter:03d}{ext}")
                    counter += 1
                
                shutil.move(old_path, new_path)
                renamed_paths[old_path] = new_path
                logging.info(f"重命名文件: {old_path} -> {new_path}")
            
            for i, path in enumerate(paths):
                if path in renamed_paths:
                    new_path = renamed_paths[path]
                    paths[i] = new_path
                    if target == "main":
                        self.main_video_durations[new_path] = durations[path]
                        del self.main_video_durations[path]
                    else:
                        self.overlay_video_durations[new_path] = durations[path]
                        del self.overlay_video_durations[path]
            
            self.update_main_video_list() if target == "main" else self.update_overlay_video_list()
            
            messagebox.showinfo("成功", "文件重命名完成")
            
        except Exception as e:
            error_msg = f"重命名文件失败: {str(e)}"
            logging.error(error_msg)
            messagebox.showerror("错误", error_msg)
            
    def update_opacity_label(self, *args):
        value = int(self.opacity_var.get())  
        self.opacity_var.set(value)  
        self.opacity_label.configure(text=f"{value}%")
        
    def get_video_preview(self, video_path, size=(200, 120)):
        try:
            cap = cv2.VideoCapture(video_path)
            if not cap.isOpened():
                return None
                
            ret, frame = cap.read()
            cap.release()
            
            if not ret:
                return None
                
            frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            frame_resized = cv2.resize(frame_rgb, size)
            image = Image.fromarray(frame_resized)
            return ImageTk.PhotoImage(image)
        except Exception as e:
            print(f"获取预览图失败: {str(e)}")
            return None
        
    def start_processing(self):
        """开始处理视频"""
        if not self.main_video_paths:
            messagebox.showwarning("警告", "请先添加主视频")
            return
        if not self.overlay_video_paths:
            messagebox.showwarning("警告", "请先添加叠加视频")
            return
        
        try:
            self.processing = True
            self.paused = False
            self.start_time = time.time()
            self.update_buttons_state()  # 立即更新按钮状态
            
            # 启动处理线程
            processing_thread = threading.Thread(
                target=self._process_videos_thread,
                daemon=True
            )
            processing_thread.start()
            
        except Exception as e:
            self.processing = False
            logging.error(f"启动处理时出错: {str(e)}")
            messagebox.showerror("错误", f"启动处理时出错: {str(e)}")
            self.update_buttons_state()

    def get_video_dimensions(self, video_path):
        probe_cmd = [
            self.ffmpeg_path,
            "-i", video_path,
            "-v", "quiet",
            "-select_streams", "v:0",
            "-show_entries", "stream=width,height",
            "-of", "default=noprint_wrappers=1:nokey=1"
        ]
        
        try:
            result = subprocess.run(probe_cmd, 
                                  capture_output=True, 
                                  text=True,
                                  creationflags=subprocess.CREATE_NO_WINDOW)
            if result.stdout.strip():
                width, height = map(int, result.stdout.strip().split('\n'))
                logging.info(f"使用ffmpeg获取视频尺寸成功: {width}x{height}")
                return width, height
        except Exception as e:
            logging.warning(f"使用ffmpeg获取视频尺寸失败: {str(e)}")
        
        try:
            cap = cv2.VideoCapture(video_path)
            if not cap.isOpened():
                raise Exception("无法打开视频文件")
            
            width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
            height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
            cap.release()
            
            if width > 0 and height > 0:
                logging.info(f"使用OpenCV获取视频尺寸成功: {width}x{height}")
                return width, height
            else:
                raise Exception("获取到的尺寸无效")
        except Exception as e:
            logging.warning(f"使用OpenCV获取视频尺寸失败: {str(e)}")
        
        return None, None

    def process_video(self, main_video_path, overlay_video_path, total_videos, processed_count):
        try:
            with self.processing_semaphore:
                if not self.processing:
                    return
                    
                # 更新进度
                progress = (processed_count / total_videos) * 100 if total_videos > 0 else 0
                self.progress_var.set(progress)
                self.status_label.configure(
                    text=f"处理中... ({processed_count}/{total_videos})"
                )
                
                # 计算剩余时间
                elapsed_time = time.time() - self.start_time
                if processed_count > 0:  # 修改条件，避免除零
                    avg_time_per_video = elapsed_time / processed_count
                    remaining_videos = total_videos - processed_count
                    remaining_time = avg_time_per_video * remaining_videos
                    remaining_mins = int(remaining_time // 60)
                    remaining_secs = int(remaining_time % 60)
                    self.time_label.configure(text=f"预计剩余时间: {remaining_mins:02d}:{remaining_secs:02d}")
                
                if self.output_directory and os.path.exists(self.output_directory):
                    output_dir = self.output_directory
                else:
                    output_dir = os.path.join(os.path.dirname(main_video_path), "output")
                
                try:
                    os.makedirs(output_dir, exist_ok=True)
                except Exception as e:
                    logging.error(f"创建输出目录失败: {str(e)}")
                    raise
                
                main_video_name = os.path.splitext(os.path.basename(main_video_path))[0]
                overlay_name = os.path.splitext(os.path.basename(overlay_video_path))[0]
                output_name = f"output_{main_video_name}_C_{overlay_name}.mp4"
                output_path = os.path.join(output_dir, sanitize_filename(output_name))
                
                # 处理输入和输出路径，确保正确处理中文
                try:
                    main_video_path = main_video_path.encode('utf-8').decode('utf-8')
                    overlay_video_path = overlay_video_path.encode('utf-8').decode('utf-8')
                    output_path = output_path.encode('utf-8').decode('utf-8')
                except UnicodeError as e:
                    logging.error(f"路径编码转换失败: {str(e)}")
                    raise
                
                # 规范化路径
                main_video_path = normalize_path(main_video_path)
                overlay_video_path = normalize_path(overlay_video_path)
                output_path = normalize_path(output_path)
                
                # 确保输出目录存在
                if not ensure_directory(output_path):
                    raise Exception(f"无法创建输出目录: {os.path.dirname(output_path)}")
                
                # 准备路径，不使用引号包裹
                main_video_path_safe = main_video_path
                overlay_video_path_safe = overlay_video_path
                output_path_safe = output_path
                
                # 记录实际使用的路径
                logging.info(f"处理视频:")
                logging.info(f"主视频: {main_video_path} -> {main_video_path_safe}")
                logging.info(f"叠加视频: {overlay_video_path} -> {overlay_video_path_safe}")
                logging.info(f"输出文件: {output_path} -> {output_path_safe}")
                
                # 获取视频尺寸
                width, height = self.get_video_dimensions(main_video_path)
                if not width or not height:
                    raise Exception(f"无法获取视频尺寸: {main_video_path}")
                
                # 检查GPU支持并设置编码器
                gpu_type = None
                if self.use_gpu.get():
                    gpu_type = self.check_gpu_support()
                    if gpu_type:
                        logging.info(f"使用 {gpu_type} GPU加速处理视频")
                    else:
                        logging.warning("GPU加速不可用，将使用CPU处理")
                
                # 根据GPU类型设置编码器和参数
                if gpu_type == "NVIDIA":
                    video_encoder = 'h264_nvenc'
                    encoder_preset = 'p1'
                    gpu_params = [
                        "-rc", "vbr",
                        "-b:v", "8M",
                        "-maxrate", "12M",
                        "-bufsize", "16M",
                        "-profile:v", "high",
                        "-level", "5.2",
                        "-spatial-aq", "1",
                        "-temporal-aq", "1",
                        "-cq", "16",
                        "-qmin", "1",
                        "-qmax", "51",
                        "-rc-lookahead", "32"
                    ]
                elif gpu_type == "AMD":
                    video_encoder = 'h264_amf'
                    encoder_preset = 'quality'
                    gpu_params = [
                        "-quality", "quality",
                        "-rc", "vbr_peak",
                        "-b:v", "8M",
                        "-maxrate", "12M",
                        "-bufsize", "16M",
                        "-profile:v", "high",
                        "-qmin", "1",
                        "-qmax", "51"
                    ]
                else:
                    video_encoder = 'libx264'
                    encoder_preset = 'slower'
                    gpu_params = [
                        "-b:v", "8M",
                        "-maxrate", "12M",
                        "-bufsize", "16M",
                        "-profile:v", "high",
                        "-level", "5.2",
                        "-movflags", "+faststart",
                        "-tune", "film",
                        "-x264opts", "me=umh:subme=10:ref=5:b-adapt=2:direct=auto:rc-lookahead=60:no-fast-pskip=1:no-dct-decimate=1",
                        "-psy-rd", "1.0:0.15"
                    ]
                
                if width and height:
                    # 构建基本的 filter_complex 字符串
                    filter_str = (
                        f"[1:v]scale={width}:{height}[scaled];"
                        f"[scaled]format=rgba,colorchannelmixer=aa={self.opacity_var.get()/100.0}[overlay];"
                        "[0:v]format=rgba[base];"
                        "[base][overlay]overlay=0:0:shortest=1[outv]"
                    )
                    
                    # 构建命令
                    command = [
                        self.ffmpeg_path,
                        "-y",
                        "-hwaccel", "auto" if gpu_type else "none",
                        "-i", main_video_path_safe,  # 移除引号
                        "-i", overlay_video_path_safe,  # 移除引号
                        "-filter_complex", filter_str,
                        "-map", "[outv]",
                        "-map", "0:a",
                        "-c:a", "aac",
                        "-b:a", "320k",
                        "-ar", "48000",
                        "-c:v", video_encoder,
                        "-preset", encoder_preset,
                        "-shortest"
                    ]
                    
                    # 添加编码器特定参数
                    command.extend(gpu_params)
                    
                    # 添加输出路径
                    command.append(output_path_safe)  # 移除引号
                    
                    # 记录完整命令
                    cmd_str = ' '.join(str(x) for x in command)
                    logging.info(f"执行命令: {cmd_str}")
                    
                    # 执行命令并实时捕获输出
                    process = subprocess.Popen(
                        command,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        universal_newlines=True,
                        creationflags=subprocess.CREATE_NO_WINDOW,
                        bufsize=8192
                    )
                    
                    process_key = f"{main_video_path}_{overlay_video_path}"
                    self.current_processes[process_key] = process
                    
                    try:
                        # 收集所有错误输出
                        error_output = []
                        
                        # 改进进程监控
                        while process.poll() is None:
                            if not self.processing:
                                process.terminate()
                                try:
                                    process.wait(timeout=5)
                                except subprocess.TimeoutExpired:
                                    process.kill()
                                logging.info(f"终止进程: {process_key}")
                                break
                            
                            if self.paused:
                                time.sleep(0.1)
                                continue
                            
                            # 读取输出
                            stderr_line = process.stderr.readline()
                            if stderr_line:
                                stderr_line = stderr_line.strip()
                                if stderr_line:  # 只记录非空行
                                    error_output.append(stderr_line)
                                    logging.debug(f"FFmpeg输出: {stderr_line}")
                        
                        # 检查进程结果
                        if process.returncode != 0:
                            stderr = process.stderr.read()
                            if stderr:
                                error_output.append(stderr.strip())
                            error_msg = "\n".join(error_output)
                            logging.error(f"FFmpeg处理失败: {error_msg}")
                            raise Exception(f"FFmpeg处理失败: {error_msg}")
                        
                    finally:
                        # 确保关闭所有文件句柄
                        if process.stdout:
                            process.stdout.close()
                        if process.stderr:
                            process.stderr.close()
                        process.wait()
                        
                        # 从当前进程列表中移除
                        if process_key in self.current_processes:
                            del self.current_processes[process_key]
                    
                    # 等待一小段时间确保文件写入完成
                    time.sleep(1.0)
                    
                    # 验证输出文件
                    if not os.path.exists(output_path):
                        error_msg = "\n".join(error_output) if error_output else "未知错误"
                        logging.error(f"输出路径: {output_path}")
                        logging.error(f"输出目录内容: {os.listdir(os.path.dirname(output_path))}")
                        logging.error(f"FFmpeg错误输出: {error_msg}")
                        raise Exception(f"输出文件未生成。FFmpeg错误: {error_msg}")
                    
                    if os.path.getsize(output_path) == 0:
                        error_msg = "\n".join(error_output) if error_output else "未知错误"
                        try:
                            os.remove(output_path)
                        except:
                            pass
                        raise Exception(f"输出文件大小为0。FFmpeg错误: {error_msg}")
                    
                    logging.info(f"视频处理完成: {output_path}")
                    
        except Exception as e:
            # 如果处理失败，尝试清理可能存在的不完整输出文件
            try:
                if os.path.exists(output_path):
                    os.remove(output_path)
            except:
                pass
            logging.error(f"处理视频时出错: {str(e)}")
            raise
        finally:
            # 清理进程引用
            if process_key in self.current_processes:
                del self.current_processes[process_key]

    def _process_videos_thread(self):
        try:
            total_videos = len(self.main_video_paths)
            processed_count = 0
            threads = []
            
            for main_video_path in self.main_video_paths:
                if not self.processing:
                    break
                
                if not os.path.exists(main_video_path):
                    logging.error(f"找不到主视频文件: {main_video_path}")
                    messagebox.showerror("错误", f"找不到主视频文件: {main_video_path}")
                    continue
                
                suitable_videos = self.get_suitable_overlay_videos(main_video_path)
                if not suitable_videos:
                    logging.warning(f"没有找到合适的混淆视频: {main_video_path}，跳过处理")
                    continue
                    
                overlay_video_path = random.choice(suitable_videos)
                
                thread = threading.Thread(
                    target=self.process_video,
                    args=(main_video_path, overlay_video_path, total_videos, processed_count),
                    daemon=True
                )
                threads.append(thread)
                thread.start()
                
                # 更新进度
                processed_count += 1
                self.update_progress(processed_count, total_videos)
            
                # 等待线程完成
                thread.join()
            
            if self.processing:
                messagebox.showinfo("完成", "所有视频处理完成")
            
        except Exception as e:
            logging.error(f"处理视频时出错: {str(e)}")
            messagebox.showerror("错误", f"处理视频时出错: {str(e)}")
        
        finally:
            self.processing = False
            self.current_processes.clear()
            self.progress_var.set(0)
            self.status_label.configure(text="就绪")
            self.time_label.configure(text="预计剩余时间: --:--")
            self.update_buttons_state()
            
    def stop_processing(self):
        """停止所有视频处理"""
        if not self.processing:
            return
            
        try:
            # 设置停止标志
            self.processing = False
            logging.info("正在停止所有处理...")
            
            # 终止所有进程
            for process_key, process in list(self.current_processes.items()):
                try:
                    if process and process.poll() is None:
                        process.terminate()
                        try:
                            process.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            process.kill()
                        logging.info(f"终止进程: {process_key}")
                except Exception as e:
                    logging.error(f"终止进程时出错 {process_key}: {str(e)}")
            
            # 清理
            self.current_processes.clear()
            self.progress_var.set(0)
            self.status_label.configure(text="已停止")
            self.time_label.configure(text="预计剩余时间: --:--")
            self.update_buttons_state()
            
            # 重置处理状态
            self.paused = False
            self.pause_button.configure(text="暂停")
            
        except Exception as e:
            logging.error(f"停止处理时出错: {str(e)}")
            messagebox.showerror("错误", f"停止处理时出错: {str(e)}")

    def toggle_pause(self):
        """切换暂停/继续状态"""
        try:
            if not self.processing:
                return
            
            self.paused = not self.paused
            status = "已暂停" if self.paused else "处理中"
            button_text = "继续" if self.paused else "暂停"
            
            self.pause_button.configure(text=button_text)
            self.status_label.configure(text=status)
            logging.info(f"处理{status}")
            
        except Exception as e:
            logging.error(f"切换暂停状态时出错: {str(e)}")
            messagebox.showerror("错误", f"切换暂停状态时出错: {str(e)}")

    def update_buttons_state(self):
        """更新按钮状态"""
        try:
            if self.processing:
                self.start_button.configure(state="disabled")
                self.pause_button.configure(state="normal")
                self.stop_button.configure(state="normal")
                # 禁用设置选项
                self.opacity_scale.configure(state="disabled")
                self.use_gpu.set(self.use_gpu.get())  # 锁定当前值
                for widget in self.root.winfo_children():
                    if isinstance(widget, ttk.Checkbutton):
                        widget.configure(state="disabled")
            else:
                self.start_button.configure(state="normal")
                self.pause_button.configure(state="disabled")
                self.stop_button.configure(state="disabled")
                # 启用设置选项
                self.opacity_scale.configure(state="normal")
                for widget in self.root.winfo_children():
                    if isinstance(widget, ttk.Checkbutton):
                        widget.configure(state="normal")
            
            # 强制更新UI
            self.root.update()
            
        except Exception as e:
            logging.error(f"更新按钮状态时出错: {str(e)}")

    def update_main_video_list(self):
        self.video_listbox.delete(0, tk.END)
        for path in self.main_video_paths:
            if path in self.main_video_durations:
                duration = self.main_video_durations[path]
                filename = os.path.basename(path)
                self.video_listbox.insert(tk.END, f"{filename} ({duration:.1f}秒)")
            else:
                logging.warning(f"找不到视频时长: {path}")
                filename = os.path.basename(path)
                self.video_listbox.insert(tk.END, f"{filename}")

    def update_overlay_video_list(self):
        self.overlay_listbox.delete(0, tk.END)
        for path in self.overlay_video_paths:
            if path in self.overlay_video_durations:
                duration = self.overlay_video_durations[path]
                filename = os.path.basename(path)
                self.overlay_listbox.insert(tk.END, f"{filename} ({duration:.1f}秒)")
            else:
                logging.warning(f"找不到视频时长: {path}")
                filename = os.path.basename(path)
                self.overlay_listbox.insert(tk.END, f"{filename}")

    def remove_selected_video(self):
        selected = self.video_listbox.curselection()
        for index in reversed(selected):
            self.video_listbox.delete(index)
            self.main_video_paths.pop(index)
            
    def remove_selected_overlay(self):
        selected = self.overlay_listbox.curselection()
        if not selected:
            messagebox.showwarning("警告", "请先选择要移除的视频")
            return
            
        for index in reversed(selected):
            path = self.overlay_video_paths[index]
            if path in self.overlay_video_durations:
                del self.overlay_video_durations[path]
            del self.overlay_video_paths[index]
            
        self.update_overlay_video_list()

    def select_overlay_video(self):
        filename = filedialog.askopenfilename(filetypes=[("视频文件", "*.mp4 *.avi *.mkv")])
        if filename:
            self.overlay_video_path = filename
            
            self.overlay_preview = self.get_video_preview(filename)
            if self.overlay_preview:
                self.overlay_preview_label.configure(image=self.overlay_preview)
                
    def select_output_directory(self):
        directory = filedialog.askdirectory()
        if directory:
            self.output_directory = directory
            self.output_dir_label.configure(text=f"当前: {directory}")
            logging.info(f"设置输出目录: {directory}")

    def validate_video_file(self, video_path):
        try:
            cap = cv2.VideoCapture(video_path)
            if not cap.isOpened():
                raise Exception("无法打开视频文件")
            
            ret, frame = cap.read()
            cap.release()
            
            if not ret:
                raise Exception("无法读取视频帧")
            
            return True
        except Exception as e:
            logging.error(f"视频文件验证失败 {video_path}: {str(e)}")
            return False

    def update_progress(self, processed_count, total_videos):
        """更新进度和预计时间"""
        if not self.processing:
            return
        
        # 更新进度条
        progress = (processed_count / total_videos) * 100 if total_videos > 0 else 0
        self.progress_var.set(progress)
        self.status_label.configure(text=f"处理中... ({processed_count}/{total_videos})")
        
        # 计算剩余时间
        elapsed_time = time.time() - self.start_time
        if processed_count > 0:  # 修改条件，避免除零
            avg_time_per_video = elapsed_time / processed_count
            remaining_videos = total_videos - processed_count
            remaining_time = avg_time_per_video * remaining_videos
            remaining_mins = int(remaining_time // 60)
            remaining_secs = int(remaining_time % 60)
            self.time_label.configure(text=f"预计剩余时间: {remaining_mins:02d}:{remaining_secs:02d}")

    def check_gpu_support(self):
        """检查GPU加速支持情况"""
        try:
            cmd = [
                self.ffmpeg_path,
                "-hide_banner",
                "-encoders"
            ]
            result = subprocess.run(cmd, 
                                  capture_output=True, 
                                  text=True, 
                                  creationflags=subprocess.CREATE_NO_WINDOW)
            
            encoders = result.stdout
            gpu_type = None
            
            # 检查 NVIDIA NVENC
            if 'h264_nvenc' in encoders:
                test_cmd = [
                    self.ffmpeg_path,
                    "-hide_banner",
                    "-f", "lavfi",
                    "-i", "color=black:s=1280x720:r=30",
                    "-t", "1",
                    "-c:v", "h264_nvenc",
                    "-f", "null",
                    "-"
                ]
                if subprocess.run(test_cmd, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW).returncode == 0:
                    gpu_type = "NVIDIA"
                    logging.info("NVIDIA GPU加速可用")
            
            # 检查 AMD AMF
            if not gpu_type and 'h264_amf' in encoders:
                test_cmd = [
                    self.ffmpeg_path,
                    "-hide_banner",
                    "-f", "lavfi",
                    "-i", "color=black:s=1280x720:r=30",
                    "-t", "1",
                    "-c:v", "h264_amf",
                    "-f", "null",
                    "-"
                ]
                if subprocess.run(test_cmd, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW).returncode == 0:
                    gpu_type = "AMD"
                    logging.info("AMD GPU加速可用")
            
            return gpu_type
            
        except Exception as e:
            logging.warning(f"检查GPU支持时出错: {str(e)}")
            return None

    def setup_drag_drop(self):
        """设置拖放功能"""
        def handle_files(files, target_type):
            for file_path in files:
                # 将 bytes 转换为 str
                if isinstance(file_path, bytes):
                    try:
                        file_path = file_path.decode('gbk')  # Windows 中文系统使用 GBK 编码
                    except UnicodeDecodeError:
                        try:
                            file_path = file_path.decode('utf-8')  # 尝试 UTF-8
                        except UnicodeDecodeError:
                            logging.error(f"无法解码文件路径: {file_path}")
                            continue

                if os.path.isdir(file_path):
                    self.import_folder(file_path, target_type)
                elif is_video_file(file_path):
                    self.add_video(file_path, target_type)

        # 为主视频列表框添加拖放功能
        windnd.hook_dropfiles(self.video_listbox, 
                            func=lambda files: handle_files(files, "main"))

        # 为叠加视频列表框添加拖放功能
        windnd.hook_dropfiles(self.overlay_listbox, 
                            func=lambda files: handle_files(files, "overlay"))

        # 为窗口添加拖放功能
        def handle_window_drop(files):
            if messagebox.askyesno(
                title="选择目标",
                message='是否添加到主视频组(A组)？\n选择"否"则添加到叠加视频组(B组)'
            ):
                handle_files(files, "main")
            else:
                handle_files(files, "overlay")

        windnd.hook_dropfiles(self.root, func=handle_window_drop)
            
if __name__ == "__main__":
    root = tk.Tk()
    app = VideoOverlayApp(root)
    root.mainloop()
