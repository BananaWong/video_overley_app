# overley

视频隐写（video steganography）桌面工具，基于 PyQt6 + OpenCV + ffmpeg。

## 运行

```bash
pip install -r requirements.txt
python main.py
```

> 需要本地可用的 `ffmpeg` / `ffprobe`（未随仓库分发，请自行安装并加入 PATH）。

## 文件

- `main.py` — PyQt6 主程序
- `video-steganography-ui.tsx` — UI 原型
- `video_steganography.spec` — PyInstaller 打包配置
- `requirements.txt` — Python 依赖
