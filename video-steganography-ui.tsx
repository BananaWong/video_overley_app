import React, { useState } from 'react';
import { Upload, Play, Pause, Square, SlidersHorizontal, Info } from "lucide-react";

const VideoSteganographyUI = () => {
  const [opacity, setOpacity] = useState(50);
  const [progress, setProgress] = useState(0);
  const [customRatio, setCustomRatio] = useState(false);
  const [ratioWidth, setRatioWidth] = useState(16);
  const [ratioHeight, setRatioHeight] = useState(9);

  return (
    <div className="flex flex-col h-screen bg-gray-100 p-4 gap-4">
      {/* 顶部标题 */}
      <div className="text-2xl font-bold text-center bg-white p-4 rounded-lg shadow">
        视频隐写工具
      </div>
      
      {/* 主要内容区域 */}
      <div className="flex flex-1 gap-4">
        {/* 左侧 - 主视频区域 */}
        <div className="flex flex-col w-1/3 bg-white rounded-lg shadow p-4">
          <div className="flex justify-between items-center mb-4">
            <h2 className="text-lg font-semibold">主视频</h2>
            <div className="flex gap-2">
              <button className="bg-blue-500 text-white px-3 py-1 rounded-md flex items-center gap-1">
                <Upload size={16} />
                添加
              </button>
              <button className="bg-gray-500 text-white px-3 py-1 rounded-md">
                清空
              </button>
            </div>
          </div>
          
          {/* 视频列表 */}
          <div className="flex-1 border rounded-lg p-2 overflow-y-auto">
            <div className="hover:bg-gray-100 p-2 cursor-pointer">video1.mp4</div>
            <div className="hover:bg-gray-100 p-2 cursor-pointer">video2.mp4</div>
          </div>

          {/* 批量重命名 */}
          <div className="mt-4">
            <button className="w-full bg-blue-500 text-white py-2 rounded-md text-sm">
              批量重命名 (main_001, main_002, ...)
            </button>
          </div>
        </div>
        
        {/* 中间 - 叠加视频区域 */}
        <div className="flex flex-col w-1/3 bg-white rounded-lg shadow p-4">
          <div className="flex justify-between items-center mb-4">
            <h2 className="text-lg font-semibold">叠加视频</h2>
            <div className="flex gap-2">
              <button className="bg-blue-500 text-white px-3 py-1 rounded-md flex items-center gap-1">
                <Upload size={16} />
                添加
              </button>
              <button className="bg-gray-500 text-white px-3 py-1 rounded-md">
                清空
              </button>
            </div>
          </div>
          
          {/* 视频列表 */}
          <div className="flex-1 border rounded-lg p-2 overflow-y-auto">
            <div className="hover:bg-gray-100 p-2 cursor-pointer">overlay1.mp4</div>
            <div className="hover:bg-gray-100 p-2 cursor-pointer">overlay2.mp4</div>
          </div>

          {/* 批量重命名 */}
          <div className="mt-4">
            <button className="w-full bg-blue-500 text-white py-2 rounded-md text-sm">
              批量重命名 (overlay_001, overlay_002, ...)
            </button>
          </div>
        </div>
        
        {/* 右侧 - 控制面板 */}
        <div className="w-1/3 flex flex-col gap-4">
          {/* 输出设置 */}
          <div className="bg-white rounded-lg shadow p-4">
            <h2 className="text-lg font-semibold mb-4">输出设置</h2>
            
            <div className="space-y-4">
              {/* 输出比例 */}
              <div>
                <div className="flex items-center justify-between mb-2">
                  <label className="text-sm font-medium">输出比例</label>
                  <div className="flex items-center gap-2">
                    <input 
                      type="checkbox" 
                      checked={customRatio}
                      onChange={(e) => setCustomRatio(e.target.checked)}
                      className="rounded"
                    />
                    <span className="text-sm">自定义比例</span>
                  </div>
                </div>
                
                {!customRatio ? (
                  <select className="w-full border rounded-md p-2">
                    <option>16:9</option>
                    <option>4:3</option>
                    <option>1:1</option>
                  </select>
                ) : (
                  <div className="flex items-center gap-2">
                    <input
                      type="number"
                      value={ratioWidth}
                      onChange={(e) => setRatioWidth(Number(e.target.value))}
                      className="w-20 border rounded-md p-2"
                    />
                    <span>:</span>
                    <input
                      type="number"
                      value={ratioHeight}
                      onChange={(e) => setRatioHeight(Number(e.target.value))}
                      className="w-20 border rounded-md p-2"
                    />
                  </div>
                )}
              </div>

              {/* 效果预览 */}
              <div>
                <label className="block text-sm font-medium mb-2">效果预览</label>
                <div className="aspect-video bg-gray-200 rounded-lg flex items-center justify-center">
                  <span className="text-gray-500">预览区域</span>
                </div>
              </div>
              
              {/* 不透明度 */}
              <div>
                <label className="block text-sm font-medium mb-1">
                  不透明度: {opacity}%
                </label>
                <div className="flex items-center gap-2">
                  <SlidersHorizontal size={16} />
                  <input
                    type="range"
                    min="0"
                    max="100"
                    value={opacity}
                    onChange={(e) => setOpacity(Number(e.target.value))}
                    className="w-full"
                  />
                </div>
              </div>
              
              {/* GPU加速 */}
              <div className="flex items-center gap-2">
                <input type="checkbox" className="rounded" />
                <label className="text-sm font-medium">启用GPU加速</label>
              </div>
              
              {/* 输出质量 */}
              <div>
                <div className="flex items-center gap-1 mb-1">
                  <label className="block text-sm font-medium">输出质量</label>
                  <Info size={16} className="text-gray-400 cursor-help" title="不同质量设置的说明"/>
                </div>
                <select className="w-full border rounded-md p-2 mb-2">
                  <option value="high">高质量 (低速)</option>
                  <option value="balanced">平衡 (推荐)</option>
                  <option value="fast">快速 (低质量)</option>
                </select>
                <div className="text-xs text-gray-500 bg-gray-50 p-2 rounded">
                  <div className="mb-1">• 高质量：两遍编码，低码率高质量，文件较小</div>
                  <div className="mb-1">• 平衡：单遍编码，中等码率和质量</div>
                  <div>• 快速：单遍编码，高码率，处理速度快</div>
                </div>
              </div>
              
              {/* 输出目录 */}
              <button className="w-full bg-gray-100 hover:bg-gray-200 py-2 rounded-md">
                选择输出目录
              </button>
            </div>
          </div>
          
          {/* 处理控制 */}
          <div className="bg-white rounded-lg shadow p-4">
            <h2 className="text-lg font-semibold mb-4">处理控制</h2>
            
            {/* 控制按钮 */}
            <div className="flex gap-2 mb-4">
              <button className="flex-1 bg-green-500 text-white py-2 rounded-md flex items-center justify-center gap-1">
                <Play size={16} />
                开始
              </button>
              <button className="flex-1 bg-yellow-500 text-white py-2 rounded-md flex items-center justify-center gap-1">
                <Pause size={16} />
                暂停
              </button>
              <button className="flex-1 bg-red-500 text-white py-2 rounded-md flex items-center justify-center gap-1">
                <Square size={16} />
                停止
              </button>
            </div>
            
            {/* 进度条 */}
            <div className="mb-2">
              <div className="w-full bg-gray-200 rounded-full h-2.5">
                <div 
                  className="bg-blue-500 h-2.5 rounded-full transition-all duration-300"
                  style={{ width: `${progress}%` }}
                ></div>
              </div>
            </div>
            
            {/* 剩余时间 */}
            <div className="text-center text-sm text-gray-600">
              预计剩余时间: 10:30
            </div>
          </div>
        </div>
      </div>
    </div>
  );
};

export default VideoSteganographyUI;