# SCD v2 —— 序与速率

旧版 Scale-Coupled Dynamics（`archive/scd-v1`，tag `scd-v1-final`）已推倒重写。
旧版的物理思想、逐条判定和教训在 [`notes/scd-v1-physical-ideas.md`](notes/scd-v1-physical-ideas.md)。

## 论点
**尺度 = 两个过程之间的对数速率比。** 原始概念有两个：事件之间的因果**序**和过程的**速率**。
因果序在束缚区把速率比定死（结构事实），在同步无标度区把它留作全局隐藏参数（切片、标架）。
能量 = 速率，所以"能标"与"尺度"是同一个类型的量。

不在全局粘合之下思考（见同作者的 [`reference/pzfc-preprint.tex`](reference/pzfc-preprint.tex)）：
没有预设的全局事件集、全局时间、全局 σ 场或全局态；它们只在可合并的区域作为**结论**出现。

## 现状
十八条结果（其中 F6、F11–F13 为条件性）（[`docs/findings.md`](docs/findings.md)）：
- **F1** 束缚观察者的相对钟速由因果序唯一决定（红移、束缚运动的时间膨胀）；
- **F2** 退行的两个观察者：Doppler 因子是结构，时间膨胀不是；未定速率恰好铺满 `(e^{−η}, e^{η})`，由标架快度参数化；
- **F3** FRW：宇宙时由因果序决定 ⟺ 减速膨胀；Milne 是临界点；
- **F4** 多个观察者：隐藏参数是渐近切片（多指时间），惯性标架是其中的线性特例；
- **F5** 坦白：这些速率论断在数学上归结为窗口几何，价值在对应关系；
- **F6**（条件性）只用撒点因果集的序数据，以上图谱依然成立；
- **F7** 把 p-ZFC 的记录系统实现为因果过去：汇合（S4.2 的 .2）⟺ 无事件视界；刚性 ⟹ 汇合；减速 / Milne / 加速恰好是三层；
- **F8** 加速宇宙里，事件族能否被一并记录 = 视界足迹的神经：由 d+1 元组决定（Helly），只允许 d-Leray 模式（Wegner）；
- **F9** 1+1 维的视界覆盖总是 α-无环，局部一致的记录总能粘合；d ≥ 2 不一定；
- **F10** 分辨率 = 民主粗粒化：速率比不随分辨率跑动，内容跑动；分辨尺度为 W 的结构需要密度约 1/W（内禀版的"能标 × 尺度 ≈ 1"）；
- **F11**（条件性）最长链过程的可区分性阈值 ρ ≳ T⁴/d⁶（数据塌缩）；
- **F12**（条件性）3+1 维最长链横向涨落指数约 0.6；**假如**存在普朗克最细层，单链轨迹每秒会有纳米级偏离，观测反过来不利于这种最细层；
- **F13**（条件性）由过去决定的单链过程涨落量级相同。

- **F14** σ 的局部读法：束缚对的速率比 = 互窗口之比（两座钟互相雷达测距的读数之比 = 红移因子，纯序恒等式）。

- **F15** 分辨率改为分块（D18）：连续极限由鞅收敛保证；σ 由份额承载、不跑动；结构逐渐显现（对应形状因子）；纯几何只给幂律型的分辨率依赖。

- **F16** 纯几何的未分辨份额 = 4·(簇尺度/窗口)，指数 1.000：对数型跑动只能来自多尺度内容；
- **F17** 规律：传递渗流在粗粒化下不封闭（χ² 达数千），且"没有最细层 + 分块"要求律作用在带权重的序上；锐利的绝对因果只是极限性质。

- **F18** 粗粒化后协变与 Bell 因果都不保持，CSG 族不封闭：被删元素是隐藏的时钟；律不能写成逐个元素的增长过程。

**清账（D16）**：框架不引入固定离散尺度，不预设背景流形；只有计数比。"离散"只表示每层记录可数，加密没有最细一层。能标 = 跨层计数比的对数，与 σ 同类型。

与物理实在的逐条对应见 `docs/findings.md` 的"与物理实在的对应"一节。

## 怎么读
00. [`docs/review-2026-09-29.md`](docs/review-2026-09-29.md) —— 整体回顾与结构需求（R1–R8；偏序极限作为候选载体）；
0. [`docs/preprint-short.md`](docs/preprint-short.md) —— 短版预印本草稿（内禀写法，推荐先读）；
0''. [`docs/law.md`](docs/law.md) —— 规律住在什么对象上（权重序、P1–P4）；
0'. [`docs/blocking.md`](docs/blocking.md) —— B 的地基：分辨率作为分块（D18，取代嵌入版）；[`docs/refinement.md`](docs/refinement.md) 为嵌入版对照；
1. [`docs/design.md`](docs/design.md) —— 方案、分层、工作规则；
2. [`docs/findings.md`](docs/findings.md) —— 结果与证据；
3. [`register.md`](register.md) —— 假设、引用、撤回（一页）；
4. [`docs/decisions.md`](docs/decisions.md) —— 为什么这样做，以及下一步；
5. [`docs/glossary.md`](docs/glossary.md) —— 术语。

## 复现
```
python calc/t1_rigidity_map.py     # F1、F3 概览
python calc/t2_rapidity.py         # F2
python calc/t3_frw_exponent.py     # F3
python calc/l2a_poisson_ticks.py   # Poisson 节拍
python calc/t4_three_chains.py     # F4
python calc/l2b_intrinsic.py       # F6（撒点 + 最长链）
python calc/l2b_window_scaling.py  # F6（窗口标度）
python calc/t5_confluence.py       # F7
python calc/t6_coexistence.py      # F8
python calc/b1_mutual_windows.py   # F14
```
Rust 部分（计算密集）：`cd calc/rs && cargo run --release -- nerve 50000`（F9）、`-- chains 8`（F6 单一撒点）、`-- collapse 6`（F11）、`-- wander D 64`（F12）、`-- perc 2000`（F17）、`-- covbell`（F18）。
依赖：numpy、sympy、scipy；Rust 工具链。输出写入 `calc/out/`。Lean 部分尚未开始（只用于数学核心，见决策 D3）。
