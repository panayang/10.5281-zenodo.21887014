# SCD v2 —— 序与速率

旧版 Scale-Coupled Dynamics（`archive/scd-v1`，tag `scd-v1-final`）已推倒重写。
旧版的物理思想、逐条判定和教训在 [`notes/scd-v1-physical-ideas.md`](notes/scd-v1-physical-ideas.md)。

## 论点
**尺度 = 两个过程之间的对数速率比。** 原始概念有两个：事件之间的因果**序**和过程的**速率**。
因果序在束缚区把速率比定死（结构事实），在同步无标度区把它留作全局隐藏参数（切片、标架）。
"能标"（跨层计数比的对数）与"尺度"是同一个类型的量。（"能量"一词未经内禀定义，见 `docs/review-2026-09-30.md`。）

不在全局粘合之下思考（见同作者的 [`reference/pzfc-preprint.tex`](reference/pzfc-preprint.tex)）：
没有预设的全局事件集、全局时间、全局 σ 场或全局态；它们只在可合并的区域作为**结论**出现。

## 现状
**框架的统一陈述见 [`docs/framework.md`](docs/framework.md)（先读这个）；阶段性总结见 [`docs/summary-2026-09-30.md`](docs/summary-2026-09-30.md)。**

任务（D22）：地位 + 强制/偶然 + 辨认；不以推出已知物理为任务，但须过实用性检验。二十一条结果（[`docs/findings.md`](docs/findings.md)），摘要：
- **F1–F6** 束缚 ⟺ 速率是序的事实；退行时速率隐藏在快度区间内；多观察者的隐藏参数是渐近切片；只用序数据依然成立（F6 条件性）；
- **F3、F7–F9** 宇宙时是序的事实 ⟺ 减速；汇合 ⟺ 无事件视界；共存模式与视界上下文性；
- **F10–F16** 分辨率：速率比不跑动，内容跑动；分块的连续极限（鞅）；纯几何只给幂律（F11–F13 条件性）；
- **F14** σ 的局部读法：束缚对的速率比 = 互窗口之比；
- **F17–F18** 序贯增长律在粗粒化下不封闭：它只有宽度方向；
- **F19** 观察者之间频率一致 ⟺ 窗口比 → 0 ⟺ 速率是事实（锚点 1：宇宙学概率问题的合法性）；
- **F20** 计数亏损 + P5（空处不区分自由方向）⟹ 内容必须改变序，外部 γ = 1，Λ 允许；源不能是记录数；
- **F21** P5 独立于全部原则（偶然、可检验）；律本身不跑动，跑动只能来自内容。
- **F29–F30** 量子的三个位置（原则给出不传信、不限制到量子；候选 P6 = 共存由成对决定）；物质个体 = 刚性内容族，框架产生界（表面速率比 ≥ 1/3）而不产生值。
- **F22** 内容 = 计数亏损的方向依赖部分；其沿共动轴的聚焦 ⟺ 刚性（时间是事实）；**F23** 放宽后的团可在 D1 中表示；**F24** 框架是非上下文的，上下文性需要加细不有向。
- 动力学（D23）：P2 + 没有最细层 + 宽度只向上 ⟹ 有序测度空间上的 Cox 型撒点（条件性）；(S, ≺, μ) 是偶然的律。

**清账（D16）**：框架不引入固定离散尺度，不预设背景流形；只有计数比。"离散"只表示每层记录可数，加密没有最细一层。能标 = 跨层计数比的对数，与 σ 同类型。

与物理实在的逐条对应见 `docs/findings.md` 的"与物理实在的对应"一节。

## 怎么读
0. [`docs/framework.md`](docs/framework.md) —— **框架陈述 v0.5（入口）**；[`docs/assessment-2026-09-30.md`](docs/assessment-2026-09-30.md) —— 解释力与实用性的审视；[`docs/summary-2026-09-30.md`](docs/summary-2026-09-30.md) —— 阶段性总结；
1. [`docs/design.md`](docs/design.md) —— §0 任务与实用性检验，其后为方案 v0.3；
2. [`docs/review-2026-09-30.md`](docs/review-2026-09-30.md) —— 借来的词、局域性、测度与信息的重审；
3. [`docs/anchor-measure.md`](docs/anchor-measure.md) —— 锚点 1：宇宙学概率问题的合法性（F19）；独立短文草稿 [`docs/note-cosmological-probabilities.md`](docs/note-cosmological-probabilities.md)；
3'. [`docs/quantum.md`](docs/quantum.md)、[`docs/matter.md`](docs/matter.md) —— 量子与物质的位置；
4. [`docs/dynamics.md`](docs/dynamics.md) —— 动力学：原则强制了什么（D1–D4，F20–F21）；
5. [`docs/findings.md`](docs/findings.md) —— 结果与证据；[`register.md`](register.md) —— 假设、引用、撤回；[`docs/decisions.md`](docs/decisions.md) —— 决定与下一步；
6. 背景与历史：[`docs/extension.md`](docs/extension.md)（扩张律）、[`docs/law.md`](docs/law.md)（规律住在什么对象上）、[`docs/blocking.md`](docs/blocking.md)（分块）、
   [`docs/gravity-directions.md`](docs/gravity-directions.md)（引力方向，部分撤回）、[`docs/overnight-2026-09-29.md`](docs/overnight-2026-09-29.md)、[`docs/review-2026-09-29.md`](docs/review-2026-09-29.md)、
   [`docs/content.md`](docs/content.md)（内容）、[`docs/contextuality.md`](docs/contextuality.md)（上下文性）、[`docs/identification.md`](docs/identification.md)（辨认）、
   [`docs/preprint-short.md`](docs/preprint-short.md)（短版草稿，早于 30 日的重审，已被 framework.md 取代）、[`docs/glossary.md`](docs/glossary.md)。

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
