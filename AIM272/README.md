# AIM 272 的 Lean 形式化

本工程使用 Lean 4.24.0 和 mathlib 提交 `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。在工程目录运行以下命令。

```sh
lake exe cache get
lake build
```

`AIM272.lean` 是根模块。`AIM272_Factorial.lean` 给出 T1–T3 的最终定理。原有的有理化、Dickson 基、下降见证和仿射逼近证明继续在同一个 Lake 工程中使用。

## 目标对照

| 目标 | Lean 定理 | 结论 |
|---|---|---|
| T0，连通类闭性 | `t0_transition_closed` | 已证明 |
| T1，真实跳链游程的阶乘占用界 | `t1` | 已证明 |
| T2，期望首次返回跳数有限 | `t2` | 已证明 |
| T3，不爆炸、正常返、唯一平稳分布及其阶乘尾界 | `t3` | 依赖目标单第 3 节第 1 条 |
| 有限类及吸收态 | `t3_finite_class`、`t3_absorbing_class` | 有限非吸收类依赖第 3 节第 1 条，吸收类已直接证明 |
| G1–G3，方向、相位及相对阶 | `directional_bounded_witness`、`descent_depth_iff`、`psi_finite_values`、`psi_antitone`、`levels_on_step`、`relativeOrders_finite`、`level_drop_gap` | 已证明。G2 的层级取值表述见论文核对说明 |
| G4，静态目标与入口目标 | `bounded_static_target`、`entranceTarget_iff_gate` | 已证明 |
| G5，具体削薄概率与分层采样下界 | `thinned_rate_bounds`、`actual_sampling_lower`、`local_lower_target_eventually` | 已证明 |
| G6–G7，控制停留与正阶损失 | `observe_resolvent`、`observedSurvival_drift`、`localPotential_le_of_clock_drift` | 已证明局部势所需的生成元估计，采用离散观察概率 |
| G8，局部势比较与首步方程 | `localPotential_eventually_upper`、`localPotential_lower`、`localPotential_poisson` | 已证明 |
| G9，拼接势与壳层漂移 | `shell_potential_eventually` | 已证明，覆盖实际外层落点 |
| G10–G11，下降路径与逐点平均访问次数 | `coordinatewise_descent`、`pointwise_return_bound` | 已证明 |
| G12–G13，壳层游程预算与尺度合成 | `excursion_bound_of_stopped_budget`、`shell_occupation_bound`、`t1` | 已证明 |
| G14，求和、平衡与正规化 | `t2_of_t1`、`occupation_invariant`、`physicalOccupation_balance`、`normalizedOccupation_total` | 已证明。实时间结论在 T3 中调用第 3 节第 1 条 |

T1 和 T2 的输入是有限物种与标签、具体质量作用网络、弱可逆性和根状态。游程占用由实际跳核的递推定义。公理审计见 [AXIOM_AUDIT.txt](AXIOM_AUDIT.txt)。

## 连续时间假设

T3 的外部输入是 `AIM272.ContinuousTime.NorrisJumpReturn (State κ)`。它是 `AIM272_ContinuousTime.lean` 中可展开的通用命题参数。对任意可数状态空间、嵌入跳核、正持有速率的闭不可约类，若根的期望返回跳数有限且类内速率有正下界，则最小连续时间链不爆炸、正常返，且唯一平稳分布由归一化物理占用给出。Lean 定义中逐项写出了跳核概率和、无自跳、闭性、不可约性、杀死递推和有限跳数前提。对应 Norris《Markov Chains》§§2.6–2.7、3.4–3.5。 [原书目录](https://www.statslab.cam.ac.uk/~jrn10/Markov/)

T1、T2 以及支撑它们的离散概率论证都由 Lean 内部证明。

```lean
def NorrisJumpReturn (S : Type) [Countable S] : Prop :=
  ∀ (P : JumpMatrix S) (q : S → ℝ≥0) (I : Set S) (o : S) (A : S → ℕ → S → ℝ≥0∞),
    (∀ x, (∑' y, P x y) = 1) →
    (∀ x ∈ I, P x x = 0) →
    (∀ x ∈ I, ∀ y, 0 < P x y → y ∈ I) →
    (∀ x ∈ I, ∀ y ∈ I, Relation.ReflTransGen (fun z w => 0 < P z w) x y) →
    o ∈ I → (∃ c : ℝ≥0, 0 < c ∧ ∀ x ∈ I, c ≤ q x) →
    (∀ r z, A r 0 z = if z = r then 1 else 0) →
    (∀ r n z, A r (n + 1) z = if z = r then 0 else ∑' y, A r n y * P y z) →
    (∑' n, ∑' z, A o n z) < ⊤ →
    NonexplosiveOn P q I ∧ PositiveRecurrentOn P q I A ∧
      StationaryOn P q I (excursionLaw q A o) ∧
      ∀ π, StationaryOn P q I π → π = excursionLaw q A o
```

## 与论文证明的对应

- 分层采样以有限标签概率质量函数和几何环数实现。对观察分布展开首轮并交换非负求和，得到 `observe_resolvent`。
- 局部势使用仍存活的观察概率作层级校正。低阶时钟的缺额支付正阶损失和逐跳奖励，有限时域 Bellman 不等式给出局部势上界。
- 壳层预算在首次外越界时取实际落点的访问上界。有限时域递推把早期访问和晚期访问合在一个估计中。入口次数用内球的总访问次数控制，内球格点数只产生一个多项式因子。
- G10 使用 Dickson 基以及极小非零增长向量，平移有限个下降路径。证明真实返回概率时允许游程无限长。

论文和目标单的文字核对见 [论文核对说明](论文核对说明.md)。
