# AIM 272 Lean 形式化：剩余目标

这份文件只写**要达到的目标**和**验收标准**。证明路线、定义方式、是否改写论文里的证明，都由你自己决定。

论文源文件在上一级目录：`main.tex`、`sec1_intro.tex` … `sec5_drift.tex`。下文用论文里的 `\label` 名称引用。

---

## 0. 环境与硬性规则

- Lean 4.24.0，Mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`。`lakefile.lean` 和 `lean-toolchain` 已在本目录。
- 每个文件开头都要有 `set_option warningAsError true`。
- 不允许出现 `sorry`、`admit`、`axiom` 声明，也不允许 `native_decide`。
- 最终定理的 `#print axioms` 只能出现 `propext`、`Classical.choice`、`Quot.sound`。
- **假设的规则。** 只有第 3 节列出的经典事实可以作为假设，而且必须写成一个单独命名的 `structure` 或 `def ... : Prop`，并在 docstring 里说明它是哪条经典定理。
  - 任何包含论文新估计的东西都不能作为假设，例如采样下界、局部势上界、漂移不等式、逃逸概率。
  - `AIM272_Conditional.lean` 里的 `ExcursionChecks`、`RankKernel`、`RankSamplingInputs`、`ReturnBridge` 目前就是这种"把新估计当假设"的接口。最终结果里，它们必须用具体对象实例化并证明各字段，或者被直接替换掉。
- 如果发现论文某一步有错，或者陈述需要改动，不要悄悄改定理陈述。请单独写一份说明，指出位置和原因。

---

## 1. 已经完成、可以直接用的部分

以下文件都已编译通过，只依赖三条标准公理。

| 文件 | 主要定理 | 内容 |
|---|---|---|
| `AIM272_Rational.lean` | `AIM272Rational.rational_points` | 格子群实张成中的非负向量可换成群中非零非负、支撑更小的向量 |
| `AIM272_Unusable.lean` | `Rxn`、`Step`、`Reach`、`Γ`、`M`、`Usable`；`dickson`、`unusable_bound`、`unusable_outside_shell` | 引理 `lem:unusable`，以及 §3 末尾的壳层排除 |
| `AIM272_Witness.lean` | `Net`、`Feas`、`Wit`；`bounded_witness`、`minimal_peak`、`wit_mono` | 引理 `lem:witness`，以及最小上限取有限多个值、对相位单调 |
| `AIM272_Affine.lean` | `exists_good_family`、`uniform_property` | 命题 `prop:Pd`（最小形式） |
| `AIM272_Translation.lean` | `wR`、`Lval`；`affine_max_form` | `eq:affine-family`–`eq:near-active`（最大形式） |
| `AIM272_Geometry.lean` | `shell_faces_usable` | §9 第一步：壳层中近活跃面都可用 |
| `AIM272_Analytic.lean` | `descFactorial_le_succ_pow`、`succ_pow_le_descFactorial`、`timeChanged_bounds`、`preemption_bound`、`weight_ratio_eventually_le_half`、`leakage_eventually_small`、`outer_face_lower_bound`、`scale_choice` | 各处的标量不等式与参数选取 |
| `AIM272_NewLemmas.lean` | `layerBoundAlongWord`、`fastCopyPreservesLayer`、`budgetInvariantAlongFast`、`boundedWitnessFromFiniteBasis` 等 | 路径与层级的抽象引理（对抽象的 layer 函数证明） |
| `AIM272_Conditional.lean` | `rankedClockLowerBound`、`finalRankBlock`、`stoppedShellEstimates`、`factorialOccupancyBound`、`aim272Conditional` | 在抽象概率接口之上的记账推理 |
| `AIM272.lean` | 根模块 | 导入全部文件，打印公理 |

目前还**没有**把这些文件接到同一个具体模型上：
- `Rxn`（Unusable）和 `Net`（Witness）是两套独立的数据；
- `Net` 里的 `δ`、`g` 还没有从方向 `a` 和反应 `s_r`、`t_r` 构造出来；
- 抽象的 layer 函数也还没有用 `ψ_a`、`ℓ_a` 实例化。

---

## 2. 最终目标

### 2.1 具体模型（需要在 Lean 中定义）

- **网络。** 物种集合 `κ`（`Fintype`），反应标签集合 `L`（`Fintype`）。每个反应有源 `s r : κ → ℕ`、目标 `t r : κ → ℕ`（要求 `s r ≠ t r`）和速率常数 `κ_r > 0`。
- **弱可逆性。** 对每个反应 `r`，在反应图中存在一条从复形 `t r` 回到复形 `s r` 的有向路径。反应图的顶点是复形，边是 `s r → t r`。
- **质量作用速率**（`eq:rates`）：`q_r(x) = κ_r * ∏ i, (x i).descFactorial (s r i)`。不可用的反应速率自动为 0。总速率 `q(x) = ∑ r, q_r(x)`。
- **跳链。** 从 `x` 沿 `r` 跳到 `x - s r + t r`（`s r ≤ x` 时），概率为 `q_r(x)/q(x)`。
- **记号。** `m(x) = max_i x_i`，`x! = ∏ i, (x i)!`。
- **类与根。** `Γ` 是一个无限的连通类，`o ∈ Γ` 为根。
- **游程占用** `L_o(x)`（`eq:occupation`）：从 `o` 出发，第一次返回 `o` 之前访问 `x` 的期望次数，计数包含时刻 0。
  - 可以用测度论定义，也可以用有限时域期望的上确界来定义。
  - 无论哪种，都必须由上面的具体跳链给出，不能作为输入数据。

### 2.2 要证明的定理

- **T0**（`lem:closed`）：每个连通类都是闭的。
- **T1**（`eq:factorial`，论文的核心结论）：对弱可逆网络、任意无限类 `Γ` 和根 `o`，对任意 `δ > 0` 存在 `C`，使得对所有 `x ∈ Γ`：
  `x! * L_o(x) ≤ C * exp(δ * m(x) * log(2 + m(x)))`。
- **T2**（§11 第一段）：`∑_{x∈Γ} L_o(x) < ∞`，即从 `o` 出发首次返回所需的期望跳数有限。
- **T3**（定理 `thm:main` 的 (ii)、(iii)）：类 `Γ` 正常返、不爆炸，且有平稳分布 `π ∝ L_o/q`，满足 `eq:main-tail` 的尾部估计。
  - 这一条可以在 T2 的基础上，借助第 3 节允许的经典假设得到。

**验收标准。** T1、T2 的 `#print axioms` 只出现三条标准公理。T1、T2 的陈述中除第 3 节允许的经典假设外，不能有其他前提。最理想的情况是 T1、T2 完全不带假设。

---

## 3. 允许作为假设的经典事实

只限下列几条。每条都要单独命名，并在 docstring 中注明出处。

1. **连续时间与跳链的关系。** 若跳链从 `o` 出发首次返回的期望跳数有限，且速率有正的下界，则连续时间链在 `Γ` 上正常返、不爆炸，平稳分布由游程占用公式给出（参考 Norris 1997）。
2. **概率论基础事实**，限 Mathlib 里没有的部分：强马氏性、Poisson 过程或指数钟的竞争与无记忆性、可选停时定理。
   - 只有在你选择用连续时间或测度论的方式证明时才需要。
   - 如果用离散跳链、有限时域的方式证明，这一条可能完全不需要。
   - 假设本身必须是一般性的概率论陈述，不能针对本文的具体量。

除此以外的一切，包括论文 §2–§11 的每一步，都必须证明。

---

## 4. 中间目标

这些目标对应论文的结构，只是供你参考的检查点。只要最终目标达到，可以合并、拆分或换一种证法。

### 4.1 §2–§5 的具体化

- **G1.** 把具体模型接到 `AIM272Unusable.Rxn` 和 `AIM272Witness.Net` 上：
  - 对方向 `a ∈ [0,1]^κ` 和 `I = {i : a_i = 0}`，相坐标集合是 `J = I`；
  - `δ r = a · (t r - s r)`，`g r = -(a · s r)`，`S = max_c a · c`。
- **G2**（§4.3）：
  - 集合 `Y_a`（存在负增量闭相位词的相位）向上封闭，并在投影边下不变；
  - 每个 `Γ` 中状态的相位都属于 `Y_a`；
  - "能下降到任意低处的最小上限"等于"首次下降 `D_a` 的最小上限"，并且落在 `[-S, C_a]` 中；
  - 由此定义 `ψ_a`、`ℓ_a(x) = a · x + ψ_a(x_I)`（`eq:level`），并证明它们取有限多个值、对相位单调不增。
  - `minimal_peak` 已经给出有限性。
- **G3**（§5）：
  - 层级沿边的不等式 `ℓ(x') ≤ max(ℓ(x), h)` 和对称形式；
  - 相对阶 `d_r(x,k)`（`eq:relorder`）取值于一个有限集；
  - 层级下降至少为某个固定的 `g_a > 0`。
  - `NewLemmas` 里的抽象版本可以用 `ℓ_a` 实例化后使用。

### 4.2 §6–§7：局部势

- **G4**（§6.2）：静态目标和统一词长 `B(a, j, A)`，以及入口目标 `A_b` 的平移不变性。
- **G5**（`lem:sampling`）：采样引理，常数与起点、层级、采样速率无关，且要在 `η` 和 `R` 选定之前就已固定。
  - 可以用论文的分层 Poisson 时钟证明；
  - 也可以在离散跳链上给出等价陈述和证明，自行决定。
- **G6**（`eq:stoptime`）：期望停止时间 `≤ C R^{bη}`。
- **G7**（`eq:preempt`、`eq:weightratio`）：正阶时钟抢先的概率，以及权重比 `≤ 1/2`。
- **G8**：局部势 `U_{a,R}`（`eq:localpotential`）满足
  - 上下界 `R^{-K_a} R^{θ a·x} ≤ U ≤ R^{K_a} R^{θ a·x}`（`eq:localcompare`）；
  - Poisson 方程 `(P - I) U = -R^{θ ℓ_a}`（`eq:poisson`）。

### 4.3 §9：拼接势

- **G9**：`V_R`（`eq:glued`）满足
  - 比较式 `eq:Vcompare`；
  - 壳层漂移 `(P - I) V_R ≤ -R^{-K} R^{θ F_R}`（`eq:shelldrift`），其中要用到 `eq:outside` 的泄漏估计；
  - 外层下界 `F_R ≥ N/2`（`eq:outerF`）。
  - 可以直接用 `shell_faces_usable`、`affine_max_form`、`leakage_eventually_small`、`outer_face_lower_bound`。

### 4.4 §10：阶乘界

- **G10**（`lem:descent`）：坐标下降引理。
- **G11**（`eq:Mx`）：从 `x` 出发，在回到 `x` 之前先到达根的概率至少为 `1/M_x`。由此得到：从任意起点出发，到达根之前访问 `x` 的期望次数至多为 `M_x`，且 `L_o(x) ≤ M_x`。
- **G12**（§10.2）：
  - 入口预算 `eq:entrancebudget`；
  - 停止漂移 `eq:stoppeddrift`；
  - 逃逸概率 `eq:escape`；
  - 截断访问次数 `eq:truncatedvisits`。
- **G13**（§10.3）：
  - 晚期访问 `eq:late`；
  - 由活跃面给出的下界 `eq:Flower`；
  - 早期访问 `eq:early`。
  - 由此合成 T1。参数选取用 `scale_choice`。

### 4.5 §11

- **G14**：由 T1 推出 T2（阶乘与格点计数的比较），再借助第 3 节第 1 条得到 T3。
  - 不变性 `eq:invariance`，以及 `G(x) > 0`：能证明就证明；若属于经典的占用公式，就放进第 3 节第 1 条的假设里。

---

## 5. 接线要求

1. 所有文件放在同一个 Lake 项目中（本目录）。`lake build` 必须通过。
2. 第 1 节的已有定理要接到具体模型上：
   - 在需要它们的地方直接调用，例如用 `shell_faces_usable` 证明 G9 的第一步，用 `bounded_witness` 证明 G2、G4；
   - 不要另起一套平行定义，也不要重新证明同一件事。
   - 已有文件中的定义如果需要调整以便接线，可以修改，但修改后原有定理必须仍然成立并通过编译。
3. `AIM272_Conditional.lean` 中的抽象接口有两种处理方式：
   - 证明具体模型满足 `ExcursionChecks`、`RankKernel`、`RankSamplingInputs` 的每个字段，然后调用 `aim272Conditional`；
   - 或者不再使用这些接口，直接证明 T1、T2。
   - 无论哪种，最终定理的前提里都不能再出现这些结构。
4. 新建一个最终文件，例如 `AIM272_Main.lean`，陈述 T0–T3，并由根模块 `AIM272.lean` 导入。根模块末尾打印 T0–T3 的 `#print axioms`。
5. 更新 `README.md` 中的对照表：每一项写明"已证明"或"依赖第 3 节第 k 条"。

---

## 6. 交付物

- 能通过 `lake build` 的完整项目。
- `#print axioms` 的输出（T0–T3 以及各中间目标的主定理）。
- 一份简短说明，包含三部分：
  - 用了第 3 节中的哪几条假设，各自的精确 Lean 陈述；
  - 哪些地方的证明与论文不同，以及原因；
  - 发现的论文问题（如果有）。
