import AIM272_StoppedExcursion

set_option warningAsError true

/-! # Excursion bound from shell drift and the actual landing price -/

noncomputable section
open AIM272Unusable (Γ Step)
open scoped NNReal ENNReal BigOperators

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

theorem nextMean_mono_on_support {f g : State κ → ℝ≥0∞} (x : State κ)
    (h : ∀ y, 0 < N.transition x y → f y ≤ g y) : N.nextMean f x ≤ N.nextMean g x := by
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hp : 0 < N.transition x y
  · exact mul_le_mul_left' (h y hp) _
  · rw [le_antisymm (le_of_not_gt hp) (zero_le _), zero_mul, zero_mul]

/-- The same finite inventory bound controls both coordinate changes of every jump. -/
theorem jump_coordinate_bound :
    ∃ J : ℕ, ∀ {x y : State κ}, 0 < N.transition x y →
      ∀ i, y i ≤ x i + J ∧ x i ≤ y i + J := by
  classical
  let J := Finset.univ.sup (fun r : L => max (radius (N.s r)) (radius (N.t r)))
  refine ⟨J, fun {x y} hp i => ?_⟩
  by_cases hq : N.totalRate x = 0
  · have he : y = x := by by_contra hn; simp [transition, hq, hn] at hp
    subst y
    exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _⟩
  obtain ⟨r, hr, hy⟩ := (N.transition_pos_iff_step hq).mp hp
  have ht : N.t r i ≤ J :=
    (coordinate_le_radius (N.t r) i).trans ((le_max_right (radius (N.s r)) _).trans
      (Finset.le_sup (f := fun r => max (radius (N.s r)) (radius (N.t r))) (Finset.mem_univ r)))
  have hs : N.s r i ≤ J :=
    (coordinate_le_radius (N.s r) i).trans ((le_max_left _ (radius (N.t r))).trans
      (Finset.le_sup (f := fun r => max (radius (N.s r)) (radius (N.t r))) (Finset.mem_univ r)))
  have h := congrFun hy i
  have hi := hr i
  change y i = x i - N.s r i + N.t r i at h
  omega

omit [Fintype L] in
theorem radius_le_of_coordinate {x y : State κ} {J : ℕ} (h : ∀ i, y i ≤ x i + J) :
    radius y ≤ radius x + J :=
  Finset.sup_le fun i _ => (h i).trans (Nat.add_le_add_right (coordinate_le_radius x i) J)

private theorem nextMean_const_mul (A : ℝ≥0∞) (V : State κ → ℝ≥0∞) (y : State κ) :
    N.nextMean (fun z => A * V z) y = A * N.nextMean V y := by
  simp only [nextMean, mul_left_comm _ A, ENNReal.tsum_mul_left]

open Classical in
/-- A shell pays for early visits at their drift price and for all later
visits at the outer landing price. The excursion can have infinite duration. -/
theorem shell_occupation_bound (wr : N.WeaklyReversible) (o x : State κ)
    (lo hi J : ℕ) (ho : radius o < lo) (hx : lo ≤ radius x ∧ radius x < hi)
    (jumpBound : ∀ {y z : State κ}, 0 < N.transition y z → radius z ≤ radius y + J)
    (V price : State κ → ℝ≥0∞) (M entrance outer : ℝ≥0∞)
    (hPrice : 0 < price x) (hPrice' : price x ≠ ⊤) (hOuter : 0 < outer) (hOuter' : outer ≠ ⊤)
    (hVisits : ∀ y, N.killedPotential {z | z ≠ o} (fun z => if z = x then 1 else 0) y ≤ M)
    (hEntrance : ∀ y ∈ Γ N.toRxn o, lo ≤ radius y → radius y ≤ lo + J → V y ≤ entrance)
    (hLanding : ∀ y ∈ Γ N.toRxn o, hi ≤ radius y → radius y ≤ hi + J → outer ≤ V y)
    (hDrift : ∀ y ∈ Γ N.toRxn o, lo ≤ radius y → radius y < hi → price y + N.nextMean V y ≤ V y) :
    N.occupation o x ≤ (price x)⁻¹ * entrance * (∑' y, if y ∈ Γ N.toRxn o ∧ radius y < lo then N.occupation o y else 0) +
      (M / outer) * entrance * (∑' y, if y ∈ Γ N.toRxn o ∧ radius y < lo then N.occupation o y else 0) := by
  classical
  let Γo := Γ N.toRxn o
  let α := (price x)⁻¹ + M / outer
  let f (y : State κ) : ℝ≥0∞ := if y = x then 1 else 0
  let S : Set (State κ) := {y | y ∈ Γo ∧ y ≠ o ∧ radius y < hi}
  let W (y : State κ) := if y ∈ Γo ∧ lo ≤ radius y ∧ radius y ≤ hi + J then α * V y
    else if y ∈ Γo ∧ radius y < lo then 0 else M
  let fee (y : State κ) := if y ∈ Γo ∧ radius y < lo then α * entrance else 0
  have hp : 1 ≤ α * price x := by
    rw [add_mul, ENNReal.inv_mul_cancel hPrice.ne' hPrice']
    exact le_self_add
  have hm : M ≤ α * outer := by
    rw [add_mul, ENNReal.div_mul_cancel hOuter.ne' hOuter']
    exact le_add_self
  have hcut : ∀ y ∉ S, y ≠ o → N.killedPotential {z | z ≠ o} f y ≤ W y := by
    intro y hy hyo
    by_cases hc : y ∈ Γo
    · have hr : hi ≤ radius y := le_of_not_gt fun hn => hy ⟨hc, hyo, hn⟩
      have hinner : ¬ (y ∈ Γo ∧ radius y < lo) := fun h => not_lt_of_ge (hx.1.trans (hx.2.le.trans hr)) h.2
      by_cases hr' : radius y ≤ hi + J
      · have hb : y ∈ Γo ∧ lo ≤ radius y ∧ radius y ≤ hi + J := ⟨hc, hx.1.trans (hx.2.le.trans hr), hr'⟩
        rw [show W y = α * V y from if_pos hb]
        exact (hVisits y).trans (hm.trans (mul_le_mul_left' (hLanding y hc hr hr') _))
      · simp only [W, if_neg (fun h : y ∈ Γo ∧ lo ≤ radius y ∧ radius y ≤ hi + J => hr' h.2.2),
          if_neg hinner]
        exact hVisits y
    · simp only [W, hc, false_and, if_false]
      exact hVisits y
  have hzero (z : State κ) (hz : z ∈ Γo) (hr : radius z < lo) : W z = 0 := by
    have hn : ¬ (z ∈ Γo ∧ lo ≤ radius z ∧ radius z ≤ hi + J) := fun h => not_le_of_gt hr h.2.1
    have hh : z ∈ Γo ∧ radius z < lo := ⟨hz, hr⟩
    simp only [W, if_neg hn, if_pos hh]
  have hit (z : State κ) : untilRoot o W z ≤ W z := by
    unfold untilRoot
    split
    · exact zero_le _
    · exact le_rfl
  have hfee (y : State κ) (hy : y ∈ Γo) (hr : radius y < lo) :
      f y + N.nextMean (untilRoot o W) y ≤ fee y := by
    have hne : y ≠ x := fun he => not_le_of_gt hr (he.symm ▸ hx.1)
    have hf : fee y = α * entrance := if_pos ⟨hy, hr⟩
    rw [show f y = 0 from if_neg hne, zero_add, hf, ← N.nextMean_const (α * entrance) y]
    apply N.nextMean_mono_on_support
    intro z hz
    have hc := N.t0_transition_closed wr o hy hz
    have hrad := (jumpBound hz).trans (Nat.add_le_add_right hr.le J)
    apply (hit z).trans
    by_cases hlo : lo ≤ radius z
    · rw [show W z = α * V z from if_pos ⟨hc, hlo, hrad.trans (Nat.add_le_add_right (hx.1.trans hx.2.le) J)⟩]
      exact mul_le_mul_left' (hEntrance z hc hlo hrad) _
    · rw [hzero z hc (lt_of_not_ge hlo)]
      exact zero_le _
  have hBudget (y : State κ) (hy : y ∈ S) :
      f y + N.nextMean (untilRoot o W) y ≤ W y + fee y := by
    obtain ⟨hc, _, hr⟩ := hy
    by_cases hinner : radius y < lo
    · rw [hzero y hc hinner, zero_add]
      exact hfee y hc hinner
    have hLo := le_of_not_gt hinner
    have hWy : W y = α * V y := if_pos ⟨hc, hLo, hr.le.trans (Nat.le_add_right _ _)⟩
    have hnext : N.nextMean (untilRoot o W) y ≤ α * N.nextMean V y := by
      rw [← N.nextMean_const_mul]
      apply N.nextMean_mono_on_support
      intro z hz
      have hc' := N.t0_transition_closed wr o hc hz
      apply (hit z).trans
      by_cases hz' : lo ≤ radius z
      · exact (show W z = α * V z from if_pos ⟨hc', hz',
          (jumpBound hz).trans (Nat.add_le_add_right hr.le J)⟩).le
      · rw [hzero z hc' (lt_of_not_ge hz')]
        exact zero_le _
    have hf : f y ≤ α * price y := by
      by_cases h : y = x
      · simpa [f, h] using hp
      · simp [f, h]
    calc
      _ ≤ α * price y + α * N.nextMean V y := add_le_add hf hnext
      _ ≤ α * V y := by rw [← mul_add]; exact mul_le_mul_left' (hDrift y hc hLo hr) _
      _ ≤ _ := by rw [hWy]; exact le_self_add
  have hpref := N.excursion_bound_of_stopped_budget o S f fee W (fun _ h => h.2.1)
    hcut hBudget (hfee o (N.root_mem_class o) ho)
  have left : (∑' y, N.occupation o y * f y) = N.occupation o x := by
    rw [tsum_eq_single x]
    · simp [f]
    · intro y hy
      simp [f, hy]
  rw [left] at hpref
  have fee_eq (y : State κ) : N.occupation o y * fee y =
      (α * entrance) * (if y ∈ Γo ∧ radius y < lo then N.occupation o y else 0) := by
    by_cases hy : y ∈ Γo ∧ radius y < lo <;> simp [fee, hy, mul_comm]
  simp only [fee_eq, α, add_mul, ENNReal.tsum_add, ENNReal.tsum_mul_left] at hpref
  exact hpref

end AIM272.Network
