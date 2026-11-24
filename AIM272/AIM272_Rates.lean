import AIM272_Potential
import AIM272_Tails
import AIM272_Analytic

set_option warningAsError true

/-! # Uniform estimates for actual label probabilities and thinned clocks -/

noncomputable section

open scoped BigOperators NNReal ENNReal

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

def maxSourceDegree : ℕ := Finset.univ.sup (fun r : L => ∑ i, N.s r i)

private def monomial (x : State κ) (r : L) : ℕ := ∏ i, (x i + 1) ^ N.s r i

private def loss (r : L) : ℕ := ∏ i, (N.s r i + 1) ^ N.s r i

omit [Fintype L] in
private theorem rateFactor_le_monomial (x : State κ) (r : L) :
    N.rateFactor x r ≤ N.monomial x r := by
  exact Finset.prod_le_prod' fun i _ => AIM272Analytic.descFactorial_le_succ_pow _ _

omit [Fintype L] in
private theorem monomial_le_loss {x : State κ} {r : L} (hr : N.s r ≤ x) :
    N.monomial x r ≤ N.loss r * N.rateFactor x r := by
  unfold monomial loss rateFactor
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod' fun i _ => AIM272Analytic.succ_pow_le_descFactorial _ _ (hr i)

theorem rateFactor_le_radius (x : State κ) (r : L) :
    N.rateFactor x r ≤ (radius x + 1) ^ N.maxSourceDegree := by
  calc
    N.rateFactor x r ≤ N.monomial x r := N.rateFactor_le_monomial x r
    _ ≤ ∏ i, (radius x + 1) ^ N.s r i := Finset.prod_le_prod' fun i _ =>
      Nat.pow_le_pow_left (Nat.succ_le_succ (coordinate_le_radius x i)) _
    _ = (radius x + 1) ^ (∑ i, N.s r i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ _ := Nat.pow_le_pow_right (Nat.succ_pos _)
      (Finset.le_sup (f := fun j : L => ∑ i, N.s j i) (Finset.mem_univ r))

theorem totalRate_le_polynomial (x : State κ) :
    N.totalRate x ≤ (∑ r, N.rateConstant r) * ((radius x : ℝ≥0) + 1) ^ N.maxSourceDegree := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun r _ => mul_le_mul_left' (by exact_mod_cast N.rateFactor_le_radius x r) _

theorem labelProbability_le_transition {x : State κ} {r : L} (hr : N.s r ≤ x) :
    (N.jumpProbability x r : ℝ≥0∞) ≤ N.transition x (N.jump x r) := by
  classical
  have hq := ((N.rate_pos_iff x r).mpr hr).trans_le (N.rate_le_totalRate x r)
  simp only [transition, if_neg hq.ne']
  apply le_trans _ (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ r))
  simp

/-- A positive uniform lower coefficient for every enabled label on a box. -/
theorem transition_floor :
    ∃ D : ℝ≥0, 1 ≤ D ∧ ∀ (M : ℕ) {x y : State κ}, radius x ≤ M →
      AIM272Unusable.Step N.toRxn x y →
      (((D * ((M : ℝ≥0) + 1) ^ N.maxSourceDegree)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ N.transition x y := by
  classical
  let u := ∑ r, N.rateConstant r
  let D := 1 + ∑ r, u / N.rateConstant r
  refine ⟨D, le_self_add, fun M x y hx hxy => ?_⟩
  obtain ⟨r, hr, rfl⟩ := hxy
  apply le_trans _ (N.labelProbability_le_transition hr)
  apply ENNReal.coe_le_coe.mpr
  have hc := N.rateConstant_pos r
  have hq := ((N.rate_pos_iff x r).mpr hr).trans_le (N.rate_le_totalRate x r)
  have hf : u / N.rateConstant r ≤ D :=
    (Finset.single_le_sum (f := fun j => u / N.rateConstant j)
      (fun _ _ => zero_le _) (Finset.mem_univ r)).trans le_add_self
  have hu : u ≤ N.rateConstant r * D := by simpa only [mul_comm] using (div_le_iff₀ hc).mp hf
  have hM : 0 < D * ((M : ℝ≥0) + 1) ^ N.maxSourceDegree :=
    mul_pos (zero_lt_one.trans_le (show 1 ≤ D from le_self_add)) (pow_pos (by positivity) _)
  rw [jumpProbability, inv_eq_one_div, div_le_div_iff₀ hM hq, one_mul]
  calc
    N.totalRate x ≤ u * ((radius x : ℝ≥0) + 1) ^ N.maxSourceDegree := N.totalRate_le_polynomial x
    _ ≤ (N.rateConstant r * D) * ((M : ℝ≥0) + 1) ^ N.maxSourceDegree := by
      gcongr
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_right' (N.rateConstant_le_rate hr) _

private theorem uniform_rate_monomial :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x r, N.s r ≤ x →
      c * (N.monomial x r : ℝ) ≤ (N.rate x r : ℝ) ∧
      (N.rate x r : ℝ) ≤ C * (N.monomial x r : ℝ) := by
  classical
  let f (r : L) : ℝ := (N.rateConstant r : ℝ) / (N.loss r : ℝ)
  let S := insert 1 (Finset.univ.image f)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hL (r : L) : (0 : ℝ) < N.loss r := by
    exact_mod_cast (Finset.prod_pos (s := Finset.univ) (fun i _ =>
      pow_pos (Nat.succ_pos (N.s r i)) (N.s r i)))
  have hf (r : L) : 0 < f r := div_pos (by exact_mod_cast N.rateConstant_pos r) (hL r)
  have hC : (0 : ℝ) < 1 + ∑ r : L, (N.rateConstant r : ℝ) := by positivity
  refine ⟨S.min' hS, _, ?_, hC, fun x r hr => ?_⟩
  · have hm := S.min'_mem hS
    rcases Finset.mem_insert.mp hm with h | h
    · rw [h]; exact zero_lt_one
    · obtain ⟨r, _, he⟩ := Finset.mem_image.mp h
      exact he ▸ hf r
  · have hm : S.min' hS ≤ f r := S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ r)))
    have hprod : (N.monomial x r : ℝ) ≤ (N.loss r : ℝ) * (N.rateFactor x r : ℝ) := by
      exact_mod_cast N.monomial_le_loss hr
    have hUpper : (N.rateConstant r : ℝ) ≤ 1 + ∑ r : L, (N.rateConstant r : ℝ) :=
      (Finset.single_le_sum (fun j _ => (N.rateConstant j).coe_nonneg) (Finset.mem_univ r)).trans
        (by linarith)
    change _ ≤ (N.rateConstant r : ℝ) * (N.rateFactor x r : ℝ) ∧
      (N.rateConstant r : ℝ) * (N.rateFactor x r : ℝ) ≤ _
    constructor
    · calc
        _ ≤ f r * ((N.loss r : ℝ) * (N.rateFactor x r : ℝ)) := mul_le_mul hm hprod (by positivity) (hf r).le
        _ = _ := by dsimp [f]; field_simp [(hL r).ne']
    · exact mul_le_mul hUpper (by exact_mod_cast N.rateFactor_le_monomial x r) (by positivity) hC.le

omit [Fintype L] in
private theorem monomial_eq_rpow {R : ℝ} (hR : 1 < R) (x : State κ) (r : L) :
    (N.monomial x r : ℝ) = R ^ weight (fun i => Real.log ((x i : ℝ) + 1) / Real.log R) (N.s r) := by
  have hR0 := zero_lt_one.trans hR
  unfold monomial weight
  push_cast
  rw [Real.rpow_def_of_pos hR0, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  have hlog : Real.log R ≠ 0 := (Real.log_pos hR).ne'
  rw [show Real.log R * (Real.log ((x i : ℝ) + 1) / Real.log R * (N.s r i : ℝ)) =
    (N.s r i : ℝ) * Real.log ((x i : ℝ) + 1) by field_simp]
  rw [Real.exp_nat_mul, Real.exp_log (by positivity)]

/-- Equation (6.1) for the actual mass-action label rate, uniformly in all local domains. -/
theorem timeChanged_label_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (wr : N.WeaklyReversible) (a : κ → ℝ) {R E η : ℝ},
      1 < R → 0 ≤ E → (N.maxSourceDegree : ℝ) * E ≤ η → ∀ {x : State κ}, x ∈ N.localDomain a R E →
      ∀ r, N.s r ≤ x →
      c * R ^ (-N.relativeOrder wr a x r - η) ≤ R ^ N.psi wr a x * (N.rate x r : ℝ) ∧
      R ^ N.psi wr a x * (N.rate x r : ℝ) ≤ C * R ^ (-N.relativeOrder wr a x r + η) := by
  obtain ⟨c, C, hc, hC, hrate⟩ := N.uniform_rate_monomial
  refine ⟨c, C, hc, hC, fun wr a R E η hR hE hη x hx r hr => ?_⟩
  let w (i : κ) := Real.log ((x i : ℝ) + 1) / Real.log R
  have hdev : |weight w (N.s r) - weight a (N.s r)| ≤ η := by
    have hsum : weight w (N.s r) - weight a (N.s r) = ∑ i, (w i - a i) * (N.s r i : ℝ) := by
      simp [weight, sub_mul, Finset.sum_sub_distrib]
    rw [hsum]
    calc
      _ ≤ ∑ i, |(w i - a i) * (N.s r i : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, E * (N.s r i : ℝ) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (N.s r i) : (0 : ℝ) ≤ _)]
        exact mul_le_mul_of_nonneg_right (hx.2.2 i).le (Nat.cast_nonneg _)
      _ ≤ η := by
        rw [← Finset.mul_sum]
        apply le_trans _ hη
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast
          (Finset.le_sup (f := fun j : L => ∑ i, N.s j i) (Finset.mem_univ r))) hE
  have hord : N.level wr a x - weight a x + weight a (N.s r) = -N.relativeOrder wr a x r := by
    simp [level, relativeOrder, directionNet]
  obtain ⟨hlo, hhi⟩ := AIM272Analytic.timeChanged_bounds hR hord hdev
  simp only [level, add_sub_cancel_left] at hlo hhi
  obtain ⟨hql, hqu⟩ := hrate x r hr
  rw [N.monomial_eq_rpow hR] at hql hqu
  have hpos := (Real.rpow_pos_of_pos (zero_lt_one.trans hR) (N.psi wr a x)).le
  constructor
  · calc
      _ ≤ c * (R ^ N.psi wr a x * R ^ weight w (N.s r)) := mul_le_mul_of_nonneg_left hlo hc.le
      _ = R ^ N.psi wr a x * (c * R ^ weight w (N.s r)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hql hpos
  · calc
      _ ≤ R ^ N.psi wr a x * (C * R ^ weight w (N.s r)) := mul_le_mul_of_nonneg_left hqu hpos
      _ = C * (R ^ N.psi wr a x * R ^ weight w (N.s r)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hhi hC.le

end AIM272.Network
