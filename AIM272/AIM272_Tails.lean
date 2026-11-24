import AIM272_Occupation

set_option warningAsError true

/-!
# Summability of the factorial occupation bound

The estimate at δ = 1/2 implies domination by a product of ordinary
geometric sequences. The proof uses the exponential series to compare
each scalar factorial to a power, so no asymptotic assumption is needed.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open AIM272Unusable (Γ)

namespace AIM272.Network

variable {κ L : Type} [Fintype κ]

theorem coordinate_le_radius (x : State κ) (i : κ) : x i ≤ radius x :=
  Finset.le_sup (Finset.mem_univ i)

theorem stateFactorial_pos (x : State κ) : 0 < stateFactorial x :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

private theorem radius_factorial_le (x : State κ) :
    (radius x).factorial ≤ stateFactorial x := by
  classical
  by_cases h : (Finset.univ : Finset κ).Nonempty
  · obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ x h
    have hm : radius x ≤ x i := Finset.sup_le hi
    exact (Nat.factorial_le hm).trans
      (Finset.single_le_prod' (f := fun j => (x j).factorial)
        (fun j _ => Nat.factorial_pos (x j)) (Finset.mem_univ i))
  · have hu : (Finset.univ : Finset κ) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [radius, stateFactorial, hu]

private theorem radius_le_sum (x : State κ) : radius x ≤ ∑ i, x i := by
  apply Finset.sup_le
  intro i _
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

private theorem log_factorial_lower (n : ℕ) {A : ℝ} (hA : 0 < A) :
    (n : ℝ) * Real.log A ≤ A + Real.log (n.factorial : ℝ) := by
  have hF : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpow := (div_le_iff₀ hF).mp (Real.pow_div_factorial_le_exp A hA.le n)
  have hh := Real.log_le_log (pow_pos hA n) hpow
  simpa only [Real.log_pow, Real.log_mul (Real.exp_ne_zero A) hF.ne', Real.log_exp] using hh

private def geometricConstant (κ : Type) [Fintype κ] : ℝ :=
  1 + (Fintype.card κ : ℝ) * Real.exp 3 / 2

private theorem factorial_exp_le_geometric (x : State κ) :
    Real.exp ((1 / 2 : ℝ) * (radius x : ℝ) * Real.log (2 + (radius x : ℝ))) /
        (stateFactorial x : ℝ) ≤
      Real.exp (geometricConstant κ - ∑ i, (x i : ℝ)) := by
  classical
  have hF : 0 < (stateFactorial x : ℝ) := by exact_mod_cast stateFactorial_pos x
  have hr := log_factorial_lower (radius x) (show 0 < 2 + (radius x : ℝ) by positivity)
  have hFr : 0 < ((radius x).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hFrLe : ((radius x).factorial : ℝ) ≤ (stateFactorial x : ℝ) := by
    exact_mod_cast radius_factorial_le x
  have hlogR := Real.log_le_log hFr hFrLe
  have hlogProd :
      Real.log (stateFactorial x : ℝ) = ∑ i, Real.log ((x i).factorial : ℝ) := by
    rw [stateFactorial, Nat.cast_prod, Real.log_prod]
    intro i _
    exact_mod_cast (Nat.factorial_ne_zero (x i))
  have hcoord (i : κ) : (3 : ℝ) * (x i : ℝ) ≤ Real.exp 3 + Real.log ((x i).factorial : ℝ) := by
    simpa only [Real.log_exp, mul_comm] using log_factorial_lower (x i) (Real.exp_pos 3)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoord i)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← hlogProd] at hsum
  have hm : (radius x : ℝ) ≤ ∑ i, (x i : ℝ) := by exact_mod_cast radius_le_sum x
  rw [← Real.exp_log hF, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  unfold geometricConstant
  linarith

private def geometricRatio : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-1))

private def geometricWeight (x : State κ) : ℝ≥0∞ :=
  ∏ i, geometricRatio ^ x i

private theorem ofReal_exp_geometric (x : State κ) :
    ENNReal.ofReal (Real.exp (geometricConstant κ - ∑ i, (x i : ℝ))) =
      ENNReal.ofReal (Real.exp (geometricConstant κ)) * geometricWeight x := by
  rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  rw [← Finset.sum_neg_distrib, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg]
  · unfold geometricWeight
    apply Finset.prod_congr rfl
    intro i _
    unfold geometricRatio
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
    congr 2
    ring
  · exact fun _ _ => Real.exp_nonneg _

private theorem geometricWeight_summable :
    (∑' x : State κ, geometricWeight x) < ⊤ := by
  classical
  let B : ℝ≥0∞ := ∑' n : ℕ, geometricRatio ^ n
  have hρ : geometricRatio < 1 := by
    unfold geometricRatio
    exact ENNReal.ofReal_lt_one.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hB : B < ⊤ := tsum_geometric_lt_top.mpr hρ
  rw [ENNReal.tsum_eq_iSup_sum]
  refine lt_of_le_of_lt (iSup_le fun s => ?_) (show (∏ _ : κ, B) < ⊤ from
    ENNReal.prod_lt_top fun _ _ => hB)
  let u := s.sup radius
  let box := Fintype.piFinset (fun _ : κ => Finset.range (u + 1))
  have hsub : s ⊆ box := by
    intro x hx
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((coordinate_le_radius x i).trans
      (Finset.le_sup hx)))
  calc
    (∑ x ∈ s, geometricWeight x) ≤ ∑ x ∈ box, geometricWeight x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => zero_le _)
    _ = ∏ _ : κ, ∑ n ∈ Finset.range (u + 1), geometricRatio ^ n :=
      Finset.sum_prod_piFinset _ (fun _ n => geometricRatio ^ n)
    _ ≤ ∏ _ : κ, B :=
      Finset.prod_le_prod' fun _ _ => ENNReal.sum_le_tsum _

variable [Fintype L] (N : AIM272.Network κ L)

/-- T2 follows from the concrete assertion of T1. -/
theorem t2_of_t1 (wr : N.WeaklyReversible) (o : State κ)
    (hT1 : N.FactorialBound o) : N.expectedReturnJumps o < ⊤ := by
  classical
  obtain ⟨C, hC⟩ := hT1 (1 / 2) (by norm_num)
  let D : ℝ≥0∞ := (C : ℝ≥0∞) * ENNReal.ofReal (Real.exp (geometricConstant κ))
  have hD : D < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top
  have hle (x : State κ) : N.occupation o x ≤ D * geometricWeight x := by
    by_cases hx : x ∈ Γ N.toRxn o
    · let v := Real.exp ((1 / 2 : ℝ) * (radius x : ℝ) * Real.log (2 + (radius x : ℝ)))
      have hpos : 0 < (stateFactorial x : ℝ) := by exact_mod_cast stateFactorial_pos x
      have hnz : (stateFactorial x : ℝ≥0∞) ≠ 0 := by exact_mod_cast (stateFactorial_pos x).ne'
      have htop : (stateFactorial x : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hdiv : N.occupation o x ≤ (C : ℝ≥0∞) * ENNReal.ofReal v /
          (stateFactorial x : ℝ≥0∞) :=
        (ENNReal.le_div_iff_mul_le (.inl hnz) (.inl htop)).mpr
          (by simpa only [mul_comm] using hC x hx)
      have heq : ENNReal.ofReal v / (stateFactorial x : ℝ≥0∞) =
          ENNReal.ofReal (v / (stateFactorial x : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos hpos]
        simp
      calc
        N.occupation o x ≤ (C : ℝ≥0∞) * (ENNReal.ofReal v / (stateFactorial x : ℝ≥0∞)) :=
          by simpa only [div_eq_mul_inv, mul_assoc] using hdiv
        _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (Real.exp (geometricConstant κ - ∑ i, (x i : ℝ))) := by
          rw [heq]
          exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal (factorial_exp_le_geometric x)) _
        _ = D * geometricWeight x := by rw [ofReal_exp_geometric, ← mul_assoc]
    · rw [N.occupation_supported wr o hx]
      exact zero_le _
  rw [← N.occupation_total o]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) ?_
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top hD geometricWeight_summable

end AIM272.Network
