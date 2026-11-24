import AIM272_ContinuousTime
import AIM272_ReturnEstimate

set_option warningAsError true

/-! # Return results for the concrete model -/

noncomputable section

open AIM272Unusable (Γ)
open AIM272.ContinuousTime
open scoped NNReal ENNReal

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

/-- On a finite class the pointwise return estimate proves T1 directly. -/
theorem t1_finite_class (o : State κ) (hfinite : (Γ N.toRxn o).Finite) : N.FactorialBound o := by
  obtain ⟨K, _, hK⟩ := N.pointwise_return_bound o
  let w (x : State κ) := (stateFactorial x : ℝ≥0∞) * N.occupation o x
  have hW (x : State κ) (hx : x ∈ Γ N.toRxn o) : w x ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ((hK x hx).1.trans_lt ENNReal.ofReal_lt_top)).ne
  intro δ hδ_pos
  obtain ⟨C, hC⟩ := (hfinite.image (fun x => (w x).toNNReal)).bddAbove
  refine ⟨C, fun x hx => ?_⟩
  -- The growth factor is at least one for each positive δ.
  have hδ : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (δ * (radius x : ℝ) * Real.log (2 + (radius x : ℝ)))) := by
    have hp := Real.log_nonneg (show (1 : ℝ) ≤ 2 + (radius x : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) (radius x)])
    exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp (mul_nonneg (mul_nonneg hδ_pos.le (Nat.cast_nonneg _)) hp))
  calc
    w x = ((w x).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal (hW x hx)).symm
    _ ≤ (C : ℝ≥0∞) := ENNReal.coe_le_coe.mpr (hC (Set.mem_image_of_mem _ hx))
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_left' hδ (C : ℝ≥0∞)

theorem t2_finite_class (wr : N.WeaklyReversible) (o : State κ) (hfinite : (Γ N.toRxn o).Finite) :
    N.expectedReturnJumps o < ⊤ :=
  N.t2_of_t1 wr o (N.t1_finite_class o hfinite)

/-- T3, including the factorial tail, follows from T1 and the allowed
classical Norris jump-chain return criterion. -/
theorem t3_of_t1 (wr : N.WeaklyReversible) (o : State κ)
    (hi : (Γ N.toRxn o).Infinite) (norris : NorrisJumpReturn (State κ))
    (hT1 : N.FactorialBound o) :
    NonexplosiveOn N.transition N.totalRate (Γ N.toRxn o) ∧
    PositiveRecurrentOn N.transition N.totalRate (Γ N.toRxn o) N.aliveMass ∧
    StationaryOn N.transition N.totalRate (Γ N.toRxn o) (N.normalizedOccupation o) ∧
    (∀ π, StationaryOn N.transition N.totalRate (Γ N.toRxn o) π → π = N.normalizedOccupation o) ∧
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ x ∈ Γ N.toRxn o,
      (stateFactorial x : ℝ≥0∞) * N.normalizedOccupation o x ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (Real.exp (δ * (radius x : ℝ) * Real.log (2 + (radius x : ℝ)))) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    N.continuousTime_of_finite_return wr o hi norris (N.t2_of_t1 wr o hT1)
  exact ⟨h₁, h₂, h₃, h₄, N.normalized_factorial_tail o hi hT1⟩

end AIM272.Network
