import AIM272_Occupation

set_option warningAsError true

/-!
# Balance of the concrete excursion occupation

Every finite step splits the surviving mass into a new surviving mass
and the mass that returns at that step. Summing this identity proves
the return mass and the balance equation once the expected number of
steps is finite.
-/

noncomputable section

open scoped ENNReal NNReal
open AIM272Unusable (Γ Reach Step)

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

theorem occupation_pos_of_reach {o x : State κ} (h : Reach N.toRxn o x) :
    0 < N.occupation o x := by
  have hx : ∃ n, 0 < N.aliveMass o n x := by
    induction h with
    | refl => exact ⟨0, by rw [N.aliveMass_zero_self]; exact zero_lt_one⟩
    | @tail y z _ hs ih =>
      by_cases he : z = o
      · subst z
        exact ⟨0, by rw [N.aliveMass_zero_self]; exact zero_lt_one⟩
      · obtain ⟨n, hy⟩ := ih
        refine ⟨n + 1, ?_⟩
        rw [N.aliveMass_apply_of_ne he]
        exact (ENNReal.mul_pos hy.ne' (N.transition_pos_of_step hs).ne').trans_le (ENNReal.le_tsum y)
  obtain ⟨n, hn⟩ := hx
  exact hn.trans_le (ENNReal.le_tsum n)

private def survivalMass (o : State κ) (n : ℕ) : ℝ≥0∞ := ∑' x, N.aliveMass o n x

private def arrivals (o : State κ) (n : ℕ) (y : State κ) : ℝ≥0∞ :=
  ∑' x, N.aliveMass o n x * N.transition x y

def returnMass (o : State κ) : ℝ≥0∞ := ∑' n, N.arrivals o n o

private theorem survival_zero (o : State κ) : N.survivalMass o 0 = 1 := by
  classical
  simp [survivalMass, aliveMass, tsum_ite_eq]

private theorem survival_step (o : State κ) (n : ℕ) :
    N.survivalMass o n = N.survivalMass o (n + 1) + N.arrivals o n o := by
  classical
  have hArrival : (∑' y, N.arrivals o n y) = N.survivalMass o n := by
    simp only [arrivals]
    rw [ENNReal.tsum_comm]
    simp only [ENNReal.tsum_mul_left, transition_tsum, mul_one, survivalMass]
  have hsplit (y : State κ) :
      N.arrivals o n y = N.aliveMass o (n + 1) y +
        (if y = o then N.arrivals o n o else 0) := by
    by_cases he : y = o
    · subst y
      simp [aliveMass]
    · rw [N.aliveMass_apply_of_ne he, if_neg he, add_zero]
      rfl
  have hr : (∑' y : State κ, if y = o then N.arrivals o n o else 0) = N.arrivals o n o := by simp
  calc
    N.survivalMass o n = ∑' y, N.arrivals o n y := hArrival.symm
    _ = ∑' y, (N.aliveMass o (n + 1) y + if y = o then N.arrivals o n o else 0) :=
      tsum_congr hsplit
    _ = _ := by rw [ENNReal.tsum_add, hr, survivalMass]

theorem returnMass_eq_one (o : State κ) (hfin : N.expectedReturnJumps o < ⊤) :
    N.returnMass o = 1 := by
  let tail := ∑' n, N.survivalMass o (n + 1)
  have hstep : N.expectedReturnJumps o = tail + N.returnMass o := by
    calc
      (∑' n, N.survivalMass o n) = ∑' n, (N.survivalMass o (n + 1) + N.arrivals o n o) :=
        tsum_congr (N.survival_step o)
      _ = _ := ENNReal.tsum_add
  have hhead : N.expectedReturnJumps o = 1 + tail := by
    change (∑' n, N.survivalMass o n) = 1 + ∑' n, N.survivalMass o (n + 1)
    exact (tsum_eq_zero_add' (f := N.survivalMass o) ENNReal.summable).trans
      (by rw [N.survival_zero])
  have htail : tail ≠ ⊤ := by
    intro he
    exact hfin.ne (by rw [hhead, he, add_top])
  apply (ENNReal.add_left_inj htail).mp
  calc
    N.returnMass o + tail = tail + N.returnMass o := add_comm _ _
    _ = N.expectedReturnJumps o := hstep.symm
    _ = 1 + tail := hhead

/-- The excursion occupation is invariant for the embedded jump chain. -/
theorem occupation_invariant (o y : State κ) (hfin : N.expectedReturnJumps o < ⊤) :
    (∑' x, N.occupation o x * N.transition x y) = N.occupation o y := by
  classical
  have h : (∑' x, N.occupation o x * N.transition x y) = ∑' n, N.arrivals o n y := by
    simp only [occupation, arrivals, ← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_comm
  rw [h]
  by_cases he : y = o
  · subst y
    exact (N.returnMass_eq_one o hfin).trans (N.occupation_root o).symm
  · simp_rw [show ∀ n, N.arrivals o n y = N.aliveMass o (n + 1) y from
      fun n => (N.aliveMass_apply_of_ne he n).symm]
    have hsum : N.occupation o y = N.aliveMass o 0 y + ∑' n, N.aliveMass o (n + 1) y :=
      tsum_eq_zero_add' (f := fun n => N.aliveMass o n y) ENNReal.summable
    rw [hsum, show N.aliveMass o 0 y = 0 by simp [aliveMass, he], zero_add]

theorem physicalOccupation_pos {o x : State κ} (hx : x ∈ Γ N.toRxn o) :
    0 < N.physicalOccupation o x :=
  ENNReal.div_pos (N.occupation_pos_of_reach hx.1).ne' ENNReal.coe_ne_top

private theorem physicalOccupation_mul_rate (wr : N.WeaklyReversible) (o x : State κ)
    (hi : (Γ N.toRxn o).Infinite) :
    N.physicalOccupation o x * (N.totalRate x : ℝ≥0∞) = N.occupation o x := by
  by_cases hx : x ∈ Γ N.toRxn o
  · have hp := N.totalRate_pos_on_class hi hx
    exact ENNReal.div_mul_cancel (by exact_mod_cast hp.ne') ENNReal.coe_ne_top
  · simp [physicalOccupation, N.occupation_supported wr o hx]

/-- Flux balance GQ = 0 in nonnegative form, including all labels. -/
theorem physicalOccupation_balance (wr : N.WeaklyReversible) (o y : State κ)
    (hi : (Γ N.toRxn o).Infinite) (hfin : N.expectedReturnJumps o < ⊤) :
    (∑' x, N.physicalOccupation o x * ((N.totalRate x : ℝ≥0∞) * N.transition x y)) =
      N.physicalOccupation o y * (N.totalRate y : ℝ≥0∞) := by
  simp only [← mul_assoc, N.physicalOccupation_mul_rate wr o _ hi]
  exact N.occupation_invariant o y hfin

def physicalTotal (o : State κ) : ℝ≥0∞ := ∑' x, N.physicalOccupation o x

theorem physicalTotal_finite (wr : N.WeaklyReversible) (o : State κ)
    (hi : (Γ N.toRxn o).Infinite) (hfin : N.expectedReturnJumps o < ⊤) :
    N.physicalTotal o < ⊤ := by
  classical
  obtain ⟨c, hc, hrate⟩ := N.totalRate_lower_bound hi
  have hdom (x : State κ) : N.physicalOccupation o x ≤ N.occupation o x / (c : ℝ≥0∞) := by
    by_cases hx : x ∈ Γ N.toRxn o
    · apply ENNReal.div_le_div_left
      exact_mod_cast hrate x hx
    · simp [physicalOccupation, N.occupation_supported wr o hx]
  calc
    N.physicalTotal o ≤ ∑' x, N.occupation o x / (c : ℝ≥0∞) := ENNReal.tsum_le_tsum hdom
    _ = N.expectedReturnJumps o / (c : ℝ≥0∞) := by
      simp only [div_eq_mul_inv, ENNReal.tsum_mul_right, N.occupation_total]
    _ < ⊤ := ENNReal.div_lt_top hfin.ne (by exact_mod_cast hc.ne')

def normalizedOccupation (o x : State κ) : ℝ≥0∞ := N.physicalOccupation o x / N.physicalTotal o

theorem normalizedOccupation_total (wr : N.WeaklyReversible) (o : State κ)
    (hi : (Γ N.toRxn o).Infinite) (hfin : N.expectedReturnJumps o < ⊤) :
    (∑' x, N.normalizedOccupation o x) = 1 := by
  have hp : 0 < N.physicalTotal o :=
    (N.physicalOccupation_pos (N.root_mem_class o)).trans_le (ENNReal.le_tsum o)
  simp only [normalizedOccupation, div_eq_mul_inv, ENNReal.tsum_mul_right]
  exact ENNReal.mul_inv_cancel hp.ne' (N.physicalTotal_finite wr o hi hfin).ne

end AIM272.Network
