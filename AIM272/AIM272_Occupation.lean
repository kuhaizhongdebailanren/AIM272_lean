import AIM272_Model

set_option warningAsError true

/-!
# Occupation before the first positive return

At time zero the entire mass is at the root. At each step the jump kernel
is applied, then arrivals at the root are removed. The surviving mass at
time n therefore counts the histories with n strictly before the return.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open AIM272Unusable (Γ)

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

open Classical in
/-- The mass at each site before the first positive return to the root. -/
def aliveMass (o : State κ) : ℕ → State κ → ℝ≥0∞
  | 0, x => if x = o then 1 else 0
  | n + 1, x => if x = o then 0 else ∑' y, aliveMass o n y * N.transition y x

theorem aliveMass_zero_self (o : State κ) : N.aliveMass o 0 o = 1 := by
  classical
  simp [aliveMass]

theorem aliveMass_succ_self (o : State κ) (n : ℕ) : N.aliveMass o (n + 1) o = 0 := by
  classical
  simp [aliveMass]

theorem aliveMass_apply_of_ne {o x : State κ} (h : x ≠ o) (n : ℕ) :
    N.aliveMass o (n + 1) x = ∑' y, N.aliveMass o n y * N.transition y x := by
  classical
  simp [aliveMass, h]

theorem aliveMass_supported (wr : N.WeaklyReversible) (o : State κ) (n : ℕ)
    {x : State κ} (hx : x ∉ Γ N.toRxn o) : N.aliveMass o n x = 0 := by
  classical
  have hne : x ≠ o := fun he => hx (he.symm ▸ N.root_mem_class o)
  induction n generalizing x with
  | zero => simp [aliveMass, hne]
  | succ n ih =>
    rw [N.aliveMass_apply_of_ne hne]
    have hterm (y : State κ) : N.aliveMass o n y * N.transition y x = 0 := by
      by_cases hy : y ∈ Γ N.toRxn o
      · have hz : N.transition y x = 0 :=
          le_antisymm (le_of_not_gt (fun h => hx (N.t0_transition_closed wr o hy h))) (zero_le _)
        rw [hz, mul_zero]
      · have hyne : y ≠ o := fun he => hy (he.symm ▸ N.root_mem_class o)
        rw [ih hy hyne, zero_mul]
    simp only [hterm, tsum_zero]

/-- Expected visits, including time zero and excluding the first return. -/
def occupation (o x : State κ) : ℝ≥0∞ := ∑' n, N.aliveMass o n x

theorem occupation_eq_iSup (o x : State κ) :
    N.occupation o x = ⨆ k : ℕ, ∑ n ∈ Finset.range k, N.aliveMass o n x :=
  ENNReal.tsum_eq_iSup_nat

theorem occupation_root (o : State κ) : N.occupation o o = 1 := by
  rw [occupation, tsum_eq_single 0, N.aliveMass_zero_self]
  intro n hn
  cases n with
  | zero => exact (hn rfl).elim
  | succ _ => exact N.aliveMass_succ_self _ _

theorem occupation_supported (wr : N.WeaklyReversible) (o : State κ)
    {x : State κ} (hx : x ∉ Γ N.toRxn o) : N.occupation o x = 0 := by
  simp only [occupation, fun n => N.aliveMass_supported wr o n hx, tsum_zero]

/-- Expected return jump count, expressed as the sum of survival masses. -/
def expectedReturnJumps (o : State κ) : ℝ≥0∞ := ∑' n, ∑' x, N.aliveMass o n x

theorem occupation_total (o : State κ) :
    (∑' x, N.occupation o x) = N.expectedReturnJumps o := by
  unfold occupation expectedReturnJumps
  exact ENNReal.tsum_comm

theorem occupation_total_on_class (wr : N.WeaklyReversible) (o : State κ) :
    (∑' x : Γ N.toRxn o, N.occupation o x) = N.expectedReturnJumps o := by
  rw [← N.occupation_total o]
  exact tsum_subtype_eq_of_support_subset (fun x hx =>
    by_contra fun h => hx (N.occupation_supported wr o h))

/-- T1 of the target sheet, stated on the concrete killed jump kernel. -/
def FactorialBound (o : State κ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ x ∈ Γ N.toRxn o,
    (stateFactorial x : ℝ≥0∞) * N.occupation o x ≤
      (C : ℝ≥0∞) * ENNReal.ofReal
        (Real.exp (δ * (radius x : ℝ) * Real.log (2 + (radius x : ℝ))))

/-- Physical occupation specified by the occupation and total rate. -/
def physicalOccupation (o x : State κ) : ℝ≥0∞ :=
  N.occupation o x / (N.totalRate x : ℝ≥0∞)

end AIM272.Network
