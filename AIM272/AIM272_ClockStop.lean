import AIM272_ClockResolvent

set_option warningAsError true

/-! # A nonpositive-clock stopping-time supersolution -/

noncomputable section
open scoped NNReal ENNReal BigOperators

namespace AIM272.RankedRace

variable {S : Type}

open Classical in
def observedSurvival (clock : ℝ → ℝ≥0) (mark : ℝ → S → PMF S)
    (ds : List ℝ) (ν : ℝ≥0) (dead : S → Prop) (x : S) : ℝ≥0∞ :=
  mean (observe clock mark ds ν x) (fun y => if dead y then 0 else 1)

theorem observedSurvival_le_one (clock : ℝ → ℝ≥0) (mark : ℝ → S → PMF S)
    (ds : List ℝ) (ν : ℝ≥0) (dead : S → Prop) (x : S) :
    observedSurvival clock mark ds ν dead x ≤ 1 := by
  classical
  calc
    _ ≤ mean (observe clock mark ds ν x) (fun _ => (1 : ℝ≥0∞)) := by
      unfold observedSurvival
      apply mean_mono
      intro y _
      by_cases hy : dead y
      · rw [if_pos hy]
        exact zero_le _
      · rw [if_neg hy]
    _ = 1 := mean_const _ _

theorem observedSurvival_dead {clock : ℝ → ℝ≥0} {mark : ℝ → S → PMF S} {dead : S → Prop}
    (hs : ∀ d x, dead x → mark d x = PMF.pure x) (ds : List ℝ) (ν : ℝ≥0)
    {x : S} (hx : dead x) : observedSurvival clock mark ds ν dead x = 0 := by
  classical
  simp only [observedSurvival, observe_stuck hs ds ν hx, mean_pure, if_pos hx]

/-- A stop-at-observation probability of at least p yields a Bellman
supersolution. Dividing it by νp gives a unit running time budget. -/
theorem observedSurvival_drift (clock : ℝ → ℝ≥0) (mark : ℝ → S → PMF S)
    (ds : List ℝ) {ν : ℝ≥0} (hν : 0 < ν) (dead : S → Prop)
    {x : S} (hx : ¬ dead x) {p : ℝ≥0} (hp : p ≤ prob (observe clock mark ds ν x) dead) :
    let U := observedSurvival clock mark ds ν dead
    (ν : ℝ≥0∞) * (p : ℝ≥0∞) +
      (ds.map (fun d => (clock d : ℝ≥0∞) * mean (mark d x) U)).sum ≤
      ((ds.map clock).sum : ℝ≥0∞) * U x := by
  classical
  let U := observedSurvival clock mark ds ν dead
  let μ := observe clock mark ds ν x
  let A : S → ℝ≥0∞ := fun y => if dead y then 0 else 1
  let D : S → ℝ≥0∞ := fun y => if dead y then 1 else 0
  let rest := (ds.map (fun d => (clock d : ℝ≥0∞) * mean (mark d x) U)).sum
  have compl : (prob μ dead : ℝ≥0∞) + U x = 1 := by
    rw [← mean_indicator, show U x = mean μ A from rfl, ← mean_add]
    have h (y : S) : D y + A y = 1 := by by_cases hy : dead y <;> simp [A, D, hy]
    change mean μ (fun y => D y + A y) = 1
    simp only [h, mean_const]
  have hle : (p : ℝ≥0∞) + U x ≤ 1 :=
    (add_le_add_right (ENNReal.coe_le_coe.mpr hp) _).trans compl.le
  have hid := observe_resolvent clock mark ds hν A x
  change ((ν + (ds.map clock).sum : ℝ≥0) : ℝ≥0∞) * U x = (ν : ℝ≥0∞) * A x + rest at hid
  rw [show A x = 1 from if_neg hx, mul_one, ENNReal.coe_add, add_mul] at hid
  have hfin : (ν : ℝ≥0∞) * U x ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((observedSurvival_le_one clock mark ds ν dead x).trans_lt ENNReal.one_lt_top)).ne
  change (ν : ℝ≥0∞) * (p : ℝ≥0∞) + rest ≤ ((ds.map clock).sum : ℝ≥0∞) * U x
  apply ENNReal.le_of_add_le_add_left hfin
  calc
    (ν : ℝ≥0∞) * U x + ((ν : ℝ≥0∞) * (p : ℝ≥0∞) + rest) =
      (ν : ℝ≥0∞) * ((p : ℝ≥0∞) + U x) + rest := by
        rw [mul_add, add_assoc, add_left_comm ((ν : ℝ≥0∞) * U x)]
    _ ≤ (ν : ℝ≥0∞) + rest := by
      simpa only [mul_one] using add_le_add_right (mul_le_mul_left' hle (ν : ℝ≥0∞)) rest
    _ = (ν : ℝ≥0∞) * U x + ((ds.map clock).sum : ℝ≥0∞) * U x := hid.symm

end AIM272.RankedRace
