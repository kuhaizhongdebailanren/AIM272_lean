import AIM272_Potential
import AIM272_Occupation

set_option warningAsError true

/-! # Finite-horizon bounds for rewards of the concrete jump chain -/

noncomputable section

open scoped ENNReal

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

def nextMean (f : State κ → ℝ≥0∞) (x : State κ) : ℝ≥0∞ := ∑' y, N.transition x y * f y

theorem nextMean_mono {f g : State κ → ℝ≥0∞} (h : ∀ y, f y ≤ g y) (x : State κ) :
    N.nextMean f x ≤ N.nextMean g x :=
  ENNReal.tsum_le_tsum fun y => mul_le_mul_left' (h y) _

theorem nextMean_const (c : ℝ≥0∞) (x : State κ) : N.nextMean (fun _ => c) x = c := by
  simp [nextMean, ENNReal.tsum_mul_right, N.transition_tsum]

theorem nextMean_add (f g : State κ → ℝ≥0∞) (x : State κ) :
    N.nextMean (fun y => f y + g y) x = N.nextMean f x + N.nextMean g x := by
  simp only [nextMean, mul_add, ENNReal.tsum_add]

theorem nextMean_sum {ι : Type*} (s : Finset ι) (f : ι → State κ → ℝ≥0∞) (x : State κ) :
    N.nextMean (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, N.nextMean (f i) x := by
  simp only [nextMean, Finset.mul_sum, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]

theorem nextMean_tsum {ι : Type*} (f : ι → State κ → ℝ≥0∞) (x : State κ) :
    N.nextMean (fun y => ∑' i, f i y) x = ∑' i, N.nextMean (f i) x := by
  simp only [nextMean, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

/-- A Bellman inequality bounds the killed reward at all finite horizons and hence in the limit. -/
theorem killedPotential_le_of_drift (Ω : Set (State κ)) (f W : State κ → ℝ≥0∞)
    (h : ∀ x ∈ Ω, f x + N.nextMean W x ≤ W x) (x : State κ) :
    N.killedPotential Ω f x ≤ W x := by
  classical
  have bound (m : ℕ) (y : State κ) : ∑ n ∈ Finset.range m, N.killedReward Ω f n y ≤ W y := by
    induction m generalizing y with
    | zero => simp
    | succ m ih =>
      by_cases hy : y ∈ Ω
      · rw [Finset.sum_range_succ']
        simp only [killedReward, if_pos hy]
        change (∑ i ∈ Finset.range m, N.nextMean (N.killedReward Ω f i) y) + f y ≤ W y
        rw [← N.nextMean_sum, add_comm]
        exact (add_le_add_left (N.nextMean_mono (fun z => ih z) y) _).trans (h y hy)
      · have hz (n : ℕ) : N.killedReward Ω f n y = 0 := by cases n <;> simp [killedReward, hy]
        simp [hz]
  rw [killedPotential, ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun k => bound k x

open Classical in
theorem aliveMass_pairing (o : State κ) (n : ℕ) (W : State κ → ℝ≥0∞) :
    (∑' z, N.aliveMass o (n + 1) z * W z) =
      ∑' y, N.aliveMass o n y * N.nextMean (fun z => if z = o then 0 else W z) y := by
  have ha (z : State κ) : N.aliveMass o (n + 1) z * W z =
      ∑' y, N.aliveMass o n y * (N.transition y z * (if z = o then 0 else W z)) := by
    by_cases hz : z = o
    · simp [hz, aliveMass]
    · rw [N.aliveMass_apply_of_ne hz, if_neg hz, ← ENNReal.tsum_mul_right]
      simp only [mul_assoc]
  simp_rw [ha]
  rw [ENNReal.tsum_comm]
  simp only [nextMean, ENNReal.tsum_mul_left]

open Classical in
/-- A superharmonic budget for the positive-return excursion. Killing is on arrival at the root. -/
theorem excursion_reward_le (o : State κ) (f W : State κ → ℝ≥0∞)
    (h : ∀ y, f y + N.nextMean (fun z => if z = o then 0 else W z) y ≤ W y) :
    (∑' z, N.occupation o z * f z) ≤ W o := by
  let prize (n : ℕ) := ∑' y, N.aliveMass o n y * f y
  let balance (n : ℕ) := ∑' y, N.aliveMass o n y * W y
  have step (n : ℕ) : prize n + balance (n + 1) ≤ balance n := by
    dsimp only [prize, balance]
    rw [N.aliveMass_pairing, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun y => by
      rw [← mul_add]
      exact mul_le_mul_left' (h y) _
  have bound (m : ℕ) : (∑ i ∈ Finset.range m, prize i) + balance m ≤ W o := by
    induction m with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, balance, aliveMass,
        ite_mul, one_mul, zero_mul]
      rw [tsum_eq_single o]
      · simp
      · intro y hy
        simp [hy]
    | succ m ih =>
      rw [Finset.sum_range_succ, add_assoc]
      exact (add_le_add_left (step m) _).trans ih
  calc
    (∑' z, N.occupation o z * f z) = ∑' n, prize n := by
      simp only [occupation, ← ENNReal.tsum_mul_right, prize]
      exact ENNReal.tsum_comm
    _ ≤ W o := by
      rw [ENNReal.tsum_eq_iSup_nat]
      exact iSup_le fun m => le_self_add.trans (bound m)

end AIM272.Network
