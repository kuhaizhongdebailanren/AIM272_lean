import AIM272_ReturnEstimate

set_option warningAsError true

/-! # Finite-horizon excursion estimates with an actual landing boundary -/

noncomputable section
open scoped BigOperators ENNReal

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

open Classical in
def untilRoot (o : State κ) (f : State κ → ℝ≥0∞) (x : State κ) : ℝ≥0∞ :=
  if x = o then 0 else f x

open Classical in
private theorem aliveMass_next_reward (o : State κ) (n : ℕ) (f : State κ → ℝ≥0∞) :
    (∑' y, N.aliveMass o (n + 1) y * f y) =
      ∑' z, N.aliveMass o n z * N.nextMean (untilRoot o f) z := by
  exact N.aliveMass_pairing o n f

open Classical in
private theorem initial_reward (o : State κ) (f : State κ → ℝ≥0∞) :
    (∑' y, N.aliveMass o 0 y * f y) = f o := by
  rw [tsum_eq_single o]
  · rw [N.aliveMass_zero_self, one_mul]
  · intro z hz
    simp [aliveMass, hz]

private theorem killedReward_succ_backward (o : State κ) (f : State κ → ℝ≥0∞) (n : ℕ) (x : State κ) :
    N.killedReward {z | z ≠ o} (N.nextMean (untilRoot o f)) n x =
      N.killedReward {z | z ≠ o} f (n + 1) x := by
  classical
  induction n generalizing x with
  | zero =>
    simp only [killedReward, nextMean, untilRoot, Set.mem_setOf_eq, ne_eq]
    by_cases hx : x = o
    · simp [hx]
    · simp only [hx, not_false_eq_true, if_true]
      exact tsum_congr fun y => by by_cases hy : y = o <;> simp [hy]
  | succ n ih =>
    rw [killedReward, killedReward]
    by_cases hx : x ∈ ({z | z ≠ o} : Set (State κ))
    · simp only [if_pos hx, ih]
    · simp only [if_neg hx]

theorem excursion_reward_eq (o : State κ) (f : State κ → ℝ≥0∞) :
    (∑' x, N.occupation o x * f x) = f o + N.nextMean (N.killedPotential {x | x ≠ o} f) o := by
  have h (n : ℕ) (g : State κ → ℝ≥0∞) :
      (∑' y, N.aliveMass o (n + 1) y * g y) = N.nextMean (N.killedReward {z | z ≠ o} g n) o := by
    induction n generalizing g with
    | zero =>
      rw [N.aliveMass_next_reward, N.initial_reward]
      congr 1
      funext z
      classical
      by_cases hz : z = o <;> simp [killedReward, untilRoot, hz]
    | succ n ih =>
      rw [N.aliveMass_next_reward, ih]
      congr 1
      funext z
      exact N.killedReward_succ_backward o g n z
  calc
    (∑' x, N.occupation o x * f x) = ∑' n, ∑' x, N.aliveMass o n x * f x := by
      simp only [occupation, ← ENNReal.tsum_mul_right]
      exact ENNReal.tsum_comm
    _ = f o + ∑' n, N.nextMean (N.killedReward {z | z ≠ o} f n) o := by
      rw [tsum_eq_zero_add' (f := fun n => ∑' x, N.aliveMass o n x * f x) ENNReal.summable,
        N.initial_reward]
      simp only [h]
    _ = _ := by
      change f o + (∑' n, N.nextMean (N.killedReward {z | z ≠ o} f n) o) =
        f o + N.nextMean (fun z => ∑' n, N.killedReward {z | z ≠ o} f n z) o
      rw [N.nextMean_tsum]

private def rewardThrough (Ω : Set (State κ)) (f : State κ → ℝ≥0∞) (n : ℕ) (x : State κ) :
    ℝ≥0∞ := ∑ i ∈ Finset.range n, N.killedReward Ω f i x

open Classical in
private theorem rewardThrough_succ (Ω : Set (State κ)) (f : State κ → ℝ≥0∞) (n : ℕ) (x : State κ) :
    N.rewardThrough Ω f (n + 1) x =
      if x ∈ Ω then f x + N.nextMean (N.rewardThrough Ω f n) x else 0 := by
  classical
  by_cases hx : x ∈ Ω
  · rw [if_pos hx, rewardThrough, Finset.sum_range_succ', add_comm]
    change N.killedReward Ω f 0 x + ∑ i ∈ Finset.range n, N.killedReward Ω f (i + 1) x = _
    simp only [killedReward, if_pos hx]
    congr 1
    exact (N.nextMean_sum _ _ x).symm
  · rw [if_neg hx]
    have hz (i : ℕ) : N.killedReward Ω f i x = 0 := by cases i <;> simp [killedReward, hx]
    simp [rewardThrough, hz]

private theorem rewardThrough_le (Ω : Set (State κ)) (f : State κ → ℝ≥0∞) (n : ℕ) (x : State κ) :
    N.rewardThrough Ω f n x ≤ N.killedPotential Ω f x :=
  ENNReal.sum_le_tsum _

private theorem rewardThrough_mono_domain {U V : Set (State κ)} (hUV : U ⊆ V)
    (f : State κ → ℝ≥0∞) (n : ℕ) (x : State κ) :
    N.rewardThrough U f n x ≤ N.rewardThrough V f n x := by
  classical
  induction n generalizing x with
  | zero => simp [rewardThrough]
  | succ n ih =>
    rw [N.rewardThrough_succ, N.rewardThrough_succ]
    by_cases hx : x ∈ U
    · rw [if_pos hx, if_pos (hUV hx)]
      exact add_le_add_left (N.nextMean_mono ih x) _
    · simp [hx]

open Classical in
/-- A one-step budget on a stopped domain. The payoff on each actual
landing point outside S may already account for all future visits. -/
theorem excursion_bound_of_stopped_budget (o : State κ) (S : Set (State κ))
    (f fee W : State κ → ℝ≥0∞) (hS : ∀ x ∈ S, x ≠ o)
    (boundary : ∀ x ∉ S, x ≠ o → N.killedPotential {y | y ≠ o} f x ≤ W x)
    (drift : ∀ x ∈ S, f x + N.nextMean (untilRoot o W) x ≤ W x + fee x)
    (source : f o + N.nextMean (untilRoot o W) o ≤ fee o) :
    (∑' x, N.occupation o x * f x) ≤ ∑' x, N.occupation o x * fee x := by
  classical
  let U : Set (State κ) := {y | y ≠ o}
  have hfinite (n : ℕ) (x : State κ) : N.rewardThrough U f n x ≤
      untilRoot o W x + N.rewardThrough S fee n x := by
    induction n generalizing x with
    | zero => simp [rewardThrough]
    | succ n ih =>
      by_cases hxo : x = o
      · rw [N.rewardThrough_succ, if_neg (show x ∉ U from not_not_intro hxo)]
        exact zero_le _
      by_cases hx : x ∈ S
      · rw [N.rewardThrough_succ, N.rewardThrough_succ, if_pos (show x ∈ U from hxo), if_pos hx]
        have h := N.nextMean_mono ih x
        rw [N.nextMean_add] at h
        rw [show untilRoot o W x = W x from if_neg hxo, ← add_assoc]
        exact (add_le_add_left h _).trans
          (by rw [← add_assoc]; exact add_le_add_right (drift x hx) _)
      · exact (N.rewardThrough_le U f (n + 1) x).trans
          ((by simpa only [untilRoot, if_neg hxo] using boundary x hx hxo :
            N.killedPotential U f x ≤ untilRoot o W x).trans le_self_add)
  have hupper (x : State κ) : N.killedPotential U f x ≤ untilRoot o W x + N.killedPotential U fee x := by
    rw [killedPotential, ENNReal.tsum_eq_iSup_nat]
    exact iSup_le fun n => (hfinite n x).trans (add_le_add_left
      ((N.rewardThrough_mono_domain hS fee n x).trans (N.rewardThrough_le U fee n x)) _)
  rw [N.excursion_reward_eq, N.excursion_reward_eq]
  have hh := N.nextMean_mono hupper o
  rw [N.nextMean_add] at hh
  exact (add_le_add_left hh _).trans (by rw [← add_assoc]; exact add_le_add_right source _)

end AIM272.Network
