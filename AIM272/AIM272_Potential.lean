import AIM272_Levels

set_option warningAsError true

/-!
# The local potential of the concrete jump chain

The killed reward at each time is calculated by iteration of the
transition kernel. Its sum satisfies the first-step Poisson identity
in extended nonnegative reals. The upper comparison requires the
separate sampling and stopping-time estimates.
-/

noncomputable section

open scoped ENNReal NNReal

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

open Classical in
/-- Expected reward at step n, killed on leaving the domain. -/
def killedReward (Ω : Set (State κ)) (reward : State κ → ℝ≥0∞) : ℕ → State κ → ℝ≥0∞
  | 0, x => if x ∈ Ω then reward x else 0
  | n + 1, x => if x ∈ Ω then ∑' y, N.transition x y * killedReward Ω reward n y else 0

def killedPotential (Ω : Set (State κ)) (reward : State κ → ℝ≥0∞) (x : State κ) : ℝ≥0∞ :=
  ∑' n, N.killedReward Ω reward n x

theorem killedPotential_zero {Ω : Set (State κ)} {x : State κ} (hx : x ∉ Ω)
    (reward : State κ → ℝ≥0∞) : N.killedPotential Ω reward x = 0 := by
  classical
  have h (n : ℕ) : N.killedReward Ω reward n x = 0 := by
    cases n <;> simp [killedReward, hx]
  simp only [killedPotential, h, tsum_zero]

theorem killedPotential_eq {Ω : Set (State κ)} {x : State κ} (hx : x ∈ Ω)
    (reward : State κ → ℝ≥0∞) :
    N.killedPotential Ω reward x = reward x + ∑' y, N.transition x y * N.killedPotential Ω reward y := by
  classical
  let f : ℕ → ℝ≥0∞ := fun n => N.killedReward Ω reward n x
  calc
    N.killedPotential Ω reward x =
        N.killedReward Ω reward 0 x + ∑' n, N.killedReward Ω reward (n + 1) x := by
      change (∑' n, f n) = f 0 + ∑' n, f (n + 1)
      exact tsum_eq_zero_add' (f := f) ENNReal.summable
    _ = reward x + ∑' n, ∑' y, N.transition x y * N.killedReward Ω reward n y := by
      simp only [killedReward, if_pos hx]
    _ = reward x + ∑' y, N.transition x y * N.killedPotential Ω reward y := by
      rw [ENNReal.tsum_comm]
      simp only [killedPotential, ENNReal.tsum_mul_left]

def localDomain (a : κ → ℝ) (R E : ℝ) : Set (State κ) :=
  {x | N.NegativeLoop a x ∧ (radius x : ℝ) ≤ R - 2 ∧
    ∀ i, |Real.log ((x i : ℝ) + 1) / Real.log R - a i| < E}

def localPotential (wr : N.WeaklyReversible) (a : κ → ℝ) (R E θ : ℝ)
    (x : State κ) : ℝ≥0∞ :=
  N.killedPotential (N.localDomain a R E)
    (fun y => ENNReal.ofReal (R ^ (θ * N.level wr a y))) x

/-- Additive form of (P - I) U = -R^(θℓ) on the local domain. -/
theorem localPotential_poisson (wr : N.WeaklyReversible) (a : κ → ℝ) (R E θ : ℝ)
    {x : State κ} (hx : x ∈ N.localDomain a R E) :
    N.localPotential wr a R E θ x = ENNReal.ofReal (R ^ (θ * N.level wr a x)) +
      ∑' y, N.transition x y * N.localPotential wr a R E θ y :=
  N.killedPotential_eq hx _

theorem localPotential_lower (wr : N.WeaklyReversible) (a : κ → ℝ) {R E θ : ℝ}
    (hR : 1 ≤ R) (hθ : 0 ≤ θ) {x : State κ} (hx : x ∈ N.localDomain a R E) :
    ENNReal.ofReal (R ^ (-(θ * N.maxComplexHeight a)) * R ^ (θ * weight a x)) ≤
      N.localPotential wr a R E θ x := by
  have hR' : 0 < R := zero_lt_one.trans_le hR
  have hp := ((N.peaks wr a).bounds x hx.1).1
  have hPow : -(θ * N.maxComplexHeight a) + θ * weight a x ≤ θ * N.level wr a x := by
    have h := mul_le_mul_of_nonneg_left hp hθ
    change θ * (-N.maxComplexHeight a) ≤ θ * N.psi wr a x at h
    unfold level
    linarith
  rw [← Real.rpow_add hR']
  apply (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hR hPow)).trans
  rw [N.localPotential_poisson wr a R E θ hx]
  exact le_self_add

end AIM272.Network
