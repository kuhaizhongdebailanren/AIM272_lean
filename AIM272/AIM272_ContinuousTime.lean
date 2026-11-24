import AIM272_Stationary
import AIM272_Tails

set_option warningAsError true

/-! # The minimal continuous-time chain and its excursion distribution -/

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory
open AIM272Unusable (Γ Step Reach)

namespace AIM272.ContinuousTime

variable {S : Type}
abbrev JumpMatrix (S : Type) := S → S → ℝ≥0∞

open Classical in
/-- Mass at y at time t with exactly n jumps, by the first holding-time decomposition. -/
def finiteJumpTerm (P : JumpMatrix S) (q : S → ℝ≥0) : ℕ → ℝ → S → S → ℝ≥0∞
  | 0, t, x, y => if x = y then ENNReal.ofReal (Real.exp (-(q x : ℝ) * t)) else 0
  | n + 1, t, x, y =>
    ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal ((q x : ℝ) * Real.exp (-(q x : ℝ) * s)) *
      ∑' z, P x z * finiteJumpTerm P q n (t - s) z y

/-- The minimal transition function counts all finite jump histories up to time t. -/
def minimalTransition (P : JumpMatrix S) (q : S → ℝ≥0) (t : ℝ) (x y : S) : ℝ≥0∞ :=
  ∑' n, finiteJumpTerm P q n t x y

def NonexplosiveOn (P : JumpMatrix S) (q : S → ℝ≥0) (I : Set S) : Prop :=
  ∀ x ∈ I, ∀ t : ℝ, 0 ≤ t → (∑' y, minimalTransition P q t x y) = 1

def StationaryOn (P : JumpMatrix S) (q : S → ℝ≥0) (I : Set S) (π : S → ℝ≥0∞) : Prop :=
  (∑' x, π x) = 1 ∧ (∀ x ∉ I, π x = 0) ∧
    ∀ t : ℝ, 0 ≤ t → ∀ y, (∑' x, π x * minimalTransition P q t x y) = π y

/-- Pre-return occupation multiplied by the mean holding time at a state. -/
def physicalMass (q : S → ℝ≥0) (A : S → ℕ → S → ℝ≥0∞) (o x : S) : ℝ≥0∞ :=
  (∑' n, A o n x) / (q x : ℝ≥0∞)

def excursionLaw (q : S → ℝ≥0) (A : S → ℕ → S → ℝ≥0∞) (o x : S) : ℝ≥0∞ :=
  physicalMass q A o x / ∑' z, physicalMass q A o z

/-- Each state returns with probability one and has finite mean physical return time. -/
def PositiveRecurrentOn (P : JumpMatrix S) (q : S → ℝ≥0) (I : Set S)
    (A : S → ℕ → S → ℝ≥0∞) : Prop :=
  ∀ x ∈ I, (∑' n, ∑' y, A x n y * P y x) = 1 ∧ (∑' y, physicalMass q A x y) < ⊤

open Classical in
/-- Norris, Markov Chains (1997), §§2.6–2.7 and 3.4–3.5, the embedded-chain
return criterion and excursion occupation formula. This is the general
classical input allowed by §3(1) of the target sheet. A is explicitly
required to satisfy the killed transition recursion for every root. -/
def NorrisJumpReturn (S : Type) [Countable S] : Prop :=
  ∀ (P : JumpMatrix S) (q : S → ℝ≥0) (I : Set S) (o : S) (A : S → ℕ → S → ℝ≥0∞),
    (∀ x, (∑' y, P x y) = 1) →
    (∀ x ∈ I, P x x = 0) →
    (∀ x ∈ I, ∀ y, 0 < P x y → y ∈ I) →
    (∀ x ∈ I, ∀ y ∈ I, Relation.ReflTransGen (fun z w => 0 < P z w) x y) →
    o ∈ I → (∃ c : ℝ≥0, 0 < c ∧ ∀ x ∈ I, c ≤ q x) →
    (∀ r z, A r 0 z = if z = r then 1 else 0) →
    (∀ r n z, A r (n + 1) z = if z = r then 0 else ∑' y, A r n y * P y z) →
    (∑' n, ∑' z, A o n z) < ⊤ →
    NonexplosiveOn P q I ∧ PositiveRecurrentOn P q I A ∧
      StationaryOn P q I (excursionLaw q A o) ∧
      ∀ π, StationaryOn P q I π → π = excursionLaw q A o

end AIM272.ContinuousTime

namespace AIM272.Network

open ContinuousTime
variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

theorem transition_self_of_enabled {x : State κ} (hq : N.totalRate x ≠ 0) :
    N.transition x x = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_not_gt
  intro hp
  obtain ⟨r, hr, he⟩ := (N.transition_pos_iff_step hq).mp hp
  apply N.distinct r
  funext i
  have hu := congrFun he i
  have hi := hr i
  change x i = x i - N.s r i + N.t r i at hu
  exact Nat.add_left_cancel ((Nat.sub_add_cancel hi).trans hu)

/-- T3(ii) and uniqueness/stationarity in T3(iii) from finite expected return jumps,
using exactly the classical assertion NorrisJumpReturn. -/
theorem continuousTime_of_finite_return (wr : N.WeaklyReversible) (o : State κ)
    (hi : (Γ N.toRxn o).Infinite) (norris : NorrisJumpReturn (State κ))
    (hfin : N.expectedReturnJumps o < ⊤) :
    NonexplosiveOn N.transition N.totalRate (Γ N.toRxn o) ∧
    PositiveRecurrentOn N.transition N.totalRate (Γ N.toRxn o) N.aliveMass ∧
    StationaryOn N.transition N.totalRate (Γ N.toRxn o) (N.normalizedOccupation o) ∧
    ∀ π, StationaryOn N.transition N.totalRate (Γ N.toRxn o) π → π = N.normalizedOccupation o := by
  classical
  apply norris N.transition N.totalRate (Γ N.toRxn o) o N.aliveMass N.transition_tsum
    (fun _ hx => N.transition_self_of_enabled (N.totalRate_pos_on_class hi hx).ne')
    (fun _ hx _ hxy => N.t0_transition_closed wr o hx hxy)
    _ (N.root_mem_class o) (N.totalRate_lower_bound hi)
    (fun r z => by by_cases he : z = r <;> simp [aliveMass, he])
    (fun r n z => by by_cases he : z = r <;> simp [aliveMass, he]) hfin
  intro x hx y hy
  exact (N.class_reach hx hy).mono (fun _ _ h => N.transition_pos_of_step h)

/-- Dividing by the total rate and the physical mass preserves the T1 exponent for every δ. -/
theorem normalized_factorial_tail (o : State κ)
    (hi : (Γ N.toRxn o).Infinite) (h : N.FactorialBound o) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ x ∈ Γ N.toRxn o,
      (stateFactorial x : ℝ≥0∞) * N.normalizedOccupation o x ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (Real.exp (δ * (radius x : ℝ) * Real.log (2 + (radius x : ℝ)))) := by
  obtain ⟨c, hc, hq⟩ := N.totalRate_lower_bound hi
  have hZ : 0 < N.physicalTotal o :=
    (N.physicalOccupation_pos (N.root_mem_class o)).trans_le (ENNReal.le_tsum o)
  intro δ hδ
  obtain ⟨C, hC⟩ := h δ hδ
  let u : ℝ≥0∞ := (c : ℝ≥0∞)⁻¹ * (N.physicalTotal o)⁻¹
  have hu : u ≠ ⊤ := (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by exact_mod_cast hc))
    (ENNReal.inv_lt_top.mpr hZ)).ne
  refine ⟨C * u.toNNReal, fun x hx => ?_⟩
  have hxq : (c : ℝ≥0∞) ≤ (N.totalRate x : ℝ≥0∞) := by exact_mod_cast hq x hx
  calc
    _ = ((stateFactorial x : ℝ≥0∞) * N.occupation o x) *
        ((N.totalRate x : ℝ≥0∞)⁻¹ * (N.physicalTotal o)⁻¹) := by
          simp only [normalizedOccupation, physicalOccupation, div_eq_mul_inv]; ac_rfl
    _ ≤ ((C : ℝ≥0∞) * ENNReal.ofReal _) * u := mul_le_mul' (hC x hx)
      (mul_le_mul_right' (ENNReal.inv_le_inv.mpr hxq) _)
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hu]; ac_rfl

end AIM272.Network
