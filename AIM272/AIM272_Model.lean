import AIM272_Unusable

set_option warningAsError true

/-!
# Stochastic mass action and closed communicating classes

The reaction graph and the count-vector reachability relation are defined
before choosing rates. The latter is reused from AIM272_Unusable.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal
open AIM272Unusable (Step Reach Γ)

namespace AIM272

abbrev State (κ : Type) := κ → ℕ

structure Network (κ L : Type) extends AIM272Unusable.Rxn κ L where
  rateConstant : L → ℝ≥0
  rateConstant_pos : ∀ r, 0 < rateConstant r
  distinct : ∀ r, s r ≠ t r

namespace Network

variable {κ L : Type} (N : Network κ L)

def ComplexEdge (a b : State κ) : Prop :=
  ∃ r, N.s r = a ∧ N.t r = b

/-- Every reaction lies on a directed cycle in the complex graph. -/
def WeaklyReversible : Prop :=
  ∀ r, Relation.ReflTransGen N.ComplexEdge (N.t r) (N.s r)

theorem complex_copy_reach (z : State κ) {a b : State κ}
    (h : Relation.ReflTransGen N.ComplexEdge a b) :
    Reach N.toRxn (a + z) (b + z) := by
  apply Relation.ReflTransGen.lift (· + z) _ h
  rintro _ _ ⟨r, rfl, rfl⟩
  exact AIM272Unusable.step_shift N.toRxn z ⟨r, le_rfl, by simp⟩

theorem step_has_return (wr : N.WeaklyReversible) {x y : State κ}
    (h : Step N.toRxn x y) : Reach N.toRxn y x := by
  obtain ⟨r, hr, hy⟩ := h
  have hx' : N.s r + (x - N.s r) = x := by
    funext i
    have hi : N.s r i ≤ x i := hr i
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have hy' : N.t r + (x - N.s r) = y := by rw [hy, add_comm]
  simpa only [hx', hy'] using N.complex_copy_reach (x - N.s r) (wr r)

theorem root_mem_class (o : State κ) : o ∈ Γ N.toRxn o :=
  ⟨.refl, .refl⟩

/-- T0 on the graph of enabled jumps. -/
theorem t0_closed (wr : N.WeaklyReversible) (o : State κ) {x y : State κ}
    (hx : x ∈ Γ N.toRxn o) (hxy : Step N.toRxn x y) : y ∈ Γ N.toRxn o :=
  ⟨.tail hx.1 hxy, (N.step_has_return wr hxy).trans hx.2⟩

theorem class_reach {o x y : State κ} (hx : x ∈ Γ N.toRxn o) (hy : y ∈ Γ N.toRxn o) :
    Reach N.toRxn x y :=
  hx.2.trans hy.1

def jump (x : State κ) (r : L) : State κ := x - N.s r + N.t r

private theorem step_exists_of_reach_ne {x y : State κ}
    (h : Reach N.toRxn x y) : x ≠ y → ∃ z, Step N.toRxn x z := by
  induction h with
  | refl => exact fun hne => (hne rfl).elim
  | @tail b c _ hs ih =>
    intro _
    by_cases heq : x = b
    · exact ⟨c, heq.symm ▸ hs⟩
    · exact ih heq

section Rates

variable [Fintype κ]

def radius (x : State κ) : ℕ := Finset.univ.sup x

def stateFactorial (x : State κ) : ℕ := ∏ i, (x i).factorial

def rateFactor (x : State κ) (r : L) : ℕ :=
  ∏ i, (x i).descFactorial (N.s r i)

def rate (x : State κ) (r : L) : ℝ≥0 := N.rateConstant r * (N.rateFactor x r : ℝ≥0)

theorem rateFactor_pos_iff (x : State κ) (r : L) :
    0 < N.rateFactor x r ↔ N.s r ≤ x := by
  classical
  constructor
  · intro h i
    by_contra hi
    have hz := Nat.descFactorial_of_lt (show x i < N.s r i from lt_of_not_ge hi)
    exact (ne_of_gt h) (Finset.prod_eq_zero (Finset.mem_univ i) hz)
  · intro h
    exact Finset.prod_pos fun i _ => Nat.descFactorial_pos.mpr (h i)

theorem rate_pos_iff (x : State κ) (r : L) : 0 < N.rate x r ↔ N.s r ≤ x := by
  constructor
  · intro h
    apply (N.rateFactor_pos_iff x r).mp
    by_contra hn
    simp [rate, Nat.eq_zero_of_not_pos hn] at h
  · intro h
    exact mul_pos (N.rateConstant_pos r)
      (by exact_mod_cast (N.rateFactor_pos_iff x r).mpr h)

theorem rateConstant_le_rate {x : State κ} {r : L} (h : N.s r ≤ x) :
    N.rateConstant r ≤ N.rate x r := by
  have hf : 1 ≤ N.rateFactor x r := (N.rateFactor_pos_iff x r).mpr h
  exact le_mul_of_one_le_right (zero_le _) (by exact_mod_cast hf)

variable [Fintype L]

def totalRate (x : State κ) : ℝ≥0 := ∑ r, N.rate x r

theorem rate_le_totalRate (x : State κ) (r : L) : N.rate x r ≤ N.totalRate x :=
  Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ r)

omit [Fintype κ] [Fintype L] in
theorem enabled_in_infinite_class {o x : State κ}
    (hi : (Γ N.toRxn o).Infinite) (hx : x ∈ Γ N.toRxn o) : ∃ r, N.s r ≤ x := by
  obtain ⟨y, hy, hyx⟩ := hi.exists_notMem_finite (Set.finite_singleton x)
  have hyx' : y ≠ x := fun h => hyx (Set.mem_singleton_iff.mpr h)
  obtain ⟨_, r, hr, _⟩ := N.step_exists_of_reach_ne (N.class_reach hx hy) hyx'.symm
  exact ⟨r, hr⟩

/-- The lower bound on the total mass-action rate in an infinite class. -/
theorem totalRate_lower_bound {o : State κ} (hi : (Γ N.toRxn o).Infinite) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ x ∈ Γ N.toRxn o, c ≤ N.totalRate x := by
  classical
  obtain ⟨r, _⟩ := N.enabled_in_infinite_class hi (N.root_mem_class o)
  obtain ⟨r₀, _, hmin⟩ :=
    Finset.exists_min_image Finset.univ N.rateConstant ⟨r, Finset.mem_univ r⟩
  refine ⟨N.rateConstant r₀, N.rateConstant_pos r₀, fun x hx => ?_⟩
  obtain ⟨r', hr'⟩ := N.enabled_in_infinite_class hi hx
  exact (hmin r' (Finset.mem_univ r')).trans
    ((N.rateConstant_le_rate hr').trans (N.rate_le_totalRate x r'))

theorem totalRate_pos_on_class {o x : State κ} (hi : (Γ N.toRxn o).Infinite)
    (hx : x ∈ Γ N.toRxn o) : 0 < N.totalRate x := by
  obtain ⟨r, hr⟩ := N.enabled_in_infinite_class hi hx
  exact ((N.rate_pos_iff x r).mpr hr).trans_le (N.rate_le_totalRate x r)

def jumpProbability (x : State κ) (r : L) : ℝ≥0 :=
  N.rate x r / N.totalRate x

open Classical in
/-- Embedded jump kernel. An absorbing state has a Dirac row. -/
def transition (x y : State κ) : ℝ≥0∞ :=
  if N.totalRate x = 0 then
    if y = x then 1 else 0
  else
    ∑ r, if N.jump x r = y then (N.jumpProbability x r : ℝ≥0∞) else 0

theorem transition_tsum (x : State κ) : (∑' y, N.transition x y) = 1 := by
  classical
  by_cases hq : N.totalRate x = 0
  · simp [transition, hq, tsum_ite_eq]
  · simp only [transition, hq, if_false]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    have hterm (r : L) :
        (∑' y : State κ, if N.jump x r = y then (N.jumpProbability x r : ℝ≥0∞) else 0) =
          (N.jumpProbability x r : ℝ≥0∞) := by
      rw [tsum_eq_single (N.jump x r)]
      · simp
      · intro y hy
        simp [Ne.symm hy]
    simp_rw [hterm]
    rw [← ENNReal.coe_finset_sum]
    have hsum : (∑ r, N.jumpProbability x r) = 1 := by
      simp only [jumpProbability, div_eq_mul_inv, ← Finset.sum_mul]
      change N.totalRate x * (N.totalRate x)⁻¹ = 1
      exact mul_inv_cancel₀ hq
    rw [hsum, ENNReal.coe_one]

theorem transition_pos_iff_step {x y : State κ} (hq : N.totalRate x ≠ 0) :
    0 < N.transition x y ↔ Step N.toRxn x y := by
  classical
  have hqt : 0 < N.totalRate x := lt_of_le_of_ne (zero_le _) (Ne.symm hq)
  simp only [transition, hq, if_false]
  constructor
  · intro h
    by_contra hs
    have hz : (∑ r, if N.jump x r = y then (N.jumpProbability x r : ℝ≥0∞) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r _
      split_ifs with hxy
      · have hr : ¬ N.s r ≤ x := fun h => hs ⟨r, h, hxy.symm⟩
        have hz' : N.rate x r = 0 :=
          le_antisymm (le_of_not_gt (mt (N.rate_pos_iff x r).mp hr)) (zero_le _)
        simp [jumpProbability, hz']
      · rfl
    exact (ne_of_gt h) hz
  · rintro ⟨r, hr, hxy⟩
    apply lt_of_lt_of_le _ (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ r))
    have e : N.jump x r = y := hxy.symm
    simp only [e, if_true, ENNReal.coe_pos, jumpProbability]
    exact div_pos ((N.rate_pos_iff x r).mpr hr) hqt

theorem transition_pos_of_step {x y : State κ} (hxy : Step N.toRxn x y) :
    0 < N.transition x y := by
  obtain ⟨r, hr, hy⟩ := hxy
  have hq := ((N.rate_pos_iff x r).mpr hr).trans_le (N.rate_le_totalRate x r)
  exact (N.transition_pos_iff_step hq.ne').mpr ⟨r, hr, hy⟩

/-- T0 stated for the support of the actual embedded jump kernel. -/
theorem t0_transition_closed (wr : N.WeaklyReversible) (o : State κ) {x y : State κ}
    (hx : x ∈ Γ N.toRxn o) (hxy : 0 < N.transition x y) : y ∈ Γ N.toRxn o := by
  classical
  by_cases hq : N.totalRate x = 0
  · by_cases heq : y = x
    · simpa only [heq] using hx
    · simp [transition, hq, heq] at hxy
  · exact N.t0_closed wr o hx ((N.transition_pos_iff_step hq).mp hxy)

end Rates
end Network
end AIM272
