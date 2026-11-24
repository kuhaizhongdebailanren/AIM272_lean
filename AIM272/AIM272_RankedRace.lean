import AIM272_Conditional
import Mathlib

set_option warningAsError true

/-! # Discrete probability law of the ranked exponential race

A rank gap and a thinned mark are probability mass functions. Conditional
on n marks, their successive applications are ordinary monadic composition.
The number of marks is geometric, including the possibility of zero marks.
-/

noncomputable section
open scoped ENNReal NNReal
open MeasureTheory
namespace AIM272.RankedRace

variable {S T : Type}

def prob (μ : PMF S) (A : S → Prop) : ℝ≥0 := (μ.toOuterMeasure {x | A x}).toNNReal

theorem coe_prob (μ : PMF S) (A : S → Prop) : (prob μ A : ℝ≥0∞) = μ.toOuterMeasure {x | A x} := by
  apply ENNReal.coe_toNNReal
  rw [PMF.toOuterMeasure_apply]
  exact μ.tsum_coe_indicator_ne_top _

theorem prob_le_one (μ : PMF S) (A : S → Prop) : prob μ A ≤ 1 := by
  apply ENNReal.coe_le_coe.mp
  rw [coe_prob, ENNReal.coe_one, ← (μ.toOuterMeasure_apply_eq_one_iff Set.univ).mpr (Set.subset_univ _)]
  exact measure_mono (Set.subset_univ _)

theorem prob_mono (μ : PMF S) {A B : S → Prop} (h : ∀ x, A x → B x) : prob μ A ≤ prob μ B := by
  apply ENNReal.coe_le_coe.mp
  rw [coe_prob, coe_prob]
  exact measure_mono fun x => h _

theorem prob_support (μ : PMF S) {A : S → Prop} (h : ∀ x ∈ μ.support, A x) : prob μ A = 1 := by
  apply ENNReal.coe_injective
  rw [coe_prob, ENNReal.coe_one]
  exact (μ.toOuterMeasure_apply_eq_one_iff _).mpr (fun _ hx => h _ hx)

theorem bind_lower (μ : PMF S) (K : S → PMF T) {E : S → Prop} {A : T → Prop} {a b : ℝ≥0}
    (hμ : a ≤ prob μ E) (hK : ∀ x, E x → b ≤ prob (K x) A) :
    a * b ≤ prob (μ.bind K) A := by
  classical
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_mul, coe_prob, PMF.toOuterMeasure_bind_apply]
  apply (mul_le_mul_right' (ENNReal.coe_le_coe.mpr hμ) _).trans
  rw [coe_prob, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : E x
  · rw [Set.indicator_of_mem (show x ∈ {z | E z} from hx)]
    apply mul_le_mul_left'
    rw [← coe_prob]
    exact ENNReal.coe_le_coe.mpr (hK x hx)
  · rw [Set.indicator_of_notMem (show x ∉ {z | E z} from hx), zero_mul]
    exact zero_le _

def run (gap mark : S → PMF S) : List RaceAction → S → PMF S
  | [], x => PMF.pure x
  | .gap :: w, x => (gap x).bind (run gap mark w)
  | .ring :: w, x => (mark x).bind (run gap mark w)

theorem run_append (gap mark : S → PMF S) (u v : List RaceAction) (x : S) :
    run gap mark (u ++ v) x = (run gap mark u x).bind (run gap mark v) := by
  induction u generalizing x with
  | nil => simp [run]
  | cons b u ih =>
    cases b <;> simp only [List.cons_append, run, PMF.bind_bind] <;> rw [funext ih]

theorem run_stuck {gap mark : S → PMF S} {x : S} (hg : gap x = PMF.pure x) (hm : mark x = PMF.pure x)
    (w : List RaceAction) : run gap mark w x = PMF.pure x := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [run, hg, hm, ih]

def kernel {fast charged : S → S → Prop} {dead : S → Prop} (gap mark : S → PMF S)
    (hg : ∀ x, dead x → gap x = PMF.pure x) (hm : ∀ x, dead x → mark x = PMF.pure x)
    (gapLaw : ∀ x y, y ∈ (gap x).support → dead y ∨ FastPath fast x y)
    (markLaw : ∀ x y, y ∈ (mark x).support → dead y ∨ x = y ∨ charged x y) :
    RankKernel (W := ℝ≥0) fast charged dead where
  probability w x := prob (run gap mark w x)
  enlarge := fun h => prob_mono _ h
  compose := by
    intro u v x E A a b ha hb
    rw [run_append]
    exact bind_lower _ _ ha hb
  stuck := by
    intro w x A hd
    rw [run_stuck (hg x hd) (hm x hd) w]
    exact (prob_support _ (fun y hy => Or.inl (((PMF.mem_support_pure_iff x y).mp hy).symm ▸ hd))).ge
  gapSupport := by
    intro x
    simpa [run] using (prob_support _ (gapLaw x)).ge
  roundsSupport := by
    intro n x
    apply (prob_support _ ?_).ge
    induction n generalizing x with
    | zero =>
      intro y hy
      have h : y = x := (PMF.mem_support_pure_iff x y).mp hy
      subst y
      exact Or.inr ⟨0, .nil x⟩
    | succ n ih =>
      intro y hy
      change y ∈ ((gap x).bind (fun v => (mark v).bind (run gap mark (rankRounds n)))).support at hy
      obtain ⟨v, hv, htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
      obtain ⟨z, hz, hyz⟩ := (PMF.mem_support_bind_iff _ _ _).mp htail
      rcases gapLaw x v hv with hd | hvf
      · rw [hm v hd] at hz
        have he := (PMF.mem_support_pure_iff v z).mp hz
        subst z
        rw [run_stuck (hg _ hd) (hm _ hd)] at hyz
        exact Or.inl (((PMF.mem_support_pure_iff v y).mp hyz).symm ▸ hd)
      rcases markLaw v z hz with hd | he | hvz
      · rw [run_stuck (hg _ hd) (hm _ hd)] at hyz
        exact Or.inl (((PMF.mem_support_pure_iff z y).mp hyz).symm ▸ hd)
      · subst z
        rcases ih v y hyz with hd | ⟨k, hpath⟩
        · exact Or.inl hd
        · exact Or.inr ⟨k, hvf.prependCharged hpath⟩
      · rcases ih z y hyz with hd | ⟨k, hpath⟩
        · exact Or.inl hd
        · exact Or.inr ⟨k + 1, hvf.prependCharged (.currentStep hvz hpath)⟩

/-- The current clock wins each race with probability p; the observation ends the sequence. -/
def ringCount (p : ℝ≥0) (hp : p < 1) : PMF ℕ := by
  let q := (p : ℝ≥0∞)
  have hq : q < 1 := ENNReal.coe_lt_one_iff.mpr hp
  refine ⟨fun n => q ^ n * (1 - q), ENNReal.summable.hasSum_iff.mpr ?_⟩
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  exact ENNReal.inv_mul_cancel (tsub_pos_of_lt hq).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)

theorem count_at_least (p : ℝ≥0) (hp : p < 1) (b : ℕ) :
    p ^ b ≤ prob (ringCount p hp) (fun n => b ≤ n) := by
  classical
  let μ := ringCount p hp
  have hmass (n : ℕ) : μ (n + b) = (p : ℝ≥0∞) ^ b * μ n := by
    change (p : ℝ≥0∞) ^ (n + b) * (1 - p) = (p : ℝ≥0∞) ^ b * ((p : ℝ≥0∞) ^ n * (1 - p))
    rw [pow_add]; ac_rfl
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_pow, coe_prob, PMF.toOuterMeasure_apply]
  let f (n : ℕ) := {n : ℕ | b ≤ n}.indicator μ n
  have hf (n : ℕ) : f (n + b) = μ (n + b) :=
    Set.indicator_of_mem (show b ≤ n + b from Nat.le_add_left b n) _
  calc
    (p : ℝ≥0∞) ^ b = ∑' n, f (n + b) := by
      simp only [hf, hmass, ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]
    _ ≤ ∑' n, f n := ENNReal.tsum_comp_le_tsum_of_injective (fun _ _ h => Nat.add_right_cancel h) f

/-- Sampling after a geometric number of conditioned rounds. The last fast gap is included. -/
def sampled (p : ℝ≥0) (hp : p < 1) (gap mark : S → PMF S) (x : S) : PMF S :=
  (ringCount p hp).bind (fun n => run gap mark (rankRounds n ++ [.gap]) x)

theorem race_mixture (p : ℝ≥0) (hp : p < 1) (gap mark : S → PMF S) (x : S)
    (A : S → Prop) {b : ℕ} {v : ℝ≥0} (h : ∀ n, b ≤ n → v ≤ prob (run gap mark (rankRounds n ++ [.gap]) x) A) :
    p ^ b * v ≤ prob (sampled p hp gap mark x) A :=
  bind_lower _ _ (count_at_least p hp b) h

def nnrealLaws : NonnegativeLaws ℝ≥0 where
  additive := ⟨⟨fun _ => le_rfl, fun h k => h.trans k, fun h c => add_le_add_right h c⟩,
    add_comm, add_assoc, add_zero⟩
  nonneg := zero_le
  mulRight := fun h c => mul_le_mul_right' h c
  mulComm := mul_comm
  mulAssoc := mul_assoc
  mulOne := mul_one
  mulPos := mul_pos
  addMul := add_mul
  cancelRight := fun h => (mul_le_mul_iff_left₀ h).mp

end AIM272.RankedRace
