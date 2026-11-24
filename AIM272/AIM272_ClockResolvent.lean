import AIM272_ClockObservation

set_option warningAsError true

/-! # Resolvent identity for discrete observation of ranked clocks -/

noncomputable section
open scoped NNReal ENNReal BigOperators

namespace AIM272.RankedRace

variable {S T : Type}

def mean (μ : PMF S) (f : S → ℝ≥0∞) : ℝ≥0∞ := ∑' x, μ x * f x

theorem mean_mono (μ : PMF S) {f g : S → ℝ≥0∞}
    (h : ∀ x ∈ μ.support, f x ≤ g x) : mean μ f ≤ mean μ g := by
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ μ.support
  · exact mul_le_mul_left' (h x hx) _
  · rw [(μ.apply_eq_zero_iff x).mpr hx, zero_mul, zero_mul]

theorem mean_const (μ : PMF S) (a : ℝ≥0∞) : mean μ (fun _ => a) = a := by
  simp [mean, ENNReal.tsum_mul_right, μ.tsum_coe]

@[simp] theorem mean_pure (x : S) (f : S → ℝ≥0∞) : mean (PMF.pure x) f = f x := by
  rw [mean, tsum_eq_single x]
  · simp
  · intro y hy
    simp [PMF.pure_apply_of_ne x y hy]

theorem mean_bind (μ : PMF S) (K : S → PMF T) (f : T → ℝ≥0∞) :
    mean (μ.bind K) f = mean μ (fun x => mean (K x) f) := by
  simp only [mean, PMF.bind_apply, ← ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.tsum_comm]
  simp only [ENNReal.tsum_mul_left]

theorem mean_map (μ : PMF S) (g : S → T) (f : T → ℝ≥0∞) :
    mean (μ.map g) f = mean μ (fun x => f (g x)) := by
  change mean (μ.bind (fun x => PMF.pure (g x))) f = _
  rw [mean_bind]
  simp only [mean_pure]

theorem mean_add (μ : PMF S) (f g : S → ℝ≥0∞) :
    mean μ (fun x => f x + g x) = mean μ f + mean μ g := by
  simp only [mean, mul_add, ENNReal.tsum_add]

theorem mean_mul (μ : PMF S) (c : ℝ≥0∞) (f : S → ℝ≥0∞) :
    mean μ (fun x => c * f x) = c * mean μ f := by
  simp only [mean, mul_left_comm _ c, ENNReal.tsum_mul_left]

theorem mean_tsum {ι : Type*} (μ : PMF S) (f : ι → S → ℝ≥0∞) :
    mean μ (fun x => ∑' i, f i x) = ∑' i, mean μ (f i) := by
  simp only [mean, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

open Classical in
theorem mean_indicator (μ : PMF S) (P : S → Prop) :
    mean μ (fun y => if P y then 1 else 0) = (prob μ P : ℝ≥0∞) := by
  rw [coe_prob, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro y
  by_cases h : P y <;> simp [h]

private theorem sampled_first_round (p : ℝ≥0) (hp : p < 1) (g m : S → PMF S)
    (f : S → ℝ≥0∞) (x : S) :
    mean (sampled p hp g m x) f = (1 - (p : ℝ≥0∞)) * mean (g x) f +
      (p : ℝ≥0∞) * mean (g x) (fun y => mean (m y) (fun z => mean (sampled p hp g m z) f)) := by
  let k (n : ℕ) (z : S) := mean (run g m (rankRounds n ++ [.gap]) z) f
  let q (n : ℕ) : ℝ≥0∞ := ringCount p hp n
  have h (z : S) : mean (sampled p hp g m z) f = ∑' n, q n * k n z := mean_bind _ _ _
  have h₀ : q 0 = 1 - (p : ℝ≥0∞) := by
    change (p : ℝ≥0∞) ^ (0 : ℕ) * (1 - (p : ℝ≥0∞)) = _
    simp
  have h₁ (n : ℕ) : q (n + 1) = (p : ℝ≥0∞) * q n := by
    change (p : ℝ≥0∞) ^ (n + 1) * (1 - (p : ℝ≥0∞)) = _
    rw [pow_succ']
    exact mul_assoc _ _ _
  have hk₀ : k 0 x = mean (g x) f := by simp [k, rankRounds, run]
  have hk₁ (n : ℕ) : k (n + 1) x =
      mean (g x) (fun y => mean (m y) (k n)) := by
    unfold k
    simp only [rankRounds, List.cons_append, List.nil_append, run, mean_bind]
  rw [h, tsum_eq_zero_add' (f := fun n => q n * k n x) ENNReal.summable, h₀, hk₀]
  simp_rw [h, mean_tsum, mean_mul, h₁, hk₁, mul_assoc, ENNReal.tsum_mul_left]

private theorem raceShare_products (c ν : ℝ≥0) (hν : 0 < ν) :
    ((c + ν : ℝ≥0) : ℝ≥0∞) * (raceShare c ν : ℝ≥0∞) = (c : ℝ≥0∞) ∧
    ((c + ν : ℝ≥0) : ℝ≥0∞) * (1 - (raceShare c ν : ℝ≥0∞)) = (ν : ℝ≥0∞) := by
  have hs : c + ν ≠ 0 := (add_pos_of_nonneg_of_pos (zero_le _) hν).ne'
  have hc : ((c + ν : ℝ≥0) : ℝ≥0∞) * (raceShare c ν : ℝ≥0∞) = (c : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul]
    apply congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞))
    rw [raceShare, mul_comm, div_mul_cancel₀ _ hs]
  refine ⟨hc, (ENNReal.add_left_inj (a := (c : ℝ≥0∞)) ENNReal.coe_ne_top).mp ?_⟩
  calc
    ((c + ν : ℝ≥0) : ℝ≥0∞) * (1 - (raceShare c ν : ℝ≥0∞)) + (c : ℝ≥0∞) =
        ((c + ν : ℝ≥0) : ℝ≥0∞) * ((1 - (raceShare c ν : ℝ≥0∞)) + (raceShare c ν : ℝ≥0∞)) := by
      conv_lhs => rw [← hc]
      exact (mul_add _ _ _).symm
    _ = ((ν : ℝ≥0∞) + (c : ℝ≥0∞)) := by
      rw [tsub_add_cancel_of_le (ENNReal.coe_lt_one_iff.mpr (raceShare_lt_one c hν)).le,
        mul_one, ENNReal.coe_add, add_comm]

/-- The first-event identity for any finite list of clocks and any payoff.
It follows from the geometric race decomposition and nonnegative sums. -/
theorem observe_resolvent (clock : ℝ → ℝ≥0) (mark : ℝ → S → PMF S) (ds : List ℝ)
    {ν : ℝ≥0} (hν : 0 < ν) (f : S → ℝ≥0∞) (x : S) :
    ((ν + (ds.map clock).sum : ℝ≥0) : ℝ≥0∞) * mean (observe clock mark ds ν x) f =
      (ν : ℝ≥0∞) * f x +
        (ds.map (fun d => (clock d : ℝ≥0∞) * mean (mark d x)
          (fun y => mean (observe clock mark ds ν y) f))).sum := by
  induction ds generalizing ν f x with
  | nil => simp [observe]
  | cons d ds ih =>
    let c := clock d
    let p := raceShare c ν
    let G := observe clock mark ds (c + ν)
    let U (y : S) := mean (observe clock mark (d :: ds) ν y) f
    let g (y : S) := (1 - (p : ℝ≥0∞)) * f y + (p : ℝ≥0∞) * mean (mark d y) U
    have hu : (fun z => mean (sampled p (raceShare_lt_one c hν) G (mark d) z) f) = U :=
      funext fun z => congrArg (fun μ => mean μ f) (observe_cons clock mark d ds hν z).symm
    have hm (y : S) : U y = mean (G y) g := by
      change mean (observe clock mark (d :: ds) ν y) f = _
      rw [observe_cons _ _ _ _ hν, sampled_first_round, hu]
      simp only [g, mean_add, mean_mul]
      rfl
    have ho := ih (add_pos_of_nonneg_of_pos (zero_le c) hν) g x
    change ((c + ν + (ds.map clock).sum : ℝ≥0) : ℝ≥0∞) * mean (G x) g =
      ((c + ν : ℝ≥0) : ℝ≥0∞) * g x +
        (ds.map (fun j => (clock j : ℝ≥0∞) * mean (mark j x) (fun y => mean (G y) g))).sum at ho
    simp_rw [← hm] at ho
    have hsplit : ((c + ν : ℝ≥0) : ℝ≥0∞) * g x =
        (ν : ℝ≥0∞) * f x + (c : ℝ≥0∞) * mean (mark d x) U := by
      obtain ⟨hc, hv⟩ := raceShare_products c ν hν
      simp only [g, p, mul_add, ← mul_assoc, hc, hv]
    rw [hsplit] at ho
    simpa only [List.map_cons, List.sum_cons, ← add_assoc, add_left_comm, add_comm c ν, U] using ho

end AIM272.RankedRace
