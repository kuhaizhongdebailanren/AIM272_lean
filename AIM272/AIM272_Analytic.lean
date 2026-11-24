import Mathlib

set_option warningAsError true

/-!
# AIM 272: the new analytic estimates (stage 1)

This file formalizes the elementary but error-prone estimates of the paper
"Weakly reversible stochastic mass-action systems are positive recurrent":

* `descFactorial_le_succ_pow`, `succ_pow_le_descFactorial`: the two-sided
  comparison between mass-action propensities and `(x+1)^s` used for (6.1);
* `timeChanged_bounds`: the time-changed rate bounds (6.1);
* `preemption_bound`: the preemption estimate (7.2);
* `weight_ratio_eventually_le_half`: choice of `η` and `R` making (7.3) at most `1/2`;
* `leakage_eventually_small`: the leakage term (9.4) is eventually below half of
  the active negative drift, which gives (9.5);
* `outer_face_lower_bound`: the endpoint estimate (9.6);
* `scale_choice`: the choice of `θ, e, A, u` in Section 10.3.

Classical results (Dickson's lemma, the strong Markov property, Poisson clocks)
are not needed here.
-/

open Real Filter Topology

namespace AIM272Analytic

/-! ## Propensity comparison (paper, before (6.1)) -/

/-- The falling factorial is at most `(x+1)^s`. -/
theorem descFactorial_le_succ_pow (x s : ℕ) : x.descFactorial s ≤ (x + 1) ^ s :=
  (Nat.descFactorial_le_pow x s).trans (Nat.pow_le_pow_left (Nat.le_succ x) s)

/-- If `s ≤ x`, then `(x+1)^s ≤ (s+1)^s · x(x-1)⋯(x-s+1)`. This is the
inequality `(n-j)/(n+1) ≥ 1/(s+1)` multiplied over `j < s`. -/
theorem succ_pow_le_descFactorial (x : ℕ) :
    ∀ s : ℕ, s ≤ x → (x + 1) ^ s ≤ (s + 1) ^ s * x.descFactorial s
  | 0, _ => by simp
  | s + 1, h => by
    have ih := succ_pow_le_descFactorial x s (Nat.le_of_succ_le h)
    rw [Nat.descFactorial_succ]
    have key : x + 1 ≤ (s + 2) * (x - s) := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [show s + 1 + t - s = t + 1 by omega]
      nlinarith
    have mono : (s + 1) ^ s ≤ (s + 2) ^ s := Nat.pow_le_pow_left (by omega) s
    calc (x + 1) ^ (s + 1) = (x + 1) * (x + 1) ^ s := by ring
      _ ≤ ((s + 2) * (x - s)) * ((s + 1) ^ s * x.descFactorial s) :=
          Nat.mul_le_mul key ih
      _ ≤ ((s + 2) * (x - s)) * ((s + 2) ^ s * x.descFactorial s) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ mono)
      _ = (s + 1 + 1) ^ (s + 1) * ((x - s) * x.descFactorial s) := by ring

/-! ## Time-changed rates (6.1) -/

/-- After the time change by `R^(k - a·x)`, a propensity comparable to
`R^(w·s)` is comparable to `R^(-d')` up to `R^(±η)`, where
`k - a·x + a·s = -d'` and `|(w-a)·s| ≤ η`. Vectors are written as their dot
products: `ws = w·s`, `as = a·s`. -/
theorem timeChanged_bounds {R k ax ws as d η : ℝ} (hR : 1 < R)
    (horder : k - ax + as = -d) (hdev : |ws - as| ≤ η) :
    R ^ (-d - η) ≤ R ^ (k - ax) * R ^ ws ∧ R ^ (k - ax) * R ^ ws ≤ R ^ (-d + η) := by
  have hR0 : 0 < R := by linarith
  rw [← Real.rpow_add hR0]
  have e : k - ax + ws = -d + (ws - as) := by linarith
  rw [e]
  have h1 := neg_abs_le (ws - as)
  have h2 := le_abs_self (ws - as)
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le hR.le (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hR.le (by linarith)

/-! ## Preemption (7.2) -/

/-- `Λ_{d'} · E S_k ≤ K₀ C R^(-d' + (b+1)η)` when `Λ_{d'} = K₀ R^(-d'+η)` and
`E S_k ≤ C R^(bη)`. -/
theorem preemption_bound {R K₀ C d b η ES : ℝ} (hR : 0 < R) (hK : 0 ≤ K₀)
    (hES : ES ≤ C * R ^ (b * η)) :
    K₀ * R ^ (-d + η) * ES ≤ K₀ * C * R ^ (-d + (b + 1) * η) := by
  have hpos : 0 ≤ K₀ * R ^ (-d + η) := mul_nonneg hK (Real.rpow_nonneg hR.le _)
  calc K₀ * R ^ (-d + η) * ES ≤ K₀ * R ^ (-d + η) * (C * R ^ (b * η)) :=
        mul_le_mul_of_nonneg_left hES hpos
    _ = K₀ * C * (R ^ (-d + η) * R ^ (b * η)) := by ring
    _ = K₀ * C * R ^ (-d + (b + 1) * η) := by
        rw [← Real.rpow_add hR]; congr 2; ring

/-! ## The weight ratio (7.3) -/

/-- Fix `g > 0`, `0 < θ < 1`, `b ≥ 0`, a constant `C`, and a finite set of
positive orders. Then some `η > 0` makes
`R^(-θ g) + Σ_{d'} C R^(-(1-θ)d' + (b+1)η)` at most `1/2` for all large `R`. -/
theorem weight_ratio_eventually_le_half {g θ b C : ℝ} (hg : 0 < g) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hb : 0 ≤ b) (orders : Finset ℝ) (hpos : ∀ d ∈ orders, 0 < d) :
    ∃ η > 0, ∀ᶠ R in atTop,
      R ^ (-(θ * g)) + ∑ d ∈ orders, C * R ^ (-(1 - θ) * d + (b + 1) * η) ≤ 1 / 2 := by
  classical
  -- `m` is a positive lower bound for all orders.
  obtain ⟨m, hm, hmle⟩ : ∃ m > 0, ∀ d ∈ orders, m ≤ d := by
    by_cases hne : orders.Nonempty
    · refine ⟨orders.min' hne, hpos _ (Finset.min'_mem _ _), fun d hd => Finset.min'_le _ _ hd⟩
    · exact ⟨1, one_pos, fun d hd => (hne ⟨d, hd⟩).elim⟩
  refine ⟨(1 - θ) * m / (2 * (b + 1)),
    div_pos (mul_pos (by linarith) hm) (by positivity), ?_⟩
  set η := (1 - θ) * m / (2 * (b + 1)) with hη
  have hbη : (b + 1) * η = (1 - θ) * m / 2 := by
    rw [hη]; field_simp
  -- every term tends to zero
  have hterm : ∀ d ∈ orders,
      Tendsto (fun R : ℝ => C * R ^ (-(1 - θ) * d + (b + 1) * η)) atTop (𝓝 0) := by
    intro d hd
    have hneg : 0 < (1 - θ) * d - (b + 1) * η := by
      rw [hbη]
      have := hmle d hd
      nlinarith [hpos d hd]
    have h := tendsto_rpow_neg_atTop hneg
    have h' : Tendsto (fun R : ℝ => C * R ^ (-((1 - θ) * d - (b + 1) * η))) atTop (𝓝 (C * 0)) :=
      h.const_mul C
    rw [mul_zero] at h'
    refine h'.congr' (Eventually.of_forall fun R => ?_)
    congr 2; ring
  have hsum := tendsto_finset_sum orders hterm
  simp only [Finset.sum_const_zero] at hsum
  have hfirst : Tendsto (fun R : ℝ => R ^ (-(θ * g))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by positivity)
  have htot := hfirst.add hsum
  rw [add_zero] at htot
  exact htot.eventually (ge_mem_nhds (by norm_num))

/-! ## Leakage versus active drift (9.4)–(9.5) -/

/-- For constants `K₁, K₂` and `θ > 0`, eventually
`R^(K₂ - θ (log R)^2) ≤ (1/2) R^(-K₁)`. This is the comparison of (9.4) with the
active negative term, the constant `θ d J_*` being absorbed into `K₂`. -/
theorem leakage_eventually_small {K₁ K₂ θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ R in atTop, R ^ (K₂ - θ * (Real.log R) ^ 2) ≤ 1 / 2 * R ^ (-K₁) := by
  set K := K₁ + K₂
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hL : ∀ᶠ R in atTop, max 1 ((|K| + 1) / θ) ≤ Real.log R :=
    hlog.eventually_ge_atTop _
  filter_upwards [hL, eventually_gt_atTop (1 : ℝ)] with R hLR hR1
  have hR0 : 0 < R := by linarith
  set L := Real.log R with hLdef
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hLR
  have hLθ : |K| + 1 ≤ θ * L := by
    have := le_trans (le_max_right _ _) hLR
    rwa [div_le_iff₀ hθ, mul_comm] at this
  -- the combined exponent is at most -1
  have hexp : (K₂ - θ * L ^ 2 + K₁) * L ≤ -1 := by
    have hK : K₁ + K₂ ≤ |K| := le_abs_self K
    have hsq : (|K| + 1) * L ≤ θ * L ^ 2 := by nlinarith
    have hab : 0 ≤ |K| := abs_nonneg K
    have hlin : |K| ≤ |K| * L := by nlinarith
    have hA : K₂ - θ * L ^ 2 + K₁ ≤ -1 := by nlinarith
    have hL0 : 0 ≤ L := by linarith
    have := mul_le_mul_of_nonneg_right hA hL0
    nlinarith
  have hpos : 0 < R ^ (-K₁) := Real.rpow_pos_of_pos hR0 _
  rw [show R ^ (K₂ - θ * L ^ 2) = R ^ (K₂ - θ * L ^ 2 + K₁) * R ^ (-K₁) by
    rw [← Real.rpow_add hR0]; congr 1; ring]
  apply mul_le_mul_of_nonneg_right _ hpos.le
  rw [Real.rpow_def_of_pos hR0]
  calc Real.exp (Real.log R * (K₂ - θ * L ^ 2 + K₁)) ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.mpr; rw [← hLdef]; linarith [hexp]
    _ ≤ 1 / 2 := by
        have := Real.exp_one_gt_d9
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith

/-! ## The outer endpoint (9.6) -/

/-- If the active slope satisfies `a_i ≥ 1 - e - η` at a maximal coordinate
`x_i + 1 ≥ N`, all other contributions are nonnegative, and the offset is at
least `-B`, then the affine value is at least `(1 - e - η) N - B`; with
`e < 1/4`, `η ≤ 1/8` and `B ≤ N/8` this is at least `N/2`. -/
theorem outer_face_lower_bound {ai xi rest b e η B N : ℝ} (hN : 0 ≤ N)
    (hai : 1 - e - η ≤ ai) (hxi : N ≤ xi + 1) (hrest : 0 ≤ rest) (hb : -B ≤ b)
    (he : e < 1 / 4) (hη : η ≤ 1 / 8) (hB : B ≤ N / 8) :
    N / 2 ≤ ai * (xi + 1) + rest + b := by
  have hcoef : 0 ≤ 1 - e - η := by linarith
  have h1 : (1 - e - η) * N ≤ ai * (xi + 1) := by
    calc (1 - e - η) * N ≤ (1 - e - η) * (xi + 1) := mul_le_mul_of_nonneg_left hxi hcoef
      _ ≤ ai * (xi + 1) := mul_le_mul_of_nonneg_right hai (by linarith)
  nlinarith

/-! ## Choice of scales (Section 10.3) -/

/-- Given `d ≥ 1`, `C₁ ≥ 0` and `δ > 0`, the parameters of Section 10.3 exist:
`θ ∈ (0,1)`, `0 < e < 1/4`, `A ≥ 2`, `u > 0` with
`d(1-θ) < δ/8`, `d e < δ/8`, `θA/4 > C₁ + d + 2`, `uA < 1/2`,
`C₂ u < θ/8` and `C₂ u A < δ/8`, where `C₂ = C₁ + d`. Consequently the
exponent of (10.9) is below `3δ/8` and that of (10.7) is below `-2`. -/
theorem scale_choice {d C₁ δ : ℝ} (hd : 1 ≤ d) (hC : 0 ≤ C₁) (hδ : 0 < δ) :
    ∃ θ e A u : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < e ∧ e < 1 / 4 ∧ 2 ≤ A ∧ 0 < u ∧
      d * (1 - θ) < δ / 8 ∧ d * e < δ / 8 ∧ C₁ + d + 2 < θ * A / 4 ∧
      u * A < 1 / 2 ∧ (C₁ + d) * u < θ / 8 ∧ (C₁ + d) * u * A < δ / 8 ∧
      d * (1 - θ) + θ * e * d + (C₁ + d) * u * A < 3 * δ / 8 ∧
      d + C₁ - θ * A / 4 < -2 := by
  have hd0 : 0 < d := by linarith
  set ε := min (1 / 8) (δ / (16 * d)) with hε
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 8 := min_le_left _ _
  have hε2 : ε ≤ δ / (16 * d) := min_le_right _ _
  have hdε : d * ε ≤ δ / 16 := by
    calc d * ε ≤ d * (δ / (16 * d)) := mul_le_mul_of_nonneg_left hε2 hd0.le
      _ = δ / 16 := by field_simp; try ring
  set θ := 1 - ε
  have hθ0 : 0 < θ := by simp only [θ]; linarith
  have hθhalf : 1 / 2 ≤ θ := by simp only [θ]; linarith
  set A := 8 * (C₁ + d + 2) + 2
  have hA : 2 ≤ A := by simp only [A]; linarith
  have hθA : C₁ + d + 2 < θ * A / 4 := by
    have : (1 / 2) * A ≤ θ * A := mul_le_mul_of_nonneg_right hθhalf (by linarith)
    simp only [A] at this ⊢; nlinarith
  set C₂ := C₁ + d
  have hC₂ : 0 < C₂ := by simp only [C₂]; linarith
  set u := min (1 / (4 * A)) (min (1 / (32 * C₂)) (δ / (16 * C₂ * A))) with hu
  have hA0 : 0 < A := by linarith
  have hu0 : 0 < u := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hu1 : u ≤ 1 / (4 * A) := min_le_left _ _
  have hu2 : u ≤ 1 / (32 * C₂) := (min_le_right _ _).trans (min_le_left _ _)
  have hu3 : u ≤ δ / (16 * C₂ * A) := (min_le_right _ _).trans (min_le_right _ _)
  have huA : u * A < 1 / 2 := by
    calc u * A ≤ 1 / (4 * A) * A := mul_le_mul_of_nonneg_right hu1 hA0.le
      _ = 1 / 4 := by field_simp; try ring
      _ < 1 / 2 := by norm_num
  have hC₂u : C₂ * u < θ / 8 := by
    calc C₂ * u ≤ C₂ * (1 / (32 * C₂)) := mul_le_mul_of_nonneg_left hu2 hC₂.le
      _ = 1 / 32 := by field_simp; try ring
      _ < θ / 8 := by linarith
  have hC₂uA : C₂ * u * A ≤ δ / 16 := by
    calc C₂ * u * A ≤ C₂ * (δ / (16 * C₂ * A)) * A := by
          apply mul_le_mul_of_nonneg_right _ hA0.le
          exact mul_le_mul_of_nonneg_left hu3 hC₂.le
      _ = δ / 16 := by field_simp; try ring
  refine ⟨θ, ε, A, u, hθ0, by simp only [θ]; linarith, hε0, by linarith, hA, hu0,
    ?_, ?_, hθA, huA, hC₂u, by linarith, ?_, by linarith⟩
  · simp only [θ]; linarith
  · linarith
  · have hθe : θ * ε * d ≤ ε * d := by
      have : θ ≤ 1 := by simp only [θ]; linarith
      have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ ε * d)
      nlinarith
    simp only [θ] at hθe ⊢
    nlinarith

end AIM272Analytic

#print axioms AIM272Analytic.descFactorial_le_succ_pow
#print axioms AIM272Analytic.succ_pow_le_descFactorial
#print axioms AIM272Analytic.timeChanged_bounds
#print axioms AIM272Analytic.preemption_bound
#print axioms AIM272Analytic.weight_ratio_eventually_le_half
#print axioms AIM272Analytic.leakage_eventually_small
#print axioms AIM272Analytic.outer_face_lower_bound
#print axioms AIM272Analytic.scale_choice
