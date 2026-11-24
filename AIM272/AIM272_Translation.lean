import AIM272_Affine

/-!
# AIM 272, Section 8: from the minimum form to (8.1)–(8.2)

`AIM272Affine.uniform_property` is the affine lemma in minimum form, with `h = 1/R`,
`p = -w_R(x)`, slopes `r = -a` and offsets `c = -b`. This file performs the substitution and
proves the statement used in Section 9: finitely many slopes `a_λ ∈ [0,1]^d` and offsets
`b_λ(R) = o(R)` such that, for all large `R` and every real `x` with `x_i > -1` and
`w_R(x) ∈ [0,1]^d`, a face within `(log R)^2` of the maximum has `‖w_R(x) - a_λ‖_∞ < E(a_λ)`.
-/

set_option warningAsError true

noncomputable section

open Filter Topology

namespace AIM272Translation

open AIM272Affine

variable {ι : Type} [Fintype ι]

/-- Logarithmic coordinates `w_R(x)_i = log(x_i + 1) / log R`. -/
def wR (R : ℝ) (x : ι → ℝ) : ι → ℝ := fun i => Real.log (x i + 1) / Real.log R

/-- The affine function `L(x) = a · (x + 1) + b(R)`. -/
def Lval (a : ι → ℝ) (b : ℝ → ℝ) (R : ℝ) (x : ι → ℝ) : ℝ := (∑ i, a i * (x i + 1)) + b R

/-- The face of the minimum form attached to a slope and an offset of the maximum form. -/
def toMax (f : Face ι) : (ι → ℝ) × (ℝ → ℝ) := (fun i => -f.r i, fun R => -f.c R⁻¹)

theorem rpow_back {R y : ℝ} (hR : 1 < R) (hy : 0 < y) :
    R⁻¹ ^ (-(Real.log y / Real.log R)) = y := by
  have hlogR : 0 < Real.log R := Real.log_pos hR
  rw [Real.rpow_def_of_pos (inv_pos.mpr (by linarith)), Real.log_inv]
  have : -Real.log R * -(Real.log y / Real.log R) = Real.log y := by
    field_simp
  rw [this, Real.exp_log hy]

theorem val_toMax (f : Face ι) {R : ℝ} (hR : 1 < R) {x : ι → ℝ} (hx : ∀ i, -1 < x i) :
    val f R⁻¹ (fun i => -wR R x i) = -Lval (toMax f).1 (toMax f).2 R x := by
  simp only [val, Lval, toMax, wR]
  have : ∀ i, R⁻¹ ^ (-(Real.log (x i + 1) / Real.log R)) = x i + 1 := fun i =>
    rpow_back hR (by linarith [hx i])
  simp only [this, neg_mul, Finset.sum_neg_distrib]
  ring

theorem gap_inv (R : ℝ) : gap R⁻¹ = (Real.log R) ^ 2 := by
  simp [gap, Real.log_inv]

/-- **The affine approximation lemma in the form (8.1)–(8.2).** -/
theorem affine_max_form_nonempty [DecidableEq ι] (E : (ι → ℝ) → ℝ) (hE : ∀ a, 0 < E a) :
    ∃ Λ : List ((ι → ℝ) × (ℝ → ℝ)), Λ ≠ [] ∧
      (∀ l ∈ Λ, ∀ i, l.1 i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ l ∈ Λ, ∀ ε > 0, ∀ᶠ R in atTop, |l.2 R| ≤ ε * R) ∧
      ∀ᶠ R in atTop, ∀ x : ι → ℝ, (∀ i, -1 < x i) → (∀ i, wR R x i ∈ Set.Icc (0 : ℝ) 1) →
        ∀ l ∈ Λ, (∀ l' ∈ Λ, Lval l'.1 l'.2 R x ≤ Lval l.1 l.2 R x + (Real.log R) ^ 2) →
          dist (wR R x) l.1 < E l.1 := by
  obtain ⟨F, hF, hslope, hsmall, hev⟩ :=
    uniform_property_nonempty (ι := ι) (A := -1) (B := 0) (by norm_num) le_rfl (fun r => E (-r))
      (fun r => hE _)
  refine ⟨F.map toMax, fun h => hF (List.map_eq_nil_iff.mp h), ?_, ?_, ?_⟩
  · intro l hl i
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hl
    obtain ⟨h1, h2⟩ := hslope f hf i
    exact ⟨by simp [toMax]; linarith, by simp [toMax]; linarith⟩
  · intro l hl ε hε
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hl
    have hs := hsmall f hf ε hε
    have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    filter_upwards [hinv.eventually hs, eventually_gt_atTop (0 : ℝ)] with R h1 hR
    have := h1 (inv_pos.mpr hR)
    simp only [toMax, abs_neg]
    rwa [Real.rpow_neg_one, inv_inv] at this
  · have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    filter_upwards [hinv.eventually hev, eventually_gt_atTop (1 : ℝ)] with R h1 hR x hx hw l hl hnear
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hl
    have hp : InCube (-1) 0 (fun i => -wR R x i) := fun i =>
      ⟨by linarith [(hw i).2], by linarith [(hw i).1]⟩
    have hna : NearActive F f R⁻¹ (fun i => -wR R x i) := by
      intro f' hf'
      have := hnear (toMax f') (List.mem_map.mpr ⟨f', hf', rfl⟩)
      rw [val_toMax f hR hx, val_toMax f' hR hx, gap_inv R]
      linarith
    have hd := h1 f hf _ hp (inv_pos.mpr (by linarith)) hna
    have hr : (toMax f).1 = fun i => -f.r i := rfl
    have hdist : dist (fun i => -wR R x i) f.r = dist (wR R x) (toMax f).1 := by
      have e1 : (fun i => -wR R x i) = -(wR R x) := rfl
      have e2 : (fun i => -f.r i) = -f.r := rfl
      rw [hr, e1, e2, ← dist_neg_neg (wR R x) (-f.r), neg_neg]
    rw [hdist] at hd
    simpa [hr] using hd

theorem affine_max_form [DecidableEq ι] (E : (ι → ℝ) → ℝ) (hE : ∀ a, 0 < E a) :
    ∃ Λ : List ((ι → ℝ) × (ℝ → ℝ)),
      (∀ l ∈ Λ, ∀ i, l.1 i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ l ∈ Λ, ∀ ε > 0, ∀ᶠ R in atTop, |l.2 R| ≤ ε * R) ∧
      ∀ᶠ R in atTop, ∀ x : ι → ℝ, (∀ i, -1 < x i) → (∀ i, wR R x i ∈ Set.Icc (0 : ℝ) 1) →
        ∀ l ∈ Λ, (∀ l' ∈ Λ, Lval l'.1 l'.2 R x ≤ Lval l.1 l.2 R x + (Real.log R) ^ 2) →
          dist (wR R x) l.1 < E l.1 := by
  obtain ⟨Λ, _, h₁, h₂, h₃⟩ := affine_max_form_nonempty E hE
  exact ⟨Λ, h₁, h₂, h₃⟩

end AIM272Translation

end

#print axioms AIM272Translation.affine_max_form
