import AIM272_Translation
import AIM272_Unusable

/-!
# AIM 272, Section 9: near-active faces in the shell are usable

This file joins the affine lemma in the form (8.1)–(8.2) with Lemma 3.1. It proves the first
step of Section 9: with `R = 2N`, for all large `N`, every face that is near-active at a state
of the class in the shell `uN ≤ m(x)`, `m(x) + 1 ≤ 2N` has a usable direction.
-/

set_option warningAsError true

noncomputable section

open Filter Topology

namespace AIM272Geometry

open AIM272Translation AIM272Unusable

variable {κ L : Type} [Fintype κ] [DecidableEq κ] (net : Rxn κ L) (o : κ → ℕ)

/-- The zero set of a slope. -/
def zeroSet (a : κ → ℝ) : Finset κ := Finset.univ.filter fun i => a i = 0

/-- Eventual statements over a finite list. -/
theorem eventually_list {α β : Type} {l : Filter α} (Λ : List β) {P : β → α → Prop}
    (h : ∀ b ∈ Λ, ∀ᶠ x in l, P b x) : ∀ᶠ x in l, ∀ b ∈ Λ, P b x := by
  induction Λ with
  | nil => exact Eventually.of_forall fun _ b hb => absurd hb (List.not_mem_nil)
  | cons b Λ ih =>
    filter_upwards [h b (by simp), ih fun c hc => h c (by simp [hc])] with x h1 h2 c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h1
    · exact h2 c hc

/-- Logarithmic coordinates bounded by `e < 1` give `x_j + 1 < R^e`. -/
theorem lt_rpow_of_wR {R : ℝ} (hR : 1 < R) {y e : ℝ} (hy : 0 < y)
    (h : Real.log y / Real.log R < e) : y < R ^ e := by
  have hlog : 0 < Real.log R := Real.log_pos hR
  rw [div_lt_iff₀ hlog] at h
  rw [← Real.log_lt_log_iff hy (Real.rpow_pos_of_pos (by linarith) _),
    Real.log_rpow (by linarith)]
  linarith

/-- **Near-active faces in the shell are usable.** Here `E` is the tolerance of the affine
lemma; it is required to be below `1`, as in Section 9. -/
theorem shell_faces_usable_nonempty (E : (κ → ℝ) → ℝ) (hE : ∀ a, 0 < E a)
    (hE1 : ∀ a, E a < 1) {u : ℝ} (hu : 0 < u) :
    ∃ Λ : List ((κ → ℝ) × (ℝ → ℝ)), Λ ≠ [] ∧
      (∀ l ∈ Λ, ∀ i, l.1 i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ l ∈ Λ, ∀ ε > 0, ∀ᶠ R in atTop, |l.2 R| ≤ ε * R) ∧
      ∀ᶠ N : ℝ in atTop, ∀ x ∈ Γ net o, (∃ i, u * N ≤ (x i : ℝ)) →
        (∀ i, (x i : ℝ) + 1 ≤ 2 * N) →
        ∀ l ∈ Λ, (∀ l' ∈ Λ, Lval l'.1 l'.2 (2 * N) (fun i => (x i : ℝ)) ≤
            Lval l.1 l.2 (2 * N) (fun i => (x i : ℝ)) + (Real.log (2 * N)) ^ 2) →
          Usable net o (zeroSet l.1) ∧ dist (wR (2 * N) fun i => (x i : ℝ)) l.1 < E l.1 := by
  obtain ⟨Λ, hΛ, hslope, hsmall, hev⟩ := affine_max_form_nonempty E hE
  refine ⟨Λ, hΛ, hslope, hsmall, ?_⟩
  have h2N : Tendsto (fun N : ℝ => 2 * N) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  -- for each unusable face, states near its direction are outside the shell
  have hexcl : ∀ l ∈ Λ, ∀ᶠ N : ℝ in atTop, ¬ Usable net o (zeroSet l.1) →
      ∀ x ∈ Γ net o, (∀ j ∈ zeroSet l.1, (x j : ℝ) + 1 < (2 * N) ^ E l.1) →
        ∀ i, (x i : ℝ) < u * N := by
    intro l _
    by_cases hU : Usable net o (zeroSet l.1)
    · exact Eventually.of_forall fun _ h => absurd hU h
    · filter_upwards [unusable_outside_shell net o (zeroSet l.1) hU (hE1 l.1) hu]
        with N hN _ using hN
  filter_upwards [h2N.eventually hev, eventually_list Λ hexcl, eventually_gt_atTop (1 : ℝ)]
    with N hA hB hN1 x hx hbig hsmallx l hl hnear
  have hR : 1 < 2 * N := by linarith
  have hlogR : 0 < Real.log (2 * N) := Real.log_pos hR
  have hxpos : ∀ i, (0 : ℝ) < (x i : ℝ) + 1 := fun i => by positivity
  have hw : ∀ i, wR (2 * N) (fun i => (x i : ℝ)) i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    refine ⟨div_nonneg (Real.log_nonneg (by linarith [(Nat.cast_nonneg (x i) : (0 : ℝ) ≤ x i)]))
      hlogR.le, ?_⟩
    show Real.log ((x i : ℝ) + 1) / Real.log (2 * N) ≤ 1
    rw [div_le_one hlogR]
    exact Real.log_le_log (hxpos i) (hsmallx i)
  have hd := hA (fun i => (x i : ℝ)) (fun i => by linarith [hxpos i]) hw l hl hnear
  refine ⟨?_, hd⟩
  by_contra hU
  have hcoord : ∀ j ∈ zeroSet l.1, (x j : ℝ) + 1 < (2 * N) ^ E l.1 := by
    intro j hj
    have hj0 : l.1 j = 0 := (Finset.mem_filter.mp hj).2
    have := (dist_pi_lt_iff (hE l.1)).1 hd j
    rw [Real.dist_eq, hj0, sub_zero] at this
    have hwj : wR (2 * N) (fun i => (x i : ℝ)) j < E l.1 := lt_of_abs_lt this
    exact lt_rpow_of_wR hR (hxpos j) hwj
  obtain ⟨i, hi⟩ := hbig
  have := hB l hl hU x hx hcoord i
  linarith

theorem shell_faces_usable (E : (κ → ℝ) → ℝ) (hE : ∀ a, 0 < E a)
    (hE1 : ∀ a, E a < 1) {u : ℝ} (hu : 0 < u) :
    ∃ Λ : List ((κ → ℝ) × (ℝ → ℝ)),
      (∀ l ∈ Λ, ∀ i, l.1 i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ l ∈ Λ, ∀ ε > 0, ∀ᶠ R in atTop, |l.2 R| ≤ ε * R) ∧
      ∀ᶠ N : ℝ in atTop, ∀ x ∈ Γ net o, (∃ i, u * N ≤ (x i : ℝ)) →
        (∀ i, (x i : ℝ) + 1 ≤ 2 * N) →
        ∀ l ∈ Λ, (∀ l' ∈ Λ, Lval l'.1 l'.2 (2 * N) (fun i => (x i : ℝ)) ≤
            Lval l.1 l.2 (2 * N) (fun i => (x i : ℝ)) + (Real.log (2 * N)) ^ 2) →
          Usable net o (zeroSet l.1) ∧ dist (wR (2 * N) fun i => (x i : ℝ)) l.1 < E l.1 := by
  obtain ⟨Λ, _, h₁, h₂, h₃⟩ := shell_faces_usable_nonempty net o E hE hE1 hu
  exact ⟨Λ, h₁, h₂, h₃⟩

end AIM272Geometry

end

#print axioms AIM272Geometry.shell_faces_usable
