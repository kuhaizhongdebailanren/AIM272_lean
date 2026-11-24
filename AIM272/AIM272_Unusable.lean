import AIM272_Rational

/-!
# AIM 272, Section 3: unusable directions

This file proves Lemma `lem:unusable` of the paper. The reaction network is given by
sources and targets; the chain moves from `x` to `x - s r + t r` when `s r ≤ x`. The
class `Γ` is the communicating class of a root `o`.

Proved here, with no hypotheses: translation of paths, the monoid `M = {v | o + v ∈ Γ}`
and its closure properties, the decomposition `Γ = ⋃_{b ∈ B₀} (b + M)` with a finite set
`B₀` (Dickson's lemma, from Mathlib), the compactness argument, and the passage to the
shell `m(x) ≥ uN` used in Section 9.

The linear-algebra input `RationalPoints` (a nonnegative real vector in the real span of a
subgroup `D ⊆ ℤ^d` can be replaced by a nonzero nonnegative vector of `D` whose support is
contained in its support) is proved in `AIM272_Rational`. No hypotheses remain.
-/

set_option warningAsError true

noncomputable section

open Filter Topology

namespace AIM272Unusable

variable {κ L : Type}

/-- A reaction network on the species `κ` with labels `L`. -/
structure Rxn (κ L : Type) where
  s : L → κ → ℕ
  t : L → κ → ℕ

variable (net : Rxn κ L)

/-- One jump of the chain. -/
def Step (x y : κ → ℕ) : Prop := ∃ r, net.s r ≤ x ∧ y = x - net.s r + net.t r

/-- Reachability. -/
def Reach : (κ → ℕ) → (κ → ℕ) → Prop := Relation.ReflTransGen (Step net)

theorem step_shift {x y : κ → ℕ} (z : κ → ℕ) (h : Step net x y) : Step net (x + z) (y + z) := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r, fun i => (hr i).trans (Nat.le_add_right _ _), ?_⟩
  funext i
  have h : net.s r i ≤ x i := hr i
  simp only [Pi.add_apply, Pi.sub_apply]
  omega

/-- Enabling conditions are monotone, so paths can be translated. -/
theorem reach_shift {x y : κ → ℕ} (z : κ → ℕ) (h : Reach net x y) :
    Reach net (x + z) (y + z) :=
  Relation.ReflTransGen.lift (· + z) (fun _ _ hs => step_shift net z hs) h

theorem reach_trans {x y z : κ → ℕ} (h₁ : Reach net x y) (h₂ : Reach net y z) : Reach net x z :=
  Relation.ReflTransGen.trans h₁ h₂

variable (o : κ → ℕ)

/-- The communicating class of the root. -/
def Γ : Set (κ → ℕ) := {x | Reach net o x ∧ Reach net x o}

/-- Growth vectors of the class. -/
def M : Set (κ → ℕ) := {v | o + v ∈ Γ net o}

/-- A direction with zero set `I` is usable if a nonzero growth vector vanishes on `I`. -/
def Usable (I : Finset κ) : Prop := ∃ v ∈ M net o, v ≠ 0 ∧ ∀ i ∈ I, v i = 0

theorem zero_mem_M : (0 : κ → ℕ) ∈ M net o := by
  simp only [M, Γ, add_zero, Set.mem_setOf_eq]
  exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem add_mem_M {u v : κ → ℕ} (hu : u ∈ M net o) (hv : v ∈ M net o) : u + v ∈ M net o := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  have e : o + v + u = o + (u + v) := by abel
  have h1 := reach_shift net u hv1
  have h2 := reach_shift net u hv2
  rw [e] at h1 h2
  exact ⟨reach_trans net hu1 h1, reach_trans net h2 hu2⟩

theorem sub_mem_M {u v : κ → ℕ} (hu : u ∈ M net o) (hv : v ∈ M net o) (hle : v ≤ u) :
    u - v ∈ M net o := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  have e : o + v + (u - v) = o + u := by
    funext i
    have h : v i ≤ u i := hle i
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have h1 := reach_shift net (u - v) hv2
  have h2 := reach_shift net (u - v) hv1
  rw [e] at h1 h2
  exact ⟨reach_trans net hu1 h1, reach_trans net h2 hu2⟩

theorem diff_mem_M {x b : κ → ℕ} (hx : x ∈ Γ net o) (hb : b ∈ Γ net o) (hle : b ≤ x) :
    x - b ∈ M net o := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hb1, hb2⟩ := hb
  have e : b + (x - b) = x := by
    funext i
    have h : b i ≤ x i := hle i
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  have h1 := reach_shift net (x - b) hb2
  have h2 := reach_shift net (x - b) hb1
  rw [e] at h1 h2
  exact ⟨reach_trans net hx1 h1, reach_trans net h2 hx2⟩

/-- **Dickson decomposition.** Finitely many minimal elements, and every state of the class
lies above one of them. -/
theorem dickson [Finite κ] :
    {x | Minimal (· ∈ Γ net o) x}.Finite ∧
      ∀ x ∈ Γ net o, ∃ b, Minimal (· ∈ Γ net o) b ∧ b ≤ x := by
  refine ⟨(setOf_minimal_antichain _).finite_of_partiallyWellOrderedOn (Pi.isPWO _), ?_⟩
  intro x hx
  obtain ⟨b, hb, hmin⟩ := (Pi.isPWO (Γ net o)).exists_le_minimal hx
  exact ⟨b, hmin, hb⟩

/-- Integer and real images. -/
def cZ (v : κ → ℕ) : κ → ℤ := fun i => v i
def cR (d : κ → ℤ) : κ → ℝ := fun i => d i

/-- The classical input: nonnegative real points of the span of a subgroup of `ℤ^κ` can be
replaced by nonzero nonnegative lattice points with smaller support. -/
def RationalPoints (κ : Type) : Prop :=
  ∀ (D : AddSubgroup (κ → ℤ)) (v : κ → ℝ), v ∈ Submodule.span ℝ (cR '' (D : Set (κ → ℤ))) →
    (∀ i, 0 ≤ v i) → v ≠ 0 → ∃ d ∈ D, (∀ i, 0 ≤ d i) ∧ d ≠ 0 ∧ ∀ i, v i = 0 → d i = 0

theorem rationalPoints [Fintype κ] : RationalPoints κ :=
  fun D v hv hp hn => AIM272Rational.rational_points D v hv hp hn

/-- Elements of the subgroup generated by `M` are differences of elements of `M`. -/
theorem closure_diff {d : κ → ℤ} (hd : d ∈ AddSubgroup.closure (cZ '' M net o)) :
    ∃ u ∈ M net o, ∃ w ∈ M net o, d = cZ u - cZ w := by
  induction hd using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨u, hu, 0, zero_mem_M net o, by funext i; simp [cZ]⟩
  | zero => exact ⟨0, zero_mem_M net o, 0, zero_mem_M net o, by funext i; simp [cZ]⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    obtain ⟨u', hu', w', hw', rfl⟩ := hy
    refine ⟨u + u', add_mem_M net o hu hu', w + w', add_mem_M net o hw hw', ?_⟩
    funext i; simp [cZ]; ring
  | neg x _ hx =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    exact ⟨w, hw, u, hu, by funext i; simp [cZ]⟩

/-- **Lemma 3.1.** If the direction with zero set `I` is not usable, every state of the class
satisfies `x_i ≤ C (1 + T)` whenever `x_j ≤ T` on `I`. -/
theorem unusable_bound [Fintype κ] (I : Finset κ)
    (hnot : ¬ Usable net o I) :
    ∃ C : ℝ, ∀ x ∈ Γ net o, ∀ T : ℝ, 0 ≤ T → (∀ j ∈ I, (x j : ℝ) ≤ T) →
      ∀ i, (x i : ℝ) ≤ C * (1 + T) := by
  have hrat : RationalPoints κ := rationalPoints
  by_contra hC
  push_neg at hC
  choose x hxΓ T hT0 hTI i hi using fun n : ℕ => hC n
  -- normalisation by the coordinate sum
  set s : ℕ → ℝ := fun n => ∑ k, (x n k : ℝ) with hs
  have hsi : ∀ n, (x n (i n) : ℝ) ≤ s n := fun n =>
    Finset.single_le_sum (f := fun k => (x n k : ℝ)) (fun k _ => Nat.cast_nonneg _)
      (Finset.mem_univ _)
  have hsbig : ∀ n : ℕ, (n : ℝ) * (1 + T n) < s n := fun n => (hi n).trans_le (hsi n)
  have hspos : ∀ n, 0 < s n := fun n => by
    have := hsbig n
    have : 0 ≤ (n : ℝ) * (1 + T n) := mul_nonneg (Nat.cast_nonneg _) (by linarith [hT0 n])
    linarith
  set y : ℕ → κ → ℝ := fun n k => (x n k : ℝ) / s n with hy
  set K : Set (κ → ℝ) := (Set.pi Set.univ fun _ : κ => Set.Icc (0 : ℝ) 1) ∩
    {v | ∑ k, v k = 1} with hK
  have hKc : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      (isClosed_eq (continuous_finset_sum _ fun k _ => continuous_apply k) continuous_const)
  have hyK : ∀ n, y n ∈ K := by
    intro n
    refine ⟨fun k _ => ⟨div_nonneg (Nat.cast_nonneg _) (hspos n).le, ?_⟩, ?_⟩
    · rw [div_le_one (hspos n)]
      exact Finset.single_le_sum (f := fun k => (x n k : ℝ)) (fun k _ => Nat.cast_nonneg _)
        (Finset.mem_univ _)
    · show ∑ k, (x n k : ℝ) / s n = 1
      rw [← Finset.sum_div]
      exact div_self (hspos n).ne'
  obtain ⟨v, hvK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hyK
  -- the limit vanishes on `I`
  have hvI : ∀ j ∈ I, v j = 0 := by
    intro j hj
    have hsmall : ∀ n, y n j * n ≤ 1 := by
      intro n
      have h1 : (x n j : ℝ) ≤ T n := hTI n j hj
      have h2 := hsbig n
      simp only [hy]
      rw [div_mul_eq_mul_div, div_le_one (hspos n)]
      nlinarith [hT0 n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hcoord : Tendsto (fun n => y (φ n) j) atTop (𝓝 (v j)) :=
      (continuous_apply j).continuousAt.tendsto.comp hlim
    have hzero : Tendsto (fun n => y (φ n) j) atTop (𝓝 0) := by
      have hb : Tendsto (fun n : ℕ => 2 * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
      refine squeeze_zero (fun n => ((hyK (φ n)).1 j (Set.mem_univ _)).1) (fun n => ?_) hb
      have h1 := hsmall (φ n)
      have h2 : (n : ℝ) + 1 ≤ φ n + 1 := by exact_mod_cast Nat.add_le_add_right (hφ.id_le n) 1
      have h3 : 0 ≤ y (φ n) j := ((hyK (φ n)).1 j (Set.mem_univ _)).1
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      have h4 : y (φ n) j ≤ 1 := ((hyK (φ n)).1 j (Set.mem_univ _)).2
      nlinarith
    exact tendsto_nhds_unique hcoord hzero
  -- the limit lies in the real span of `M`
  set D : AddSubgroup (κ → ℤ) := AddSubgroup.closure (cZ '' M net o) with hD
  set V : Submodule ℝ (κ → ℝ) := Submodule.span ℝ (cR '' (D : Set (κ → ℤ))) with hV
  obtain ⟨hfin, hbelow⟩ := dickson net o
  choose b hbmin hbx using fun n => hbelow (x n) (hxΓ n)
  obtain ⟨U, hU⟩ : ∃ U : κ → ℕ, ∀ n, b n ≤ U := by
    obtain ⟨U, hU⟩ := hfin.bddAbove
    exact ⟨U, fun n => hU (hbmin n)⟩
  set z : ℕ → κ → ℝ := fun n => (1 / s n) • cR (cZ (x n - b n)) with hz
  have hzV : ∀ n, z n ∈ V := by
    intro n
    refine V.smul_mem _ (Submodule.subset_span ⟨cZ (x n - b n), ?_, rfl⟩)
    exact AddSubgroup.subset_closure
      ⟨_, diff_mem_M net o (hxΓ n) (hbmin n).1 (hbx n), rfl⟩
  have hzlim : Tendsto (fun n => z (φ n)) atTop (𝓝 v) := by
    rw [tendsto_pi_nhds]
    intro k
    have hyk : Tendsto (fun n => y (φ n) k) atTop (𝓝 (v k)) :=
      (continuous_apply k).continuousAt.tendsto.comp hlim
    have hbk : Tendsto (fun n => (b (φ n) k : ℝ) / s (φ n)) atTop (𝓝 0) := by
      have hb : Tendsto (fun n : ℕ => (U k : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (U k : ℝ)
      refine squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (hspos _).le)
        (fun n => ?_) hb
      have h1 : (b (φ n) k : ℝ) ≤ U k := by exact_mod_cast hU (φ n) k
      have h2 : ((n : ℝ) + 1) ≤ s (φ n) := by
        have := hsbig (φ n)
        have h3 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
        have h4 := hT0 (φ n)
        have h5 : (φ n : ℝ) ≤ (φ n : ℝ) * (1 + T (φ n)) := by nlinarith
        have h6 : ((n : ℝ) + 1) ≤ s (φ n) ∨ s (φ n) < (n : ℝ) + 1 := le_or_gt _ _
        -- `s` takes natural values, so `s > φ n ≥ n` gives `s ≥ n + 1`
        rcases h6 with h6 | h6
        · exact h6
        · exfalso
          have hnat : s (φ n) = ((∑ k, x (φ n) k : ℕ) : ℝ) := by simp [hs]
          rw [hnat] at this h6
          have : φ n < ∑ k, x (φ n) k := by exact_mod_cast (h5.trans_lt this)
          have : (∑ k, x (φ n) k : ℕ) < n + 1 := by exact_mod_cast h6
          have h7 : n ≤ φ n := hφ.id_le n
          omega
      rw [div_le_iff₀ (hspos _)]
      calc (b (φ n) k : ℝ) ≤ U k := h1
        _ = (U k : ℝ) * (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) := by field_simp
        _ ≤ (U k : ℝ) * (1 / ((n : ℝ) + 1)) * s (φ n) := by
          apply mul_le_mul_of_nonneg_left h2; positivity
    have := hyk.sub hbk
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    simp only [hz, hy, cR, cZ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hle := hbx (φ n) k
    rw [Nat.cast_sub hle]
    push_cast
    ring
  have hvV : v ∈ V :=
    (V.closed_of_finiteDimensional).mem_of_tendsto hzlim (Eventually.of_forall fun n => hzV _)
  -- the classical input produces a growth vector vanishing on `I`
  have hv0 : v ≠ 0 := by
    intro h
    have := hvK.2
    simp [h] at this
  obtain ⟨d, hdD, hdpos, hdne, hdsupp⟩ := hrat D v hvV (fun k => (hvK.1 k (Set.mem_univ _)).1) hv0
  obtain ⟨u, hu, w, hw, hdeq⟩ := closure_diff net o hdD
  have hdk : ∀ k, d k = (u k : ℤ) - (w k : ℤ) := fun k => by
    rw [hdeq]; simp [cZ]
  have hwu : ∀ k, w k ≤ u k := fun k => by
    have h1 := hdpos k
    rw [hdk k] at h1
    omega
  apply hnot
  refine ⟨u - w, sub_mem_M net o hu hw hwu, ?_, ?_⟩
  · intro h
    apply hdne
    funext k
    have h1 : u k - w k = 0 := congrFun h k
    have h2 := hwu k
    rw [hdk k, Pi.zero_apply]
    omega
  · intro k hk
    have h1 := hdsupp k (hvI k hk)
    rw [hdk k] at h1
    have h2 := hwu k
    show u k - w k = 0
    omega

/-- **Shell exclusion** (end of Section 3). With `R = 2N` and `e < 1`, states of the class whose
logarithmic coordinates on `I` are below `e` lie outside the shell `m(x) ≥ uN` for all large `N`. -/
theorem unusable_outside_shell [Fintype κ] (I : Finset κ)
    (hnot : ¬ Usable net o I) {e u : ℝ} (he : e < 1) (hu : 0 < u) :
    ∀ᶠ N : ℝ in atTop, ∀ x ∈ Γ net o, (∀ j ∈ I, (x j : ℝ) + 1 < (2 * N) ^ e) →
      ∀ i, (x i : ℝ) < u * N := by
  obtain ⟨C, hC⟩ := unusable_bound net o I hnot
  set C' := max C 1 with hC'
  have hpow : Tendsto (fun N : ℝ => N ^ (e - 1)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := 1 - e) (by linarith)
    simpa using this
  have hev1 : ∀ᶠ N : ℝ in atTop, N ^ (e - 1) < u / (4 * C') :=
    (hpow.eventually (gt_mem_nhds (by positivity)))
  have hev2 : ∀ᶠ N : ℝ in atTop, 2 * C' / u < N := eventually_gt_atTop _
  filter_upwards [hev1, hev2, eventually_gt_atTop (1 : ℝ)] with N h1 h2 hN1 x hx hxI i
  have hNpos : 0 < N := by linarith
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hRe : (2 * N) ^ e ≤ 2 * N ^ e := by
    rw [Real.mul_rpow (by norm_num) hNpos.le]
    have : (2 : ℝ) ^ e ≤ 2 := by
      calc (2 : ℝ) ^ e ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he.le
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hNpos.le _)
  have hNe : N ^ e = N ^ (e - 1) * N := by
    rw [← Real.rpow_add_one hNpos.ne']; ring_nf
  have hT0 : 0 ≤ (2 * N) ^ e := Real.rpow_nonneg (by positivity) _
  have hb := hC x hx ((2 * N) ^ e) hT0 (fun j hj => by linarith [hxI j hj]) i
  have hCC : C * (1 + (2 * N) ^ e) ≤ C' * (1 + (2 * N) ^ e) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hq : 0 ≤ N ^ (e - 1) := Real.rpow_nonneg hNpos.le _
  have h3 : C' * (2 * N ^ (e - 1)) < u / 2 := by
    have h4C : 0 < 4 * C' := by linarith
    have := (lt_div_iff₀ h4C).1 h1
    linarith
  have h4 : C' < u * N / 2 := by
    have := (div_lt_iff₀ hu).1 h2
    linarith
  have key : C' * (1 + 2 * (N ^ (e - 1) * N)) < u * N := by
    have : C' * (2 * (N ^ (e - 1) * N)) < u / 2 * N := by
      have := mul_lt_mul_of_pos_right h3 hNpos
      linarith
    nlinarith
  calc (x i : ℝ) ≤ C * (1 + (2 * N) ^ e) := hb
    _ ≤ C' * (1 + (2 * N) ^ e) := hCC
    _ ≤ C' * (1 + 2 * (N ^ (e - 1) * N)) := by
        rw [← hNe]; apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ < u * N := key

end AIM272Unusable

end

#print axioms AIM272Unusable.unusable_bound
#print axioms AIM272Unusable.unusable_outside_shell
