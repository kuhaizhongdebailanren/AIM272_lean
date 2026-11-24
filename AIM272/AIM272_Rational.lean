import Mathlib

/-!
# Rational points in the real span of a lattice subgroup

If `v` is a nonnegative nonzero real vector in the real span of a subgroup `D ⊆ ℤ^κ`, then
`D` contains a nonnegative nonzero vector whose support is contained in that of `v`.

Proof. Write `v = ∑ c_k d_k` with `d_k ∈ D`. The reals `c_k` span a finite-dimensional
`ℚ`-subspace `F` of `ℝ`. A `ℚ`-linear map `φ : F → ℚ` that is close to the inclusion on the
finitely many coordinates `v_i` gives the rational vector `∑ φ(c_k) d_k`. Its coordinates are
`φ(v_i)`, hence positive where `v_i > 0` and zero where `v_i = 0`. Clearing denominators gives
an integer vector of `D`.
-/

set_option warningAsError true

noncomputable section

namespace AIM272Rational

/-- A `ℚ`-linear functional on a finite-dimensional `ℚ`-subspace of `ℝ`, close to the
inclusion at finitely many prescribed points. -/
theorem approx_functional (F : Submodule ℚ ℝ) [FiniteDimensional ℚ F] {ι₀ : Type}
    [Fintype ι₀] (y : ι₀ → F) (ε : ι₀ → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ φ : F →ₗ[ℚ] ℚ, ∀ i, |((φ (y i) : ℚ) : ℝ) - (y i : ℝ)| < ε i := by
  set β := Module.finBasis ℚ F
  set W : ℝ := 1 + ∑ i, ∑ l, |((β.repr (y i) l : ℚ) : ℝ)| with hW
  have hW1 : 1 ≤ W := by
    have : 0 ≤ ∑ i, ∑ l, |((β.repr (y i) l : ℚ) : ℝ)| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set Sε : ℝ := ∑ i, 1 / ε i with hSdef
  have hS0 : 0 ≤ Sε := Finset.sum_nonneg fun i _ => (one_div_pos.mpr (hε i)).le
  set δ : ℝ := 1 / (W * (1 + Sε)) with hδ
  have hδpos : 0 < δ := by positivity
  have hr : ∀ l, ∃ q : ℚ, |(q : ℝ) - (β l : ℝ)| < δ := by
    intro l
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show (β l : ℝ) - δ < β l + δ by linarith)
    exact ⟨q, abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩⟩
  choose r hr using hr
  refine ⟨β.constr ℚ r, fun i => ?_⟩
  have hφ : ((β.constr ℚ r (y i) : ℚ) : ℝ) = ∑ l, ((β.repr (y i) l : ℚ) : ℝ) * (r l : ℝ) := by
    rw [Module.Basis.constr_apply_fintype]
    simp [Module.Basis.equivFun_apply, smul_eq_mul]
  have hy : (y i : ℝ) = ∑ l, ((β.repr (y i) l : ℚ) : ℝ) * (β l : ℝ) := by
    conv_lhs => rw [← β.sum_repr (y i)]
    rw [Submodule.coe_sum]
    simp [Rat.smul_def]
  rw [hφ, hy, ← Finset.sum_sub_distrib]
  have hsum : ∑ l, |((β.repr (y i) l : ℚ) : ℝ)| ≤ W := by
    have := Finset.single_le_sum (f := fun i => ∑ l, |((β.repr (y i) l : ℚ) : ℝ)|)
      (fun i _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    simp only at this
    linarith
  calc |∑ l, (((β.repr (y i) l : ℚ) : ℝ) * (r l : ℝ) - ((β.repr (y i) l : ℚ) : ℝ) * (β l : ℝ))|
      ≤ ∑ l, |((β.repr (y i) l : ℚ) : ℝ) * (r l : ℝ) - ((β.repr (y i) l : ℚ) : ℝ) * (β l : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |((β.repr (y i) l : ℚ) : ℝ)| * δ := by
        apply Finset.sum_le_sum
        intro l _
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (hr l).le (abs_nonneg _)
    _ = δ * ∑ l, |((β.repr (y i) l : ℚ) : ℝ)| := by rw [Finset.mul_sum]; simp [mul_comm]
    _ ≤ δ * W := mul_le_mul_of_nonneg_left hsum hδpos.le
    _ = 1 / (1 + Sε) := by rw [hδ]; field_simp
    _ < ε i := by
        have hi : 1 / ε i ≤ Sε := Finset.single_le_sum (f := fun i => 1 / ε i)
          (fun i _ => (one_div_pos.mpr (hε i)).le) (Finset.mem_univ i)
        rw [div_lt_iff₀ (by linarith)]
        have := hε i
        have : 1 = ε i * (1 / ε i) := by field_simp
        nlinarith

/-- **Rational points.** -/
theorem rational_points {κ : Type} [Fintype κ] (D : AddSubgroup (κ → ℤ)) (v : κ → ℝ)
    (hv : v ∈ Submodule.span ℝ ((fun d : κ → ℤ => fun i => (d i : ℝ)) '' (D : Set (κ → ℤ))))
    (hpos : ∀ i, 0 ≤ v i) (hne : v ≠ 0) :
    ∃ d ∈ D, (∀ i, 0 ≤ d i) ∧ d ≠ 0 ∧ ∀ i, v i = 0 → d i = 0 := by
  classical
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hv
  choose d hdD hdg using fun k => (g k).2
  have hvi : ∀ i, v i = ∑ k, c k * (d k i : ℝ) := by
    intro i
    rw [← hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hdg k]
  -- the ℚ-span of the coefficients
  set F : Submodule ℚ ℝ := Submodule.span ℚ (Set.range c) with hF
  haveI : FiniteDimensional ℚ F := FiniteDimensional.span_of_finite ℚ (Set.finite_range c)
  have hc : ∀ k, c k ∈ F := fun k => Submodule.subset_span ⟨k, rfl⟩
  set cF : Fin n → F := fun k => ⟨c k, hc k⟩
  set yF : κ → F := fun i => ∑ k, ((d k i : ℤ) : ℚ) • cF k with hyF
  have hyF_coe : ∀ i, (yF i : ℝ) = v i := by
    intro i
    rw [hvi i, hyF, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Rat.smul_def]
    push_cast
    ring
  -- a functional close to the inclusion at the positive coordinates
  obtain ⟨φ, hφ⟩ := approx_functional F (ι₀ := {i // 0 < v i}) (fun i => yF i.1)
    (fun i => v i.1) (fun i => i.2)
  set q : Fin n → ℚ := fun k => φ (cF k) with hq
  have hφy : ∀ i, φ (yF i) = ∑ k, ((d k i : ℤ) : ℚ) * q k := by
    intro i
    simp only [hyF, map_sum, map_smul, smul_eq_mul, hq]
  have hposU : ∀ i, 0 < v i → 0 < φ (yF i) := by
    intro i hi
    have h1 := hφ ⟨i, hi⟩
    simp only at h1
    rw [hyF_coe] at h1
    have h2 : (0 : ℝ) < (φ (yF i) : ℝ) := by
      have := (abs_sub_lt_iff.mp h1).2
      linarith
    exact_mod_cast h2
  have hzero : ∀ i, v i = 0 → φ (yF i) = 0 := by
    intro i hi
    have : yF i = 0 := Subtype.ext (by rw [hyF_coe, hi]; rfl)
    rw [this, map_zero]
  -- clear denominators
  set P : Fin n → ℤ := fun k => ∏ l ∈ Finset.univ.erase k, ((q l).den : ℤ) with hP
  set z : Fin n → ℤ := fun k => (q k).num * P k with hzdef
  set Nn : ℕ := ∏ l, (q l).den with hNn
  have hz : ∀ k, (z k : ℚ) = (Nn : ℚ) * q k := by
    intro k
    have hN : (Nn : ℚ) = (q k).den * ∏ l ∈ Finset.univ.erase k, ((q l).den : ℚ) := by
      rw [hNn, Nat.cast_prod,
        ← Finset.mul_prod_erase Finset.univ (fun l => ((q l).den : ℚ)) (Finset.mem_univ k)]
    simp only [hzdef, hP]
    push_cast
    rw [hN, ← Rat.mul_den_eq_num]
    ring
  have hNpos : (0 : ℚ) < Nn := by
    have : 0 < Nn := Finset.prod_pos fun l _ => (q l).den_pos
    exact_mod_cast this
  set e : κ → ℤ := ∑ k, z k • d k with he_def
  have he : ∀ i, (e i : ℚ) = Nn * φ (yF i) := by
    intro i
    rw [hφy, Finset.mul_sum]
    simp only [he_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hz]
    ring
  refine ⟨e, D.sum_mem fun k _ => D.zsmul_mem (hdD k) _, ?_, ?_, ?_⟩
  · intro i
    rcases (hpos i).lt_or_eq with h | h
    · have h1 : (0 : ℚ) ≤ e i := by rw [he]; exact (mul_pos hNpos (hposU i h)).le
      exact_mod_cast h1
    · have h1 : (e i : ℚ) = 0 := by rw [he, hzero i h.symm, mul_zero]
      have h2 : e i = 0 := by exact_mod_cast h1
      omega
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h'
      push_neg at h'
      exact hne (funext h')
    have hlt : 0 < v i := lt_of_le_of_ne (hpos i) (Ne.symm hi)
    have h1 : (e i : ℚ) = 0 := by rw [h]; simp
    rw [he] at h1
    have := mul_pos hNpos (hposU i hlt)
    linarith
  · intro i hi
    have h1 : (e i : ℚ) = 0 := by rw [he, hzero i hi, mul_zero]
    exact_mod_cast h1

end AIM272Rational

end

#print axioms AIM272Rational.rational_points
