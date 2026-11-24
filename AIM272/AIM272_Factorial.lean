import AIM272_Glued
import AIM272_Main

set_option warningAsError true

/-! # Factorial occupation for the entire embedded chain -/

noncomputable section
open Filter AIM272Unusable AIM272.ContinuousTime
open scoped BigOperators NNReal ENNReal Topology

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

open Classical in
private def radiusBox (κ : Type) [Fintype κ] (n : ℕ) : Finset (State κ) :=
  Fintype.piFinset (fun _ : κ => Finset.range (n + 1))

private theorem mem_radiusBox {n : ℕ} {x : State κ} (hx : radius x ≤ n) : x ∈ radiusBox κ n := by
  classical
  exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr
    (Nat.lt_succ_of_le ((coordinate_le_radius x i).trans hx))

open Classical in
private theorem inner_mass_bound (o : State κ) (lo : ℕ) {R A : ℝ} (hR : 1 < R)
    (hsize : (lo : ℝ) + 1 ≤ R)
    (hOcc : ∀ y ∈ Γ N.toRxn o, radius y < lo → N.occupation o y ≤ realScale R A) :
    (∑' y, if y ∈ Γ N.toRxn o ∧ radius y < lo then N.occupation o y else 0) ≤
      realScale R ((Fintype.card κ : ℝ) + A) := by
  classical
  let B := radiusBox κ lo
  rw [tsum_eq_sum (s := B)]
  · refine (Finset.sum_le_sum (g := fun _ => realScale R A) fun y _ => ?_).trans ?_
    · by_cases h : y ∈ Γ N.toRxn o ∧ radius y < lo
      · simpa only [if_pos h] using hOcc y h.1 h.2
      · simp [h]
    · rw [Finset.sum_const, nsmul_eq_mul, realScale_add (zero_lt_one.trans hR)]
      apply mul_le_mul_right'
      have hc : B.card = (lo + 1) ^ Fintype.card κ := by
        simp [B, radiusBox]
      rw [hc, realScale, Real.rpow_natCast]
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      push_cast
      exact pow_le_pow_left₀ (by positivity) hsize _
  · intro y hy
    have hn : ¬ (y ∈ Γ N.toRxn o ∧ radius y < lo) := fun h => hy (mem_radiusBox h.2.le)
    simp [hn]

private theorem log_factorial_upper (x : State κ) {R : ℝ} (hR : (radius x : ℝ) + 1 ≤ R) :
    Real.log (stateFactorial x : ℝ) ≤ (Fintype.card κ : ℝ) * (radius x : ℝ) * Real.log R := by
  have hprod : Real.log (stateFactorial x : ℝ) = ∑ i, Real.log ((x i).factorial : ℝ) := by
    rw [stateFactorial, Nat.cast_prod, Real.log_prod]
    exact fun i _ => by exact_mod_cast Nat.factorial_ne_zero (x i)
  rw [hprod]
  have hb (i : κ) : Real.log ((x i).factorial : ℝ) ≤ (radius x : ℝ) * Real.log R := by
    have h : (x i).factorial ≤ (radius x + 1) ^ radius x :=
      ((x i).factorial_le_pow.trans
        (Nat.pow_le_pow_left ((coordinate_le_radius x i).trans (Nat.le_succ _)) _)).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) (coordinate_le_radius x i))
    have hreal : ((x i).factorial : ℝ) ≤ ((radius x : ℝ) + 1) ^ radius x := by exact_mod_cast h
    have hb := Real.log_le_log (show (0 : ℝ) < (x i).factorial by exact_mod_cast Nat.factorial_pos _) hreal
    rw [Real.log_pow] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) hR) (Nat.cast_nonneg _))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)

private theorem factorial_eq_scale (x : State κ) {R : ℝ} (hR : 1 < R) :
    (stateFactorial x : ℝ≥0∞) = realScale R (Real.log (stateFactorial x : ℝ) / Real.log R) := by
  rw [realScale, Real.rpow_def_of_pos (zero_lt_one.trans hR)]
  have hlog : Real.log R ≠ 0 := (Real.log_pos hR).ne'
  rw [show Real.log R * (Real.log (stateFactorial x : ℝ) / Real.log R) =
    Real.log (stateFactorial x : ℝ) by field_simp,
    Real.exp_log (by exact_mod_cast stateFactorial_pos x), ENNReal.ofReal_natCast]

private theorem realScale_inv {R : ℝ} (hR : 0 < R) (t : ℝ) : (realScale R t)⁻¹ = realScale R (-t) := by
  simp [realScale, Real.rpow_neg hR.le, ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hR t)]

private theorem pointBudget_le_scale {k R : ℝ} (hk : 0 ≤ k) (hR : 1 < R) {r : ℕ}
    (hr : 2 + (r : ℝ) ≤ R) :
    ENNReal.ofReal (Real.exp (k * (1 + (r : ℝ)) * Real.log (2 + (r : ℝ)))) ≤
      realScale R (k * (1 + (r : ℝ))) := by
  unfold realScale
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hR)]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm (Real.log R)] using mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) hr) (by positivity : 0 ≤ k * (1 + (r : ℝ)))

set_option maxHeartbeats 1000000 in
private theorem finish_large_states [Nonempty κ] (wr : N.WeaklyReversible) (o : State κ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r : ℝ in atTop, ∀ x ∈ Γ N.toRxn o, (radius x : ℝ) = r →
      (stateFactorial x : ℝ≥0∞) * N.occupation o x ≤
        2 * ENNReal.ofReal (Real.exp (δ * r * Real.log (2 + r))) := by
  classical
  let d : ℝ := Fintype.card κ
  have hd : 1 ≤ d := by
    change 1 ≤ (Fintype.card κ : ℝ)
    have hp : 0 < Fintype.card κ := Fintype.card_pos
    have h := (Nat.succ_le_of_lt hp)
    exact_mod_cast h
  obtain ⟨J, hJ⟩ := N.jump_coordinate_bound
  obtain ⟨C₁, hC₁, hVisits⟩ := N.pointwise_return_bound o
  obtain ⟨θ, e, A, u, hθ, hθ', he, he', hA, hu, hθd, hed, hθA, huA, hsmall, hsmall', hearly, hlate⟩ :=
    AIM272Analytic.scale_choice hd hC₁ hδ
  have hA0 : 0 < A := by linarith
  have hul : u < 1 := by
    have h := mul_le_mul_of_nonneg_left hA hu.le
    linarith
  obtain ⟨K, hK, hall⟩ := N.shell_potential_eventually wr o hθ hθ' he he' hu hul J (fun hp i => (hJ hp i).1)
  let ε := min (θ / 16) (δ / (64 * A))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεθ : ε ≤ θ / 16 := min_le_left _ _
  have hεδ : 4 * ε * A ≤ δ / 16 := by
    have h := (le_div_iff₀ (by positivity : 0 < 64 * A)).mp
      (show ε ≤ δ / (64 * A) from min_le_right _ _)
    nlinarith
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hall ε hε)
  let D := d + C₁ + K + d * (2 + (J : ℝ))
  let earlyConstant := D + K + (C₁ + d) * u + θ * e * d + 4 * ε
  let lateConstant := D + K + C₁
  filter_upwards [eventually_ge_atTop (max 2 (2 * A + 2)), eventually_ge_atTop n₀,
    eventually_ge_atTop (((radius o : ℝ) + 1) / (u * A)),
    eventually_ge_atTop (earlyConstant / (δ / 16)), eventually_ge_atTop lateConstant]
    with r hr hlarge hroot hlargeEarly hlargeLate x hx hxr
  have hr2 : 2 ≤ r := (le_max_left _ _).trans hr
  have hrA : 2 * A + 2 ≤ r := (le_max_right _ _).trans hr
  have hr0 : 0 ≤ r := by linarith
  let n := ⌈A * r⌉₊
  let lo := ⌈u * (n : ℝ)⌉₊
  let R := 2 * (n : ℝ)
  have hnr : A * r ≤ (n : ℝ) := Nat.le_ceil _
  have hnr' : (n : ℝ) ≤ A * r + 1 := (Nat.ceil_lt_add_one (mul_nonneg hA0.le hr0)).le
  have hrn : 2 * r ≤ (n : ℝ) := (mul_le_mul_of_nonneg_right hA hr0).trans hnr
  have hn : 0 < (n : ℝ) := by linarith
  have hR : 1 < R := by dsimp [R]; linarith
  have hR0 := zero_lt_one.trans hR
  have hRlr : 2 + r ≤ R := by dsimp [R]; linarith
  have hRl : R ≤ (2 + r) ^ (2 : ℕ) := by
    dsimp [R]
    nlinarith [mul_le_mul_of_nonneg_right hrA hr0]
  have huN : u * (n : ℝ) ≤ r := by
    have h₁ := mul_le_mul_of_nonneg_left hnr' hu.le
    have h₂ := mul_le_mul_of_nonneg_right huA.le hr0
    have h₃ : u < 1 := hul
    nlinarith
  have hL : lo ≤ radius x := Nat.ceil_le.mpr (hxr.symm ▸ huN)
  have hH : radius x < n := by
    exact_mod_cast (show (radius x : ℝ) < n by rw [hxr]; linarith)
  have ho : radius o < lo := Nat.lt_ceil.mpr (by
    have h₁ := (div_le_iff₀ (mul_pos hu hA0)).mp hroot
    have h₂ := mul_le_mul_of_nonneg_left hnr hu.le
    nlinarith)
  obtain ⟨V, F, hV, hOut, hDrift⟩ := hn₀ (n : ℝ) (show n₀ ≤ (n : ℝ) by linarith)
  let C₂ := C₁ + d
  let entExp := K + d * (u * (n : ℝ) + 2 + J) + ε * R
  let massExp := d + C₁ * (1 + u * (n : ℝ))
  let expBase := D + C₂ * u * (n : ℝ) + ε * R
  let price (y : State κ) := realScale R (-K + θ * F y)
  let outer := realScale R (-K + θ * ((n : ℝ) / 2))
  let M := ENNReal.ofReal (Real.exp (C₁ * (1 + r) * Real.log (2 + r)))
  have hM : ∀ y, N.killedPotential {z | z ≠ o} (fun z => if z = x then 1 else 0) y ≤ M := by
    have hne : x ≠ o := fun e => (lt_of_lt_of_le ho (e ▸ hL)).false
    simpa only [M, hxr] using ((hVisits x hx).2 hne).2
  have hVEnt (y : State κ) (_ : y ∈ Γ N.toRxn o) (_ : lo ≤ radius y) (hy : radius y ≤ lo + J) :
      V y ≤ realScale R entExp := by
    have heq : (lo : ℝ) ≤ u * (n : ℝ) + 1 := (Nat.ceil_lt_add_one (mul_nonneg hu.le hn.le)).le
    have hry : (radius y : ℝ) ≤ (lo : ℝ) + J := by exact_mod_cast hy
    apply (hV y).trans
    apply realScale_mono hR.le
    have hz : 0 ≤ d * ((radius y : ℝ) + 1) + ε * R := by positivity
    have hstay := mul_le_mul_of_nonneg_right hθ'.le hz
    have hh := mul_le_mul_of_nonneg_left (show (radius y : ℝ) + 1 ≤ u * (n : ℝ) + 2 + J by linarith)
      (by linarith : 0 ≤ d)
    dsimp [entExp]
    linarith
  have hPpos (p : ℝ) : 0 < realScale R p := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hR0 _)
  have hoc := N.shell_occupation_bound wr o x lo n J ho ⟨hL, hH⟩
    (fun hp => radius_le_of_coordinate fun i => (hJ hp i).1) V price M (realScale R entExp) outer
    (hPpos _) ENNReal.ofReal_ne_top (hPpos _) ENNReal.ofReal_ne_top hM hVEnt
    (fun y hy hp hq => hOut y hy (by exact_mod_cast hp) (by exact_mod_cast hq))
    (fun y hy hp hq => (hDrift y hy (Nat.le_ceil _ |>.trans (by exact_mod_cast hp)) (by exact_mod_cast hq)).1)
  have hMass : (∑' y, if y ∈ Γ N.toRxn o ∧ radius y < lo then N.occupation o y else 0) ≤ realScale R massExp := by
    have hl : (lo : ℝ) < u * (n : ℝ) + 1 := Nat.ceil_lt_add_one (mul_nonneg hu.le hn.le)
    apply N.inner_mass_bound o lo hR (by dsimp [R]; nlinarith) _
    intro y hy hr'
    have hrad : (radius y : ℝ) < u * (n : ℝ) := Nat.lt_ceil.mp hr'
    have hradR : 2 + (radius y : ℝ) ≤ R := by dsimp [R]; nlinarith
    exact (hVisits y hy).1.trans ((pointBudget_le_scale hC₁ hR hradR).trans
      (realScale_mono hR.le (mul_le_mul_of_nonneg_left (by linarith) hC₁)))
  have hM' : M ≤ realScale R (C₁ * (1 + r)) := by
    simpa only [M, hxr] using pointBudget_le_scale hC₁ hR (r := radius x) (by rwa [hxr])
  have hscale : realScale R entExp * realScale R massExp = realScale R expBase := by
    rw [← realScale_add hR0]
    congr 1
    dsimp [entExp, massExp, expBase, D, C₂]
    ring
  have hfull : N.occupation o x ≤ realScale R (expBase + K - θ * F x) +
      realScale R (expBase + C₁ * (1 + r) + K - θ * ((n : ℝ) / 2)) := by
    apply hoc.trans
    simp only [price, outer, div_eq_mul_inv, realScale_inv hR0]
    have h₁ := mul_le_mul_left' hMass (realScale R (-(-K + θ * F x)) * realScale R entExp)
    have h₂ := mul_le_mul' (mul_le_mul_right' (mul_le_mul_right' hM'
      (realScale R (-(-K + θ * ((n : ℝ) / 2))))) (realScale R entExp)) hMass
    apply (add_le_add h₁ h₂).trans
    rw [mul_assoc (realScale R (-(-K + θ * F x))) (realScale R entExp) (realScale R massExp),
      mul_assoc (realScale R (C₁ * (1 + r)) * realScale R (-(-K + θ * ((n : ℝ) / 2))))
        (realScale R entExp) (realScale R massExp), hscale]
    simp only [← realScale_add hR0]
    apply le_of_eq
    congr 1 <;> congr 1 <;> ring
  let U := Real.log (stateFactorial x : ℝ) / Real.log R
  have hlogR := Real.log_pos hR
  have hU : U ≤ d * r := by
    apply (div_le_iff₀ hlogR).mpr
    simpa only [hxr] using log_factorial_upper x (R := R) (by rw [hxr]; linarith)
  have hF : U ≤ F x + e * d * (r + 1) + ε * R := by
    apply (div_le_iff₀ hlogR).mpr
    simpa only [hxr] using (hDrift x hx (hxr.symm ▸ huN) (by exact_mod_cast hH)).2
  have hearlyExp : U + (expBase + K - θ * F x) ≤ (δ / 2) * r := by
    have hp : U - θ * F x ≤ d * (1 - θ) * r + θ * (e * d * (r + 1) + ε * R) := by
      nlinarith [mul_le_mul_of_nonneg_left hF hθ.le,
        mul_le_mul_of_nonneg_left hU (sub_nonneg.mpr hθ'.le)]
    have hbase : C₂ * u * (n : ℝ) ≤ C₂ * u * (A * r + 1) :=
      mul_le_mul_of_nonneg_left hnr' (by dsimp [C₂]; positivity)
    have hεR : (1 + θ) * ε * R ≤ 4 * ε * (A * r + 1) := by
      have h₁ := mul_le_mul_of_nonneg_right (show 1 + θ ≤ 2 by linarith) (mul_nonneg hε.le hR0.le)
      have h₂ := mul_le_mul_of_nonneg_left (show R ≤ 2 * (A * r + 1) by dsimp [R]; linarith) (by positivity : 0 ≤ 2 * ε)
      nlinarith
    have h₁ := mul_le_mul_of_nonneg_right hearly.le hr0
    have h₂ := mul_le_mul_of_nonneg_right hεδ hr0
    have h₃ := (div_le_iff₀ (show 0 < δ / 16 by positivity)).mp hlargeEarly
    dsimp [expBase, C₂, earlyConstant] at hbase h₃ ⊢
    nlinarith only [hp, hbase, hεR, h₁, h₂, h₃]
  have hlateExp : U + (expBase + C₁ * (1 + r) + K - θ * ((n : ℝ) / 2)) ≤ 0 := by
    have h₁ := mul_le_mul_of_nonneg_right hsmall.le hn.le
    have h₂ := mul_le_mul_of_nonneg_right hεθ hn.le
    have h₃ := mul_le_mul_of_nonneg_left hnr (show 0 ≤ θ / 4 by positivity)
    have h₄ := mul_le_mul_of_nonneg_right hlate.le hr0
    dsimp [expBase, R, C₂, lateConstant] at hlargeLate ⊢
    nlinarith only [hU, h₁, h₂, h₃, h₄, hlargeLate, hr0]
  have hTarget : realScale R ((δ / 2) * r) ≤ ENNReal.ofReal (Real.exp (δ * r * Real.log (2 + r))) := by
    rw [realScale, Real.rpow_def_of_pos hR0]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hl := Real.log_le_log hR0 hRl
    rw [Real.log_pow] at hl
    have hh := mul_le_mul_of_nonneg_right hl (mul_nonneg (by positivity : 0 ≤ δ / 2) hr0)
    nlinarith only [hh]
  rw [factorial_eq_scale x hR]
  calc
    _ ≤ realScale R (U + (expBase + K - θ * F x)) +
        realScale R (U + (expBase + C₁ * (1 + r) + K - θ * ((n : ℝ) / 2))) := by
      rw [realScale_add hR0, realScale_add hR0, ← mul_add]
      exact mul_le_mul_left' hfull _
    _ ≤ realScale R ((δ / 2) * r) + realScale R ((δ / 2) * r) :=
      add_le_add (realScale_mono hR.le hearlyExp)
        (realScale_mono hR.le (hlateExp.trans (by positivity)))
    _ ≤ _ := by rw [two_mul]; exact add_le_add hTarget hTarget

/-- T1, the factorial tail of the actual weakly reversible jump excursion. -/
theorem t1 (wr : N.WeaklyReversible) (o : State κ) : N.FactorialBound o := by
  classical
  rcases isEmpty_or_nonempty κ with he | hn
  · letI := he
    haveI : Subsingleton (State κ) := ⟨fun x y => funext fun i => isEmptyElim i⟩
    exact N.t1_finite_class o (Set.toFinite _)
  letI : Nonempty κ := hn
  intro δ hδ
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp (N.finish_large_states wr o hδ)
  obtain ⟨n, hn⟩ := exists_nat_ge r₀
  obtain ⟨C₁, _, hC₁⟩ := N.pointwise_return_bound o
  let w (x : State κ) := (stateFactorial x : ℝ≥0∞) * N.occupation o x
  obtain ⟨C, hC⟩ := ((radiusBox κ n).finite_toSet.image (fun x => (w x).toNNReal)).bddAbove
  refine ⟨max 2 C, fun x hx => ?_⟩
  by_cases hm : n ≤ radius x
  · have hh := hr₀ (radius x : ℝ) (show r₀ ≤ (radius x : ℝ) from hn.trans (by exact_mod_cast hm)) x hx rfl
    exact hh.trans (mul_le_mul_right' (ENNReal.coe_le_coe.mpr (le_max_left (2 : ℝ≥0) C)) _)
  have hfinite : w x ≠ ⊤ := (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
    ((hC₁ x hx).1.trans_lt ENNReal.ofReal_lt_top)).ne
  have hZ : 1 ≤ ENNReal.ofReal (Real.exp (δ * (radius x : ℝ) * Real.log (2 + (radius x : ℝ)))) :=
    ENNReal.one_le_ofReal.mpr (Real.one_le_exp (mul_nonneg (mul_nonneg hδ.le (Nat.cast_nonneg _))
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (radius x)]))))
  calc
    _ = ((w x).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hfinite).symm
    _ ≤ (C : ℝ≥0∞) := ENNReal.coe_le_coe.mpr
      (hC (Set.mem_image_of_mem _ (mem_radiusBox (le_of_lt (lt_of_not_ge hm)))))
    _ ≤ (max 2 C : ℝ≥0) := ENNReal.coe_le_coe.mpr (le_max_right _ _)
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_left' hZ ((max 2 C : ℝ≥0) : ℝ≥0∞)

theorem t2 (wr : N.WeaklyReversible) (o : State κ) : N.expectedReturnJumps o < ⊤ :=
  N.t2_of_t1 wr o (N.t1 wr o)

theorem t3 (wr : N.WeaklyReversible) (o : State κ) (hi : (Γ N.toRxn o).Infinite)
    (norris : NorrisJumpReturn (State κ)) :
    NonexplosiveOn N.transition N.totalRate (Γ N.toRxn o) ∧
    PositiveRecurrentOn N.transition N.totalRate (Γ N.toRxn o) N.aliveMass ∧
    StationaryOn N.transition N.totalRate (Γ N.toRxn o) (N.normalizedOccupation o) ∧
    (∀ π, StationaryOn N.transition N.totalRate (Γ N.toRxn o) π → π = N.normalizedOccupation o) ∧
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ≥0, ∀ x ∈ Γ N.toRxn o,
      (stateFactorial x : ℝ≥0∞) * N.normalizedOccupation o x ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (Real.exp (δ * (radius x : ℝ) * Real.log (2 + (radius x : ℝ)))) :=
  N.t3_of_t1 wr o hi norris (N.t1 wr o)

end AIM272.Network
