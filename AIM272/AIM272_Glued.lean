import AIM272_LocalComparison
import AIM272_ShellBudget
import AIM272_Geometry

set_option warningAsError true

/-! # Gluing the local potentials on a shell -/

noncomputable section
open Filter AIM272Unusable AIM272Translation
open scoped BigOperators ENNReal Topology

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

theorem radius_attained [Nonempty κ] (x : State κ) : ∃ i, x i = radius x := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  exact ⟨i, le_antisymm (coordinate_le_radius x i) (Finset.sup_le hi)⟩

private theorem face_jump_upper (a : κ → ℝ) (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ → ℝ) (R : ℝ) {x y : State κ} {J : ℕ} (hJ : ∀ i, y i ≤ x i + J) :
    Lval a b R (fun i => (y i : ℝ)) ≤ Lval a b R (fun i => (x i : ℝ)) + (Fintype.card κ : ℝ) * J := by
  unfold Lval
  have hs : ∑ i, a i * ((y i : ℝ) + 1) ≤
      ∑ i, (a i * ((x i : ℝ) + 1) + (J : ℝ)) := by
    apply Finset.sum_le_sum
    intro i _
    have h : (y i : ℝ) ≤ (x i : ℝ) + J := by exact_mod_cast hJ i
    have h₁ := mul_le_mul_of_nonneg_left (show (y i : ℝ) + 1 ≤ (x i : ℝ) + 1 + J by linarith) (ha i).1
    have h₂ := mul_le_mul_of_nonneg_right (ha i).2 (Nat.cast_nonneg (α := ℝ) J)
    nlinarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  linarith

private theorem log_factorial_le_face (a : κ → ℝ) (b : ℝ → ℝ) {R e u : ℝ}
    (hR : 1 < R) (he : 0 ≤ e) (x : State κ)
    (h : ∀ i, |Real.log ((x i : ℝ) + 1) / Real.log R - a i| ≤ e) (hb : -u ≤ b R) :
    Real.log (stateFactorial x : ℝ) ≤
      (Lval a b R (fun i => (x i : ℝ)) + e * (Fintype.card κ : ℝ) * ((radius x : ℝ) + 1) + u) *
        Real.log R := by
  classical
  have hlog := Real.log_pos hR
  have hprod : Real.log (stateFactorial x : ℝ) = ∑ i, Real.log ((x i).factorial : ℝ) := by
    rw [stateFactorial, Nat.cast_prod, Real.log_prod]
    exact fun i _ => by exact_mod_cast Nat.factorial_ne_zero (x i)
  have hc (i : κ) : Real.log ((x i).factorial : ℝ) ≤
      (a i * ((x i : ℝ) + 1) + e * ((radius x : ℝ) + 1)) * Real.log R := by
    have h₁ : Real.log ((x i : ℝ) + 1) ≤ (a i + e) * Real.log R := by
      have hupper := (abs_le.mp (h i)).2
      exact (div_le_iff₀ hlog).mp (by linarith)
    have h₂ : (x i).factorial ≤ (x i + 1) ^ (x i + 1) :=
      ((x i).factorial_le_pow.trans (Nat.pow_le_pow_left (Nat.le_succ _) _)).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _))
    have hcast : ((x i).factorial : ℝ) ≤ ((x i : ℝ) + 1) ^ (x i + 1) := by exact_mod_cast h₂
    have h₃ := Real.log_le_log (show (0 : ℝ) < (x i).factorial by exact_mod_cast Nat.factorial_pos _) hcast
    push_cast at h₃
    rw [Real.log_pow] at h₃
    simp only [Nat.cast_add, Nat.cast_one] at h₃
    refine h₃.trans ?_
    have hr : (x i : ℝ) ≤ radius x := by exact_mod_cast coordinate_le_radius x i
    calc
      _ ≤ ((x i : ℝ) + 1) * ((a i + e) * Real.log R) :=
        mul_le_mul_of_nonneg_left h₁ (by positivity)
      _ = (a i * ((x i : ℝ) + 1) + e * ((x i : ℝ) + 1)) * Real.log R := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right hr 1) he) _) hlog.le
  rw [hprod]
  refine (Finset.sum_le_sum (fun i _ => hc i)).trans ?_
  rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hlog.le
  unfold Lval
  linarith

private theorem nextMean_const_mul' (A : ℝ≥0∞) (U : State κ → ℝ≥0∞) (x : State κ) :
    N.nextMean (fun y => A * U y) x = A * N.nextMean U x := by
  simp only [nextMean, mul_left_comm _ A, ENNReal.tsum_mul_left]

/-- G9 and the active-face factorial comparison. The bounds include actual
outer landing states. K is fixed independently of the offset tolerance ε. -/
theorem shell_potential_eventually [Nonempty κ] (wr : N.WeaklyReversible) (o : State κ)
    {θ e u : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) (he : 0 < e) (he' : e < 1 / 4)
    (hu : 0 < u) (hu' : u < 1) (J : ℕ)
    (hJ : ∀ {x y : State κ}, 0 < N.transition x y → ∀ i, y i ≤ x i + J) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε > 0, ∀ᶠ n : ℝ in atTop,
      ∃ (V : State κ → ℝ≥0∞) (F : State κ → ℝ),
        (∀ y, V y ≤ realScale (2 * n)
          (K + θ * ((Fintype.card κ : ℝ) * ((radius y : ℝ) + 1) + ε * (2 * n)))) ∧
        (∀ y ∈ Γ N.toRxn o, n ≤ (radius y : ℝ) → (radius y : ℝ) ≤ n + J →
          realScale (2 * n) (-K + θ * (n / 2)) ≤ V y) ∧
        ∀ x ∈ Γ N.toRxn o, u * n ≤ (radius x : ℝ) → (radius x : ℝ) < n →
          (realScale (2 * n) (-K + θ * F x) + N.nextMean V x ≤ V x) ∧
          Real.log (stateFactorial x : ℝ) ≤ (F x + e * (Fintype.card κ : ℝ) *
            ((radius x : ℝ) + 1) + ε * (2 * n)) * Real.log (2 * n) := by
  classical
  have hchoose (a : κ → ℝ) : ∃ E C : ℝ, 0 < E ∧ E ≤ e ∧ 0 ≤ C ∧
      ((∀ i, 0 ≤ a i) → ∀ᶠ R : ℝ in atTop, ∀ x ∈ N.localDomain a R E,
        N.localPotential wr a R E θ x ≤ realScale R (C + θ * weight a x)) := by
    by_cases ha : ∀ i, 0 ≤ a i
    · obtain ⟨E, C, hE, hEe, hC, hU⟩ := N.localPotential_eventually_upper wr a ha hθ hθ' he
      exact ⟨E, C, hE, hEe, hC, fun _ => hU⟩
    · exact ⟨e, 0, he, le_rfl, le_rfl, fun h => (ha h).elim⟩
  choose E C hE hEe hC hU using hchoose
  obtain ⟨Λ, hΛ, hSlope, hOff, hGeo⟩ := AIM272Geometry.shell_faces_usable_nonempty N.toRxn o E hE
    (fun a => (hEe a).trans_lt (by linarith)) (u := u / 2) (by linarith)
  let S := Λ.toFinset
  have hS : S.Nonempty := by
    cases Λ with
    | nil => exact (hΛ rfl).elim
    | cons l ls => exact ⟨l, List.mem_toFinset.mpr List.mem_cons_self⟩
  let B := S.sup' hS (fun l => max (C l.1) (θ * N.maxComplexHeight l.1))
  let K := B + 1
  have hB (l) (hl : l ∈ S) : C l.1 ≤ B ∧ θ * N.maxComplexHeight l.1 ≤ B := by
    have hh := Finset.le_sup' (fun l => max (C l.1) (θ * N.maxComplexHeight l.1)) hl
    exact ⟨(le_max_left _ _).trans hh, (le_max_right _ _).trans hh⟩
  have hB0 : 0 ≤ B := by
    obtain ⟨l, hl⟩ := hS
    exact (hC l.1).trans (hB l hl).1
  refine ⟨K, by dsimp [K]; linarith, fun ε hε => ?_⟩
  have h2 : Tendsto (fun n : ℝ => 2 * n) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
  have hOff' := AIM272Geometry.eventually_list Λ (fun l hl => hOff l hl (min ε (1 / 16))
    (lt_min hε (by norm_num)))
  have hU' := AIM272Geometry.eventually_list Λ (fun l hl => hU l.1 (fun i => (hSlope l hl i).1))
  have hLeak := AIM272Analytic.leakage_eventually_small (K₁ := B)
    (K₂ := B + θ * ((Fintype.card κ : ℝ) * J) + 1) hθ
  have hPow := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).eventually_ge_atTop 2
  filter_upwards [hGeo, h2.eventually hOff', h2.eventually hU', h2.eventually hLeak,
    h2.eventually hPow, eventually_ge_atTop ((J : ℝ) + 3),
    h2.eventually (eventually_ge_atTop (S.card : ℝ))]
    with n hGeo hOff hU hLeak hPow hn hcard
  let R := 2 * n
  have hn0 : 0 < n := by linarith [Nat.cast_nonneg (α := ℝ) J]
  have hR2 : 2 ≤ R := by dsimp [R]; linarith
  have hR : 1 < R := by linarith
  have hR0 := zero_lt_one.trans hR
  let Fval (l : (κ → ℝ) × (ℝ → ℝ)) (x : State κ) := Lval l.1 l.2 R (fun i => (x i : ℝ))
  let F (x : State κ) := S.sup' hS (fun l => Fval l x)
  let coeff (l : (κ → ℝ) × (ℝ → ℝ)) :=
    realScale R (θ * ((∑ i, l.1 i) + l.2 R))
  let W (l : (κ → ℝ) × (ℝ → ℝ)) (x : State κ) :=
    coeff l * N.localPotential wr l.1 R (E l.1) θ x
  let V (x : State κ) := ∑ l ∈ S, W l x
  have hF (x : State κ) (l) (hl : l ∈ S) : Fval l x ≤ F x :=
    Finset.le_sup' (fun l => Fval l x) hl
  have hActive (x : State κ) : ∃ l ∈ S, F x = Fval l x := Finset.exists_mem_eq_sup' hS _
  have hShift (l) (x : State κ) :
      θ * ((∑ i, l.1 i) + l.2 R) + θ * weight l.1 x = θ * Fval l x := by
    simp only [Fval, Lval, weight, mul_add, mul_one, Finset.sum_add_distrib]
    ring
  have hW (l) (hl : l ∈ S) (x : State κ) : W l x ≤ realScale R (B + θ * Fval l x) := by
    by_cases hx : x ∈ N.localDomain l.1 R (E l.1)
    · calc
        _ ≤ coeff l * realScale R (C l.1 + θ * weight l.1 x) :=
          mul_le_mul_left' (hU l (List.mem_toFinset.mp hl) x hx) _
        _ = realScale R (C l.1 + θ * Fval l x) := by
          dsimp only [coeff]
          rw [← realScale_add hR0, ← hShift]
          congr 1
          ring
        _ ≤ _ := realScale_mono hR.le (add_le_add_right (hB l hl).1 _)
    · dsimp only [W, localPotential]
      rw [N.killedPotential_zero hx, mul_zero]
      exact zero_le _
  have hSize (s : ℝ) :
      (∑ _ ∈ S, realScale R s) ≤ realScale R (s + 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, realScale_add hR0, mul_comm (S.card : ℝ≥0∞)]
    apply mul_le_mul_left'
    simpa only [ENNReal.ofReal_natCast, realScale, Real.rpow_one] using ENNReal.ofReal_le_ofReal hcard
  have hV (x : State κ) : V x ≤ realScale R (K + θ * F x) := by
    refine (Finset.sum_le_sum (fun l hl => (hW l hl x).trans
      (realScale_mono hR.le (add_le_add_left (mul_le_mul_of_nonneg_left (hF x l hl) hθ.le) B)))).trans ?_
    have hs := hSize (B + θ * F x)
    rw [show B + θ * F x + 1 = K + θ * F x by dsimp [K]; ring] at hs
    exact hs
  have hNear (x : State κ) (hx : x ∈ Γ N.toRxn o)
      (hlow : (u / 2) * n ≤ (radius x : ℝ)) (hhi : (radius x : ℝ) ≤ n + J)
      (l) (hl : l ∈ S) (ha : F x ≤ Fval l x + Real.log R ^ 2) :
      x ∈ N.localDomain l.1 R (E l.1) := by
    obtain ⟨i, hi⟩ := radius_attained x
    have hcoord (j : κ) : (x j : ℝ) + 1 ≤ R := by
      have h := coordinate_le_radius x j
      dsimp [R]
      linarith [show (x j : ℝ) ≤ radius x by exact_mod_cast h]
    have hf := hGeo x hx ⟨i, by simpa only [hi] using hlow⟩ hcoord l (List.mem_toFinset.mp hl)
      (fun l' hl' => (hF x l' (List.mem_toFinset.mpr hl')).trans ha)
    refine ⟨N.negativeLoop_of_usable l.1 (fun j => (hSlope l (List.mem_toFinset.mp hl) j).1) hf.1 hx,
      by dsimp [R]; linarith, fun j => ?_⟩
    have hh := (dist_pi_lt_iff (hE l.1)).mp hf.2 j
    simpa only [Real.dist_eq, wR] using hh
  have hVlow (x : State κ) (hx : x ∈ Γ N.toRxn o)
      (hlow : (u / 2) * n ≤ (radius x : ℝ)) (hhi : (radius x : ℝ) ≤ n + J) :
      realScale R (-B + θ * F x) ≤ V x := by
    obtain ⟨l, hl, heq⟩ := hActive x
    have hd := hNear x hx hlow hhi l hl (heq.trans_le (le_add_of_nonneg_right (sq_nonneg _)))
    refine le_trans ?_ (Finset.single_le_sum (f := fun l => W l x) (fun _ _ => zero_le _) hl)
    have hw := N.localPotential_lower wr l.1 hR.le hθ.le hd
    have hv : coeff l * realScale R (-(θ * N.maxComplexHeight l.1) + θ * weight l.1 x) ≤ W l x := by
      simpa only [realScale, Real.rpow_add hR0] using mul_le_mul_left' hw (coeff l)
    apply le_trans _ hv
    dsimp only [coeff]
    rw [← realScale_add hR0]
    apply realScale_mono hR.le
    rw [heq]
    linarith [hShift l x, (hB l hl).2]
  refine ⟨V, F, fun y => ?_, fun y hy houter hupper => ?_, fun x hx hlow hhi => ?_⟩
  · apply (hV y).trans
    apply realScale_mono hR.le
    apply add_le_add_left
    apply mul_le_mul_of_nonneg_left _ hθ.le
    obtain ⟨l, hl, hf⟩ := hActive y
    rw [hf]
    have hl' := List.mem_toFinset.mp hl
    have hoff := (abs_le.mp (hOff l hl')).2.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hR0.le)
    have hsum : ∑ i, l.1 i * ((y i : ℝ) + 1) ≤ (Fintype.card κ : ℝ) * ((radius y : ℝ) + 1) := by
      calc
        _ ≤ ∑ _ : κ, ((radius y : ℝ) + 1) := Finset.sum_le_sum fun i _ => mul_le_of_le_one_left
          (by positivity) (hSlope l hl' i).2 |>.trans (by exact_mod_cast Nat.add_le_add_right (coordinate_le_radius y i) 1)
        _ = _ := by simp [mul_add]
    exact add_le_add hsum hoff
  · have hsmall : (u / 2) * n ≤ (radius y : ℝ) := by nlinarith
    obtain ⟨l, hl, hf⟩ := hActive y
    have hmem := hNear y hy hsmall hupper l hl (hf.trans_le (le_add_of_nonneg_right (sq_nonneg _)))
    obtain ⟨i, hi⟩ := radius_attained y
    have hiN : n ≤ (y i : ℝ) + 1 := by rw [hi]; linarith
    have hiW : 1 - 1 / 8 ≤ Real.log ((y i : ℝ) + 1) / Real.log R := by
      by_contra! h
      have hY := AIM272Geometry.lt_rpow_of_wR hR (by positivity) h
      have hRpow : R ^ (1 - (1 : ℝ) / 8) ≤ n := by
        have hx := mul_le_mul_of_nonneg_right hPow (Real.rpow_nonneg hR0.le (1 - (1 : ℝ) / 8))
        rw [← Real.rpow_add hR0, show (1 : ℝ) / 8 + (1 - 1 / 8) = (1 : ℝ) by ring, Real.rpow_one] at hx
        dsimp [R] at hx
        linarith
      linarith
    have ha : 1 - e - 1 / 8 ≤ l.1 i := by
      have hx := (abs_lt.mp (hmem.2.2 i)).2
      linarith [hEe l.1]
    have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, l.1 j * ((y j : ℝ) + 1) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hSlope l (List.mem_toFinset.mp hl) j).1 (by positivity)
    have hoff : -(n / 8) ≤ l.2 R := by
      have hb := (abs_le.mp (hOff l (List.mem_toFinset.mp hl))).1
      have he := mul_le_mul_of_nonneg_right (min_le_right ε (1 / 16)) hR0.le
      dsimp [R] at he
      linarith
    have hFouter : n / 2 ≤ F y := by
      rw [hf]
      dsimp only [Fval, Lval]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp only [add_comm (∑ j ∈ Finset.univ.erase i, l.1 j * ((y j : ℝ) + 1))]
      exact AIM272Analytic.outer_face_lower_bound hn0.le ha hiN hrest hoff he' le_rfl le_rfl
    exact (realScale_mono hR.le (by dsimp [K]; nlinarith [mul_le_mul_of_nonneg_left hFouter hθ.le])).trans
      (hVlow y hy hsmall hupper)
  · have hlow' : (u / 2) * n ≤ (radius x : ℝ) := by nlinarith
    have hhi' : (radius x : ℝ) ≤ n + J := by linarith [Nat.cast_nonneg (α := ℝ) J]
    obtain ⟨a, ha, haF⟩ := hActive x
    have haDom := hNear x hx hlow' hhi' a ha (haF.trans_le (le_add_of_nonneg_right (sq_nonneg _)))
    constructor
    · let debit (l : (κ → ℝ) × (ℝ → ℝ)) : ℝ≥0∞ :=
        if x ∈ N.localDomain l.1 R (E l.1) then coeff l * realScale R (θ * N.level wr l.1 x) else 0
      let loss (l : (κ → ℝ) × (ℝ → ℝ)) : ℝ≥0∞ :=
        if x ∈ N.localDomain l.1 R (E l.1) then 0 else N.nextMean (W l) x
      have heq (l) : debit l + N.nextMean (W l) x = W l x + loss l := by
        by_cases hd : x ∈ N.localDomain l.1 R (E l.1)
        · simp only [debit, loss, if_pos hd, add_zero, W, nextMean_const_mul']
          rw [← mul_add, N.localPotential_poisson wr l.1 R (E l.1) θ hd]
          rfl
        · simp [debit, loss, hd, W, localPotential, N.killedPotential_zero hd]
      have hb (l) (hl : l ∈ S) : loss l ≤ realScale R
          (B + θ * ((Fintype.card κ : ℝ) * J) + θ * F x - θ * Real.log R ^ 2) := by
        by_cases hd : x ∈ N.localDomain l.1 R (E l.1)
        · simp [loss, hd]
        have hnot : Fval l x + Real.log R ^ 2 < F x :=
          lt_of_not_ge (fun he => hd (hNear x hx hlow' hhi' l hl he))
        rw [show loss l = N.nextMean (W l) x from if_neg hd,
          ← N.nextMean_const (realScale R
            (B + θ * ((Fintype.card κ : ℝ) * J) + θ * F x - θ * Real.log R ^ 2)) x]
        apply N.nextMean_mono_on_support
        intro y hy
        apply (hW l hl y).trans
        apply realScale_mono hR.le
        have hh := face_jump_upper l.1 (hSlope l (List.mem_toFinset.mp hl)) l.2 R (hJ hy)
        change Fval l y ≤ Fval l x + (Fintype.card κ : ℝ) * J at hh
        nlinarith [mul_le_mul_of_nonneg_left hh hθ.le, mul_le_mul_of_nonneg_left hnot.le hθ.le]
      let half := ENNReal.ofReal (1 / 2 : ℝ)
      have hLeak' : (∑ l ∈ S, loss l) ≤ half * realScale R (-B + θ * F x) := by
        refine (Finset.sum_le_sum (fun l hl => hb l hl)).trans ((hSize _).trans ?_)
        rw [show B + θ * ((Fintype.card κ : ℝ) * J) + θ * F x - θ * Real.log R ^ 2 + 1 =
            (B + θ * ((Fintype.card κ : ℝ) * J) + 1 - θ * Real.log R ^ 2) + θ * F x by ring,
          realScale_add hR0 (B + θ * ((Fintype.card κ : ℝ) * J) + 1 - θ * Real.log R ^ 2),
          realScale_add hR0 (-B), ← mul_assoc half]
        apply mul_le_mul_right'
        dsimp only [realScale, half]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact ENNReal.ofReal_le_ofReal hLeak
      have hDebit : realScale R (-B + θ * F x) ≤ ∑ l ∈ S, debit l := by
        refine le_trans ?_ (Finset.single_le_sum (f := debit) (fun _ _ => zero_le _) ha)
        dsimp only [debit, coeff]
        rw [if_pos haDom, ← realScale_add hR0]
        apply realScale_mono hR.le
        have hp := ((N.peaks wr a.1).bounds x haDom.1).1
        change -N.maxComplexHeight a.1 ≤ N.psi wr a.1 x at hp
        rw [haF]
        dsimp [level]
        nlinarith [hShift a x, (hB a ha).2, mul_le_mul_of_nonneg_left hp hθ.le]
      have hPrice : realScale R (-K + θ * F x) ≤ half * realScale R (-B + θ * F x) := by
        rw [show -K + θ * F x = -1 + (-B + θ * F x) by dsimp [K]; ring, realScale_add hR0]
        apply mul_le_mul_right'
        rw [realScale, Real.rpow_neg_one]
        apply ENNReal.ofReal_le_ofReal
        simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hR2
      have hSum := Finset.sum_congr (s₁ := S) rfl (fun l _ => heq l)
      simp only [Finset.sum_add_distrib, ← N.nextMean_sum] at hSum
      have hPay : realScale R (-K + θ * F x) + ∑ l ∈ S, loss l ≤ ∑ l ∈ S, debit l := by
        refine (add_le_add hPrice hLeak').trans ?_
        have hh : half + half = 1 := by dsimp only [half]; rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
        rw [← add_mul, hh, one_mul]
        exact hDebit
      have hfin : (∑ l ∈ S, loss l) ≠ ⊤ := ne_top_of_le_ne_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne hLeak'
      apply ENNReal.le_of_add_le_add_right hfin
      rw [add_right_comm _ (N.nextMean V x), ← hSum]
      exact add_le_add_right hPay _
    · rw [haF]
      apply log_factorial_le_face a.1 a.2 hR he.le x (fun i => (haDom.2.2 i).le.trans (hEe a.1))
      have h := (abs_le.mp (hOff a (List.mem_toFinset.mp ha))).1
      have h' := mul_le_mul_of_nonneg_right (min_le_left ε (1 / 16)) hR0.le
      linarith

end AIM272.Network
