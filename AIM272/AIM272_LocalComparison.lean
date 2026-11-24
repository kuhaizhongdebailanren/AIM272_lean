import AIM272_LocalBarrier

set_option warningAsError true

/-! # Polynomial comparison of the local mass-action potential -/

noncomputable section
open AIM272 RankedRace Filter
open scoped NNReal ENNReal BigOperators Topology

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

private def rankSet (wr : N.WeaklyReversible) (a : κ → ℝ) : Finset ℝ :=
  insert 0 (N.relativeOrders_finite wr a).toFinset

private theorem nonpositive_sum {M : Type*} [AddCommMonoid M] (wr : N.WeaklyReversible)
    (a : κ → ℝ) (f : ℝ → M) :
    ((N.nonpositiveRanks wr a).map f).sum = ∑ d ∈ (N.rankSet wr a).filter (· ≤ 0), f d := by
  classical
  have he : (N.nonpositiveRanks wr a).toFinset = (N.rankSet wr a).filter (· ≤ 0) := by
    ext d
    simp only [List.mem_toFinset, nonpositiveRanks, rankSet, Finset.mem_sort, Finset.mem_insert, Finset.mem_filter]
    by_cases h : d = 0
    · simp [h]
    · simp [h]
  have hnd : (N.nonpositiveRanks wr a).Nodup := by
    unfold nonpositiveRanks
    exact Finset.sort_nodup _ _
  rw [← he, List.sum_toFinset f hnd]

private theorem select_tolerance (a : κ → ℝ) (ha : ∀ i, 0 ≤ a i)
    {e η : ℝ} (he : 0 < e) (hη : 0 < η) :
    ∃ E : ℝ, 0 < E ∧ E ≤ e ∧ (N.maxSourceDegree : ℝ) * E ≤ η ∧
      ∀ i, a i ≠ 0 → E < a i := by
  classical
  let S := insert 1 (Finset.univ.image (fun i : κ => if a i = 0 then 1 else a i / 2))
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let t := S.min' hS
  have ht : 0 < t := by
    dsimp [t]
    rcases Finset.mem_insert.mp (S.min'_mem hS) with hz | hz
    · rw [hz]
      exact zero_lt_one
    · obtain ⟨i, _, hr⟩ := Finset.mem_image.mp hz
      rw [← hr]
      split_ifs with hai
      · norm_num
      · exact div_pos ((ha i).lt_of_ne' hai) (by norm_num)
  let p := (N.maxSourceDegree : ℝ)
  let E := min t (min e (η / (p + 1)))
  have hp : 0 ≤ p := Nat.cast_nonneg _
  refine ⟨E, lt_min ht (lt_min he (div_pos hη (by linarith))), (min_le_right _ _).trans (min_le_left _ _),
    ?_, fun i hi => ?_⟩
  · have hE' : E ≤ η / (p + 1) := (min_le_right t _).trans (min_le_right e _)
    have hB := mul_le_mul_of_nonneg_left hE' hp
    apply hB.trans
    rw [← mul_div_assoc, div_le_iff₀ (show 0 < p + 1 by linarith)]
    nlinarith
  · have hM : t ≤ a i / 2 := S.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, if_neg hi⟩))
    exact lt_of_le_of_lt ((min_le_left t _).trans hM) (by linarith [(ha i).lt_of_ne' hi])

private theorem scaledRate_total_bound (wr : N.WeaklyReversible) (a : κ → ℝ)
    {R E : ℝ} (hR : 1 < R) {x : State κ} (hx : x ∈ N.localDomain a R E) :
    ((∑ r, N.scaledLabelRate wr a R x r : ℝ≥0) : ℝ) ≤
      (∑ r, (N.rateConstant r : ℝ)) * R ^ ((N.maxSourceDegree : ℝ) + (N.peaks wr a).cap) := by
  have hR0 := zero_lt_one.trans hR
  have hq := NNReal.coe_le_coe.mpr (N.totalRate_le_polynomial x)
  push_cast at hq
  have hψ := ((N.peaks wr a).bounds x hx.1).2
  have hrad : (radius x : ℝ) + 1 ≤ R := by linarith [hx.2.1]
  rw [N.scaledRate_factor, NNReal.coe_mul, Real.coe_toNNReal _ (Real.rpow_nonneg hR0.le _)]
  calc
    _ ≤ R ^ (N.peaks wr a).cap * ((∑ r, (N.rateConstant r : ℝ)) * R ^ N.maxSourceDegree) :=
      mul_le_mul (Real.rpow_le_rpow_of_exponent_le hR.le hψ) (hq.trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrad _) (by positivity)))
        (by positivity) (Real.rpow_nonneg hR0.le _)
    _ = _ := by rw [← Real.rpow_natCast R, Real.rpow_add hR0]; ring

/-- G8. For every prescribed tolerance ceiling and θ in (0,1), the
local potential has a uniform polynomial multiplier over its directional
weight. The proof uses a survival probability as level-wise correction. -/
theorem localPotential_eventually_upper (wr : N.WeaklyReversible) (a : κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) {θ e : ℝ} (hθ : 0 < θ) (hθ' : θ < 1) (he : 0 < e) :
    ∃ E C : ℝ, 0 < E ∧ E ≤ e ∧ 0 ≤ C ∧ ∀ᶠ R : ℝ in atTop, ∀ x ∈ N.localDomain a R E,
      N.localPotential wr a R E θ x ≤ realScale R (C + θ * weight a x) := by
  classical
  obtain ⟨b, K, c, hK, hc, hc', hthin, hsample⟩ := N.actual_sampling_lower wr a (N.lowerTarget wr a)
  obtain ⟨g, hg, hgap⟩ := N.level_drop_gap wr a
  let D := N.rankSet wr a
  let Dp := D.filter (fun d => ¬ d ≤ 0)
  have hp : ∀ d ∈ Dp, 0 < d := fun d hd => lt_of_not_ge (Finset.mem_filter.mp hd).2
  obtain ⟨η, hη, hsmall⟩ := AIM272Analytic.weight_ratio_eventually_le_half
    hg hθ hθ' (show 0 ≤ (2 * (b : ℝ)) by positivity) Dp hp
    (C := 4 / c ^ b)
  obtain ⟨E, hE, hEe, hdev, hpos⟩ := N.select_tolerance a ha he hη
  let P := (N.peaks wr a).cap
  let p := (N.maxSourceDegree : ℝ)
  let f := (1 - 2 * (b : ℝ)) * η
  let U := (∑ r, (N.rateConstant r : ℝ))
  let B := K * c ^ b / 2
  have hB : 0 < B := by dsimp [B]; positivity
  let exponent := 1 + p + P - f
  let C := max 0 (exponent + 1 + θ * P)
  refine ⟨E, C, hE, hEe, le_max_left _ _, ?_⟩
  filter_upwards [hsmall, hsample η hη.le, N.local_lower_target_eventually wr a hpos,
    eventually_gt_atTop (2 : ℝ), eventually_ge_atTop (U / B)]
    with R hsmall hsample hwit hR2 hRlarge x hx
  have hR : 1 < R := by linarith
  have hR0 := zero_lt_one.trans hR
  have hR' : (2 : ℝ≥0∞) ≤ realScale R 1 := by
    simpa only [realScale, Real.rpow_one, ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal hR2.le
  let dclock := orderClockRate K R η
  let num : ℝ≥0 := (c * R ^ (-2 * η)).toNNReal ^ b
  let ν := dclock 0
  let β := ENNReal.ofReal (B * R ^ f)
  have hβ : 0 ≤ B * R ^ f := mul_nonneg hB.le (Real.rpow_nonneg hR0.le _)
  have hν : 0 < ν := orderClockRate_pos hK hR0
  have hnum : (num : ℝ≥0∞) = ENNReal.ofReal (c ^ b * R ^ ((-2 * (b : ℝ)) * η)) := by
    have hn : 0 ≤ c * R ^ (-2 * η) := mul_nonneg hc.le (Real.rpow_nonneg hR0.le _)
    change ENNReal.ofReal (c * R ^ (-2 * η)) ^ b = _
    rw [← ENNReal.ofReal_pow hn, mul_pow, ← Real.rpow_natCast (R ^ (-2 * η)),
        ← Real.rpow_mul hR0.le]
    congr 2
    ring
  have hβ2 : β + β = (ν : ℝ≥0∞) * (num : ℝ≥0∞) := by
    rw [hnum, show (ν : ℝ≥0∞) = ENNReal.ofReal (K * R ^ η) by
      dsimp [ν, dclock, orderClockRate]; simp only [neg_zero, zero_add]; rfl,
      ← ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg hR0.le _)), ← ENNReal.ofReal_add hβ hβ]
    congr 1
    calc
      _ = (K * c ^ b) * R ^ f := by dsimp [B]; ring
      _ = _ := by
        have hf : f = η + -2 * (b : ℝ) * η := by dsimp [f]; ring
        rw [hf, Real.rpow_add hR0]; ring
  have hdrop (z : State κ) (_ : z ∈ N.localDomain a R E) (r : L) (hr : N.s r ≤ z)
      (hd : N.level wr a (N.jump z r) < N.level wr a z) :
      2 * realScale R (θ * N.level wr a (N.jump z r)) ≤ realScale R (θ * N.level wr a z) := by
    have hs : R ^ (-(θ * g)) ≤ 1 / 2 :=
      le_trans (le_add_of_nonneg_right (Finset.sum_nonneg fun d _ => by positivity)) hsmall
    have h2 : (2 : ℝ≥0∞) * realScale R (-(θ * g)) ≤ 1 := by
      change (2 : ℝ≥0∞) * ENNReal.ofReal _ ≤ 1
      rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_one.mpr (by linarith)
    have hh := hgap z r hr hd
    calc
      _ ≤ 2 * realScale R (-(θ * g) + θ * N.level wr a z) := by
        apply mul_le_mul_left'
        exact realScale_mono hR.le (by nlinarith)
      _ ≤ _ := by rw [realScale_add hR0, ← mul_assoc]; simpa only [one_mul] using mul_le_mul_right' h2 _
  have hcap (z : State κ) (hz : z ∈ N.localDomain a R E) (d : ℝ) (_ : d ∈ D) :
      (∑ r, N.markWeight wr a R (dclock d) d z r) ≤ 1 :=
    (hthin wr a hR hE.le hdev z hz d).1.trans (by norm_num)
  have hq (z : State κ) (hz : z ∈ N.localDomain a R E) : N.totalRate z ≠ 0 := by
    obtain ⟨y, hy, path⟩ := hwit z hz
    cases path with
    | nil => exact (lt_irrefl _ hy).elim
    | cons hp _ =>
      obtain ⟨_, _, r, _, _, hr, _, _⟩ := hp
      exact (((N.rate_pos_iff z r).mpr hr).trans_le (N.rate_le_totalRate z r)).ne'
  have hrate (z : State κ) (hz : z ∈ N.localDomain a R E) :
      ((∑ r, N.scaledLabelRate wr a R z r : ℝ≥0) : ℝ≥0∞) ≤ realScale R exponent * β := by
    rw [show β = ENNReal.ofReal (B * R ^ f) from rfl, realScale,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hR0.le _), ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ((N.scaledRate_total_bound wr a hR hz).trans ?_)
    change U * R ^ (p + P) ≤ R ^ exponent * (B * R ^ f)
    rw [mul_left_comm, ← Real.rpow_add hR0, show exponent + f = 1 + (p + P) by dsimp [exponent]; ring,
      Real.rpow_add hR0 1 (p + P), Real.rpow_one, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hB).mp hRlarge |>.trans_eq (mul_comm _ _))
      (Real.rpow_nonneg hR0.le _)
  let T (k : ℝ) := observedSurvival dclock (fun d => N.rankMark wr a R E η K k d)
    (N.nonpositiveRanks wr a) ν (N.levelDead wr a R E k)
  have hstop (z : State κ) (hz : z ∈ N.localDomain a R E) :
      β + β + ∑ d ∈ D.filter (· ≤ 0), (dclock d : ℝ≥0∞) *
        mean (N.rankMark wr a R E η K (N.level wr a z) d z) (T (N.level wr a z)) ≤
        (∑ d ∈ D.filter (· ≤ 0), (dclock d : ℝ≥0∞)) * T (N.level wr a z) z := by
    let k := N.level wr a z
    let m d := N.rankMark wr a R E η K k d
    let dead := N.levelDead wr a R E k
    let μ := observe dclock m (N.nonpositiveRanks wr a) ν z
    have hprob : num ≤ prob μ dead := by
      have hs := hsample E hE.le hdev k ν hν le_rfl z (Or.inr (hwit z hz))
      exact hs.trans (prob_mono _ fun y h => h.elim id (fun h => Or.inr h.ne))
    have hlive : ¬ dead z := fun h => h.elim (fun e => e hz) (fun e => e rfl)
    have hh := observedSurvival_drift dclock m (N.nonpositiveRanks wr a) hν dead hlive hprob
    dsimp only at hh
    simp only [← hβ2, N.nonpositive_sum, ENNReal.coe_finset_sum] at hh
    exact hh
  have hslow : (∑ d ∈ Dp, (dclock d : ℝ≥0∞) * (2 * realScale R (θ * d))) ≤ β := by
    let v (d : ℝ) := 2 * K * R ^ (-d + η + θ * d)
    have hv (d : ℝ) : 0 ≤ v d := by dsimp [v]; positivity
    have hterm (d : ℝ) : (dclock d : ℝ≥0∞) * (2 * realScale R (θ * d)) = ENNReal.ofReal (v d) := by
      dsimp [dclock, orderClockRate, realScale, v]
      rw [← ENNReal.ofReal_ofNat (n := 2)]
      change ENNReal.ofReal (K * R ^ (-d + η)) * (ENNReal.ofReal 2 * ENNReal.ofReal (R ^ (θ * d))) = _
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (mul_nonneg hK.le (Real.rpow_nonneg hR0.le _)),
        Real.rpow_add hR0 (-d + η) (θ * d)]
      congr 1
      ring
    simp only [hterm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun d _ => hv d)]
    apply ENNReal.ofReal_le_ofReal
    have hsum : ∑ d ∈ Dp, (4 / c ^ b) * R ^ (-(1 - θ) * d + (2 * (b : ℝ) + 1) * η) ≤ 1 := by
      apply le_trans _ (by norm_num : (1 : ℝ) / 2 ≤ 1)
      exact (le_add_of_nonneg_left (Real.rpow_nonneg hR0.le _)).trans hsmall
    calc
      _ ≤ (B * R ^ f) * ∑ d ∈ Dp, (4 / c ^ b) * R ^ (-(1 - θ) * d + (2 * (b : ℝ) + 1) * η) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d _
        have hcoeff : B * (4 / c ^ b) = 2 * K := by
          dsimp [B]
          field_simp [(pow_pos hc b).ne']
          ring
        have hexp : -d + η + θ * d ≤ f + (-(1 - θ) * d + (2 * (b : ℝ) + 1) * η) := by
          dsimp [f]
          nlinarith
        calc
          _ ≤ (2 * K) * R ^ (f + (-(1 - θ) * d + (2 * (b : ℝ) + 1) * η)) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR.le hexp) (by positivity)
          _ = _ := by rw [Real.rpow_add hR0, ← hcoeff]; ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsum hβ
  have hU := N.localPotential_le_of_clock_drift wr a R E η K θ hR hK hθ.le D
    (fun z r => Finset.mem_insert_of_mem ((N.relativeOrders_finite wr a).mem_toFinset.mpr ⟨(z, r), rfl⟩))
    β (realScale R exponent) T (fun k z => observedSurvival_le_one _ _ _ _ _ _) hcap hq hrate hdrop hstop hslow x hx
  have hψ := ((N.peaks wr a).bounds x hx.1).2
  have hPower : exponent + 1 + θ * N.level wr a x ≤ C + θ * weight a x := by
    have hy : exponent + 1 + θ * P ≤ C := le_max_right _ _
    change N.psi wr a x ≤ P at hψ
    unfold level
    nlinarith [mul_le_mul_of_nonneg_left hψ hθ.le]
  calc
    _ ≤ realScale R exponent * (2 * realScale R (θ * N.level wr a x)) := hU
    _ ≤ realScale R exponent * (realScale R 1 * realScale R (θ * N.level wr a x)) := by gcongr
    _ = realScale R (exponent + 1 + θ * N.level wr a x) := by rw [realScale_add hR0, realScale_add hR0, mul_assoc]
    _ ≤ _ := realScale_mono hR.le hPower

end AIM272.Network
