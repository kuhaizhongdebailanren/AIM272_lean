import AIM272_Rates
import AIM272_RankedRace
import AIM272_RankPaths
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option warningAsError true

/-! # Thinning the finite set of mass-action labels at a given order -/

noncomputable section

open AIM272 RankedRace
open scoped NNReal ENNReal BigOperators

namespace AIM272.RankedRace

variable {S A : Type}

open Classical in
/-- Assign p to the real marks, and the remaining mass to a null mark. -/
def markDistribution [Fintype A] (p : A → ℝ≥0) (hp : ∑ r, p r ≤ 1) : PMF (Option A) :=
  PMF.ofFintype (fun i => ((i.elim (1 - ∑ r, p r) p : ℝ≥0) : ℝ≥0∞)) (by
    rw [← ENNReal.coe_finset_sum, Fintype.sum_option]
    exact_mod_cast (tsub_add_cancel_of_le hp))

theorem markDistribution_apply [Fintype A] (p : A → ℝ≥0) (hp : ∑ r, p r ≤ 1) (i : Option A) :
    markDistribution p hp i = ((i.elim (1 - ∑ r, p r) p : ℝ≥0) : ℝ≥0∞) :=
  rfl

theorem le_prob_of_map_point (μ : PMF A) (g : A → S) (i : A) {P : S → Prop} (hi : P (g i)) :
    (μ i).toNNReal ≤ prob (μ.map g) P := by
  apply ENNReal.coe_le_coe.mp
  rw [coe_prob, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.one_ne_top (μ.coe_le_one i)),
    PMF.toOuterMeasure_apply]
  apply le_trans _ (ENNReal.le_tsum (g i))
  rw [Set.indicator_of_mem (show g i ∈ {x | P x} from hi), PMF.map_apply]
  classical
  exact (by simp : μ i ≤ if g i = g i then μ i else 0).trans (ENNReal.le_tsum i)

end AIM272.RankedRace

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

def scaledLabelRate (wr : N.WeaklyReversible) (a : κ → ℝ) (R : ℝ) (x : State κ) (r : L) : ℝ≥0 :=
  (R ^ N.psi wr a x).toNNReal * N.rate x r

def orderClockRate (K R η d : ℝ) : ℝ≥0 := (K * R ^ (-d + η)).toNNReal

theorem orderClockRate_pos {K R η d : ℝ} (hK : 0 < K) (hR : 0 < R) :
    0 < orderClockRate K R η d :=
  Real.toNNReal_pos.mpr (mul_pos hK (Real.rpow_pos_of_pos hR _))

open Classical in
def markWeight (wr : N.WeaklyReversible) (a : κ → ℝ) (R : ℝ) (clock : ℝ≥0) (d : ℝ)
    (x : State κ) (r : L) : ℝ≥0 :=
  if N.s r ≤ x ∧ N.relativeOrder wr a x r = d then N.scaledLabelRate wr a R x r / clock else 0

/-- The two uniform thinning inequalities for the common constants K and c. -/
def ThinnedRateBounds (K c : ℝ) : Prop :=
  ∀ (wr : N.WeaklyReversible) (a : κ → ℝ) {R E η : ℝ},
      1 < R → 0 ≤ E → (N.maxSourceDegree : ℝ) * E ≤ η →
      ∀ x ∈ N.localDomain a R E, ∀ d : ℝ,
        (∑ r, N.markWeight wr a R (orderClockRate K R η d) d x r) ≤ 1 / 2 ∧
        ∀ r, N.s r ≤ x → N.relativeOrder wr a x r = d →
          (c * R ^ (-2 * η)).toNNReal ≤ N.markWeight wr a R (orderClockRate K R η d) d x r

/-- The thinning constants are independent of the direction, level and scale. -/
theorem thinned_rate_bounds :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ c ≤ 1 / 2 ∧ N.ThinnedRateBounds K c := by
  classical
  obtain ⟨lo, hi, hlo, hhi, hbounds⟩ := N.timeChanged_label_bounds
  let K : ℝ := 2 * ((Fintype.card L : ℝ) + 1) * hi
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, min (1 / 2) (lo / K), hK, lt_min (by norm_num) (div_pos hlo hK),
    min_le_left _ _, fun wr a R E η hR hE hη x hx d => ?_⟩
  have hR0 := zero_lt_one.trans hR
  let q := orderClockRate K R η d
  let p := N.markWeight wr a R q d x
  have hq := orderClockRate_pos (η := η) (d := d) hK hR0
  have hq' : (q : ℝ) = K * R ^ (-d + η) :=
    Real.coe_toNNReal _ (mul_nonneg hK.le (Real.rpow_nonneg hR0.le _))
  have hscale (r : L) : (N.scaledLabelRate wr a R x r : ℝ) = R ^ N.psi wr a x * (N.rate x r : ℝ) := by
    simp [scaledLabelRate, Real.coe_toNNReal _ (Real.rpow_nonneg hR0.le _)]
  have hupper (r : L) : (p r : ℝ) ≤ hi / K := by
    by_cases hr : N.s r ≤ x ∧ N.relativeOrder wr a x r = d
    · obtain ⟨_, hb⟩ := hbounds wr a hR hE hη hx r hr.1
      rw [hr.2] at hb
      simp only [p, markWeight, if_pos hr, NNReal.coe_div, hq', hscale]
      rw [div_le_div_iff₀ (mul_pos hK (Real.rpow_pos_of_pos hR0 _)) hK]
      calc
        _ ≤ (hi * R ^ (-d + η)) * K := mul_le_mul_of_nonneg_right hb hK.le
        _ = _ := by ring
    · simp [p, markWeight, hr, div_nonneg hhi.le hK.le]
  constructor
  · change ∑ r, p r ≤ _
    apply NNReal.coe_le_coe.mp
    push_cast
    calc
      ∑ r, (p r : ℝ) ≤ ∑ _ : L, hi / K := Finset.sum_le_sum fun r _ => hupper r
      _ = (Fintype.card L : ℝ) * (hi / K) := by simp
      _ ≤ (1 : ℝ) / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ hK (by norm_num : (0 : ℝ) < 2)]
        dsimp [K]
        nlinarith
  · intro r hr hd
    change _ ≤ p r
    apply NNReal.coe_le_coe.mp
    have en : 0 ≤ min (1 / 2) (lo / K) * R ^ (-2 * η) :=
      mul_nonneg (le_min (by norm_num) (div_nonneg hlo.le hK.le)) (Real.rpow_nonneg hR0.le _)
    have hrd : N.s r ≤ x ∧ N.relativeOrder wr a x r = d := ⟨hr, hd⟩
    simp only [p, markWeight, if_pos hrd, NNReal.coe_div, hq', hscale, Real.coe_toNNReal _ en]
    apply (le_div_iff₀ (mul_pos hK (Real.rpow_pos_of_pos hR0 _))).mpr
    have hb := (hbounds wr a hR hE hη hx r hr).1
    rw [hd] at hb
    calc
      _ ≤ (lo / K * R ^ (-2 * η)) * (K * R ^ (-d + η)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _)
          (Real.rpow_nonneg hR0.le _)) (mul_nonneg hK.le (Real.rpow_nonneg hR0.le _))
      _ = lo * R ^ (-d - η) := by
        calc
          _ = lo * (R ^ (-2 * η) * R ^ (-d + η)) := by field_simp
          _ = _ := by rw [← Real.rpow_add hR0]; congr 2; ring
      _ ≤ _ := hb

open Classical in
/-- Thinned order-d mark stopped outside the local domain and the chosen level. -/
def rankMark (wr : N.WeaklyReversible) (a : κ → ℝ) (R E η K k d : ℝ)
    (x : State κ) : PMF (State κ) :=
  let p := N.markWeight wr a R (orderClockRate K R η d) d x
  if h : x ∈ N.localDomain a R E ∧ N.level wr a x = k ∧ ∑ r, p r ≤ 1 then
    (markDistribution p h.2.2).map (fun r => r.elim x (N.jump x))
  else PMF.pure x

def levelDead (wr : N.WeaklyReversible) (a : κ → ℝ) (R E k : ℝ) (x : State κ) : Prop :=
  x ∉ N.localDomain a R E ∨ N.level wr a x ≠ k

theorem rankMark_stuck {wr : N.WeaklyReversible} {a : κ → ℝ} {R E η K k d : ℝ} {x : State κ}
    (hd : N.levelDead wr a R E k x) : N.rankMark wr a R E η K k d x = PMF.pure x := by
  classical
  rcases hd with h | h <;> simp [rankMark, h]

theorem rankMark_support_move (wr : N.WeaklyReversible) (a : κ → ℝ) (R E η K k d : ℝ)
    (x y : State κ) (hs : y ∈ (N.rankMark wr a R E η K k d x).support) :
    x = y ∨ N.rankStep wr a k d x y := by
  classical
  by_cases hf : x ∈ N.localDomain a R E ∧ N.level wr a x = k ∧
      ∑ r, N.markWeight wr a R (orderClockRate K R η d) d x r ≤ 1
  · simp only [rankMark, dif_pos hf] at hs
    obtain ⟨i, hi, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
    cases i with
    | none => exact Or.inl he
    | some r =>
      have hpos := (PMF.mem_support_iff _ _).mp hi
      simp only [markDistribution_apply, Option.elim_some] at hpos
      have hr : N.s r ≤ x ∧ N.relativeOrder wr a x r = d := by
        by_contra h
        exact hpos (by simp [markWeight, if_neg h])
      refine Or.inr ⟨r, hf.1.1, hf.2.1, hr.1, ?_, he.symm⟩
      simpa only [N.relativeOrder_eq, hf.2.1] using hr.2
  · simp only [rankMark, dif_neg hf] at hs
    exact Or.inl ((PMF.mem_support_pure_iff _ _).mp hs).symm

theorem rankMark_null (wr : N.WeaklyReversible) (a : κ → ℝ) (R E η K k d : ℝ)
    (x : State κ)
    (hcap : x ∈ N.localDomain a R E → ∑ r, N.markWeight wr a R (orderClockRate K R η d) d x r ≤ 1 / 2) :
    1 / 2 ≤ prob (N.rankMark wr a R E η K k d x) (fun y => N.levelDead wr a R E k y ∨ y = x) := by
  classical
  let p := N.markWeight wr a R (orderClockRate K R η d) d x
  by_cases hf : x ∈ N.localDomain a R E ∧ N.level wr a x = k ∧
      ∑ r, N.markWeight wr a R (orderClockRate K R η d) d x r ≤ 1
  · simp only [rankMark, dif_pos hf]
    apply le_trans _ (le_prob_of_map_point _ (fun r => r.elim x (N.jump x)) none
      (P := fun y => N.levelDead wr a R E k y ∨ y = x) (Or.inr rfl))
    simp only [markDistribution_apply, Option.elim_none, ENNReal.toNNReal_coe]
    have hh := hcap hf.1
    change ∑ r, p r ≤ 1 / 2 at hh
    rw [le_tsub_iff_right hf.2.2]
    exact (add_le_add_left hh _).trans (by norm_num)
  · simp only [rankMark, dif_neg hf]
    rw [prob_support _ (fun y hy => Or.inr ((PMF.mem_support_pure_iff _ _).mp hy))]
    norm_num

theorem rankMark_label (wr : N.WeaklyReversible) (a : κ → ℝ) (R E η K k d : ℝ)
    {x y : State κ} (he : N.rankStep wr a k d x y)
    {b : ℝ≥0} (hb : b ≤ 1)
    (hcap : x ∈ N.localDomain a R E → ∑ r, N.markWeight wr a R (orderClockRate K R η d) d x r ≤ 1)
    (hfloor : x ∈ N.localDomain a R E → ∀ r, N.s r ≤ x → N.relativeOrder wr a x r = d →
      b ≤ N.markWeight wr a R (orderClockRate K R η d) d x r) :
    b ≤ prob (N.rankMark wr a R E η K k d x) (fun z => N.levelDead wr a R E k z ∨ z = y) := by
  classical
  obtain ⟨r, _, hk, hr, hd, rfl⟩ := he
  by_cases hx : x ∈ N.localDomain a R E
  · have hoe : N.relativeOrder wr a x r = d := by rwa [N.relativeOrder_eq, hk]
    have hf : x ∈ N.localDomain a R E ∧ N.level wr a x = k ∧
        ∑ q, N.markWeight wr a R (orderClockRate K R η d) d x q ≤ 1 := ⟨hx, hk, hcap hx⟩
    simp only [rankMark, dif_pos hf]
    apply le_trans _ (le_prob_of_map_point _ (fun i => i.elim x (N.jump x)) (some r)
      (P := fun z => N.levelDead wr a R E k z ∨ z = N.jump x r) (Or.inr rfl))
    simpa only [markDistribution_apply, Option.elim_some, ENNReal.toNNReal_coe] using hfloor hx r hr hoe
  · rw [N.rankMark_stuck (Or.inl hx),
      prob_support _ (fun z hz => Or.inl (((PMF.mem_support_pure_iff _ _).mp hz).symm ▸ Or.inl hx))]
    exact hb

end AIM272.Network
