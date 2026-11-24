import AIM272_Thinning
import AIM272_ClockResolvent
import AIM272_Budgets

set_option warningAsError true

/-! # Exact relation between clock means and the mass-action jump kernel -/

noncomputable section
open AIM272.RankedRace
open scoped NNReal ENNReal BigOperators

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

theorem scaledRate_factor (wr : N.WeaklyReversible) (a : κ → ℝ) (R : ℝ) (x : State κ) :
    (∑ r, N.scaledLabelRate wr a R x r) = (R ^ N.psi wr a x).toNNReal * N.totalRate x := by
  simp only [scaledLabelRate, totalRate, Finset.mul_sum]

private theorem clock_mul_markWeight (wr : N.WeaklyReversible) (a : κ → ℝ) (R : ℝ)
    {v : ℝ≥0} (hv : 0 < v) (d : ℝ) (x : State κ) (r : L) :
    v * N.markWeight wr a R v d x r =
      if N.relativeOrder wr a x r = d then N.scaledLabelRate wr a R x r else 0 := by
  classical
  by_cases hd : N.relativeOrder wr a x r = d
  · by_cases hr : N.s r ≤ x
    · have h : N.s r ≤ x ∧ N.relativeOrder wr a x r = d := ⟨hr, hd⟩
      simp only [markWeight, if_pos hd, if_pos h]
      rw [mul_comm, div_mul_cancel₀ _ hv.ne']
    · have hz : N.rate x r = 0 := le_antisymm (le_of_not_gt (fun hp => hr ((N.rate_pos_iff x r).mp hp))) (zero_le _)
      simp [markWeight, hr, hd, scaledLabelRate, hz]
  · simp [markWeight, hd]

private theorem mean_markDistribution (p : L → ℝ≥0) (hp : ∑ r, p r ≤ 1)
    (a : ℝ≥0∞) (b : L → ℝ≥0∞) :
    mean (markDistribution p hp) (fun i => i.elim a b) =
      ((1 - ∑ r, p r : ℝ≥0) : ℝ≥0∞) * a + ∑ r, (p r : ℝ≥0∞) * b r := by
  classical
  rw [mean, tsum_fintype, Fintype.sum_option]
  simp only [markDistribution_apply, Option.elim_none, Option.elim_some]

theorem nextMean_label_sum (x : State κ) (hq : N.totalRate x ≠ 0) (f : State κ → ℝ≥0∞) :
    N.nextMean f x = ∑ r, (N.jumpProbability x r : ℝ≥0∞) * f (N.jump x r) := by
  classical
  simp only [nextMean, transition, if_neg hq, Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro r _
  rw [tsum_eq_single (N.jump x r)]
  · simp
  · intro y hy
    simp [Ne.symm hy]

private theorem sum_matching_order (wr : N.WeaklyReversible) (a : κ → ℝ) (x : State κ)
    (ds : Finset ℝ) (hds : ∀ r, N.relativeOrder wr a x r ∈ ds) (f : L → ℝ≥0∞) :
    (∑ d ∈ ds, ∑ r : L, if N.relativeOrder wr a x r = d then f r else 0) = ∑ r, f r := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_eq_single_of_mem (N.relativeOrder wr a x r) (hds r)]
  · simp
  · intro j _ h
    simp [Ne.symm h]

/-- The null rings cancel in the summed generator, leaving exactly the
jump kernel multiplied by the total time-changed rate. -/
theorem clockMean_balance (wr : N.WeaklyReversible) (a : κ → ℝ) (R E η K : ℝ)
    (hR : 0 < R) (hK : 0 < K) (x : State κ) (hx : x ∈ N.localDomain a R E)
    (hq : N.totalRate x ≠ 0) (ds : Finset ℝ) (hds : ∀ r, N.relativeOrder wr a x r ∈ ds)
    (hcap : ∀ d ∈ ds, ∑ r, N.markWeight wr a R (orderClockRate K R η d) d x r ≤ 1)
    (f : State κ → ℝ≥0∞) :
    let c := orderClockRate K R η
    let m d := N.rankMark wr a R E η K (N.level wr a x) d x
    let q := ((∑ r, N.scaledLabelRate wr a R x r : ℝ≥0) : ℝ≥0∞)
    (∑ d ∈ ds, (c d : ℝ≥0∞) * mean (m d) f) + q * f x =
      (∑ d ∈ ds, (c d : ℝ≥0∞)) * f x + q * N.nextMean f x := by
  classical
  let c := orderClockRate K R η
  let m d := N.rankMark wr a R E η K (N.level wr a x) d x
  let v (r : L) : ℝ≥0∞ := (N.scaledLabelRate wr a R x r : ℝ≥0∞)
  let v' (d : ℝ) (r : L) : ℝ≥0∞ := if N.relativeOrder wr a x r = d then v r else 0
  let q : ℝ≥0∞ := ((∑ r, N.scaledLabelRate wr a R x r : ℝ≥0) : ℝ≥0∞)
  have hterm (d : ℝ) (hd : d ∈ ds) :
      (c d : ℝ≥0∞) * mean (m d) f + (∑ r, v' d r) * f x =
        (c d : ℝ≥0∞) * f x + ∑ r, v' d r * f (N.jump x r) := by
    let p := N.markWeight wr a R (c d) d x
    have hp : (∑ r, p r) ≤ 1 := hcap d hd
    have hm : m d = (markDistribution p hp).map (fun i => i.elim x (N.jump x)) := by
      have hcond : x ∈ N.localDomain a R E ∧ N.level wr a x = N.level wr a x ∧
          ∑ r, N.markWeight wr a R (orderClockRate K R η d) d x r ≤ 1 := ⟨hx, rfl, hp⟩
      unfold m rankMark
      dsimp only
      rw [dif_pos hcond]
    have hcoef (r : L) : (c d : ℝ≥0∞) * (p r : ℝ≥0∞) = v' d r := by
      rw [← ENNReal.coe_mul, N.clock_mul_markWeight wr a R (orderClockRate_pos hK hR)]
      by_cases h : N.relativeOrder wr a x r = d <;> simp [v', v, h]
    have hsum : (c d : ℝ≥0∞) * ((∑ r, p r : ℝ≥0) : ℝ≥0∞) = ∑ r, v' d r := by
      rw [ENNReal.coe_finset_sum, Finset.mul_sum]
      simp only [hcoef]
    have hnull :
        (c d : ℝ≥0∞) * ((1 - ∑ r, p r : ℝ≥0) : ℝ≥0∞) + (∑ r, v' d r) =
          (c d : ℝ≥0∞) := by
      rw [← hsum, ← mul_add, ← ENNReal.coe_add, tsub_add_cancel_of_le hp, ENNReal.coe_one, mul_one]
    have hmap : (fun i : Option L => f (i.elim x (N.jump x))) =
        (fun i => i.elim (f x) (fun r => f (N.jump x r))) :=
      funext fun i => by cases i <;> rfl
    rw [hm, mean_map, hmap, mean_markDistribution, mul_add, Finset.mul_sum]
    simp only [← mul_assoc, hcoef]
    calc
      _ = ((c d : ℝ≥0∞) * ((1 - ∑ r, p r : ℝ≥0) : ℝ≥0∞) + (∑ r, v' d r)) * f x +
          ∑ r, v' d r * f (N.jump x r) := by
            rw [add_mul, add_assoc, add_comm (∑ r, v' d r * f (N.jump x r)),
              ← add_assoc]
      _ = _ := by rw [hnull]
  have hs := Finset.sum_congr (s₁ := ds) rfl (fun d hd => hterm d hd)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul] at hs
  have hpay (d : ℝ) : (∑ r, v' d r * f (N.jump x r)) =
      ∑ r, if N.relativeOrder wr a x r = d then v r * f (N.jump x r) else 0 := by
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : N.relativeOrder wr a x r = d <;> simp [v', h]
  simp_rw [hpay, v', N.sum_matching_order wr a x ds hds] at hs
  have hQ : q = ∑ r, v r := ENNReal.coe_finset_sum
  have hP : q * N.nextMean f x = ∑ r, v r * f (N.jump x r) := by
    rw [N.nextMean_label_sum x hq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [← mul_assoc]
    congr 1
    rw [← ENNReal.coe_mul]
    apply congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞))
    dsimp [q, v]
    rw [N.scaledRate_factor, mul_assoc, jumpProbability, mul_comm (N.totalRate x), div_mul_cancel₀ _ hq]
    rfl
  simpa only [← hP, ← hQ] using hs

end AIM272.Network
