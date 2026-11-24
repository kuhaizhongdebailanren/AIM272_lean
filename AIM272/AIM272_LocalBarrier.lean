import AIM272_ActualSampling
import AIM272_ClockStop
import AIM272_ClockBalance

set_option warningAsError true

/-! # Local potential comparison by a generator inequality -/

noncomputable section
open AIM272.RankedRace
open scoped NNReal ENNReal BigOperators

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

def realScale (R e : ℝ) : ℝ≥0∞ := ENNReal.ofReal (R ^ e)

theorem realScale_add {R : ℝ} (hR : 0 < R) (e f : ℝ) :
    realScale R (e + f) = realScale R e * realScale R f := by
  rw [realScale, Real.rpow_add hR, ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
  rfl

theorem realScale_mono {R e f : ℝ} (hR : 1 ≤ R) (h : e ≤ f) :
    realScale R e ≤ realScale R f := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hR h)

@[simp] theorem realScale_zero (R : ℝ) : realScale R 0 = 1 := by simp [realScale]

private theorem nextMean_scale (A : ℝ≥0∞) (f : State κ → ℝ≥0∞) (x : State κ) :
    N.nextMean (fun y => A * f y) x = A * N.nextMean f x := by
  simp only [nextMean, mul_left_comm _ A, ENNReal.tsum_mul_left]

open Classical in
/-- The level-wise correction T pays for the nonpositive evolution.
The loss from positive orders is charged by the uniform order bound.
Summing cancels null rings and proves the jump-kernel drift. -/
theorem localPotential_le_of_clock_drift (wr : N.WeaklyReversible) (a : κ → ℝ)
    (R E η K θ : ℝ) (hR : 1 < R) (hK : 0 < K) (hθ : 0 ≤ θ)
    (D : Finset ℝ) (hD : ∀ x r, N.relativeOrder wr a x r ∈ D)
    (β A : ℝ≥0∞) (T : ℝ → State κ → ℝ≥0∞)
    (hT : ∀ k x, T k x ≤ 1)
    (hcap : ∀ x ∈ N.localDomain a R E, ∀ d ∈ D,
      ∑ r, N.markWeight wr a R (orderClockRate K R η d) d x r ≤ 1)
    (hq : ∀ x ∈ N.localDomain a R E, N.totalRate x ≠ 0)
    (hrate : ∀ x ∈ N.localDomain a R E,
      ((∑ r, N.scaledLabelRate wr a R x r : ℝ≥0) : ℝ≥0∞) ≤ A * β)
    (hdrop : ∀ x ∈ N.localDomain a R E, ∀ r, N.s r ≤ x →
      N.level wr a (N.jump x r) < N.level wr a x →
      2 * realScale R (θ * N.level wr a (N.jump x r)) ≤ realScale R (θ * N.level wr a x))
    (hstop : ∀ x ∈ N.localDomain a R E,
      let k := N.level wr a x
      let c := orderClockRate K R η
      β + β + ∑ d ∈ D.filter (· ≤ 0),
        (c d : ℝ≥0∞) * mean (N.rankMark wr a R E η K k d x) (T k) ≤
        (∑ d ∈ D.filter (· ≤ 0), (c d : ℝ≥0∞)) * T k x)
    (hslow : (∑ d ∈ D.filter (fun d => ¬ d ≤ 0),
      (orderClockRate K R η d : ℝ≥0∞) * (2 * realScale R (θ * d))) ≤ β) :
    ∀ x ∈ N.localDomain a R E, N.localPotential wr a R E θ x ≤
      A * (2 * realScale R (θ * N.level wr a x)) := by
  classical
  let Ω := N.localDomain a R E
  let ℓ := N.level wr a
  let w (x : State κ) := realScale R (θ * ℓ x)
  let V (x : State κ) := if x ∈ Ω then w x * (1 + T (ℓ x) x) else 0
  have R0 := zero_lt_one.trans hR
  have hV (x : State κ) : V x ≤ 2 * w x := by
    by_cases hx : x ∈ Ω
    · rw [show V x = w x * (1 + T (ℓ x) x) from if_pos hx, mul_comm (2 : ℝ≥0∞)]
      exact mul_le_mul_left' ((add_le_add_left (hT _ _) _).trans_eq one_add_one_eq_two) _
    · rw [show V x = 0 from if_neg hx]
      exact zero_le _
  have hf (x : State κ) (hx : x ∈ Ω) : w x + N.nextMean (fun y => A * V y) x ≤ A * V x := by
    let k := ℓ x
    let c := orderClockRate K R η
    let m d := N.rankMark wr a R E η K k d x
    let Dn := D.filter (· ≤ 0)
    let Dp := D.filter (fun d => ¬ d ≤ 0)
    let s (ds : Finset ℝ) := ∑ d ∈ ds, (c d : ℝ≥0∞)
    let h (ds : Finset ℝ) := ∑ d ∈ ds, (c d : ℝ≥0∞) * mean (m d) V
    let q := ((∑ r, N.scaledLabelRate wr a R x r : ℝ≥0) : ℝ≥0∞)
    have hvx : V x = w x * (1 + T k x) := if_pos hx
    have hterm (d : ℝ) (hd : d ≤ 0) :
        mean (m d) V ≤ w x * (1 + mean (m d) (T k)) := by
      have hmean : mean (m d) (fun y => w x + w x * T k y) =
          w x * (1 + mean (m d) (T k)) := by
        rw [mean_add, mean_const, mean_mul, mul_add, mul_one]
      rw [← hmean]
      apply mean_mono
      intro y hy
      have same (he : ℓ y = k) : V y ≤ w x + w x * T k y := by
        by_cases hdom : y ∈ Ω
        · have hw : w y = w x := by simp only [w, he, k]
          rw [show V y = w y * (1 + T (ℓ y) y) from if_pos hdom, hw, he, mul_add, mul_one]
        · exact (show V y = 0 from if_neg hdom).le.trans (zero_le _)
      rcases N.rankMark_support_move wr a R E η K k d x y hy with rfl | he
      · exact same rfl
      obtain ⟨r, hloop, _, hr, hd', rfl⟩ := he
      have hlev : ℓ (N.jump x r) ≤ k :=
        (N.levels_on_step wr a x r hloop hr).1.trans (max_le le_rfl (by linarith [hd, hd']))
      rcases lt_or_eq_of_le hlev with hlt | he
      · exact ((hV _).trans (hdrop x hx r hr hlt)).trans le_self_add
      · exact same he
    have hn : β * w x + β * w x + h Dn ≤ s Dn * V x := by
      have hs : h Dn ≤ (s Dn) * w x +
          w x * (∑ d ∈ Dn, (c d : ℝ≥0∞) * mean (m d) (T k)) := by
        unfold h s
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro d hd
        exact (mul_le_mul_left' (hterm d (Finset.mem_filter.mp hd).2) _).trans_eq (by
          rw [mul_add, mul_one]; ring)
      have hold := mul_le_mul_left' (hstop x hx) (w x)
      calc
        _ ≤ β * w x + β * w x + (s Dn * w x + w x *
            (∑ d ∈ Dn, (c d : ℝ≥0∞) * mean (m d) (T k))) := add_le_add_left hs _
        _ = s Dn * w x + w x * (β + β + ∑ d ∈ Dn, (c d : ℝ≥0∞) * mean (m d) (T k)) := by
          ring
        _ ≤ s Dn * w x + w x * (s Dn * T k x) := add_le_add_left hold _
        _ = _ := by rw [hvx, mul_add, mul_one, mul_add]; ac_rfl
    have hpositive (d : ℝ) (hd : 0 ≤ d) :
        mean (m d) V ≤ w x * (2 * realScale R (θ * d)) := by
      rw [← mean_const (m d) (w x * (2 * realScale R (θ * d)))]
      apply mean_mono
      intro y hy
      have hmax : ℓ y ≤ k + d := by
        rcases N.rankMark_support_move wr a R E η K k d x y hy with rfl | he
        · exact le_add_of_nonneg_right hd
        obtain ⟨r, hloop, _, hr, hd', rfl⟩ := he
        exact (N.levels_on_step wr a x r hloop hr).1.trans (max_le
          (le_add_of_nonneg_right hd) (by linarith))
      have hbound : w y ≤ w x * realScale R (θ * d) := by
        rw [← realScale_add R0]
        apply realScale_mono hR.le
        dsimp [w, k] at *
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left hmax hθ
      exact ((hV y).trans (mul_le_mul_left' hbound _)).trans_eq (by ac_rfl)
    have hp : h Dp ≤ β * w x := by
      calc
        h Dp ≤ (∑ d ∈ Dp, (c d : ℝ≥0∞) * (2 * realScale R (θ * d))) * w x := by
          unfold h
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun d hd => (mul_le_mul_left' (hpositive d
            (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hd).2))) _).trans_eq (by ac_rfl)
        _ ≤ _ := mul_le_mul_right' hslow _
    have hall : β * w x + h D ≤ s D * V x := by
      have hsum : h Dn + h Dp = h D := Finset.sum_filter_add_sum_filter_not D (· ≤ 0) _
      have hsum' : s Dn + s Dp = s D := Finset.sum_filter_add_sum_filter_not D (· ≤ 0) _
      rw [← hsum, ← hsum', add_mul]
      calc
        _ ≤ β * w x + (h Dn + β * w x) := add_le_add_left (add_le_add_left hp _) _
        _ = β * w x + β * w x + h Dn := by ring
        _ ≤ _ := hn.trans le_self_add
    have hbal : h D + q * V x = s D * V x + q * N.nextMean V x :=
      N.clockMean_balance wr a R E η K R0 hK x hx (hq x hx) D (hD x) (hcap x hx) V
    have hsfin : s D * V x ≠ ⊤ := (ENNReal.mul_lt_top
      (ENNReal.sum_lt_top.mpr fun d _ => ENNReal.coe_lt_top)
      ((hV x).trans_lt (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top))).ne
    have hdrift : β * w x + q * N.nextMean V x ≤ q * V x := by
      apply ENNReal.le_of_add_le_add_left hsfin
      calc
        _ = β * w x + (s D * V x + q * N.nextMean V x) := by ring
        _ = β * w x + (h D + q * V x) := by rw [← hbal]
        _ ≤ _ := by rw [← add_assoc]; exact add_le_add_right hall _
    have qpos : q ≠ 0 := by
      dsimp [q]
      rw [N.scaledRate_factor]
      exact_mod_cast (mul_ne_zero (Real.toNNReal_pos.mpr (Real.rpow_pos_of_pos R0 _)).ne' (hq x hx))
    apply (ENNReal.mul_le_mul_left qpos ENNReal.coe_ne_top).mp
    rw [mul_add, N.nextMean_scale]
    calc
      _ ≤ (A * β) * w x + q * (A * N.nextMean V x) :=
        add_le_add_right (mul_le_mul_right' (hrate x hx) _) _
      _ = A * (β * w x + q * N.nextMean V x) := by simp only [mul_add]; ac_rfl
      _ ≤ A * (q * V x) := mul_le_mul_left' hdrift _
      _ = _ := by ac_rfl
  intro x hx
  have hP := N.killedPotential_le_of_drift Ω w (fun y => A * V y) hf x
  exact hP.trans (mul_le_mul_left' (hV x) _)

end AIM272.Network
