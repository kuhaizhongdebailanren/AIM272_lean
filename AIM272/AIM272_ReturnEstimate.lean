import AIM272_Descent
import AIM272_Rates
import AIM272_Budgets

set_option warningAsError true

/-! # Hitting the root before revisiting a point and the Green function bound -/

noncomputable section
open scoped NNReal ENNReal BigOperators
open AIM272Unusable (Step Γ)

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

open Classical in
/-- First hit of o exactly at time n, with x and o as stopping states. -/
def firstHitMass (o x : State κ) : ℕ → State κ → ℝ≥0∞
  | 0, y => if y = o then 1 else 0
  | n + 1, y => if y = o ∨ y = x then 0 else N.nextMean (firstHitMass o x n) y

def hitRootBefore (o x y : State κ) : ℝ≥0∞ := ∑' n, N.firstHitMass o x n y

/-- The first jump from x is made before the two-boundary hitting experiment starts. -/
def escapeToRoot (o x : State κ) : ℝ≥0∞ := N.nextMean (N.hitRootBefore o x) x

theorem hitRootBefore_root (o x : State κ) : N.hitRootBefore o x o = 1 := by
  classical
  rw [hitRootBefore, tsum_eq_single 0]
  · simp [firstHitMass]
  · intro n hn
    cases n with
    | zero => contradiction
    | succ _ => simp [firstHitMass]

theorem hitRootBefore_start {o x : State κ} (hne : x ≠ o) : N.hitRootBefore o x x = 0 := by
  classical
  have hf (n : ℕ) : N.firstHitMass o x n x = 0 := by cases n <;> simp [firstHitMass, hne]
  simp only [hitRootBefore, hf, tsum_zero]

theorem hitRootBefore_harmonic {o x y : State κ} (ho : y ≠ o) (hx : y ≠ x) :
    N.nextMean (N.hitRootBefore o x) y = N.hitRootBefore o x y := by
  classical
  unfold hitRootBefore
  rw [N.nextMean_tsum, tsum_eq_zero_add' (f := fun n => N.firstHitMass o x n y) ENNReal.summable]
  simp only [firstHitMass, if_neg ho, zero_add, not_or_intro ho hx, if_false]

theorem hitRootBefore_le_one (o x y : State κ) : N.hitRootBefore o x y ≤ 1 := by
  classical
  rw [hitRootBefore, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun m => ?_
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    by_cases hs : y = o ∨ y = x
    · simp only [firstHitMass, if_pos hs, Finset.sum_const_zero, zero_add]
      split <;> simp
    · have h₀ : y ≠ o := fun h => hs (.inl h)
      simp only [firstHitMass, if_neg hs, if_neg h₀, add_zero]
      rw [← N.nextMean_sum]
      exact (N.nextMean_mono ih y).trans (N.nextMean_const 1 y).le

private theorem capped_escape {o x : State κ} (hne : x ≠ o) {cap : State κ} {a : ℝ≥0∞}
    (ha : a ≤ 1) (floor : ∀ {y z : State κ}, y ≤ cap → Step N.toRxn y z → a ≤ N.transition y z)
    {n : ℕ} (path : N.CappedPath cap x o n) : a ^ n ≤ N.escapeToRoot o x := by
  let H := N.hitRootBefore o x
  have hfinish {y z : State κ} (hs : Step N.toRxn y z) (hy : y ≤ cap) :
      a * H z ≤ N.nextMean H y :=
    (mul_le_mul_right' (floor hy hs) _).trans (ENNReal.le_tsum z)
  have hstep {y : State κ} (hy : y ≠ x) : N.nextMean H y ≤ H y := by
    by_cases he : y = o
    · subst y
      exact (N.nextMean_mono (N.hitRootBefore_le_one o x) o).trans
        ((N.nextMean_const 1 o).le.trans (N.hitRootBefore_root o x).ge)
    · exact (N.hitRootBefore_harmonic he hy).le
  have hm {y : State κ} {k : ℕ} (hp : N.CappedPath cap x y k) :
      y ≤ cap ∧ a ^ k * H y ≤ N.escapeToRoot o x := by
    induction hp with
    | nil hx => exact ⟨hx, by simp [H, N.hitRootBefore_start hne]⟩
    | @snoc y z n _ hs hz ih =>
      refine ⟨hz, ?_⟩
      rw [pow_succ, mul_assoc]
      by_cases he : y = x
      · subst y
        exact (mul_le_of_le_one_left' (pow_le_one' ha _)).trans (hfinish hs ih.1)
      · exact (mul_le_mul_left' ((hfinish hs ih.1).trans (hstep he)) _).trans ih.2
  have last := (hm path).2
  simpa only [H, N.hitRootBefore_root, mul_one] using last

open Classical in
private theorem escape_budget {o x : State κ} (hne : x ≠ o) :
    let H := N.hitRootBefore o x
    let p := N.escapeToRoot o x
    ∀ y, y ≠ o → (if y = x then p else 0) + N.nextMean (fun z => 1 - H z) y ≤ 1 - H y := by
  let H := N.hitRootBefore o x
  dsimp only
  intro y hy
  have split : N.nextMean H y + N.nextMean (fun z => 1 - H z) y = 1 := by
    rw [← N.nextMean_add]
    have h (z : State κ) : H z + (1 - H z) = 1 := add_tsub_cancel_of_le (N.hitRootBefore_le_one o x z)
    simp only [h]
    exact N.nextMean_const 1 y
  by_cases he : y = x
  · subst y
    simpa only [if_true, H, N.hitRootBefore_start hne, tsub_zero] using split.le
  · simp only [if_neg he, zero_add]
    apply ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top ENNReal.one_ne_top (N.hitRootBefore_le_one o x y))
    rw [← N.hitRootBefore_harmonic hy he]
    exact split.le

open Classical in
/-- One success probability pays for all pre-root visits, including a positive-return excursion. -/
theorem visits_times_escape_le_one {o x : State κ} (hne : x ≠ o) :
    N.occupation o x * N.escapeToRoot o x ≤ 1 ∧
    ∀ y, N.killedPotential {z | z ≠ o} (fun z => if z = x then 1 else 0) y *
      N.escapeToRoot o x ≤ 1 := by
  classical
  let H := N.hitRootBefore o x
  let p := N.escapeToRoot o x
  let f (y : State κ) : ℝ≥0∞ := if y = x then p else 0
  let W (y : State κ) : ℝ≥0∞ := if y = o then 1 else 1 - H y
  have hguard (z : State κ) : (if z = o then 0 else W z) = 1 - H z := by
    by_cases he : z = o <;> simp [W, H, he, hitRootBefore_root]
  have hex := N.excursion_reward_le o f W (by
    intro y
    simp_rw [hguard]
    by_cases he : y = o
    · subst y
      simpa only [f, if_neg hne.symm, zero_add, W, if_true] using
        (N.nextMean_mono (f := fun z => 1 - H z) (g := fun _ => 1) (fun _ => tsub_le_self) o).trans
          (N.nextMean_const 1 o).le
    · simpa only [W, if_neg he] using N.escape_budget hne y he)
  have hsum : (∑' z, N.occupation o z * f z) = N.occupation o x * p := by
    rw [tsum_eq_single x]
    · simp [f]
    · intro z hz
      simp [f, hz]
  refine ⟨by simpa only [hsum, W, if_true] using hex, fun y => ?_⟩
  let Ω : Set (State κ) := {z | z ≠ o}
  let g (z : State κ) : ℝ≥0∞ := if z = x then 1 else 0
  have hmul (n : ℕ) (z : State κ) : N.killedReward Ω f n z = N.killedReward Ω g n z * p := by
    induction n generalizing z with
    | zero =>
      by_cases hΩ : z ∈ Ω <;> by_cases he : z = x <;> simp [killedReward, f, g, hΩ, he]
    | succ n ih =>
      by_cases hΩ : z ∈ Ω
      · simp only [killedReward, if_pos hΩ, ih, ← mul_assoc, ENNReal.tsum_mul_right]
      · simp only [killedReward, if_neg hΩ, zero_mul]
  have hK : N.killedPotential Ω f y = N.killedPotential Ω g y * p := by
    simp only [killedPotential, hmul, ENNReal.tsum_mul_right]
  rw [← hK]
  exact (N.killedPotential_le_of_drift Ω f (fun z => 1 - H z) (fun z hz => N.escape_budget hne z hz) y).trans
    tsub_le_self

private theorem pathCost_exponential (D : ℝ≥0) (C p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
      (((D * (((m + C : ℕ) : ℝ≥0) + 1) ^ p) ^ (C * (1 + m)) : ℝ≥0) : ℝ) ≤
        Real.exp (K * (1 + (m : ℝ)) * Real.log (2 + (m : ℝ))) := by
  obtain ⟨d, hd⟩ := exists_nat_ge (D : ℝ)
  let e := d + (C + 2) * p
  refine ⟨(e * C : ℕ), by positivity, fun m => ?_⟩
  have base (j : ℕ) : j ≤ (m + 2) ^ j :=
    (Nat.le_of_lt (Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left (by omega) _)
  have addCap : m + C + 1 ≤ (m + 2) ^ (C + 2) := by
    calc
      _ ≤ (C + 1) * (m + 2) := by nlinarith
      _ ≤ (m + 2) ^ (C + 1) * (m + 2) := Nat.mul_le_mul_right _ (base _)
      _ = _ := (pow_succ _ _).symm
  have upper : (D : ℝ) * (((m + C : ℕ) : ℝ) + 1) ^ p ≤ ((m + 2 : ℕ) : ℝ) ^ e := by
    have comb : (m + 2) ^ d * ((m + 2) ^ (C + 2)) ^ p = (m + 2) ^ e := by
      rw [← pow_mul, ← pow_add]
    calc
      _ ≤ (((m + 2) ^ d : ℕ) : ℝ) * ((((m + 2) ^ (C + 2) : ℕ) : ℝ) ^ p) :=
        mul_le_mul (hd.trans (by exact_mod_cast base d))
          (pow_le_pow_left₀ (by positivity) (by exact_mod_cast addCap) _) (by positivity) (by positivity)
      _ = _ := by exact_mod_cast comb
  have final := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (D : ℝ) * (((m + C : ℕ) : ℝ) + 1) ^ p) upper (C * (1 + m))
  push_cast at final ⊢
  apply final.trans
  rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (m : ℝ) + 2)]
  apply Real.exp_le_exp.mpr
  push_cast
  rw [add_comm (m : ℝ) 2]
  dsimp [e]
  push_cast
  ring_nf
  exact le_rfl

open Classical in
/-- G11, including the uniform bound for visits from an arbitrary start. -/
theorem pointwise_return_bound (o : State κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Γ N.toRxn o,
      let M := ENNReal.ofReal (Real.exp (K * (1 + (radius x : ℝ)) * Real.log (2 + (radius x : ℝ))))
      N.occupation o x ≤ M ∧ (x ≠ o → M⁻¹ ≤ N.escapeToRoot o x ∧
        ∀ y, N.killedPotential {z | z ≠ o} (fun z => if z = x then 1 else 0) y ≤ M) := by
  obtain ⟨C, hC⟩ := N.coordinatewise_descent o
  obtain ⟨D, hD, hfloor⟩ := N.transition_floor
  obtain ⟨K, hK, hcost⟩ := pathCost_exponential D C N.maxSourceDegree
  refine ⟨K, hK, fun x hx => ?_⟩
  let m := radius x
  let V := Real.exp (K * (1 + (m : ℝ)) * Real.log (2 + (m : ℝ)))
  have hV : 1 ≤ V := Real.one_le_exp (mul_nonneg (mul_nonneg hK (by positivity))
    (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m] : (1 : ℝ) ≤ 2 + (m : ℝ))))
  let M := ENNReal.ofReal V
  have hM : (1 : ℝ≥0∞) ≤ M := by exact_mod_cast ENNReal.ofReal_le_ofReal hV
  by_cases he : x = o
  · subst x
    exact ⟨(N.occupation_root _).le.trans hM, fun h => (h rfl).elim⟩
  let base := D * ((((m + C : ℕ) : ℝ≥0) + 1) ^ N.maxSourceDegree)
  have hb : 1 ≤ base := one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ (by simp))
  let a : ℝ≥0∞ := ((base⁻¹ : ℝ≥0) : ℝ≥0∞)
  have ha : a ≤ 1 := ENNReal.coe_le_coe.mpr (show base⁻¹ ≤ (1 : ℝ≥0) from inv_le_one_of_one_le₀ hb)
  obtain ⟨n, hn, hp⟩ := hC x hx
  have hexc : a ^ n ≤ N.escapeToRoot o x := N.capped_escape he ha (fun {y z} hy hs =>
    hfloor (m + C) (Finset.sup_le fun i _ => (hy i).trans (Nat.add_le_add_right (coordinate_le_radius x i) C)) hs) hp
  have hbase : (base : ℝ≥0∞) ^ (C * (1 + m)) ≤ M := by
    have h := ENNReal.ofReal_le_ofReal (hcost m)
    simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow, base, M, V] using h
  have hlow : M⁻¹ ≤ N.escapeToRoot o x := by
    apply (ENNReal.inv_le_inv.mpr hbase).trans
    have hpow := pow_le_pow_right_of_le_one' ha hn
    rw [ENNReal.inv_pow]
    exact (show ((base : ℝ≥0∞)⁻¹) ^ (C * (1 + m)) ≤ a ^ n by
      rw [← ENNReal.coe_inv (zero_lt_one.trans_le hb).ne']; exact hpow).trans hexc
  have bound {z : ℝ≥0∞} (hz : z * N.escapeToRoot o x ≤ 1) : z ≤ M := by
    have hm0 : M ≠ 0 := (zero_lt_one.trans_le hM).ne'
    have hh := (mul_le_mul_left' hlow z).trans hz
    calc
      z = z * (M⁻¹ * M) := by rw [ENNReal.inv_mul_cancel hm0 ENNReal.ofReal_ne_top, mul_one]
      _ ≤ M := by rw [← mul_assoc]; simpa only [one_mul] using mul_le_mul_right' hh M
  obtain ⟨hocc, hall⟩ := N.visits_times_escape_le_one he
  exact ⟨bound hocc, fun _ => ⟨hlow, fun y => bound (hall y)⟩⟩

end AIM272.Network
