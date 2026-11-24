import AIM272_Sampling
import AIM272_Thinning
import AIM272_Geometry

set_option warningAsError true

/-! # The sampling estimate for the actual mass-action marks -/

noncomputable section

open AIM272 RankedRace Filter
open scoped NNReal ENNReal Topology

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

def nonpositiveRanks (wr : N.WeaklyReversible) (a : κ → ℝ) : List ℝ :=
  (insert 0 ((N.relativeOrders_finite wr a).toFinset.filter (· ≤ 0))).sort (· ≥ ·)

theorem mem_nonpositiveRanks (wr : N.WeaklyReversible) (a : κ → ℝ) (d : ℝ) :
    d ∈ N.nonpositiveRanks wr a ↔
      d = 0 ∨ (d ≤ 0 ∧ ∃ x r, d = N.relativeOrder wr a x r) := by
  classical
  simp only [nonpositiveRanks, Finset.mem_sort, Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_range]
  constructor
  · rintro (h | ⟨⟨⟨x, r⟩, hr⟩, hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hd, x, r, hr.symm⟩
  · rintro (h | ⟨hd, x, r, hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨(x, r), hr.symm⟩, hd⟩

theorem nonpositiveRanks_complete (wr : N.WeaklyReversible) (a : κ → ℝ) :
    N.CompleteRanks wr a (N.nonpositiveRanks wr a) := by
  classical
  have h_nonpos d (hd : d ∈ N.nonpositiveRanks wr a) : d ≤ 0 := by
    rcases (N.mem_nonpositiveRanks wr a d).mp hd with rfl | h
    · exact le_rfl
    · exact h.1
  refine ⟨by unfold nonpositiveRanks; exact Finset.sort_sorted_gt _, h_nonpos, fun d hd x r h => ?_⟩
  exact (N.mem_nonpositiveRanks wr a _).mpr (Or.inr ⟨h.trans (h_nonpos d hd), x, r, rfl⟩)

private theorem clock_eventually_separated {K : ℝ} (hK : 0 < K) (η : ℝ) (ds : List ℝ) :
    ∀ᶠ R : ℝ in atTop, ∀ u ∈ ds, ∀ v ∈ ds, u < v →
      2 * orderClockRate K R η v ≤ orderClockRate K R η u := by
  apply AIM272Geometry.eventually_list
  intro u _
  apply AIM272Geometry.eventually_list
  intro v _
  by_cases huv : u < v
  · filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr huv)).eventually_ge_atTop 2,
      eventually_gt_atTop (0 : ℝ)] with R hR hR0 _
    apply NNReal.coe_le_coe.mp
    simp only [orderClockRate, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal _
      (mul_nonneg hK.le (Real.rpow_nonneg hR0.le _))]
    calc
      _ ≤ R ^ (v - u) * (K * R ^ (-v + η)) :=
        mul_le_mul_of_nonneg_right hR (mul_nonneg hK.le (Real.rpow_nonneg hR0.le _))
      _ = K * R ^ (-u + η) := by
        rw [mul_left_comm, ← Real.rpow_add hR0]
        congr 2
        ring
  · exact Eventually.of_forall fun _ hu => (huv hu).elim

/-- G5. The exponent and label constant are fixed before η and R.
The observation is the discrete geometric-race construction. -/
theorem actual_sampling_lower (wr : N.WeaklyReversible) (a : κ → ℝ) (A : N.Target wr a) :
    ∃ b : ℕ, ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ c ≤ 1 / 2 ∧ N.ThinnedRateBounds K c ∧
      ∀ η : ℝ, 0 ≤ η → ∀ᶠ R : ℝ in atTop, ∀ E : ℝ, 0 ≤ E → (N.maxSourceDegree : ℝ) * E ≤ η →
      ∀ (k : ℝ) (ν : ℝ≥0), 0 < ν → ν ≤ orderClockRate K R η 0 → ∀ x,
        (N.levelDead wr a R E k x ∨
          ∃ y, A.holds y k ∧ FastPath (allowedStep (N.rankStep wr a k) (N.nonpositiveRanks wr a)) x y) →
        (c * R ^ (-2 * η)).toNNReal ^ b ≤
          prob (observe (orderClockRate K R η) (fun d => N.rankMark wr a R E η K k d)
            (N.nonpositiveRanks wr a) ν x) (fun y => N.levelDead wr a R E k y ∨ A.holds y k) := by
  classical
  let ds := N.nonpositiveRanks wr a
  have hds := N.nonpositiveRanks_complete wr a
  obtain ⟨b, hb⟩ := N.rank_sampling_power wr a ds hds A
  obtain ⟨K, c, hK, hc, hc', hmark⟩ := N.thinned_rate_bounds
  refine ⟨b, K, c, hK, hc, hc', hmark, fun η hη => ?_⟩
  filter_upwards [clock_eventually_separated hK η ds, eventually_gt_atTop (1 : ℝ)]
    with R hSep hR E hE hdev k ν hν hν' x hx
  let ρ := (c * R ^ (-2 * η)).toNNReal
  have hR0 := zero_lt_one.trans hR
  have hρ : 0 < ρ := Real.toNNReal_pos.mpr (mul_pos hc (Real.rpow_pos_of_pos hR0 _))
  have hρ' : ρ ≤ 1 / 2 := by
    apply NNReal.coe_le_coe.mp
    change (ρ : ℝ) ≤ (1 : ℝ) / 2
    rw [Real.coe_toNNReal _ (mul_nonneg hc.le (Real.rpow_nonneg hR0.le _))]
    calc
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hR.le (by linarith)) hc.le
      _ ≤ _ := by simpa using hc'
  let F : N.LevelClockFamily wr a k ρ := {
    dead := N.levelDead wr a R E k
    live := fun z h => by
      have hd : z ∈ N.localDomain a R E := by
        by_contra hbad
        exact h (Or.inl hbad)
      exact ⟨hd.1, by_contra fun hbad => h (Or.inr hbad)⟩
    clock := orderClockRate K R η
    clock_pos := fun _ => orderClockRate_pos hK hR0
    mark := fun d => N.rankMark wr a R E η K k d
    stuck := fun _ _ h => N.rankMark_stuck h
    support := fun d z y h => Or.inr (N.rankMark_support_move wr a R E η K k d z y h)
    null := fun d z => hρ'.trans (N.rankMark_null wr a R E η K k d z
      (fun hz => (hmark wr a hR hE hdev z hz d).1))
    label := fun d {z y} he => N.rankMark_label wr a R E η K k d he (hρ'.trans (by norm_num))
      (fun hz => (hmark wr a hR hE hdev z hz d).1.trans (by norm_num))
      (fun hz => (hmark wr a hR hE hdev z hz d).2) }
  apply hb hρ hρ' F hSep hν _ x hx
  intro d hd
  have hnonpos := hds.2.1 d hd
  refine hν'.trans (Real.toNNReal_le_toNNReal ?_)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR.le (by linarith)) hK.le

private theorem rankedWord_to_allowed {wr : N.WeaklyReversible} {a : κ → ℝ} {A : N.Target wr a}
    {k : ℝ} {x : State κ} {w : List L} {n : ℕ} (h : N.RankedWord A k 0 x w n)
    (hx : N.NegativeLoop a x) :
    ∃ y, A.holds y k ∧ FastPath (allowedStep (N.rankStep wr a k) (N.nonpositiveRanks wr a)) x y := by
  obtain ⟨y, hy, hp⟩ := h.counted N hx
  refine ⟨y, hy, ?_⟩
  clear h hx hy w
  induction hp with
  | nil => exact .nil _
  | @fastStep x y z m hf hp ih =>
    obtain ⟨r, hz, hk, hr, hd, rfl⟩ := hf
    let d := N.relativeOrder wr a x r
    have hdef : d = N.copyHeight a x r - k := by
      dsimp [d]
      rw [N.relativeOrder_eq, hk]
    refine .cons ⟨d, (N.mem_nonpositiveRanks wr a d).mpr (Or.inr ⟨?_, x, r, rfl⟩),
      r, hz, hk, hr, hdef.symm, rfl⟩ ih
    rw [hdef]
    exact hd.le
  | currentStep hc _ ih =>
    exact .cons ⟨0, (N.mem_nonpositiveRanks wr a 0).mpr (Or.inl rfl), hc⟩ ih

/-- The hypothesis of the sampling bound for a level drop holds
throughout the local domain once R is large enough. -/
theorem local_lower_target_eventually (wr : N.WeaklyReversible) (a : κ → ℝ) {E : ℝ}
    (hE : ∀ i, a i ≠ 0 → E < a i) :
    ∀ᶠ R : ℝ in atTop, ∀ x ∈ N.localDomain a R E,
      ∃ y, N.level wr a y < N.level wr a x ∧
        FastPath (allowedStep (N.rankStep wr a (N.level wr a x)) (N.nonpositiveRanks wr a)) x y := by
  classical
  obtain ⟨K, hK⟩ := N.lower_target_reachable wr a
  have hlarge (i : κ) : ∀ᶠ R : ℝ in atTop, a i ≠ 0 → (K : ℝ) + 1 ≤ R ^ (a i - E) := by
    by_cases hi : a i = 0
    · exact Eventually.of_forall fun _ h => (h hi).elim
    · exact (tendsto_rpow_atTop (sub_pos.mpr (hE i hi))).eventually_ge_atTop _ |>.mono
        fun _ h _ => h
  have hL := AIM272Geometry.eventually_list (Finset.univ : Finset κ).toList (fun i _ => hlarge i)
  filter_upwards [hL, eventually_gt_atTop (1 : ℝ)] with R hR hR1 x hx
  have hstock (i : κ) (hi : i ∉ phaseCoords a) : K ≤ x i := by
    have hai : a i ≠ 0 := fun hp => hi ((mem_phaseCoords a i).mpr hp)
    have hgeom := hR i (by simp) hai
    have hlog := (abs_lt.mp (hx.2.2 i)).1
    have hlogR := Real.log_pos hR1
    have hdiv : (a i - E) * Real.log R < Real.log ((x i : ℝ) + 1) := by
      apply (lt_div_iff₀ hlogR).mp
      linarith
    have hxp : R ^ (a i - E) < (x i : ℝ) + 1 := by
      apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos (zero_lt_one.trans hR1) _) (by positivity)).mp
      rwa [Real.log_rpow (zero_lt_one.trans hR1)]
    exact_mod_cast (show (K : ℝ) ≤ (x i : ℝ) by linarith)
  obtain ⟨w, n, hw⟩ := hK x hx.1 hstock
  exact N.rankedWord_to_allowed hw hx.1

end AIM272.Network
