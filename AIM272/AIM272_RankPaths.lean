import AIM272_Targets
import AIM272_Conditional

set_option warningAsError true

/-! # Static support of the rank kernels on actual complex copies -/

noncomputable section

open AIM272Witness (Feas hsum)
open AIM272 (FastPath CountedPath canReachWithin gateWithin)
open scoped BigOperators

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

def fastStep (wr : N.WeaklyReversible) (a : κ → ℝ) (k d : ℝ) (x y : State κ) : Prop :=
  ∃ r, N.NegativeLoop a x ∧ N.level wr a x = k ∧ N.s r ≤ x ∧
    N.copyHeight a x r - k < d ∧ y = N.jump x r

def rankStep (wr : N.WeaklyReversible) (a : κ → ℝ) (k d : ℝ) (x y : State κ) : Prop :=
  ∃ r, N.NegativeLoop a x ∧ N.level wr a x = k ∧ N.s r ≤ x ∧
    N.copyHeight a x r - k = d ∧ y = N.jump x r

private def copyStep (a : κ → ℝ) (h : ℝ) (x y : State κ) : Prop :=
  ∃ r, N.s r ≤ x ∧ N.copyHeight a x r = h ∧ y = N.jump x r

omit [Fintype L] in
private theorem copyStep_return (wr : N.WeaklyReversible) (a : κ → ℝ)
    {x : State κ} {r : L} (hr : N.s r ≤ x) :
    Relation.ReflTransGen (N.copyStep a (N.copyHeight a x r)) (N.jump x r) x := by
  let z := x - N.s r
  have hsa : N.s r + z = x := funext fun i => Nat.add_sub_of_le (hr i)
  have hta : N.t r + z = N.jump x r := add_comm _ _
  have hc : weight a z = N.copyHeight a x r := by
    have h := congrArg (weight a) hsa
    simp only [weight_add] at h
    change weight a z = weight a x + -weight a (N.s r)
    linarith
  rw [← hta, ← hc]
  conv_rhs => rw [← hsa]
  apply Relation.ReflTransGen.lift (· + z) _ (wr r)
  rintro _ _ ⟨q, rfl, rfl⟩
  refine ⟨q, fun i => Nat.le_add_right _ _, ?_, ?_⟩
  · simp [copyHeight, directionNet, weight_add]
  · funext i
    change N.t q i + z i = N.s q i + z i - N.s q i + N.t q i
    omega

omit [Fintype L] in
private theorem loop_next (wr : N.WeaklyReversible) (a : κ → ℝ) {x : State κ} {r : L}
    (hx : N.NegativeLoop a x) (hr : N.s r ≤ x) : N.NegativeLoop a (N.jump x r) :=
  (N.negativeLoop_iff_projected_step wr a x r (fun i _ => hr i)).mpr hx

theorem fastStep_preserves_level (wr : N.WeaklyReversible) (a : κ → ℝ) {k d : ℝ} (hd : d ≤ 0)
    {x y : State κ} (h : N.fastStep wr a k d x y) :
    N.NegativeLoop a y ∧ N.level wr a y = k := by
  obtain ⟨r, hx, hk, hr, hf, rfl⟩ := h
  exact ⟨N.loop_next wr a hx hr, (N.faster_step_preserves_level wr a hx hr (by linarith)).trans hk⟩

private theorem reverse_fast_step {wr : N.WeaklyReversible} {a : κ → ℝ} {k d : ℝ} (hd : d ≤ 0)
    {x y : State κ} (h : N.fastStep wr a k d x y) : FastPath (N.fastStep wr a k d) y x := by
  obtain ⟨r, hx, hk, hr, hf, rfl⟩ := h
  have hy := N.fastStep_preserves_level wr a hd ⟨r, hx, hk, hr, hf, rfl⟩
  let b := N.copyHeight a x r
  have hb : b - k < d := hf
  have lift {u v : State κ} (p : Relation.ReflTransGen (N.copyStep a b) u v)
      (hu : N.NegativeLoop a u ∧ N.level wr a u = k) : FastPath (N.fastStep wr a k d) u v := by
    induction p using Relation.ReflTransGen.head_induction_on with
    | refl => exact .nil _
    | head h _ ih =>
      obtain ⟨q, hq, he, rfl⟩ := h
      have e : N.fastStep wr a k d _ _ := ⟨q, hu.1, hu.2, hq, he.symm ▸ hb, rfl⟩
      exact .cons e (ih (N.fastStep_preserves_level wr a hd e))
  exact lift (N.copyStep_return wr a hr) hy

theorem reverse_fast_path {wr : N.WeaklyReversible} {a : κ → ℝ} {k d : ℝ} (hd : d ≤ 0)
    {x y : State κ} (h : FastPath (N.fastStep wr a k d) x y) : FastPath (N.fastStep wr a k d) y x := by
  have append {u v z : State κ} (p : FastPath (N.fastStep wr a k d) u v)
      (q : FastPath (N.fastStep wr a k d) v z) : FastPath (N.fastStep wr a k d) u z := by
    induction p with
    | nil => exact q
    | cons hp _ ih => exact .cons hp (ih q)
  induction h with
  | nil => exact .nil _
  | cons he _ ih => exact append ih (N.reverse_fast_step hd he)

private theorem copy_to_counted_or_drop {wr : N.WeaklyReversible} {a : κ → ℝ} {k d b : ℝ}
    (hd : d ≤ 0) (hb : b - k ≤ d) {u v : State κ}
    (p : Relation.ReflTransGen (N.copyStep a b) u v)
    (hu : N.NegativeLoop a u) (hk : N.level wr a u ≤ k) :
    (∃ n, CountedPath (N.fastStep wr a k d) (N.rankStep wr a k d) u v n) ∨
      ∃ z n, N.NegativeLoop a z ∧ N.level wr a z < k ∧
        CountedPath (N.fastStep wr a k d) (N.rankStep wr a k d) u z n := by
  induction p using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl ⟨0, .nil _⟩
  | @head x y he _ ih =>
    by_cases hlow : N.level wr a x < k
    · exact Or.inr ⟨x, 0, hu, hlow, .nil _⟩
    have hxe : N.level wr a x = k := le_antisymm hk (le_of_not_gt hlow)
    obtain ⟨r, hr, hh, rfl⟩ := he
    have hNext : N.level wr a (N.jump x r) ≤ k := by
      apply (N.levels_on_step wr a x r hu hr).1.trans
      exact max_le hk (by linarith)
    rcases lt_or_eq_of_le (hh.symm ▸ hb) with hf | hc
    · have hstep : N.fastStep wr a k d x (N.jump x r) := ⟨r, hu, hxe, hr, hf, rfl⟩
      rcases ih (N.loop_next wr a hu hr) hNext with ⟨n, hn⟩ | ⟨z, n, hz, hz', hn⟩
      · exact Or.inl ⟨n, .fastStep hstep hn⟩
      · exact Or.inr ⟨z, n, hz, hz', .fastStep hstep hn⟩
    · have hstep : N.rankStep wr a k d x (N.jump x r) := ⟨r, hu, hxe, hr, hc, rfl⟩
      rcases ih (N.loop_next wr a hu hr) hNext with ⟨n, hn⟩ | ⟨z, n, hz, hz', hn⟩
      · exact Or.inl ⟨n + 1, .currentStep hstep hn⟩
      · exact Or.inr ⟨z, n + 1, hz, hz', .currentStep hstep hn⟩

theorem reverse_or_reach_target {wr : N.WeaklyReversible} {a : κ → ℝ} (A : N.Target wr a)
    {k d : ℝ} (hd : d ≤ 0) {x y : State κ}
    (he : N.fastStep wr a k d x y ∨ N.rankStep wr a k d x y) :
    (∃ n, CountedPath (N.fastStep wr a k d) (N.rankStep wr a k d) y x n) ∨
      (∃ n, canReachWithin (N.fastStep wr a k d) (N.rankStep wr a k d) (fun z => A.holds z k) y n) := by
  obtain ⟨r, hx, hk, hr, hh, rfl⟩ :
      ∃ r, N.NegativeLoop a x ∧ N.level wr a x = k ∧ N.s r ≤ x ∧
        N.copyHeight a x r - k ≤ d ∧ y = N.jump x r := by
    rcases he with ⟨r, hx, hk, hr, hh, hy⟩ | ⟨r, hx, hk, hr, hh, hy⟩
    · exact ⟨r, hx, hk, hr, hh.le, hy⟩
    · exact ⟨r, hx, hk, hr, hh.le, hy⟩
  have hy : N.level wr a (N.jump x r) ≤ k :=
    (N.levels_on_step wr a x r hx hr).1.trans (max_le hk.le (by linarith))
  rcases N.copy_to_counted_or_drop hd hh (N.copyStep_return wr a hr) (N.loop_next wr a hx hr) hy with h | h
  · exact Or.inl h
  · obtain ⟨z, n, hz, hbelow, hp⟩ := h
    exact Or.inr ⟨n, z, n, A.lower z k hz hbelow, hp, le_rfl⟩

theorem RankedWord.counted {wr : N.WeaklyReversible} {a : κ → ℝ} {A : N.Target wr a} {k d : ℝ}
    {x : State κ} {w : List L} {n : ℕ} (h : N.RankedWord A k d x w n) (hx : N.NegativeLoop a x) :
    ∃ y, A.holds y k ∧ CountedPath (N.fastStep wr a k d) (N.rankStep wr a k d) x y n := by
  classical
  induction h with
  | stop hA => exact ⟨_, hA, .nil _⟩
  | @next x r w n hk hr hle _ ih =>
    obtain ⟨y, hy, hp⟩ := ih (N.loop_next wr a hx hr)
    rcases lt_or_eq_of_le hle with hf | hc
    · simpa only [if_neg hf.ne, add_zero] using
        (show ∃ z, A.holds z k ∧ CountedPath _ _ x z n from
          ⟨y, hy, .fastStep (show N.fastStep wr a k d x _ from ⟨r, hx, hk, hr, hf, rfl⟩) hp⟩)
    · simpa only [if_pos hc] using
        (show ∃ z, A.holds z k ∧ CountedPath _ _ x z (n + 1) from
          ⟨y, hy, .currentStep (show N.rankStep wr a k d x _ from ⟨r, hx, hk, hr, hc, rfl⟩) hp⟩)

theorem rankedWord_of_counted {wr : N.WeaklyReversible} {a : κ → ℝ} {A : N.Target wr a} {k d : ℝ}
    {x y : State κ} {n : ℕ} (p : CountedPath (N.fastStep wr a k d) (N.rankStep wr a k d) x y n)
    (hy : A.holds y k) : ∃ w, N.RankedWord A k d x w n := by
  classical
  induction p with
  | nil => exact ⟨[], .stop hy⟩
  | fastStep h _ ih =>
    obtain ⟨r, _, hk, hr, hd, rfl⟩ := h
    obtain ⟨w, hw⟩ := ih hy
    exact ⟨r :: w, by simpa only [if_neg hd.ne, add_zero] using (RankedWord.next hk hr hd.le hw)⟩
  | currentStep h _ ih =>
    obtain ⟨r, _, hk, hr, hd, rfl⟩ := h
    obtain ⟨w, hw⟩ := ih hy
    exact ⟨r :: w, by simpa only [if_pos hd] using (RankedWord.next hk hr hd.le hw)⟩

theorem entranceTarget_iff_gate {wr : N.WeaklyReversible} {a : κ → ℝ} (A : N.Target wr a)
    {x : State κ} {k d : ℝ} {b : ℕ} (hx : N.NegativeLoop a x) :
    (N.entranceTarget A d b).holds x k ↔
      gateWithin (fun z => N.level wr a z < k) (N.fastStep wr a k d) (N.rankStep wr a k d)
        (fun z => A.holds z k) b x := by
  constructor
  · rintro (hl | ⟨r, hk, hr, hd, w, n, hw, hn⟩)
    · exact Or.inl hl
    · obtain ⟨y, hy, hp⟩ := hw.counted N (N.loop_next wr a hx hr)
      exact Or.inr ⟨_, ⟨r, hx, hk, hr, hd, rfl⟩, y, n, hy, hp, hn⟩
  · rintro (hl | ⟨z, ⟨r, _, hk, hr, hd, rfl⟩, y, n, hy, hp, hn⟩)
    · exact Or.inl hl
    · obtain ⟨w, hw⟩ := N.rankedWord_of_counted hp hy
      exact Or.inr ⟨r, hk, hr, hd, w, n, hw, hn⟩

private theorem RankedWord.count_le_length {wr : N.WeaklyReversible} {a : κ → ℝ}
    {A : N.Target wr a} {k d : ℝ} {x : State κ} {w : List L} {n : ℕ}
    (h : N.RankedWord A k d x w n) : n ≤ w.length := by
  induction h with
  | stop => rfl
  | next _ _ _ _ ih =>
    simp only [List.length_cons]
    split <;> omega

theorem rank_budget {wr : N.WeaklyReversible} {a : κ → ℝ} (A : N.Target wr a) (d : ℝ) :
    ∃ B, ∀ {k x}, N.NegativeLoop a x → N.level wr a x = k →
      (∃ n, canReachWithin (N.fastStep wr a k d) (N.rankStep wr a k d) (fun y => A.holds y k) x n) →
        canReachWithin (N.fastStep wr a k d) (N.rankStep wr a k d) (fun y => A.holds y k) x B := by
  obtain ⟨B, hB⟩ := N.bounded_static_target A d
  refine ⟨B, fun {k x} hx hk h => ?_⟩
  subst k
  obtain ⟨_, y, n, hy, hp, _⟩ := h
  obtain ⟨w, hw⟩ := N.rankedWord_of_counted hp hy
  obtain ⟨v, m, hv, hlen⟩ := hB x hx ⟨w, n, hw⟩
  obtain ⟨z, hz, hpath⟩ := hv.counted N hx
  exact ⟨z, m, hz, hpath, (hv.count_le_length N).trans hlen⟩

/-- The target used to stop a nonpositive-order segment. -/
def lowerTarget (wr : N.WeaklyReversible) (a : κ → ℝ) : N.Target wr a where
  holds x k := N.level wr a x < k
  lower _ _ _ h := h
  translate x k z hx h := by
    have hp := N.psi_antitone wr a hx (show x ≤ x + z from fun i => Nat.le_add_right _ _)
    simp only [level, weight_add] at *
    linarith

/-- A projected word can be lifted when each forgotten coordinate has
enough inventory for its entire length. -/
private theorem full_feas (a : κ → ℝ) (b : ℝ) (w : List L) (x : State κ) (H : ℝ)
    (hf : Feas (N.directionNet a) (phaseCoords a) b x H w)
    (hstock : ∀ i ∉ phaseCoords a, N.sourceInventoryBound * w.length ≤ x i) :
    Feas (N.directionNet a) Finset.univ b x H w := by
  classical
  induction w generalizing x H with
  | nil => trivial
  | cons r w ih =>
    refine ⟨fun i _ => ?_, hf.2.1, ih _ _ hf.2.2 ?_⟩
    · by_cases hi : i ∈ phaseCoords a
      · exact hf.1 i hi
      · have hs := N.source_le_inventoryBound r i
        have hn := hstock i hi
        change N.s r i ≤ x i
        rw [List.length_cons, Nat.mul_succ] at hn
        omega
    · intro i hi
      have hs := N.source_le_inventoryBound r i
      have hn := hstock i hi
      change _ ≤ x i - N.s r i + N.t r i
      rw [List.length_cons, Nat.mul_succ] at hn
      omega

private theorem descend_of_full_feas (wr : N.WeaklyReversible) (a : κ → ℝ)
    (k : ℝ) (w : List L) {x : State κ} (hx : N.NegativeLoop a x) (hk : N.level wr a x ≤ k)
    (hf : Feas (N.directionNet a) Finset.univ k x (weight a x) w)
    (hlow : weight a x + hsum (N.directionNet a) w + (N.peaks wr a).cap < k) :
    ∃ v n, N.RankedWord (N.lowerTarget wr a) k 0 x v n := by
  classical
  by_cases hlt : N.level wr a x < k
  · exact ⟨[], 0, .stop hlt⟩
  have he := le_antisymm hk (le_of_not_gt hlt)
  induction w generalizing x with
  | nil =>
    have hh := ((N.peaks wr a).bounds x hx).2
    simp only [AIM272Witness.hsum_nil, add_zero] at hlow
    change N.psi wr a x ≤ _ at hh
    change weight a x + N.psi wr a x = k at he
    linarith
  | cons r w ih =>
    have hr : N.s r ≤ x := fun i => hf.1 i (Finset.mem_univ _)
    have hcap : N.copyHeight a x r ≤ k := hf.2.1
    have hlevel := (N.levels_on_step wr a x r hx hr).1.trans (max_le hk hcap)
    have hweight := N.weight_jump a hr
    have hnew : weight a (N.jump x r) = weight a x + (N.directionNet a).δ r := by linarith
    have hf' : Feas (N.directionNet a) Finset.univ k (N.jump x r) (weight a (N.jump x r)) w := by
      rw [hnew]
      exact hf.2.2
    have hlow' : weight a (N.jump x r) + hsum (N.directionNet a) w + (N.peaks wr a).cap < k := by
      rw [AIM272Witness.hsum_cons] at hlow
      linarith
    by_cases hdesc : N.level wr a (N.jump x r) < k
    · exact ⟨_, _, .next he hr (sub_nonpos.mpr hcap) (.stop hdesc)⟩
    · obtain ⟨v, n, hv⟩ := ih (N.loop_next wr a hx hr) hlevel hf' hlow' hdesc
        (le_antisymm hlevel (le_of_not_gt hdesc))
      exact ⟨r :: v, _, .next he hr (sub_nonpos.mpr hcap) hv⟩

/-- At every phase with enough stock in its positive coordinates, a
bounded witness reaches a lower level using actual nonpositive edges. -/
theorem lower_target_reachable (wr : N.WeaklyReversible) (a : κ → ℝ) :
    ∃ K : ℕ, ∀ x, N.NegativeLoop a x → (∀ i ∉ phaseCoords a, K ≤ x i) →
      ∃ w n, N.RankedWord (N.lowerTarget wr a) (N.level wr a x) 0 x w n := by
  classical
  let Q := N.peaks wr a
  have hD : 0 < Q.depth := by linarith [Q.cap_nonneg, Q.depth_large, N.maxComplexHeight_nonneg a]
  obtain ⟨B, hB⟩ := N.directional_bounded_witness a Q.cap_nonneg hD.le
  refine ⟨N.sourceInventoryBound * B, fun x hx hstock => ?_⟩
  have hψ := Q.bounds x hx
  obtain ⟨u, hu⟩ := (Q.depth_iff x hx (N.psi wr a x)).mp le_rfl
  obtain ⟨w, hlen, hw⟩ := hB x (N.psi wr a x) Q.depth u hψ.2 le_rfl hu
  let W := N.directionNet a
  have hcap : N.level wr a x - weight a x = N.psi wr a x := by simp [level]
  have hshift := (AIM272Witness.feas_shift W (b := N.level wr a x) (weight a x) w x (weight a x)).mpr
    (by rw [hcap, sub_self]; exact hw.1)
  have hfull := N.full_feas a (N.level wr a x) w x (weight a x) hshift
    (fun i hi => (Nat.mul_le_mul_left _ hlen).trans (hstock i hi))
  have hdescent := hw.2
  apply N.descend_of_full_feas wr a _ w hx le_rfl hfull
  change weight a x + hsum (N.directionNet a) w + Q.cap < weight a x + N.psi wr a x
  have hmin : -N.maxComplexHeight a ≤ N.psi wr a x := hψ.1
  linarith [Q.depth_large]

end AIM272.Network
