import AIM272_Levels

set_option warningAsError true

/-!
# Static reachability and entrance targets

Translation can lower a state below the current level. In that case the
translated word stops immediately. While the translated path stays on the
level, every copy height minus the level is unchanged.
-/

noncomputable section

open AIM272Witness (Enabled)

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

structure Target (wr : N.WeaklyReversible) (a : κ → ℝ) where
  holds : State κ → ℝ → Prop
  lower : ∀ x k, N.NegativeLoop a x → N.level wr a x < k → holds x k
  translate : ∀ x k z, N.NegativeLoop a x → holds x k → holds (x + z) (k + weight a z)

private theorem level_shift_le (wr : N.WeaklyReversible) (a : κ → ℝ) {x : State κ}
    (hx : N.NegativeLoop a x) (z : State κ) :
    N.level wr a (x + z) ≤ N.level wr a x + weight a z := by
  have hle : x ≤ x + z := fun i => Nat.le_add_right _ _
  have hs := N.psi_antitone wr a hx hle
  simp only [level, weight_add]
  linarith

omit [Fintype L] in
private theorem loop_after_jump (wr : N.WeaklyReversible) (a : κ → ℝ) {x : State κ} {r : L}
    (hx : N.NegativeLoop a x) (hr : N.s r ≤ x) :
    N.NegativeLoop a (N.jump x r) :=
  (N.negativeLoop_iff_projected_step wr a x r (fun i _ => hr i)).mpr hx

omit [Fintype κ] [Fintype L] in
private theorem jump_shift {x : State κ} {r : L} (hr : N.s r ≤ x) (z : State κ) :
    N.jump (x + z) r = N.jump x r + z := by
  funext i
  have hi : N.s r i ≤ x i := hr i
  change x i + z i - N.s r i + N.t r i = x i - N.s r i + N.t r i + z i
  omega

omit [Fintype L] in
private theorem copy_order_shift (a : κ → ℝ) (k : ℝ) (x z : State κ) (r : L) :
    N.copyHeight a (x + z) r - (k + weight a z) = N.copyHeight a x r - k := by
  simp only [copyHeight, weight_add]
  ring

open Classical in
/-- A static word at level k with orders at most d. Its final index counts
the uses of the boundary order d. -/
inductive RankedWord {wr : N.WeaklyReversible} {a : κ → ℝ} (A : N.Target wr a) (k d : ℝ) :
    State κ → List L → ℕ → Prop
  | stop {x} : A.holds x k → RankedWord A k d x [] 0
  | next {x r w n} : N.level wr a x = k → N.s r ≤ x → N.copyHeight a x r - k ≤ d →
      RankedWord A k d (N.jump x r) w n →
      RankedWord A k d x (r :: w) (n + if N.copyHeight a x r - k = d then 1 else 0)

theorem rankedWord_shift {wr : N.WeaklyReversible} {a : κ → ℝ} {A : N.Target wr a}
    {k d : ℝ} {x : State κ} {w : List L} {n : ℕ}
    (h : N.RankedWord A k d x w n) (hx : N.NegativeLoop a x) (z : State κ) :
    ∃ v m, N.RankedWord A (k + weight a z) d (x + z) v m ∧ v.length ≤ w.length ∧ m ≤ n := by
  classical
  induction h with
  | @stop x ht =>
    exact ⟨[], 0, .stop (A.translate x k z hx ht), le_rfl, le_rfl⟩
  | @next x r w n hk hr hd _ ih =>
    have hle : x ≤ x + z := fun i => Nat.le_add_right _ _
    have hLevel := N.level_shift_le wr a hx z
    rw [hk] at hLevel
    by_cases hdrop : N.level wr a (x + z) < k + weight a z
    · exact ⟨[], 0, .stop (A.lower _ _ (N.negativeLoop_upward a hx hle) hdrop),
        Nat.zero_le _, Nat.zero_le _⟩
    have hSame := le_antisymm hLevel (le_of_not_gt hdrop)
    obtain ⟨v, m, hv, hlen, hm⟩ := ih (N.loop_after_jump wr a hx hr)
    have hEnabled : N.s r ≤ x + z := hr.trans hle
    have hGuard : N.copyHeight a (x + z) r - (k + weight a z) ≤ d := by
      rw [N.copy_order_shift]
      exact hd
    rw [← N.jump_shift hr z] at hv
    refine ⟨r :: v, m + if N.copyHeight a x r - k = d then 1 else 0, ?_,
      Nat.succ_le_succ hlen, Nat.add_le_add_right hm _⟩
    simpa only [N.copy_order_shift] using
      (RankedWord.next hSame hEnabled hGuard hv : N.RankedWord A (k + weight a z) d _ _ _)

/-- A uniform length bound for static words, before rates are introduced. -/
theorem bounded_static_target {wr : N.WeaklyReversible} {a : κ → ℝ}
    (A : N.Target wr a) (d : ℝ) :
    ∃ B : ℕ, ∀ x, N.NegativeLoop a x →
      (∃ w n, N.RankedWord A (N.level wr a x) d x w n) →
      ∃ w n, N.RankedWord A (N.level wr a x) d x w n ∧ w.length ≤ B := by
  classical
  let candidates (s : ℝ) : Set (State κ) := {x | N.psi wr a x = s ∧ N.NegativeLoop a x ∧
    ∃ w n, N.RankedWord A (N.level wr a x) d x w n}
  let mins (s : ℝ) : Set (State κ) := {x | Minimal (· ∈ candidates s) x}
  let base := ⋃ s ∈ Set.range (N.psi wr a), mins s
  have hMin (s) : (mins s).Finite :=
    (setOf_minimal_antichain (candidates s)).finite_of_partiallyWellOrderedOn (Pi.isPWO _)
  have hBase : base.Finite := (N.psi_finite_values wr a).biUnion (fun s _ => hMin s)
  letI : Finite base := hBase.to_subtype
  have hsel (x : base) : ∃ w n, N.RankedWord A (N.level wr a x.val) d x.val w n := by
    obtain ⟨s, _, hs⟩ := Set.mem_iUnion₂.mp x.property
    have hm : Minimal (· ∈ candidates s) x.val := hs
    exact hm.1.2.2
  choose word count hword using hsel
  obtain ⟨B, hB⟩ := (Set.finite_range (fun x : base => (word x).length)).bddAbove
  refine ⟨B, fun x hx hReach => ?_⟩
  let s := N.psi wr a x
  have hmem : x ∈ candidates s := ⟨rfl, hx, hReach⟩
  obtain ⟨b, hbx, hb⟩ := (Pi.isPWO (candidates s)).exists_le_minimal hmem
  let p : base := ⟨b, Set.mem_iUnion₂.mpr ⟨s, ⟨x, rfl⟩, hb⟩⟩
  let z := x - b
  have hz : b + z = x := funext fun i => Nat.add_sub_of_le (hbx i)
  obtain ⟨v, m, hv, hl, _⟩ := N.rankedWord_shift (hword p) hb.1.2.1 z
  have hShift : N.level wr a b + weight a z = N.level wr a x := by
    have hW := congrArg (weight a) hz
    rw [weight_add] at hW
    have hψ : N.psi wr a b = N.psi wr a x := hb.1.1
    simp only [level]
    linarith
  change N.RankedWord A (N.level wr a b + weight a z) d (b + z) v m at hv
  rw [hShift, hz] at hv
  exact ⟨v, m, hv, hl.trans (hB ⟨p, rfl⟩)⟩

/-- Entrance target with a remaining budget b after crossing the boundary order. -/
def entranceTarget {wr : N.WeaklyReversible} {a : κ → ℝ}
    (A : N.Target wr a) (d : ℝ) (b : ℕ) : N.Target wr a where
  holds x k := N.level wr a x < k ∨
    ∃ r, N.level wr a x = k ∧ N.s r ≤ x ∧ N.copyHeight a x r - k = d ∧
      ∃ w n, N.RankedWord A k d (N.jump x r) w n ∧ n ≤ b
  lower _ _ _ h := Or.inl h
  translate x k z hx h := by
    have hLevel := N.level_shift_le wr a hx z
    rcases h with h | ⟨r, hk, hr, hd, w, n, hw, hn⟩
    · exact Or.inl (hLevel.trans_lt (add_lt_add_right h _))
    · rw [hk] at hLevel
      by_cases hdrop : N.level wr a (x + z) < k + weight a z
      · exact Or.inl hdrop
      · obtain ⟨v, m, hv, _, hm⟩ := N.rankedWord_shift hw (N.loop_after_jump wr a hx hr) z
        rw [← N.jump_shift hr z] at hv
        exact Or.inr ⟨r, le_antisymm hLevel (le_of_not_gt hdrop),
          hr.trans (fun i => Nat.le_add_right _ _), (N.copy_order_shift a k x z r).trans hd,
          v, m, hv, hm.trans hn⟩

end AIM272.Network
