import AIM272_Model
import AIM272_Witness

set_option warningAsError true

/-!
# Projecting the concrete network onto a logarithmic direction

This module uses the phase words and height caps of AIM272_Witness on
the zero coordinates of a direction. Its paths are built from the same
reaction labels as the stochastic model.
-/

noncomputable section

open scoped BigOperators
open AIM272Unusable (Step Reach Γ Usable)
open AIM272Witness (Enabled Feas endP hsum stepP Wit)

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] (N : AIM272.Network κ L)

def weight (a : κ → ℝ) (x : State κ) : ℝ := ∑ i, a i * (x i : ℝ)

theorem weight_add (a : κ → ℝ) (x y : State κ) :
    weight a (x + y) = weight a x + weight a y := by
  simp only [weight, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]

open Classical in
def phaseCoords (a : κ → ℝ) : Finset κ := Finset.univ.filter (fun i => a i = 0)

theorem mem_phaseCoords (a : κ → ℝ) (i : κ) : i ∈ phaseCoords a ↔ a i = 0 := by
  classical
  simp [phaseCoords]

def directionNet (a : κ → ℝ) : AIM272Witness.Net κ L where
  s := N.s
  t := N.t
  δ r := weight a (N.t r) - weight a (N.s r)
  g r := -weight a (N.s r)

theorem weight_jump (a : κ → ℝ) {x : State κ} {r : L} (hr : N.s r ≤ x) :
    weight a (N.jump x r) - weight a x = (N.directionNet a).δ r := by
  have he : (x - N.s r) + N.s r = x := by
    funext i
    exact Nat.sub_add_cancel (hr i)
  have hw : weight a (x - N.s r) + weight a (N.s r) = weight a x := by
    rw [← weight_add, he]
  simp only [jump, weight_add, directionNet]
  linarith

section Bounds

variable [Fintype L]

open Classical in
private def complexHeights (a : κ → ℝ) : Finset ℝ :=
  insert 0 ((Finset.univ.image (fun r : L => weight a (N.s r))) ∪
    (Finset.univ.image (fun r : L => weight a (N.t r))))

/-- The maximum height of a complex, with value zero for an empty network. -/
def maxComplexHeight (a : κ → ℝ) : ℝ :=
  (N.complexHeights a).sup' (by classical simp [complexHeights]) id

theorem maxComplexHeight_nonneg (a : κ → ℝ) : 0 ≤ N.maxComplexHeight a := by
  classical
  exact Finset.le_sup' id (by simp [complexHeights])

theorem sourceHeight_le_max (a : κ → ℝ) (r : L) :
    weight a (N.s r) ≤ N.maxComplexHeight a := by
  classical
  apply Finset.le_sup' id
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩))

theorem targetHeight_le_max (a : κ → ℝ) (r : L) :
    weight a (N.t r) ≤ N.maxComplexHeight a := by
  classical
  apply Finset.le_sup' id
  exact Finset.mem_insert_of_mem (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩))

def sourceInventoryBound : ℕ := Finset.univ.sup (fun r : L => Finset.univ.sup (N.s r))

theorem source_le_inventoryBound (r : L) (i : κ) : N.s r i ≤ N.sourceInventoryBound :=
  (Finset.le_sup (f := N.s r) (Finset.mem_univ i)).trans
    (Finset.le_sup (f := fun q => Finset.univ.sup (N.s q)) (Finset.mem_univ r))

theorem delta_sub_guard_le_max (a : κ → ℝ) (r : L) :
    (N.directionNet a).δ r - (N.directionNet a).g r ≤ N.maxComplexHeight a := by
  simp only [directionNet, sub_neg_eq_add, sub_add_cancel]
  exact N.targetHeight_le_max a r

/-- G1 connects the existing bounded-witness theorem to the concrete network. -/
theorem directional_bounded_witness (a : κ → ℝ) {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ B, AIM272Witness.HasBound (N.directionNet a) (phaseCoords a) C D B := by
  classical
  exact AIM272Witness.bounded_witness (N.directionNet a) (N.maxComplexHeight_nonneg a)
    (N.delta_sub_guard_le_max a) N.source_le_inventoryBound (phaseCoords a) C D hC hD

end Bounds

/-- A labelled projected path with specified net height increment.
The endpoint is prescribed only on the phase coordinates. -/
def PhasePath (a : κ → ℝ) (x y : State κ) (d : ℝ) : Prop :=
  ∃ w : List L, ∃ b : ℝ, Feas (N.directionNet a) (phaseCoords a) b x 0 w ∧
    (∀ i ∈ phaseCoords a, endP (N.directionNet a) x w i = y i) ∧
    hsum (N.directionNet a) w = d

private theorem append_feasible (a : κ → ℝ) {x : State κ} {u v : List L} {b c : ℝ}
    (hu : Feas (N.directionNet a) (phaseCoords a) b x 0 u)
    (hv : Feas (N.directionNet a) (phaseCoords a) c (endP (N.directionNet a) x u) 0 v) :
    Feas (N.directionNet a) (phaseCoords a) (max b (c + hsum (N.directionNet a) u))
      x 0 (u ++ v) := by
  let W := N.directionNet a
  rw [AIM272Witness.feas_append]
  constructor
  · exact AIM272Witness.feas_cap W (le_max_left _ _) _ _ _ hu
  · have hs := (AIM272Witness.feas_shift W (-hsum W u) v (endP W x u) 0).mp hv
    simp only [zero_add]
    exact AIM272Witness.feas_cap W (le_max_right _ _) _ _ _ (by simpa only [sub_neg_eq_add,
      zero_add] using hs)

theorem phasePath_same (a : κ → ℝ) {x y : State κ}
    (h : ∀ i ∈ phaseCoords a, x i = y i) : N.PhasePath a x y 0 :=
  ⟨[], 0, trivial, h, AIM272Witness.hsum_nil _⟩

theorem phasePath_trans (a : κ → ℝ) {x y z : State κ} {d e : ℝ}
    (h₁ : N.PhasePath a x y d) (h₂ : N.PhasePath a y z e) :
    N.PhasePath a x z (d + e) := by
  let W := N.directionNet a
  obtain ⟨u, b, hu, hy, hd⟩ := h₁
  obtain ⟨v, c, hv, hz, he⟩ := h₂
  have hf := AIM272Witness.feas_le W v y (endP W x u) 0 0 hv
    (fun i hi => (hy i hi).ge) le_rfl
  refine ⟨u ++ v, _, N.append_feasible a hu hf, ?_, ?_⟩
  · intro i hi
    rw [AIM272Witness.endP_append, AIM272Witness.endP_agree W v _ _ hy i hi]
    exact hz i hi
  · rw [AIM272Witness.hsum_append, hd, he]

theorem phasePath_one (a : κ → ℝ) (x : State κ) (r : L)
    (hr : Enabled (N.directionNet a) (phaseCoords a) r x) :
    N.PhasePath a x (N.jump x r) ((N.directionNet a).δ r) := by
  refine ⟨[r], (N.directionNet a).g r, ⟨hr, by simp, trivial⟩, ?_, ?_⟩
  · exact fun _ _ => rfl
  · simp

private theorem word_of_reach (a : κ → ℝ) {x y : State κ} (h : Reach N.toRxn x y) :
    ∃ w : List L, ∃ b : ℝ, Feas (N.directionNet a) (phaseCoords a) b x 0 w ∧
      endP (N.directionNet a) x w = y ∧
      hsum (N.directionNet a) w = weight a y - weight a x := by
  let W := N.directionNet a
  induction h with
  | refl => exact ⟨[], 0, trivial, rfl, by simp⟩
  | @tail y z _ hstep ih =>
    obtain ⟨w, b, hw, hy, hsumw⟩ := ih
    obtain ⟨r, hr, hz⟩ := hstep
    have hLast : Feas W (phaseCoords a) (W.g r) (endP W x w) 0 [r] := by
      rw [hy]
      exact ⟨fun i _ => hr i, by simp, trivial⟩
    refine ⟨w ++ [r], _, N.append_feasible a hw hLast, ?_, ?_⟩
    · rw [AIM272Witness.endP_append, hy]
      exact hz.symm
    · have hzr : z = N.jump y r := hz
      calc
        hsum W (w ++ [r]) = hsum W w + W.δ r := by simp [AIM272Witness.hsum_append]
        _ = weight a z - weight a x := by
          rw [hsumw, ← N.weight_jump a hr, ← hzr]
          ring

theorem phasePath_of_reach (a : κ → ℝ) {x y : State κ} (h : Reach N.toRxn x y) :
    N.PhasePath a x y (weight a y - weight a x) := by
  obtain ⟨w, b, hw, e, hd⟩ := N.word_of_reach a h
  exact ⟨w, b, hw, fun i _ => congrFun e i, hd⟩

theorem phasePath_return (wr : N.WeaklyReversible) (a : κ → ℝ) (x : State κ)
    (r : L) (hr : Enabled (N.directionNet a) (phaseCoords a) r x) :
    N.PhasePath a (N.jump x r) x (-(N.directionNet a).δ r) := by
  let z := x - N.s r
  have hj : N.t r + z = N.jump x r := add_comm _ _
  have hreach := N.complex_copy_reach z (wr r)
  rw [hj] at hreach
  obtain ⟨w, b, hf, he, hd⟩ := N.word_of_reach a hreach
  refine ⟨w, b, hf, ?_, hd.trans ?_⟩
  · intro i hi
    rw [he]
    exact Nat.add_sub_of_le (hr i hi)
  · rw [← hj]
    simp only [weight_add, directionNet]
    ring

theorem phaseEnd_add (a : κ → ℝ) (w : List L) (x z : State κ) {b H : ℝ}
    (h : Feas (N.directionNet a) (phaseCoords a) b x H w) :
    ∀ i ∈ phaseCoords a, endP (N.directionNet a) (x + z) w i =
      endP (N.directionNet a) x w i + z i := by
  let W := N.directionNet a
  induction w generalizing x H with
  | nil => intro i _; rfl
  | cons r w ih =>
    intro i hi
    have hh : ∀ j ∈ phaseCoords a, stepP W r (x + z) j = (stepP W r x + z) j := by
      intro j hj
      have he : W.s r j ≤ x j := h.1 j hj
      simp only [stepP, Pi.add_apply]
      omega
    change endP W (stepP W r (x + z)) w i = endP W (stepP W r x) w i + z i
    rw [AIM272Witness.endP_agree W w _ _ hh i hi]
    exact ih _ h.2.2 i hi

theorem phasePath_add (a : κ → ℝ) {x y : State κ} {d : ℝ} (h : N.PhasePath a x y d)
    (z : State κ) : N.PhasePath a (x + z) (y + z) d := by
  obtain ⟨w, b, hf, he, hd⟩ := h
  refine ⟨w, b, AIM272Witness.feas_le _ w x (x + z) 0 0 hf
    (fun i _ => Nat.le_add_right _ _) le_rfl, ?_, hd⟩
  intro i hi
  rw [N.phaseEnd_add a w x z hf i hi, he i hi]
  rfl

/-- The phase set Y_a of the manuscript. -/
def NegativeLoop (a : κ → ℝ) (x : State κ) : Prop :=
  ∃ d : ℝ, d < 0 ∧ N.PhasePath a x x d

theorem negativeLoop_upward (a : κ → ℝ) {x y : State κ}
    (hx : N.NegativeLoop a x) (hle : x ≤ y) : N.NegativeLoop a y := by
  obtain ⟨d, hd, h⟩ := hx
  have he : x + (y - x) = y := by
    funext i
    exact Nat.add_sub_of_le (hle i)
  exact ⟨d, hd, by simpa only [he] using N.phasePath_add a h (y - x)⟩

private theorem negativeLoop_transport (a : κ → ℝ) {x y : State κ} {d : ℝ}
    (hxy : N.PhasePath a x y d) (hyx : N.PhasePath a y x (-d)) (hx : N.NegativeLoop a x) :
    N.NegativeLoop a y := by
  obtain ⟨e, he, hloop⟩ := hx
  refine ⟨e, he, ?_⟩
  have h := N.phasePath_trans a (N.phasePath_trans a hyx hloop) hxy
  rw [show -d + e + d = e by ring] at h
  exact h

theorem negativeLoop_iff_projected_step (wr : N.WeaklyReversible) (a : κ → ℝ)
    (x : State κ) (r : L) (hr : Enabled (N.directionNet a) (phaseCoords a) r x) :
    N.NegativeLoop a (N.jump x r) ↔ N.NegativeLoop a x := by
  have h := N.phasePath_one a x r hr
  have h' := N.phasePath_return wr a x r hr
  exact ⟨N.negativeLoop_transport a h' (by simpa only [neg_neg] using h),
    N.negativeLoop_transport a h h'⟩

theorem negativeLoop_of_usable (a : κ → ℝ) (ha : ∀ i, 0 ≤ a i)
    {o x : State κ} (huse : Usable N.toRxn o (phaseCoords a)) (hx : x ∈ Γ N.toRxn o) :
    N.NegativeLoop a x := by
  obtain ⟨v, hv, hvne, hvzero⟩ := huse
  have hn : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hvne
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hn
  have ha' : 0 < a i := lt_of_le_of_ne (ha i) (fun eq =>
    hi (hvzero i ((mem_phaseCoords a i).mpr eq.symm)))
  have hweight : 0 < weight a v :=
    Finset.sum_pos' (fun j _ => mul_nonneg (ha j) (Nat.cast_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos ha' (by exact_mod_cast Nat.pos_of_ne_zero hi)⟩
  have holink : N.PhasePath a o (o + v) 0 :=
    N.phasePath_same a (fun j hj => by simp [hvzero j hj])
  have hreturn := N.phasePath_of_reach a (show Reach N.toRxn (o + v) o from hv.2)
  have ho : N.NegativeLoop a o := by
    refine ⟨0 + (weight a o - weight a (o + v)), ?_, N.phasePath_trans a holink hreturn⟩
    rw [weight_add]
    linarith
  exact N.negativeLoop_transport a (N.phasePath_of_reach a hx.1)
    (by simpa only [neg_sub] using N.phasePath_of_reach a hx.2) ho

end AIM272.Network
