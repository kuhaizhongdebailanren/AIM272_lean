import AIM272_Directions

set_option warningAsError true

/-!
# Minimal peaks of a concrete projected network

The finite phase basis gives a common cap for repeatable negative loops.
Past a fixed descent depth, such a loop can be appended within the
original cap. This identifies the minimum for one descent with that
for arbitrarily deep descent.
-/

noncomputable section

open scoped BigOperators
open AIM272Witness (Feas Wit endP hsum rep Enabled)

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] (N : AIM272.Network κ L)

def NegativeLoopUnder (a : κ → ℝ) (b : ℝ) (y : State κ) : Prop :=
  ∃ w : List L, Feas (N.directionNet a) (phaseCoords a) b y 0 w ∧
    (∀ i ∈ phaseCoords a, endP (N.directionNet a) y w i = y i) ∧
    hsum (N.directionNet a) w < 0

private theorem has_loop_cap (a : κ → ℝ) {y : State κ} (hy : N.NegativeLoop a y) :
    ∃ b, N.NegativeLoopUnder a b y := by
  obtain ⟨d, hd, w, b, hf, he, hw⟩ := hy
  exact ⟨b, w, hf, he, hw ▸ hd⟩

private theorem loop_under_mono (a : κ → ℝ) {x y : State κ} {b : ℝ}
    (h : N.NegativeLoopUnder a b x) (hxy : x ≤ y) : N.NegativeLoopUnder a b y := by
  obtain ⟨w, hf, he, hd⟩ := h
  refine ⟨w, AIM272Witness.feas_le _ w x y 0 0 hf (fun i _ => hxy i) le_rfl, ?_, hd⟩
  have hadd : x + (y - x) = y := by
    funext i
    exact Nat.add_sub_of_le (hxy i)
  intro i hi
  have he' : endP (N.directionNet a) (x + (y - x)) w i = y i := by
    rw [N.phaseEnd_add a w x (y - x) hf i hi, he i hi]
    exact congrFun hadd i
  simpa only [hadd] using he'

/-- One cap works for a negative loop at every phase in Y_a. -/
theorem uniform_negative_loop_cap (a : κ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, N.NegativeLoop a y → N.NegativeLoopUnder a C y := by
  classical
  let Y : Set (State κ) := {y | N.NegativeLoop a y}
  let B : Set (State κ) := {y | Minimal (· ∈ Y) y}
  have hB : B.Finite :=
    (setOf_minimal_antichain Y).finite_of_partiallyWellOrderedOn (Pi.isPWO _)
  letI : Finite B := hB.to_subtype
  have hex (y : B) : ∃ b, N.NegativeLoopUnder a b y :=
    N.has_loop_cap a y.property.1
  choose cap hcap using hex
  obtain ⟨C, hC⟩ := (Set.finite_range cap).bddAbove
  refine ⟨max 0 C, le_max_left _ _, fun y hy => ?_⟩
  obtain ⟨z, hzy, hz⟩ := (Pi.isPWO Y).exists_le_minimal (show y ∈ Y from hy)
  obtain ⟨w, hf, he, hd⟩ := N.loop_under_mono a (hcap ⟨z, hz⟩) hzy
  have hh : cap ⟨z, hz⟩ ≤ max 0 C := (hC ⟨⟨z, hz⟩, rfl⟩).trans (le_max_right _ _)
  exact ⟨w, AIM272Witness.feas_cap _ hh _ _ _ hf, he, hd⟩

def ArbitrarilyLow (a : κ → ℝ) (b : ℝ) (y : State κ) : Prop :=
  ∀ u : ℝ, 0 < u → ∃ w, Wit (N.directionNet a) (phaseCoords a) b u y w

theorem arbitrarilyLow_of_loop (a : κ → ℝ) {b : ℝ} {y : State κ}
    (h : N.NegativeLoopUnder a b y) : N.ArbitrarilyLow a b y := by
  intro u _
  obtain ⟨w, hf, he, hd⟩ := h
  let W := N.directionNet a
  obtain ⟨k, hk⟩ := exists_nat_gt (u / (-hsum W w))
  have hk' := (div_lt_iff₀ (neg_pos.mpr hd)).mp hk
  refine ⟨rep w k, AIM272Witness.feas_rep _ hf he hd.le k _ _ (fun _ _ => rfl) le_rfl, ?_⟩
  rw [AIM272Witness.hsum_rep]
  linarith

private theorem negativeLoop_at_end (wr : N.WeaklyReversible) (a : κ → ℝ)
    (w : List L) {b : ℝ} {y : State κ} {H : ℝ}
    (hw : Feas (N.directionNet a) (phaseCoords a) b y H w)
    (hy : N.NegativeLoop a y) : N.NegativeLoop a (endP (N.directionNet a) y w) := by
  induction w generalizing y H with
  | nil => exact hy
  | cons r w ih =>
    have hNext := (N.negativeLoop_iff_projected_step wr a y r hw.1).mpr hy
    exact ih hw.2.2 hNext

variable [Fintype L]

private theorem cap_lower_bound (a : κ → ℝ) {b u : ℝ} {y : State κ} {w : List L}
    (hu : 0 < u) (hw : Wit (N.directionNet a) (phaseCoords a) b u y w) :
    -N.maxComplexHeight a ≤ b := by
  cases w with
  | nil =>
    have h := hw.2
    simp only [AIM272Witness.hsum_nil] at h
    linarith
  | cons r w =>
    have h : 0 + (N.directionNet a).g r ≤ b := hw.1.2.1
    have hr := N.sourceHeight_le_max a r
    simp only [zero_add, directionNet] at h
    linarith

theorem descent_depth_iff (wr : N.WeaklyReversible) (a : κ → ℝ) {C D b : ℝ}
    (hC : 0 ≤ C) (hD : C + N.maxComplexHeight a + 1 < D)
    (huniform : ∀ y, N.NegativeLoop a y → N.ArbitrarilyLow a C y)
    {y : State κ} (hy : N.NegativeLoop a y) :
    (∃ w, Wit (N.directionNet a) (phaseCoords a) b D y w) ↔ N.ArbitrarilyLow a b y := by
  have hDpos : 0 < D := by linarith [N.maxComplexHeight_nonneg a]
  refine ⟨?_, fun h => h D hDpos⟩
  rintro ⟨w, hw⟩ u hu
  let W := N.directionNet a
  have hb := N.cap_lower_bound a hDpos hw
  have hEnd := N.negativeLoop_at_end wr a w hw.1 hy
  obtain ⟨v, hv⟩ := huniform _ hEnd u hu
  have hCap : C + hsum W w ≤ b := by
    have hd : hsum W w ≤ -D := hw.2
    linarith
  refine ⟨w ++ v, ?_, ?_⟩
  · change Feas W (phaseCoords a) b y 0 (w ++ v)
    rw [AIM272Witness.feas_append, zero_add]
    refine ⟨hw.1, AIM272Witness.feas_cap W hCap _ _ _ ?_⟩
    have hf := (AIM272Witness.feas_shift W (-hsum W w) v (endP W y w) 0).mp hv.1
    simpa only [sub_neg_eq_add, zero_add] using hf
  · rw [AIM272Witness.hsum_append]
    exact add_le_of_nonpos_of_le (hw.2.trans (neg_nonpos.mpr hDpos.le)) hv.2

/-- Data whose fields are obtained below from the bounded-witness theorem. -/
structure PeakData (a : κ → ℝ) where
  cap : ℝ
  depth : ℝ
  phasePeak : State κ → ℝ
  cap_nonneg : 0 ≤ cap
  depth_large : cap + N.maxComplexHeight a + 1 < depth
  finite_values : (Set.range phasePeak).Finite
  bounds : ∀ y, N.NegativeLoop a y → -N.maxComplexHeight a ≤ phasePeak y ∧ phasePeak y ≤ cap
  depth_iff : ∀ y, N.NegativeLoop a y → ∀ b, phasePeak y ≤ b ↔
    ∃ w, Wit (N.directionNet a) (phaseCoords a) b depth y w
  arbitrary_iff : ∀ y, N.NegativeLoop a y → ∀ b,
    phasePeak y ≤ b ↔ N.ArbitrarilyLow a b y

theorem peakData_exists (wr : N.WeaklyReversible) (a : κ → ℝ) : Nonempty (N.PeakData a) := by
  classical
  obtain ⟨C, hC, hUniform⟩ := N.uniform_negative_loop_cap a
  let D := C + N.maxComplexHeight a + 2
  have hDpos : 0 < D := by dsimp [D]; linarith [N.maxComplexHeight_nonneg a]
  have hDepth : C + N.maxComplexHeight a + 1 < D := by dsimp [D]; linarith
  let W := N.directionNet a
  have hLow (y) (hy : N.NegativeLoop a y) : N.ArbitrarilyLow a C y :=
    N.arbitrarilyLow_of_loop a (hUniform y hy)
  obtain ⟨P, hP, hmin⟩ := AIM272Witness.minimal_peak W (N.maxComplexHeight_nonneg a)
    (N.delta_sub_guard_le_max a) N.source_le_inventoryBound (phaseCoords a) C D hC hDpos.le
  have hpick (y) (hy : N.NegativeLoop a y) :=
    hmin y D hDpos le_rfl ⟨C, le_rfl, hLow y hy D hDpos⟩
  let ψ (y) := if hy : N.NegativeLoop a y then (hpick y hy).choose else 0
  have hψ (y) (hy : N.NegativeLoop a y) :
      ψ y ∈ P ∧ ψ y ≤ C ∧ (∃ w, Wit W (phaseCoords a) (ψ y) D y w) ∧
        (∀ b ≤ C, (∃ w, Wit W (phaseCoords a) b D y w) → ψ y ≤ b) := by
    simpa only [ψ, dif_pos hy] using (hpick y hy).choose_spec
  have hIff (y) (hy : N.NegativeLoop a y) (b : ℝ) :
      ψ y ≤ b ↔ ∃ w, Wit W (phaseCoords a) b D y w := by
    obtain ⟨_, hψC, ⟨w, hw⟩, hleast⟩ := hψ y hy
    refine ⟨fun h => ⟨w, AIM272Witness.feas_cap W h _ _ _ hw.1, hw.2⟩, fun h => ?_⟩
    by_cases hb : b ≤ C
    · exact hleast b hb h
    · exact hψC.trans (le_of_not_ge hb)
  refine ⟨{
    cap := C
    depth := D
    phasePeak := ψ
    cap_nonneg := hC
    depth_large := hDepth
    finite_values := ?_
    bounds := ?_
    depth_iff := hIff
    arbitrary_iff := fun y hy b => (hIff y hy b).trans
      (N.descent_depth_iff wr a hC hDepth hLow hy) }⟩
  · apply (hP.insert 0).subset
    rintro _ ⟨y, rfl⟩
    by_cases hy : N.NegativeLoop a y
    · exact Set.mem_insert_of_mem _ (hψ y hy).1
    · exact Set.mem_insert_iff.mpr (Or.inl (by simp [ψ, hy]))
  · intro y hy
    obtain ⟨_, huv, ⟨_, hw⟩, _⟩ := hψ y hy
    exact ⟨N.cap_lower_bound a hDpos hw, huv⟩

def peaks (wr : N.WeaklyReversible) (a : κ → ℝ) : N.PeakData a :=
  Classical.choice (N.peakData_exists wr a)

def psi (wr : N.WeaklyReversible) (a : κ → ℝ) (x : State κ) : ℝ :=
  (N.peaks wr a).phasePeak x

def level (wr : N.WeaklyReversible) (a : κ → ℝ) (x : State κ) : ℝ :=
  weight a x + N.psi wr a x

theorem psi_finite_values (wr : N.WeaklyReversible) (a : κ → ℝ) :
    (Set.range (N.psi wr a)).Finite :=
  (N.peaks wr a).finite_values

theorem psi_antitone (wr : N.WeaklyReversible) (a : κ → ℝ) {x y : State κ}
    (hx : N.NegativeLoop a x) (hxy : x ≤ y) :
    N.psi wr a y ≤ N.psi wr a x := by
  let Q := N.peaks wr a
  have hy := N.negativeLoop_upward a hx hxy
  obtain ⟨w, hw⟩ := (Q.depth_iff x hx (N.psi wr a x)).mp le_rfl
  exact (Q.depth_iff y hy _).mpr ⟨w, AIM272Witness.wit_mono _ hw
    (fun i _ => hxy i)⟩

theorem psi_eq_of_phase_eq (wr : N.WeaklyReversible) (a : κ → ℝ) {x y : State κ}
    (hx : N.NegativeLoop a x) (hy : N.NegativeLoop a y)
    (hxy : ∀ i ∈ phaseCoords a, x i = y i) : N.psi wr a x = N.psi wr a y := by
  let Q := N.peaks wr a
  have move {z z'} (hz : N.NegativeLoop a z) (hz' : N.NegativeLoop a z')
      (hle : ∀ i ∈ phaseCoords a, z i ≤ z' i) : N.psi wr a z' ≤ N.psi wr a z := by
    obtain ⟨w, hf⟩ := (Q.depth_iff z hz (N.psi wr a z)).mp le_rfl
    exact (Q.depth_iff z' hz' _).mpr ⟨w, AIM272Witness.wit_mono _ hf hle⟩
  exact le_antisymm (move hy hx (fun i hi => (hxy i hi).ge))
    (move hx hy (fun i hi => (hxy i hi).le))

/-- The variational description of the level at the actual initial height. -/
theorem level_le_iff (wr : N.WeaklyReversible) (a : κ → ℝ) {x : State κ}
    (hx : N.NegativeLoop a x) (b : ℝ) :
    N.level wr a x ≤ b ↔
      ∀ u : ℝ, 0 < u → ∃ w, Feas (N.directionNet a) (phaseCoords a) b x (weight a x) w ∧
        hsum (N.directionNet a) w ≤ -u := by
  let W := N.directionNet a
  let Q := N.peaks wr a
  have shift (w : List L) : Feas W (phaseCoords a) b x (weight a x) w ↔
      Feas W (phaseCoords a) (b - weight a x) x 0 w := by
    simpa only [sub_self] using AIM272Witness.feas_shift W (b := b) (weight a x) w x (weight a x)
  constructor
  · intro h u hu
    have hp : Q.phasePeak x ≤ b - weight a x := by
      change weight a x + Q.phasePeak x ≤ b at h
      linarith
    obtain ⟨w, hf, hh⟩ := ((Q.arbitrary_iff x hx _).mp hp) u hu
    exact ⟨w, (shift w).mpr hf, hh⟩
  · intro h
    have hp : Q.phasePeak x ≤ b - weight a x := (Q.arbitrary_iff x hx _).mpr (by
      intro u hu
      obtain ⟨w, hw, hh⟩ := h u hu
      exact ⟨w, (shift w).mp hw, hh⟩)
    change weight a x + Q.phasePeak x ≤ b
    linarith

theorem level_le_max_of_word (wr : N.WeaklyReversible) (a : κ → ℝ) {x y : State κ}
    {b : ℝ} {w : List L} (hx : N.NegativeLoop a x) (hy : N.NegativeLoop a y)
    (hf : Feas (N.directionNet a) (phaseCoords a) b x (weight a x) w)
    (he : endP (N.directionNet a) x w = y)
    (hH : weight a x + hsum (N.directionNet a) w = weight a y) :
    N.level wr a x ≤ max (N.level wr a y) b := by
  let W := N.directionNet a
  let m := max (N.level wr a y) b
  refine (N.level_le_iff wr a hx m).mpr fun u hu => ?_
  have hDepth : 0 < u + max (hsum W w) 0 := by
    linarith [le_max_right (hsum W w) (0 : ℝ)]
  obtain ⟨w', hw', hdepth'⟩ :=
    ((N.level_le_iff wr a hy m).mp (le_max_left _ _)) _ hDepth
  refine ⟨w ++ w', ?_, ?_⟩
  · rw [AIM272Witness.feas_append, he, hH]
    exact ⟨AIM272Witness.feas_cap W (le_max_right _ _) _ _ _ hf, hw'⟩
  · rw [AIM272Witness.hsum_append]
    linarith [le_max_left (hsum W w) (0 : ℝ)]

def copyHeight (a : κ → ℝ) (x : State κ) (r : L) : ℝ :=
  weight a x + (N.directionNet a).g r

omit [Fintype L] in
private theorem feasible_copy_word (a : κ → ℝ) (z : State κ) {c d : State κ}
    (p : Relation.ReflTransGen N.ComplexEdge c d) :
    ∃ w, Feas (N.directionNet a) (phaseCoords a) (weight a z) (c + z) (weight a (c + z)) w ∧
      endP (N.directionNet a) (c + z) w = d + z ∧
      weight a (c + z) + hsum (N.directionNet a) w = weight a (d + z) := by
  let W := N.directionNet a
  induction p with
  | refl => exact ⟨[], trivial, rfl, by simp⟩
  | tail _ hedge ih =>
    obtain ⟨r, rfl, rfl⟩ := hedge
    obtain ⟨w, hf, he, hh⟩ := ih
    have hstep : endP W (N.s r + z) [r] = N.t r + z := by
      funext i
      change (N.s r i + z i) - N.s r i + N.t r i = N.t r i + z i
      omega
    have hs : Feas W (phaseCoords a) (weight a z) (N.s r + z) (weight a (N.s r + z)) [r] := by
      refine ⟨fun i _ => Nat.le_add_right _ _, ?_, trivial⟩
      simp [W, directionNet, weight_add]
    refine ⟨w ++ [r], ?_, ?_, ?_⟩
    · rw [AIM272Witness.feas_append, he, hh]
      exact ⟨hf, hs⟩
    · rw [AIM272Witness.endP_append, he, hstep]
    · rw [AIM272Witness.hsum_append, ← add_assoc, hh]
      simp only [AIM272Witness.hsum_cons, AIM272Witness.hsum_nil, add_zero, weight_add, directionNet]
      ring

/-- The two level inequalities of Section 5 follow from the same-copy return. -/
theorem levels_on_step (wr : N.WeaklyReversible) (a : κ → ℝ) (x : State κ) (r : L)
    (hx : N.NegativeLoop a x) (hr : N.s r ≤ x) :
    N.level wr a (N.jump x r) ≤ max (N.level wr a x) (N.copyHeight a x r) ∧
      N.level wr a x ≤ max (N.level wr a (N.jump x r)) (N.copyHeight a x r) := by
  let W := N.directionNet a
  let y := N.jump x r
  let h := N.copyHeight a x r
  have hEnabled : Enabled W (phaseCoords a) r x := fun i _ => hr i
  have hy : N.NegativeLoop a y := (N.negativeLoop_iff_projected_step wr a x r hEnabled).mpr hx
  have hF : Feas W (phaseCoords a) h x (weight a x) [r] :=
    ⟨hEnabled, le_rfl, trivial⟩
  have hY : weight a x + hsum W [r] = weight a y := by
    have he := N.weight_jump a hr
    simp only [AIM272Witness.hsum_cons, AIM272Witness.hsum_nil, add_zero]
    change weight a y - weight a x = W.δ r at he
    linarith
  refine ⟨?_, N.level_le_max_of_word wr a hx hy hF rfl hY⟩
  let z := x - N.s r
  have hxz : N.s r + z = x := by
    funext i
    exact Nat.add_sub_of_le (hr i)
  have hyz : N.t r + z = y := add_comm _ _
  have hCap : weight a z = h := by
    have h' := congrArg (weight a) hxz
    rw [weight_add] at h'
    change weight a z = weight a x - weight a (N.s r)
    linarith
  obtain ⟨w, hw, he, hh⟩ := N.feasible_copy_word a z (wr r)
  rw [hyz, hCap] at hw
  rw [hxz, hyz] at he hh
  exact N.level_le_max_of_word wr a hy hx hw he hh

theorem faster_step_preserves_level (wr : N.WeaklyReversible) (a : κ → ℝ)
    {x : State κ} {r : L} (hx : N.NegativeLoop a x) (hr : N.s r ≤ x)
    (hfast : N.copyHeight a x r < N.level wr a x) :
    N.level wr a (N.jump x r) = N.level wr a x := by
  obtain ⟨hf, hb⟩ := N.levels_on_step wr a x r hx hr
  rw [max_eq_left hfast.le] at hf
  exact le_antisymm hf ((le_max_iff.mp hb).resolve_right (not_le_of_gt hfast))

def relativeOrder (wr : N.WeaklyReversible) (a : κ → ℝ) (x : State κ) (r : L) : ℝ :=
  (N.directionNet a).g r - N.psi wr a x

theorem relativeOrder_eq (wr : N.WeaklyReversible) (a : κ → ℝ) (x : State κ) (r : L) :
    N.relativeOrder wr a x r = N.copyHeight a x r - N.level wr a x := by
  unfold relativeOrder copyHeight level
  ring

theorem relativeOrders_finite (wr : N.WeaklyReversible) (a : κ → ℝ) :
    (Set.range (fun p : State κ × L => N.relativeOrder wr a p.1 p.2)).Finite := by
  let G := Set.range (N.directionNet a).g
  let P := Set.range (N.psi wr a)
  have hG : G.Finite := Set.finite_range _
  have hP : P.Finite := N.psi_finite_values wr a
  apply ((hG.prod hP).image (fun p : ℝ × ℝ => p.1 - p.2)).subset
  rintro _ ⟨⟨x, r⟩, rfl⟩
  exact ⟨((N.directionNet a).g r, N.psi wr a x), ⟨⟨r, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩

private def levelDrops (wr : N.WeaklyReversible) (a : κ → ℝ) : Set ℝ :=
  {d | 0 < d ∧ ∃ (x : State κ) (r : L), N.s r ≤ x ∧
    d = N.level wr a x - N.level wr a (N.jump x r)}

private theorem levelDrops_finite (wr : N.WeaklyReversible) (a : κ → ℝ) :
    (N.levelDrops wr a).Finite := by
  let D := Set.range (N.directionNet a).δ
  let P := Set.range (N.psi wr a)
  have hD : D.Finite := Set.finite_range _
  have hP : P.Finite := N.psi_finite_values wr a
  apply ((hD.prod (hP.prod hP)).image (fun p : ℝ × (ℝ × ℝ) => -p.1 + p.2.1 - p.2.2)).subset
  rintro d ⟨_, x, r, hr, rfl⟩
  refine ⟨((N.directionNet a).δ r, N.psi wr a x, N.psi wr a (N.jump x r)),
    ⟨⟨r, rfl⟩, ⟨⟨x, rfl⟩, ⟨_, rfl⟩⟩⟩, ?_⟩
  have h := N.weight_jump a hr
  simp only [level]
  linarith

theorem level_drop_gap (wr : N.WeaklyReversible) (a : κ → ℝ) :
    ∃ g : ℝ, 0 < g ∧ ∀ (x : State κ) (r : L), N.s r ≤ x →
      N.level wr a (N.jump x r) < N.level wr a x →
        g ≤ N.level wr a x - N.level wr a (N.jump x r) := by
  classical
  by_cases hne : (N.levelDrops wr a).Nonempty
  · obtain ⟨g, hg, hmin⟩ := Set.exists_min_image (N.levelDrops wr a) id (N.levelDrops_finite wr a) hne
    exact ⟨g, hg.1, fun x r hr hl => hmin _ ⟨sub_pos.mpr hl, x, r, hr, rfl⟩⟩
  · exact ⟨1, zero_lt_one, fun x r hr hl => (hne ⟨_,
      sub_pos.mpr hl, x, r, hr, rfl⟩).elim⟩

end AIM272.Network
