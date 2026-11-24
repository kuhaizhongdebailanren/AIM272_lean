import Mathlib

/-!
# AIM 272, Section 4: the bounded witness lemma

This file proves Lemma `lem:witness` of the paper (bounded descent witnesses) in full,
including the induction on the number of phase coordinates, and the corollary that
minimal peaks take finitely many values.

## Model

A label `r` has a source `s r` and a target `t r` on the phase coordinates, a height
increment `δ r = a · Δ_r` and a copy offset `g r = -a · s_r`, so that the copy height of
an edge taken at height `H` is `H + g r`. A state is a phase `y : κ → ℕ` and a real
height. Only the coordinates in a finite set `J` are checked for enabling; forgetting a
coordinate means passing from `J` to `J.erase i`.

The landing bound `δ r - g r ≤ S` is `a · t_r ≤ S`, the constant `S` of (4.1).
No hypotheses beyond these data are used.
-/

set_option warningAsError true

noncomputable section

namespace AIM272Witness

/-- Projected network data for a fixed direction. -/
structure Net (κ L : Type) where
  s : L → κ → ℕ
  t : L → κ → ℕ
  δ : L → ℝ
  g : L → ℝ

variable {κ L : Type} (N : Net κ L)

/-- Label `r` is enabled at phase `y` on the coordinates `J`. -/
def Enabled (J : Finset κ) (r : L) (y : κ → ℕ) : Prop := ∀ i ∈ J, N.s r i ≤ y i

/-- Phase after one edge. -/
def stepP (r : L) (y : κ → ℕ) : κ → ℕ := fun i => y i - N.s r i + N.t r i

/-- A word is feasible from `(y, H)` under the cap `b` on the coordinates `J`. -/
def Feas (J : Finset κ) (b : ℝ) : (κ → ℕ) → ℝ → List L → Prop
  | _, _, [] => True
  | y, H, r :: w => Enabled N J r y ∧ H + N.g r ≤ b ∧ Feas J b (stepP N r y) (H + N.δ r) w

/-- Final phase of a word. -/
def endP : (κ → ℕ) → List L → (κ → ℕ)
  | y, [] => y
  | y, r :: w => endP (stepP N r y) w

/-- Height increment of a word. -/
def hsum (w : List L) : ℝ := (w.map N.δ).sum

@[simp] theorem hsum_nil : hsum N ([] : List L) = 0 := by simp [hsum]

@[simp] theorem hsum_cons (r : L) (w : List L) : hsum N (r :: w) = N.δ r + hsum N w := by
  simp [hsum]

theorem hsum_append (u v : List L) : hsum N (u ++ v) = hsum N u + hsum N v := by
  simp [hsum]

theorem endP_append (y : κ → ℕ) (u v : List L) :
    endP N y (u ++ v) = endP N (endP N y u) v := by
  induction u generalizing y with
  | nil => rfl
  | cons r u ih => exact ih _

theorem feas_append (J : Finset κ) (b : ℝ) (u v : List L) :
    ∀ (y : κ → ℕ) (H : ℝ), Feas N J b y H (u ++ v) ↔
      Feas N J b y H u ∧ Feas N J b (endP N y u) (H + hsum N u) v := by
  induction u with
  | nil => intro y H; simp [Feas, endP]
  | cons r u ih =>
    intro y H
    simp only [List.cons_append, Feas, ih, endP, hsum_cons, ← add_assoc]
    tauto

/-- Feasibility is preserved by a larger phase inventory and a lower start. -/
theorem feas_le {J : Finset κ} {b : ℝ} : ∀ (w : List L) (y y' : κ → ℕ) (H H' : ℝ),
    Feas N J b y H w → (∀ i ∈ J, y i ≤ y' i) → H' ≤ H → Feas N J b y' H' w
  | [], _, _, _, _, _, _, _ => trivial
  | r :: w, y, y', H, H', ⟨he, hc, hf⟩, hy, hH => by
    refine ⟨fun i hi => le_trans (he i hi) (hy i hi), by linarith, ?_⟩
    refine feas_le w _ _ _ _ hf (fun i hi => ?_) (by linarith)
    have h1 := he i hi
    have h2 := hy i hi
    simp only [stepP]
    omega

/-- Feasibility is preserved by raising the cap. -/
theorem feas_cap {J : Finset κ} {b b' : ℝ} (hb : b ≤ b') : ∀ (w : List L) (y : κ → ℕ) (H : ℝ),
    Feas N J b y H w → Feas N J b' y H w
  | [], _, _, _ => trivial
  | _ :: w, _, _, ⟨he, hc, hf⟩ => ⟨he, by linarith, feas_cap hb w _ _ hf⟩

/-- Forgetting coordinates preserves feasibility. -/
theorem feas_sub {J J' : Finset κ} {b : ℝ} (hJ : J' ⊆ J) : ∀ (w : List L) (y : κ → ℕ) (H : ℝ),
    Feas N J b y H w → Feas N J' b y H w
  | [], _, _, _ => trivial
  | _ :: w, _, _, ⟨he, hc, hf⟩ => ⟨fun i hi => he i (hJ hi), hc, feas_sub hJ w _ _ hf⟩

/-- Translating heights and the cap by the same constant. -/
theorem feas_shift {J : Finset κ} {b : ℝ} (c : ℝ) : ∀ (w : List L) (y : κ → ℕ) (H : ℝ),
    Feas N J b y H w ↔ Feas N J (b - c) y (H - c) w
  | [], _, _ => Iff.rfl
  | r :: w, y, H => by
    have ih := feas_shift (J := J) (b := b) c w (stepP N r y) (H + N.δ r)
    have e : H - c + N.δ r = H + N.δ r - c := by ring
    simp only [Feas, e]
    rw [ih]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by linarith, h3⟩

/-- Coordinates evolve independently, so agreement on `J` persists. -/
theorem endP_agree {J : Finset κ} : ∀ (w : List L) (y y' : κ → ℕ),
    (∀ i ∈ J, y i = y' i) → ∀ i ∈ J, endP N y w i = endP N y' w i
  | [], _, _, h => h
  | r :: w, y, y', h => endP_agree w _ _ (fun i hi => by simp only [stepP, h i hi])

/-- Restoring a forgotten coordinate with a large inventory. -/
theorem feas_lift [DecidableEq κ] {J : Finset κ} {b : ℝ} {i : κ} (hi : i ∈ J) {sM : ℕ}
    (hsM : ∀ r, N.s r i ≤ sM) : ∀ (w : List L) (y : κ → ℕ) (H : ℝ),
    Feas N (J.erase i) b y H w → 1 + w.length * sM ≤ y i → Feas N J b y H w
  | [], _, _, _, _ => trivial
  | r :: w, y, H, ⟨he, hc, hf⟩, hy => by
    have hs := hsM r
    simp only [List.length_cons, Nat.succ_mul] at hy
    refine ⟨fun j hj => ?_, hc, feas_lift hi hsM w _ _ hf ?_⟩
    · by_cases hji : j = i
      · subst hji
        generalize w.length * sM = X at hy
        omega
      · exact he j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    · simp only [stepP]
      generalize w.length * sM = X at hy ⊢
      omega

/-- The landing height of a nonempty feasible word is at most `b + S`. -/
theorem feas_land {J : Finset κ} {b S : ℝ} (hS : ∀ r, N.δ r - N.g r ≤ S) :
    ∀ (w : List L) (y : κ → ℕ) (H : ℝ), w ≠ [] → Feas N J b y H w → H + hsum N w ≤ b + S
  | [], _, _, h, _ => absurd rfl h
  | [r], _, H, _, ⟨_, hc, _⟩ => by
    have := hS r
    simp only [hsum_cons, hsum_nil]
    linarith
  | r :: r' :: w, _, H, _, ⟨_, _, hf⟩ => by
    have := feas_land hS (r' :: w) _ _ (List.cons_ne_nil _ _) hf
    rw [hsum_cons]
    linarith

/-- `k` repetitions of a word. -/
def rep (seg : List L) : ℕ → List L
  | 0 => []
  | k + 1 => seg ++ rep seg k

theorem rep_length (seg : List L) (k : ℕ) : (rep seg k).length = k * seg.length := by
  induction k with
  | zero => simp [rep]
  | succ k ih => simp [rep, ih, Nat.succ_mul, Nat.add_comm]

theorem hsum_rep (seg : List L) (k : ℕ) : hsum N (rep seg k) = k * hsum N seg := by
  induction k with
  | zero => simp [rep]
  | succ k ih => rw [rep, hsum_append, ih]; push_cast; ring

/-- Repeating a closed phase segment with nonpositive increment. -/
theorem feas_rep {J : Finset κ} {b : ℝ} {seg : List L} {y : κ → ℕ} {H : ℝ}
    (hf : Feas N J b y H seg) (hag : ∀ i ∈ J, endP N y seg i = y i) (hneg : hsum N seg ≤ 0)
    (k : ℕ) : ∀ (y' : κ → ℕ) (H' : ℝ), (∀ i ∈ J, y' i = y i) → H' ≤ H →
      Feas N J b y' H' (rep seg k) := by
  induction k with
  | zero => intros; trivial
  | succ k ih =>
    intro y' H' hy hH
    rw [rep, feas_append]
    refine ⟨feas_le N seg y y' H H' hf (fun i hi => (hy i hi).ge) hH, ih _ _ ?_ (by linarith)⟩
    intro i hi
    rw [endP_agree N seg y' y hy i hi, hag i hi]

/-- A witness: feasible from height zero and descending by at least `u`. -/
def Wit (J : Finset κ) (b u : ℝ) (y : κ → ℕ) (w : List L) : Prop :=
  Feas N J b y 0 w ∧ hsum N w ≤ -u

/-- Witnesses for caps `≤ C` and targets `≤ D` can be shortened to length `≤ B`. -/
def HasBound (J : Finset κ) (C D : ℝ) (B : ℕ) : Prop :=
  ∀ (y : κ → ℕ) (b u : ℝ) (w : List L), b ≤ C → u ≤ D → Wit N J b u y w →
    ∃ w' : List L, w'.length ≤ B ∧ Wit N J b u y w'

theorem HasBound.mono {J : Finset κ} {C D C' D' : ℝ} {B B' : ℕ} (h : HasBound N J C D B)
    (hC : C' ≤ C) (hD : D' ≤ D) (hB : B ≤ B') : HasBound N J C' D' B' := by
  intro y b u w hb hu hw
  obtain ⟨w', hl, hw'⟩ := h y b u w (hb.trans hC) (hu.trans hD) hw
  exact ⟨w', hl.trans hB, hw'⟩

/-- Prefix and suffix of a feasible word. -/
theorem feas_split {J : Finset κ} {b : ℝ} {y : κ → ℕ} {H : ℝ} {w : List L}
    (hf : Feas N J b y H w) (j : ℕ) :
    Feas N J b y H (w.take j) ∧
      Feas N J b (endP N y (w.take j)) (H + hsum N (w.take j)) (w.drop j) := by
  rw [← feas_append]
  rwa [List.take_append_drop]

theorem hsum_take_drop (w : List L) (j : ℕ) :
    hsum N (w.take j) + hsum N (w.drop j) = hsum N w := by
  rw [← hsum_append, List.take_append_drop]

/-- **Bounded witness lemma** (Lemma `lem:witness`). -/
theorem bounded_witness [DecidableEq κ] [Finite L] {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ r, N.δ r - N.g r ≤ S) {sM : ℕ} (hsM : ∀ r i, N.s r i ≤ sM) (J : Finset κ) :
    ∀ C D : ℝ, 0 ≤ C → 0 ≤ D → ∃ B, HasBound N J C D B := by
  induction J using Finset.strongInduction with
  | H J ih =>
  intro C D hC hD
  -- bounds after forgetting one coordinate, with the enlarged parameters (4.3)
  have hlow : ∀ i, ∃ B, i ∈ J → HasBound N (J.erase i) (C + D) (D + C + S) B := by
    intro i
    by_cases hi : i ∈ J
    · obtain ⟨B, hB⟩ := ih _ (Finset.erase_ssubset hi) (C + D) (D + C + S) (by linarith)
        (by linarith)
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose Bf hBf using hlow
  set B1 := J.sup Bf with hB1def
  have hB1 : ∀ i ∈ J, HasBound N (J.erase i) (C + D) (D + C + S) B1 := fun i hi =>
    (hBf i hi).mono N le_rfl le_rfl (Finset.le_sup hi)
  set K := 1 + B1 * sM with hKdef
  -- a large initial inventory: forget the coordinate and restore it
  have big : ∀ (y : κ → ℕ) (b u : ℝ) (w : List L), b ≤ C + D → u ≤ D + C + S →
      (∃ i ∈ J, K ≤ y i) → Wit N J b u y w → ∃ w' : List L, w'.length ≤ B1 ∧ Wit N J b u y w' := by
    rintro y b u w hb hu ⟨i, hi, hK⟩ ⟨hf, hs⟩
    obtain ⟨w', hl, hf', hs'⟩ :=
      hB1 i hi y b u w hb hu ⟨feas_sub N (Finset.erase_subset i J) w y 0 hf, hs⟩
    refine ⟨w', hl, feas_lift N hi (fun r => hsM r i) w' y 0 hf' ?_, hs'⟩
    have : w'.length * sM ≤ B1 * sM := Nat.mul_le_mul_right _ hl
    omega
  set M0 := Fintype.card ({x // x ∈ J} → Fin K) with hM0
  -- number of rounds of a negative loop of length at most `M0`
  obtain ⟨kmax, hk⟩ : ∃ kmax : ℕ, ∀ seg : List L, seg.length ≤ M0 → hsum N seg < 0 →
      C + S + D ≤ kmax * (-hsum N seg) := by
    obtain ⟨m, hm⟩ := ((List.finite_length_le L M0).image
      (fun seg => ⌈(C + S + D) / (-hsum N seg)⌉₊)).bddAbove
    refine ⟨m, fun seg hl hneg => ?_⟩
    have h1 : ⌈(C + S + D) / (-hsum N seg)⌉₊ ≤ m := hm ⟨seg, hl, rfl⟩
    have h2 : (C + S + D) / (-hsum N seg) ≤ m :=
      (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have hpos : 0 < -hsum N seg := by linarith
    rwa [div_le_iff₀ hpos] at h2
  refine ⟨M0 * (kmax + 1) + B1, ?_⟩
  intro y b u w hb hu hw
  suffices main : ∀ n, ∀ w : List L, w.length = n → Wit N J b u y w →
      ∃ w' : List L, w'.length ≤ M0 * (kmax + 1) + B1 ∧ Wit N J b u y w' from
    main _ w rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro w hlen ⟨hf, hs⟩
  by_cases hbig : ∃ i ∈ J, K ≤ y i
  · obtain ⟨w', hl, hw'⟩ := big y b u w (by linarith) (by linarith) hbig ⟨hf, hs⟩
    exact ⟨w', by omega, hw'⟩
  push_neg at hbig
  -- states along the word
  set Y : ℕ → κ → ℕ := fun j => endP N y (w.take j) with hY
  set Hj : ℕ → ℝ := fun j => hsum N (w.take j) with hHj
  have hsplit : ∀ j, Feas N J b y 0 (w.take j) ∧ Feas N J b (Y j) (Hj j) (w.drop j) := by
    intro j
    have := feas_split N hf j
    simpa [hY, hHj] using this
  have hland : ∀ j, j ≤ n → Hj j ≤ C + S := by
    intro j hj
    by_cases h0 : j = 0
    · simp [hHj, h0]; linarith
    · have hne : w.take j ≠ [] := by
        have hl : (w.take j).length = j := by rw [List.length_take]; omega
        intro h
        rw [h, List.length_nil] at hl
        omega
      have := feas_land N hS (w.take j) y 0 hne (hsplit j).1
      simp only [zero_add] at this
      simp only [hHj]
      linarith
  -- (a) the target is reached within the first `M0` steps
  by_cases ha : ∃ j, j ≤ M0 ∧ j ≤ n ∧ Hj j ≤ -u
  · obtain ⟨j, hjM, _, hju⟩ := ha
    refine ⟨w.take j, ?_, (hsplit j).1, hju⟩
    rw [List.length_take]
    have := Nat.min_le_left j w.length
    nlinarith
  push_neg at ha
  -- (b) the phase leaves the cube within the first `M0` steps
  by_cases hb' : ∃ j, j ≤ M0 ∧ j ≤ n ∧ ∃ i ∈ J, K ≤ Y j i
  · obtain ⟨j, hjM, hjn, hex⟩ := hb'
    have hHu := ha j hjM hjn
    have hHS := hland j hjn
    have hsuf := (feas_shift N (J := J) (b := b) (Hj j) (w.drop j) (Y j) (Hj j)).1 (hsplit j).2
    rw [sub_self] at hsuf
    have hsum_eq := hsum_take_drop N w j
    obtain ⟨w'', hl'', hf'', hs''⟩ := big (Y j) (b - Hj j) (u + Hj j) (w.drop j)
      (by linarith) (by linarith) hex ⟨hsuf, by have e : Hj j = hsum N (w.take j) := rfl; linarith⟩
    have hback := (feas_shift N (J := J) (b := b) (Hj j) w'' (Y j) (Hj j)).2 (by rwa [sub_self])
    refine ⟨w.take j ++ w'', ?_, ?_, ?_⟩
    · rw [List.length_append, List.length_take]
      have := Nat.min_le_left j w.length
      nlinarith
    · rw [feas_append]
      exact ⟨(hsplit j).1, by simpa [hY, hHj] using hback⟩
    · rw [hsum_append]
      simp only [hHj] at *
      linarith
  push_neg at hb'
  -- (c) both fail: the first `M0 + 1` phases lie in the cube
  have hMn : M0 < n := by
    by_contra hle
    push_neg at hle
    have := ha n hle le_rfl
    have hwt : w.take n = w := List.take_of_length_le (by omega)
    simp only [hHj, hwt] at this
    linarith
  have key : ∀ i j : ℕ, i < j → j ≤ M0 → (∀ x ∈ J, Y i x = Y j x) →
      ∃ w' : List L, w'.length ≤ M0 * (kmax + 1) + B1 ∧ Wit N J b u y w' := by
    intro i j hij hjM hag
    set seg := (w.take j).drop i with hseg
    have htake : w.take j = w.take i ++ seg := by
      have := List.take_append_drop i (w.take j)
      rw [List.take_take, Nat.min_eq_left hij.le] at this
      exact this.symm
    have hYj : Y j = endP N (Y i) seg := by
      simp only [hY, htake, endP_append]
    have hHjj : Hj j = Hj i + hsum N seg := by
      simp only [hHj, htake, hsum_append]
    have hsegf : Feas N J b (Y i) (Hj i) seg := by
      have := (hsplit j).1
      rw [htake, feas_append] at this
      simpa [hY, hHj] using this.2
    have hseglen : seg.length = j - i := by
      simp only [hseg, List.length_drop, List.length_take]
      omega
    by_cases hnn : 0 ≤ hsum N seg
    · -- delete the closed segment
      have hsuf : Feas N J b (Y i) (Hj i) (w.drop j) :=
        feas_le N _ _ _ _ _ (hsplit j).2 (fun x hx => (hag x hx).ge) (by linarith)
      have hw'f : Feas N J b y 0 (w.take i ++ w.drop j) := by
        rw [feas_append]
        exact ⟨(hsplit i).1, by simpa [hY, hHj] using hsuf⟩
      have hw's : hsum N (w.take i ++ w.drop j) ≤ -u := by
        rw [hsum_append]
        have := hsum_take_drop N w j
        simp only [hHj] at hHjj
        linarith
      have hlt : (w.take i ++ w.drop j).length < n := by
        rw [List.length_append, List.length_take, List.length_drop]
        omega
      exact ihn _ hlt _ rfl ⟨hw'f, hw's⟩
    · -- repeat the negative segment
      push_neg at hnn
      have hrep := feas_rep N hsegf (by
          intro x hx
          rw [← hYj]
          exact (hag x hx).symm) hnn.le kmax (Y i) (Hj i) (fun _ _ => rfl) le_rfl
      have hkk := hk seg (by omega) hnn
      have hHi := hland i (by omega)
      refine ⟨w.take i ++ rep seg kmax, ?_, ?_, ?_⟩
      · rw [List.length_append, List.length_take, rep_length, hseglen]
        have h1 := Nat.min_le_left i w.length
        have h2 : kmax * (j - i) ≤ kmax * M0 := Nat.mul_le_mul_left _ (by omega)
        nlinarith
      · rw [feas_append]
        exact ⟨(hsplit i).1, by simpa [hY, hHj] using hrep⟩
      · rw [hsum_append, hsum_rep]
        simp only [hHj] at hHi
        nlinarith
  -- pigeonhole on the first `M0 + 1` phases
  let f : Fin (M0 + 1) → ({x // x ∈ J} → Fin K) := fun j x =>
    ⟨Y j x, hb' j (by omega) (by omega) x x.2⟩
  obtain ⟨j1, j2, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by rw [Fintype.card_fin]; omega)
  have hag : ∀ x ∈ J, Y j1 x = Y j2 x := by
    intro x hx
    have := congrFun heq ⟨x, hx⟩
    simpa [f] using congrArg Fin.val this
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact key j1 j2 h (by omega) hag
  · exact key j2 j1 h (by omega) (fun x hx => (hag x hx).symm)

/-! ## Minimal peaks take finitely many values -/

/-- Peak copy height of a word started at height `H`. -/
def peak : ℝ → List L → ℝ
  | _, [] => 0
  | H, [r] => H + N.g r
  | H, r :: r' :: w => max (H + N.g r) (peak (H + N.δ r) (r' :: w))

/-- A word is feasible under its own peak. -/
theorem feas_peak {J : Finset κ} {b : ℝ} : ∀ (w : List L) (y : κ → ℕ) (H : ℝ),
    Feas N J b y H w → Feas N J (peak N H w) y H w
  | [], _, _, _ => trivial
  | [_], _, _, ⟨he, _, _⟩ => ⟨he, le_rfl, trivial⟩
  | _ :: r' :: w, _, _, ⟨he, _, hf⟩ =>
    ⟨he, le_max_left _ _, feas_cap N (le_max_right _ _) _ _ _ (feas_peak (r' :: w) _ _ hf)⟩

/-- The peak of a nonempty feasible word is at most the cap. -/
theorem peak_le {J : Finset κ} {b : ℝ} : ∀ (w : List L) (y : κ → ℕ) (H : ℝ), w ≠ [] →
    Feas N J b y H w → peak N H w ≤ b
  | [], _, _, h, _ => absurd rfl h
  | [_], _, _, _, ⟨_, hc, _⟩ => hc
  | _ :: r' :: w, _, _, _, ⟨_, hc, hf⟩ =>
    max_le hc (peak_le (r' :: w) _ _ (List.cons_ne_nil _ _) hf)

/-- Witnesses can be translated by a larger phase inventory. -/
theorem wit_mono {J : Finset κ} {b u : ℝ} {y y' : κ → ℕ} {w : List L}
    (hw : Wit N J b u y w) (hy : ∀ i ∈ J, y i ≤ y' i) : Wit N J b u y' w :=
  ⟨feas_le N w y y' 0 0 hw.1 hy le_rfl, hw.2⟩

/-- **Minimal peaks.** For caps in `(-∞, C]` and targets in `(0, D]` there is one finite set
of real numbers containing the minimal admissible cap of every phase. -/
theorem minimal_peak [DecidableEq κ] [Finite L] {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ r, N.δ r - N.g r ≤ S) {sM : ℕ} (hsM : ∀ r i, N.s r i ≤ sM) (J : Finset κ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ P : Set ℝ, P.Finite ∧ ∀ (y : κ → ℕ) (u : ℝ), 0 < u → u ≤ D →
      (∃ b ≤ C, ∃ w, Wit N J b u y w) →
      ∃ ψ ∈ P, ψ ≤ C ∧ (∃ w, Wit N J ψ u y w) ∧ ∀ b ≤ C, (∃ w, Wit N J b u y w) → ψ ≤ b := by
  obtain ⟨B, hB⟩ := bounded_witness N hS0 hS hsM J C D hC hD
  refine ⟨(fun w => peak N 0 w) '' {w : List L | w.length ≤ B},
    (List.finite_length_le L B).image _, ?_⟩
  intro y u hu huD hadm
  -- every admissible cap dominates an admissible peak of a short word
  have hdom : ∀ b ≤ C, (∃ w, Wit N J b u y w) → ∃ p ∈ (fun w => peak N 0 w) ''
      {w : List L | w.length ≤ B}, p ≤ b ∧ ∃ w, Wit N J p u y w := by
    rintro b hb ⟨w, hw⟩
    obtain ⟨w', hl, hf', hs'⟩ := hB y b u w hb huD hw
    have hne : w' ≠ [] := by
      rintro rfl
      simp only [hsum_nil] at hs'
      linarith
    exact ⟨_, ⟨w', hl, rfl⟩, peak_le N w' y 0 hne hf', w', feas_peak N w' y 0 hf', hs'⟩
  set T := {p | p ∈ (fun w => peak N 0 w) '' {w : List L | w.length ≤ B} ∧ p ≤ C ∧
    ∃ w, Wit N J p u y w} with hT
  have hTfin : T.Finite :=
    ((List.finite_length_le L B).image _).subset (fun p hp => hp.1)
  have hTne : T.Nonempty := by
    obtain ⟨b, hb, hw⟩ := hadm
    obtain ⟨p, hp, hpb, hpw⟩ := hdom b hb hw
    exact ⟨p, hp, hpb.trans hb, hpw⟩
  obtain ⟨ψ, ⟨hψP, hψC, hψw⟩, hmin⟩ := Set.exists_min_image T id hTfin hTne
  refine ⟨ψ, hψP, hψC, hψw, fun b hb hw => ?_⟩
  obtain ⟨p, hp, hpb, hpw⟩ := hdom b hb hw
  exact (hmin p ⟨hp, hpb.trans hb, hpw⟩).trans hpb

end AIM272Witness

end

#print axioms AIM272Witness.bounded_witness
#print axioms AIM272Witness.minimal_peak
