import AIM272_Tails

set_option warningAsError true

/-!
# Coordinatewise controlled paths to the root

The Dickson basis of the communicating class and the minimal nonzero
growth vectors yield two finite families of paths. Translates of the
growth-vector paths lower inventories without accumulating excess.
-/

noncomputable section

open scoped BigOperators
open AIM272Unusable (Step Reach Γ M)

namespace AIM272.Network

variable {κ L : Type} (N : AIM272.Network κ L)

/-- A path of a specified length whose states all lie below the cap. -/
inductive CappedPath (cap : State κ) : State κ → State κ → ℕ → Prop
  | nil {x} : x ≤ cap → CappedPath cap x x 0
  | snoc {x y z n} : CappedPath cap x y n → Step N.toRxn y z → z ≤ cap →
      CappedPath cap x z (n + 1)

theorem cappedPath_mono {cap cap' x y : State κ} {n : ℕ}
    (h : N.CappedPath cap x y n) (hle : cap ≤ cap') : N.CappedPath cap' x y n := by
  induction h with
  | nil hx => exact .nil (hx.trans hle)
  | snoc _ hs hz ih => exact .snoc ih hs (hz.trans hle)

theorem cappedPath_shift {cap x y : State κ} {n : ℕ}
    (h : N.CappedPath cap x y n) (z : State κ) :
    N.CappedPath (cap + z) (x + z) (y + z) n := by
  induction h with
  | nil hx => exact .nil fun i => Nat.add_le_add_right (hx i) _
  | snoc _ hs hz ih =>
    exact .snoc ih (AIM272Unusable.step_shift N.toRxn z hs)
      (fun i => Nat.add_le_add_right (hz i) _)

theorem cappedPath_append {cap x y z : State κ} {m n : ℕ}
    (h : N.CappedPath cap x y m) (h' : N.CappedPath cap y z n) :
    N.CappedPath cap x z (m + n) := by
  induction h' with
  | nil _ => simpa only [Nat.add_zero] using h
  | snoc _ hs hz ih => exact .snoc ih hs hz

variable [Fintype κ]

private theorem reach_has_cappedPath {x y : State κ} (h : Reach N.toRxn x y) :
    ∃ B n : ℕ, n ≤ B ∧ N.CappedPath (x + fun _ => B) x y n := by
  induction h with
  | refl =>
    exact ⟨0, 0, le_rfl, .nil (fun i => Nat.le_add_right _ _)⟩
  | @tail y z _ hs ih =>
    obtain ⟨B, n, hn, hp⟩ := ih
    let C := max (B + 1) (radius z)
    have hC : B + 1 ≤ C := le_max_left _ _
    have hOld : (x + fun _ => B) ≤ (x + fun _ => C) :=
      fun i => Nat.add_le_add_left (B.le_succ.trans hC) (x i)
    have hNew : z ≤ (x + fun _ => C) :=
      fun i => (coordinate_le_radius z i).trans ((le_max_right _ _).trans (Nat.le_add_left _ _))
    exact ⟨C, n + 1, (Nat.succ_le_succ hn).trans hC, .snoc (N.cappedPath_mono hp hOld) hs hNew⟩

/-- G10. Each state in the communicating class has a linear-length path
to the root with a uniformly bounded coordinatewise excess. -/
theorem coordinatewise_descent (o : State κ) :
    ∃ C : ℕ, ∀ x ∈ Γ N.toRxn o, ∃ n : ℕ, n ≤ C * (1 + radius x) ∧
      N.CappedPath (x + fun _ => C) x o n := by
  classical
  let B : Set (State κ) := {x | Minimal (· ∈ Γ N.toRxn o) x}
  let V : Set (State κ) := {v | v ∈ M N.toRxn o ∧ v ≠ 0}
  let D : Set (State κ) := {v | Minimal (· ∈ V) v}
  have hB : B.Finite := (AIM272Unusable.dickson N.toRxn o).1
  have hD : D.Finite :=
    (setOf_minimal_antichain V).finite_of_partiallyWellOrderedOn (Pi.isPWO _)
  letI : Fintype B := hB.fintype
  letI : Fintype D := hD.fintype
  have hFinal (b : B) : ∃ C n : ℕ, n ≤ C ∧ N.CappedPath (b.val + fun _ => C) b.val o n :=
    N.reach_has_cappedPath b.property.1.2
  have hDrop (b : B) (u : D) : ∃ C n : ℕ, n ≤ C ∧
      N.CappedPath (b.val + u.val + fun _ => C) (b.val + u.val) b.val n := by
    have hbo : Reach N.toRxn b.val o := b.property.1.2
    have hob : Reach N.toRxn o b.val := b.property.1.1
    have hu : Reach N.toRxn (o + u.val) o := u.property.1.1.2
    exact N.reach_has_cappedPath ((AIM272Unusable.reach_shift N.toRxn u.val hbo).trans (hu.trans hob))
  choose Cf nf hnf hpFinal using hFinal
  choose Cd nd hnd hpDrop using hDrop
  let C := max (Finset.univ.sup Cf) (Finset.univ.sup (fun p : B × D => Cd p.1 p.2))
  have hCf (b : B) : Cf b ≤ C :=
    (Finset.le_sup (Finset.mem_univ b)).trans (le_max_left _ _)
  have hCd (b : B) (u : D) : Cd b u ≤ C :=
    (Finset.le_sup (f := fun p : B × D => Cd p.1 p.2) (Finset.mem_univ (b, u))).trans (le_max_right _ _)
  let mass (v : State κ) := ∑ i, v i
  have descend (b : B) (k : ℕ) :
      ∀ v ∈ M N.toRxn o, mass v = k → ∃ n, n ≤ C * (k + 1) ∧
        N.CappedPath (b.val + v + fun _ => C) (b.val + v) o n := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv hk
      by_cases hzero : v = 0
      · subst v
        have hl : (b.val + fun _ => Cf b) ≤ (b.val + fun _ => C) :=
          fun i => Nat.add_le_add_left (hCf b) (b.val i)
        refine ⟨nf b, (hnf b).trans ((hCf b).trans ?_), ?_⟩
        · exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
        · simpa only [add_zero] using N.cappedPath_mono (hpFinal b) hl
      · obtain ⟨u, huv, hu⟩ := (Pi.isPWO V).exists_le_minimal (show v ∈ V from ⟨hv, hzero⟩)
        let e : D := ⟨u, hu⟩
        let w := v - u
        have hw : w ∈ M N.toRxn o := AIM272Unusable.sub_mem_M N.toRxn o hv hu.1.1 huv
        have heq : u + w = v := by
          funext i
          exact Nat.add_sub_of_le (huv i)
        have hui : ∃ i, u i ≠ 0 := by
          by_contra hh
          apply hu.1.2
          funext i
          by_contra hi
          exact hh ⟨i, hi⟩
        obtain ⟨i, hi⟩ := hui
        have hpu : 0 < mass u :=
          Finset.sum_pos' (fun j _ => Nat.zero_le (u j))
            ⟨i, Finset.mem_univ _, Nat.pos_of_ne_zero hi⟩
        have hsum : mass v = mass u + mass w := by
          rw [← heq]
          simp only [mass, Pi.add_apply, Finset.sum_add_distrib]
        have hsmall : mass w < k := by omega
        obtain ⟨m, hm, hpw⟩ := ih (mass w) hsmall w hw rfl
        have hs := N.cappedPath_shift (hpDrop b e) w
        have hstart : b.val + e.val + w = b.val + v := by
          change b.val + u + w = b.val + v
          rw [add_assoc, heq]
        have hCap₁ : (b.val + e.val + (fun _ => Cd b e) + w) ≤ (b.val + v + fun _ => C) := by
          have hl := hCd b e
          intro j
          have hj := congrFun heq j
          change b.val j + u j + Cd b e + w j ≤ b.val j + v j + C
          change u j + w j = v j at hj
          omega
        have hCap₂ : (b.val + w + fun _ => C) ≤ (b.val + v + fun _ => C) :=
          fun j => by
            change b.val j + (v j - u j) + C ≤ b.val j + v j + C
            omega
        have hfirst := N.cappedPath_mono hs hCap₁
        rw [hstart] at hfirst
        refine ⟨nd b e + m, ?_, N.cappedPath_append hfirst (N.cappedPath_mono hpw hCap₂)⟩
        calc
          nd b e + m ≤ C + C * (mass w + 1) := Nat.add_le_add ((hnd b e).trans (hCd b e)) hm
          _ ≤ C + C * k := Nat.add_le_add_left (Nat.mul_le_mul_left _ hsmall) _
          _ = C * (k + 1) := by rw [Nat.mul_add, mul_one, Nat.add_comm]
  let E := C * (Fintype.card κ + 1)
  refine ⟨E, fun x hx => ?_⟩
  obtain ⟨b, hb, hbx⟩ := (AIM272Unusable.dickson N.toRxn o).2 x hx
  let v := x - b
  have hv : v ∈ M N.toRxn o := AIM272Unusable.diff_mem_M N.toRxn o hx hb.1 hbx
  have hEq : b + v = x := by
    funext i
    exact Nat.add_sub_of_le (hbx i)
  obtain ⟨n, hn, hp⟩ := descend ⟨b, hb⟩ (mass v) v hv rfl
  change N.CappedPath (b + v + fun _ => C) (b + v) o n at hp
  rw [hEq] at hp
  have hmass : mass v ≤ Fintype.card κ * radius x := by
    calc
      mass v ≤ ∑ _ : κ, radius x := Finset.sum_le_sum fun i _ =>
        (Nat.sub_le _ _).trans (coordinate_le_radius x i)
      _ = Fintype.card κ * radius x := by simp
  have hlen : mass v + 1 ≤ (Fintype.card κ + 1) * (1 + radius x) := by
    nlinarith
  have hCE : C ≤ E := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  refine ⟨n, hn.trans ?_, N.cappedPath_mono hp (fun i => Nat.add_le_add_left hCE (x i))⟩
  change C * (mass v + 1) ≤ (C * (Fintype.card κ + 1)) * (1 + radius x)
  rw [mul_assoc]
  exact Nat.mul_le_mul_left _ hlen

end AIM272.Network
