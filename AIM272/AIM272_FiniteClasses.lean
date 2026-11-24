import AIM272_Main

set_option warningAsError true

/-! # Finite communicating classes and one-point stationary distributions -/

noncomputable section
open AIM272.ContinuousTime AIM272Unusable
open scoped NNReal ENNReal

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

private theorem reach_eq_of_zero_rate {x y : State κ} (hq : N.totalRate x = 0)
    (h : Reach N.toRxn x y) : y = x := by
  induction h with
  | refl => rfl
  | @tail y z _ hstep ih =>
    have hy : N.totalRate y = 0 := ih.symm ▸ hq
    obtain ⟨r, hr, _⟩ := hstep
    have hp := ((N.rate_pos_iff y r).mpr hr).trans_le (N.rate_le_totalRate y r)
    rw [hy] at hp
    exact (lt_irrefl _ hp).elim

private theorem totalRate_floor_of_positive_root (o : State κ) (ho : N.totalRate o ≠ 0) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ x ∈ Γ N.toRxn o, c ≤ N.totalRate x := by
  classical
  have hank (x : State κ) (hx : N.totalRate x ≠ 0) : ∃ r, N.s r ≤ x := by
    by_contra! habs
    apply hx
    apply Finset.sum_eq_zero
    intro r _
    exact le_antisymm (le_of_not_gt (fun hp => habs r ((N.rate_pos_iff x r).mp hp))) (zero_le _)
  obtain ⟨r, _⟩ := hank o ho
  obtain ⟨r₀, _, hr₀⟩ := Finset.exists_min_image Finset.univ N.rateConstant ⟨r, Finset.mem_univ r⟩
  refine ⟨N.rateConstant r₀, N.rateConstant_pos r₀, fun x hx => ?_⟩
  have hp : N.totalRate x ≠ 0 := by
    intro hz
    have h := N.reach_eq_of_zero_rate hz hx.2
    exact ho (h.symm ▸ hz)
  obtain ⟨r', hr'⟩ := hank x hp
  exact (hr₀ r' (Finset.mem_univ r')).trans ((N.rateConstant_le_rate hr').trans (N.rate_le_totalRate x r'))

/-- A finite nonabsorbing class has the same continuous-time conclusion and unique excursion law. -/
theorem t3_finite_class (wr : N.WeaklyReversible) (o : State κ)
    (hfinite : (Γ N.toRxn o).Finite) (hroot : N.totalRate o ≠ 0)
    (norris : NorrisJumpReturn (State κ)) :
    NonexplosiveOn N.transition N.totalRate (Γ N.toRxn o) ∧
    PositiveRecurrentOn N.transition N.totalRate (Γ N.toRxn o) N.aliveMass ∧
    StationaryOn N.transition N.totalRate (Γ N.toRxn o) (N.normalizedOccupation o) ∧
    ∀ π, StationaryOn N.transition N.totalRate (Γ N.toRxn o) π → π = N.normalizedOccupation o := by
  classical
  obtain ⟨c, hc, hC⟩ := N.totalRate_floor_of_positive_root o hroot
  apply norris N.transition N.totalRate (Γ N.toRxn o) o N.aliveMass N.transition_tsum
    (fun x hx => N.transition_self_of_enabled (hc.trans_le (hC x hx)).ne')
    (fun _ hx _ hxy => N.t0_transition_closed wr o hx hxy)
    _ (N.root_mem_class o) ⟨c, hc, hC⟩
    (fun r z => by by_cases he : z = r <;> simp [aliveMass, he])
    (fun r n z => by by_cases he : z = r <;> simp [aliveMass, he])
    (N.t2_finite_class wr o hfinite)
  intro x hx y hy
  exact (N.class_reach hx hy).mono (fun _ _ h => N.transition_pos_of_step h)

open Classical in
def diracLaw (o : State κ) (y : State κ) : ℝ≥0∞ :=
  if y = o then 1 else 0

theorem minimalTransition_at_absorbing (o : State κ) (h : N.totalRate o = 0) (t : ℝ) (y : State κ) :
    minimalTransition N.transition N.totalRate t o y = diracLaw o y := by
  classical
  rw [minimalTransition, tsum_eq_single 0]
  · by_cases he : y = o
    · subst y
      simp [finiteJumpTerm, diracLaw, h]
    · simp [finiteJumpTerm, diracLaw, he, Ne.symm he]
  · intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n => simp [finiteJumpTerm, h]

/-- An absorbing root has an explicit nonexplosive, unique point distribution. -/
theorem t3_absorbing_class (o : State κ) (hroot : N.totalRate o = 0) :
    NonexplosiveOn N.transition N.totalRate (Γ N.toRxn o) ∧
    StationaryOn N.transition N.totalRate (Γ N.toRxn o) (diracLaw o) ∧
    ∀ π, StationaryOn N.transition N.totalRate (Γ N.toRxn o) π → π = diracLaw o := by
  classical
  have hclass (z : State κ) (hz : z ∈ Γ N.toRxn o) : z = o :=
    N.reach_eq_of_zero_rate hroot hz.1
  have hsum : (∑' y, diracLaw o y) = 1 := by simp [diracLaw, tsum_ite_eq]
  refine ⟨fun x hx t _ => ?_, ⟨hsum, ?_, ?_⟩, ?_⟩
  · have h := hclass x hx
    subst x
    simp only [N.minimalTransition_at_absorbing o hroot t, hsum]
  · intro x hx
    have he : x ≠ o := fun e => hx (e.symm ▸ N.root_mem_class o)
    simp [diracLaw, he]
  · intro t _ y
    rw [tsum_eq_single o]
    · rw [N.minimalTransition_at_absorbing o hroot t]
      simp [diracLaw]
    · intro z hz
      simp [diracLaw, hz]
  · intro π hπ
    have hz (z : State κ) (hz : z ≠ o) : π z = 0 :=
      hπ.2.1 z (fun hc => hz (hclass z hc))
    have ho : π o = 1 := (tsum_eq_single o hz).symm.trans hπ.1
    funext z
    by_cases he : z = o
    · subst z
      simp [diracLaw, ho]
    · simp [diracLaw, he, hz z he]

end AIM272.Network
