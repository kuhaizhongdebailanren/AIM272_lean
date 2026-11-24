import AIM272_Levels

set_option warningAsError true

/-! # The phase correction has finite range, while the height level is unbounded -/

noncomputable section
open AIM272Unusable (Γ M Usable)

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

/-- Along a usable growth ray the phase stays fixed and the level increases linearly. -/
theorem level_on_growth_ray (wr : N.WeaklyReversible) (a : κ → ℝ) (ha : ∀ i, 0 ≤ a i)
    {o v : State κ} (hv : v ∈ M N.toRxn o) (hne : v ≠ 0)
    (hphase : ∀ i ∈ phaseCoords a, v i = 0) :
    0 < weight a v ∧ ∀ n : ℕ, o + n • v ∈ Γ N.toRxn o ∧
      N.psi wr a (o + n • v) = N.psi wr a o ∧
      N.level wr a (o + n • v) = N.level wr a o + (n : ℝ) * weight a v := by
  classical
  have huse : Usable N.toRxn o (phaseCoords a) := ⟨v, hv, hne, hphase⟩
  have hex : ∃ i, v i ≠ 0 := by
    by_contra! he
    exact hne (funext he)
  obtain ⟨i, hi⟩ := hex
  have hpos : 0 < a i := (ha i).lt_of_ne' fun h => hi (hphase i ((mem_phaseCoords a i).mpr h))
  have hw : 0 < weight a v := Finset.sum_pos' (fun j _ => mul_nonneg (ha j) (Nat.cast_nonneg _))
    ⟨i, Finset.mem_univ _, mul_pos hpos (by exact_mod_cast Nat.pos_of_ne_zero hi)⟩
  have hmem (n : ℕ) : n • v ∈ M N.toRxn o := by
    induction n with
    | zero => simpa only [zero_smul] using AIM272Unusable.zero_mem_M N.toRxn o
    | succ n ih =>
      rw [succ_nsmul]
      exact AIM272Unusable.add_mem_M N.toRxn o ih hv
  refine ⟨hw, fun n => ⟨hmem n, ?_⟩⟩
  have hψ : N.psi wr a (o + n • v) = N.psi wr a o :=
    N.psi_eq_of_phase_eq wr a (N.negativeLoop_of_usable a ha huse (hmem n))
      (N.negativeLoop_of_usable a ha huse (N.root_mem_class o)) (fun j hj => by simp [hphase j hj])
  have wmultiple (k : ℕ) : weight a (k • v) = (k : ℝ) * weight a v := by
    induction k with
    | zero => simp [weight]
    | succ k ih => rw [succ_nsmul, weight_add, ih, Nat.cast_succ]; ring
  exact ⟨hψ, by simp only [level, weight_add, wmultiple, hψ]; ring⟩

theorem level_unbounded_of_usable (wr : N.WeaklyReversible) (a : κ → ℝ) (ha : ∀ i, 0 ≤ a i)
    {o : State κ} (hu : Usable N.toRxn o (phaseCoords a)) :
    ¬ BddAbove (N.level wr a '' Γ N.toRxn o) := by
  obtain ⟨v, hv, hne, hphase⟩ := hu
  obtain ⟨hw, hray⟩ := N.level_on_growth_ray wr a ha hv hne hphase
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - N.level wr a o) / weight a v)
  have hlarge := (div_lt_iff₀ hw).mp hn
  have hb := hB (Set.mem_image_of_mem _ (hray n).1)
  rw [(hray n).2.2] at hb
  linarith

/-- The reversible pair 0 ⇄ A, with both rate constants equal to one. -/
def oneSpeciesPair : AIM272.Network Unit Bool where
  s r := fun _ => if r then 1 else 0
  t r := fun _ => if r then 0 else 1
  rateConstant _ := 1
  rateConstant_pos _ := zero_lt_one
  distinct r h := by cases r <;> have := congrFun h () <;> simp_all

private theorem pair_wr : oneSpeciesPair.WeaklyReversible := by
  intro r
  apply Relation.ReflTransGen.single
  exact ⟨!r, by cases r <;> rfl, by cases r <;> rfl⟩

private theorem pair_usable : Usable oneSpeciesPair.toRxn 0 (phaseCoords (fun _ => 1)) := by
  refine ⟨fun _ => 1, ⟨Relation.ReflTransGen.single ?_, Relation.ReflTransGen.single ?_⟩, ?_, ?_⟩
  · exact ⟨false, fun _ => Nat.zero_le _, funext fun _ => rfl⟩
  · exact ⟨true, fun _ => le_rfl, funext fun _ => rfl⟩
  · intro h
    have he := congrFun h ()
    exact Nat.one_ne_zero he
  · intro i hi
    have he := (mem_phaseCoords _ i).mp hi
    exact (one_ne_zero he).elim

/-- A concrete counterexample to the literal finite-range requirement for ℓ in G2. -/
theorem level_range_counterexample :
    (oneSpeciesPair.level pair_wr (fun _ => 1) '' Γ oneSpeciesPair.toRxn 0).Infinite := by
  intro hf
  exact oneSpeciesPair.level_unbounded_of_usable pair_wr _ (fun _ => zero_le_one) pair_usable hf.bddAbove

end AIM272.Network
