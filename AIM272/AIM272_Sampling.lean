import AIM272_RankPaths
import AIM272_ClockObservation

set_option warningAsError true

/-! # Induction for sampling the concrete static targets -/

noncomputable section

open AIM272 RankedRace
open scoped NNReal ENNReal

namespace AIM272.Network

variable {κ L : Type} [Fintype κ] [Fintype L] (N : AIM272.Network κ L)

/-- Relative orders are complete downwards in the set of orders of the network. -/
def CompleteRanks (wr : N.WeaklyReversible) (a : κ → ℝ) (ds : List ℝ) : Prop :=
  ds.Pairwise (· > ·) ∧ (∀ d ∈ ds, d ≤ 0) ∧
    ∀ d ∈ ds, ∀ x r, N.relativeOrder wr a x r ≤ d → N.relativeOrder wr a x r ∈ ds

private theorem CompleteRanks.tail {wr : N.WeaklyReversible} {a : κ → ℝ}
    {d : ℝ} {ds : List ℝ} (h : N.CompleteRanks wr a (d :: ds)) : N.CompleteRanks wr a ds := by
  obtain ⟨hord, hnon, hcover⟩ := h
  obtain ⟨hlt, pair⟩ := List.pairwise_cons.mp hord
  refine ⟨pair, fun u hu => hnon u (List.mem_cons_of_mem _ hu), fun u hu x r hr => ?_⟩
  rcases List.mem_cons.mp (hcover u (List.mem_cons_of_mem _ hu) x r hr) with he | he
  · exact (not_le_of_gt (he.symm ▸ hlt u hu) hr).elim
  · exact he

private theorem fastStep_iff_allowed_tail {wr : N.WeaklyReversible} {a : κ → ℝ}
    {d k : ℝ} {ds : List ℝ} (h : N.CompleteRanks wr a (d :: ds)) (x y : State κ) :
    N.fastStep wr a k d x y ↔ allowedStep (N.rankStep wr a k) ds x y := by
  have hh (q : ℝ) (hq : q ∈ ds) : q < d := (List.pairwise_cons.mp h.1).1 q hq
  constructor
  · rintro ⟨r, hx, hk, hr, hf, he⟩
    have hd : N.relativeOrder wr a x r < d := by simpa only [N.relativeOrder_eq, hk] using hf
    have hm := h.2.2 d List.mem_cons_self x r hd.le
    refine ⟨_, (List.mem_cons.mp hm).resolve_left hd.ne, r, hx, hk, hr, ?_, he⟩
    rw [N.relativeOrder_eq, hk]
  · rintro ⟨q, hq, r, hx, hk, hr, he, rfl⟩
    exact ⟨r, hx, hk, hr, he ▸ hh q hq, rfl⟩

private theorem allowed_cons_iff {wr : N.WeaklyReversible} {a : κ → ℝ}
    {d k : ℝ} {ds : List ℝ} (h : N.CompleteRanks wr a (d :: ds)) (x y : State κ) :
    allowedStep (N.rankStep wr a k) (d :: ds) x y ↔ N.fastStep wr a k d x y ∨ N.rankStep wr a k d x y := by
  constructor
  · rintro ⟨u, hu, he⟩
    rcases List.mem_cons.mp hu with rfl | ht
    · exact Or.inr he
    · exact Or.inl ((N.fastStep_iff_allowed_tail h x y).mpr ⟨u, ht, he⟩)
  · rintro (hf | hr)
    · obtain ⟨u, hu, he⟩ := (N.fastStep_iff_allowed_tail h x y).mp hf
      exact ⟨u, List.mem_cons_of_mem _ hu, he⟩
    · exact ⟨d, List.mem_cons_self, hr⟩

private theorem canReach_of_fastPath {S : Type} {E f c : S → S → Prop} {A : S → Prop}
    (hedge : ∀ x y, E x y → f x y ∨ c x y) {x y : S}
    (p : FastPath E x y) (ha : A y) : ∃ n, canReachWithin f c A x n := by
  have h : ∃ n, CountedPath f c x y n := by
    induction p with
    | nil => exact ⟨0, .nil _⟩
    | cons hp _ ih =>
      obtain ⟨n, hn⟩ := ih ha
      rcases hedge _ _ hp with hf | hc
      · exact ⟨n, .fastStep hf hn⟩
      · exact ⟨n + 1, .currentStep hc hn⟩
  obtain ⟨n, hn⟩ := h
  exact ⟨n, y, n, ha, hn, le_rfl⟩

private theorem uniform_rank_budget {wr : N.WeaklyReversible} {a : κ → ℝ} (A : N.Target wr a) (d : ℝ) :
    ∃ B, ∀ {k x},
      (∃ n, canReachWithin (N.fastStep wr a k d) (N.rankStep wr a k d) (fun y => A.holds y k) x n) →
        canReachWithin (N.fastStep wr a k d) (N.rankStep wr a k d) (fun y => A.holds y k) x B := by
  obtain ⟨B, hB⟩ := N.rank_budget A d
  refine ⟨B, fun {k x} h => ?_⟩
  obtain ⟨b, y, n, hy, hp, hb⟩ := h
  cases hp with
  | nil => exact ⟨_, 0, hy, .nil _, Nat.zero_le _⟩
  | fastStep hf hp =>
    obtain ⟨r, hx, hk, hr, hd, he⟩ := hf
    exact hB hx hk ⟨b, y, _, hy, .fastStep ⟨r, hx, hk, hr, hd, he⟩ hp, hb⟩
  | currentStep hc hp =>
    obtain ⟨r, hx, hk, hr, hd, he⟩ := hc
    exact hB hx hk ⟨b, y, _, hy, .currentStep ⟨r, hx, hk, hr, hd, he⟩ hp, hb⟩

/-- The induction uses only the support, absorbing and label-floor facts
of a family of thinned kernels. These facts are proved for mass action
in AIM272_Thinning. -/
structure LevelClockFamily (wr : N.WeaklyReversible) (a : κ → ℝ) (k : ℝ) (ρ : ℝ≥0) where
  dead : State κ → Prop
  live : ∀ x, ¬ dead x → N.NegativeLoop a x ∧ N.level wr a x = k
  clock : ℝ → ℝ≥0
  clock_pos : ∀ d, 0 < clock d
  mark : ℝ → State κ → PMF (State κ)
  stuck : ∀ d x, dead x → mark d x = PMF.pure x
  support : ∀ d x y, y ∈ (mark d x).support → dead y ∨ x = y ∨ N.rankStep wr a k d x y
  null : ∀ d x, ρ ≤ prob (mark d x) (fun y => dead y ∨ y = x)
  label : ∀ d {x y}, N.rankStep wr a k d x y → ρ ≤ prob (mark d x) (fun z => dead z ∨ z = y)

private theorem finalBlock_pow (ρ : ℝ≥0) (M B : ℕ) :
    finalBlockLower (ρ ^ M) ρ B = ρ ^ (B * (M + 1) + M) := by
  induction B with
  | zero => simp [finalBlockLower]
  | succ B ih =>
    rw [finalBlockLower, ih, ← pow_succ, ← pow_add]
    congr 1
    rw [Nat.succ_mul]
    omega

/-- The power b is chosen from the graph and target before any rates or
the lower probability ρ are fixed. For mass action, ρ is a constant
times R^(-2η). -/
theorem rank_sampling_power (wr : N.WeaklyReversible) (a : κ → ℝ) (ds : List ℝ)
    (hds : N.CompleteRanks wr a ds) (A : N.Target wr a) :
    ∃ b : ℕ, ∀ {ρ : ℝ≥0}, 0 < ρ → ρ ≤ 1 / 2 → ∀ {k : ℝ} (F : N.LevelClockFamily wr a k ρ),
      (∀ u ∈ ds, ∀ v ∈ ds, u < v → 2 * F.clock v ≤ F.clock u) →
      ∀ {ν : ℝ≥0}, 0 < ν → (∀ d ∈ ds, ν ≤ F.clock d) → ∀ x,
        (F.dead x ∨ ∃ y, A.holds y k ∧ FastPath (allowedStep (N.rankStep wr a k) ds) x y) →
        ρ ^ b ≤ prob (observe F.clock F.mark ds ν x) (fun y => F.dead y ∨ A.holds y k) := by
  classical
  induction ds generalizing A with
  | nil =>
    refine ⟨0, fun {ρ} _ _ {k} F _ {ν} _ _ x hx => ?_⟩
    have ht : F.dead x ∨ A.holds x k := by
      rcases hx with hx | ⟨y, hy, p⟩
      · exact Or.inl hx
      · cases p with
        | nil => exact Or.inr hy
        | cons he _ => obtain ⟨u, hu, _⟩ := he; simp at hu
    rw [pow_zero]
    exact (prob_support (PMF.pure x) (fun y hy => ((PMF.mem_support_pure_iff x y).mp hy).symm ▸ ht)).ge
  | cons d ds ih =>
    have hd : d ≤ 0 := hds.2.1 d List.mem_cons_self
    have htail := hds.tail N
    obtain ⟨B, hB⟩ := N.uniform_rank_budget A d
    choose exponent hs using fun T : N.Target wr a => ih htail T
    let M := max (exponent A) ((Finset.range B).sup (fun i => exponent (N.entranceTarget A d i)))
    refine ⟨B + (B * (M + 1) + M), fun {ρ} hρ hρ' {k} F hSep {ν} hν hRate x hx => ?_⟩
    let dead := F.dead
    let mark := F.mark d
    let gap := observe F.clock F.mark ds (F.clock d + ν)
    have hgap_stuck (y) (hy : dead y) : gap y = PMF.pure y :=
      observe_stuck F.stuck ds (F.clock d + ν) hy
    have hgap (u v) (hv : v ∈ (gap u).support) : dead v ∨ FastPath (N.fastStep wr a k d) u v :=
      (observe_support F.clock F.mark F.stuck F.support ds (F.clock d + ν) u v hv).imp_right
        (fastPath_mono fun x y => (N.fastStep_iff_allowed_tail hds x y).mpr)
    let J := kernel gap mark hgap_stuck (F.stuck d) hgap (F.support d)
    have hρ1 : ρ ≤ 1 := hρ'.trans (by norm_num)
    have himp (T : N.Target wr a) (hM : exponent T ≤ M) {u v}
        (p : FastPath (N.fastStep wr a k d) u v) (ht : T.holds v k) :
        ρ ^ M ≤ prob (gap u) (fun y => dead y ∨ T.holds y k) := by
      apply (pow_le_pow_right_of_le_one' hρ1 hM).trans
      apply hs T hρ hρ' F (fun u hu v hv => hSep u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv))
        (add_pos_of_pos_of_nonneg (F.clock_pos d) (zero_le _))
      · intro u hu
        have hlt := (List.pairwise_cons.mp hds.1).1 u hu
        calc
          F.clock d + ν ≤ 2 * F.clock d := by rw [two_mul]; exact add_le_add_left (hRate d List.mem_cons_self) _
          _ ≤ F.clock u := hSep u (List.mem_cons_of_mem _ hu) d List.mem_cons_self hlt
      · exact Or.inr ⟨v, ht, fastPath_mono (fun x y => (N.fastStep_iff_allowed_tail hds x y).mp) p⟩
    have hin : RankSamplingInputs (N.fastStep wr a k d) (N.rankStep wr a k d)
        (fun y => N.level wr a y < k) dead (fun y => A.holds y k) J B (ρ ^ M) ρ := by
      refine ⟨pow_pos hρ M, pow_le_one' hρ1 M, hρ, hρ1, ?_,
        fun p => N.reverse_fast_path hd p, fun _ _ h => N.reverse_or_reach_target A hd h, fun _ h => hB h,
        ?_, ?_, ?_, ?_⟩
      · intro y hlt
        by_contra hn
        exact hlt.ne (F.live y hn).2
      · intro y
        simpa [J, kernel, run, mark] using F.null d y
      · intro u v he
        simpa [J, kernel, run, mark] using F.label d he
      · intro u v hp ht
        simpa [J, kernel, run] using himp A (le_max_left _ _) hp ht
      · intro n u v hn hp hgate
        have hM : exponent (N.entranceTarget A d n) ≤ M :=
          (Finset.le_sup (f := fun i => exponent (N.entranceTarget A d i))
            (Finset.mem_range.mpr hn)).trans (le_max_right _ _)
        have hgate' : (N.entranceTarget A d n).holds v k := by
          rcases hgate with h | ⟨z, ⟨r, _, hk, hr, he, rfl⟩, y, m, hy, hpath, hb⟩
          · exact Or.inl h
          · obtain ⟨w, hw⟩ := N.rankedWord_of_counted hpath hy
            exact Or.inr ⟨r, hk, hr, he, w, m, hw, hb⟩
        have hh := (himp _ hM hp hgate').trans (prob_mono _ (B := fun y => dead y ∨
          gateWithin (fun z => N.level wr a z < k) (N.fastStep wr a k d) (N.rankStep wr a k d)
            (fun y => A.holds y k) n y) (fun y hy => by
          by_cases h : dead y
          · exact Or.inl h
          · exact Or.inr ((N.entranceTarget_iff_gate A (F.live y h).1).mp (hy.resolve_left h))))
        simpa [J, kernel, run] using hh
    rcases hx with hx | ⟨y, hy, path⟩
    · rw [observe_stuck F.stuck _ _ hx]
      apply (pow_le_one' hρ1 _).trans
      exact (prob_support _ (fun y hy => Or.inl (((PMF.mem_support_pure_iff x y).mp hy).symm ▸ hx))).ge
    have hreach := canReach_of_fastPath (A := fun z => A.holds z k)
      (fun u v => (N.allowed_cons_iff hds u v).mp) path hy
    let p := raceShare (F.clock d) ν
    have hp := raceShare_lt_one (F.clock d) hν
    have hpm : ρ ≤ p := hρ'.trans (one_half_le_raceShare (F.clock_pos d) (hRate d List.mem_cons_self))
    have hprob := (rankedClockLowerBound nnrealLaws hin (pow_pos hρ B) hreach
      (prob (sampled p hp gap mark x) (fun y => dead y ∨ A.holds y k)) (by
        intro v hv
        exact (mul_le_mul_right' (pow_le_pow_left' hpm B) v).trans (race_mixture p hp gap mark x _ hv))).2
    rw [observe_cons _ _ _ _ hν, pow_add, ← finalBlock_pow]
    exact hprob

end AIM272.Network
