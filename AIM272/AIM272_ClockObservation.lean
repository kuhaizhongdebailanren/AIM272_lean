import AIM272_RankedRace

set_option warningAsError true

/-! # Observation of a finite list of ranked thinned clocks -/

noncomputable section
open scoped NNReal ENNReal

namespace AIM272.RankedRace

variable {S : Type}

def raceShare (c ν : ℝ≥0) : ℝ≥0 := c / (c + ν)

theorem raceShare_lt_one (c : ℝ≥0) {ν : ℝ≥0} (hν : 0 < ν) : raceShare c ν < 1 := by
  rw [raceShare, div_lt_one (add_pos_of_nonneg_of_pos (zero_le _) hν)]
  exact lt_add_of_pos_right _ hν

theorem one_half_le_raceShare {c ν : ℝ≥0} (hc : 0 < c) (hν : ν ≤ c) : 1 / 2 ≤ raceShare c ν := by
  rw [raceShare, div_le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)
    (add_pos_of_pos_of_nonneg hc (zero_le _)), one_mul]
  change (c : ℝ) + (ν : ℝ) ≤ (c : ℝ) * 2
  have h : (ν : ℝ) ≤ (c : ℝ) := hν
  linarith

open Classical in
/-- The slowest mark competes with the observation. Between these events
the faster clocks are observed at the sum of the two competing rates.
The list is supplied in decreasing order of relative orders. -/
def observe (clock : ℝ → ℝ≥0) (mark : ℝ → S → PMF S) : List ℝ → ℝ≥0 → S → PMF S
  | [], _, x => PMF.pure x
  | d :: ds, ν, x =>
    if hp : raceShare (clock d) ν < 1 then
      sampled _ hp (observe clock mark ds (clock d + ν)) (mark d) x
    else PMF.pure x

theorem observe_cons (clock : ℝ → ℝ≥0) (mark : ℝ → S → PMF S) (d : ℝ) (ds : List ℝ)
    {ν : ℝ≥0} (hν : 0 < ν) (x : S) :
    observe clock mark (d :: ds) ν x =
      sampled _ (raceShare_lt_one (clock d) hν) (observe clock mark ds (clock d + ν)) (mark d) x := by
  simp only [observe, dif_pos (raceShare_lt_one (clock d) hν)]

theorem observe_stuck {dead : S → Prop} {clock : ℝ → ℝ≥0} {mark : ℝ → S → PMF S}
    (h : ∀ d x, dead x → mark d x = PMF.pure x) (ds : List ℝ) (ν : ℝ≥0) {x : S} (hx : dead x) :
    observe clock mark ds ν x = PMF.pure x := by
  classical
  induction ds generalizing ν with
  | nil => rfl
  | cons d ds ih =>
    simp only [observe]
    split_ifs with hp
    · simp only [sampled, funext (fun n => run_stuck (ih (clock d + ν)) (h d x hx)
        (rankRounds n ++ [.gap])), PMF.bind_const]
    · rfl

theorem fastPath_append {edge : S → S → Prop} {x y z : S}
    (p : FastPath edge x y) (q : FastPath edge y z) : FastPath edge x z := by
  induction p with
  | nil => exact q
  | cons he _ ih => exact .cons he (ih q)

theorem fastPath_mono {edge edge' : S → S → Prop} (h : ∀ x y, edge x y → edge' x y)
    {x y : S} (p : FastPath edge x y) : FastPath edge' x y := by
  induction p with
  | nil => exact .nil _
  | cons he _ ih => exact .cons (h _ _ he) ih

private theorem run_path_support {dead : S → Prop} {edge : S → S → Prop}
    {g m : S → PMF S} (hg : ∀ x, dead x → g x = PMF.pure x) (hm : ∀ x, dead x → m x = PMF.pure x)
    (hgs : ∀ x y, y ∈ (g x).support → dead y ∨ FastPath edge x y)
    (hms : ∀ x y, y ∈ (m x).support → dead y ∨ FastPath edge x y)
    (w : List RaceAction) (x y : S) (hy : y ∈ (run g m w x).support) :
    dead y ∨ FastPath edge x y := by
  induction w generalizing x with
  | nil =>
    have he : y = x := (PMF.mem_support_pure_iff x y).mp hy
    subst y
    exact Or.inr (.nil _)
  | cons a w ih =>
    let step := match a with | .gap => g | .ring => m
    have hs (u v : S) : v ∈ (step u).support → dead v ∨ FastPath edge u v := by
      cases a
      · exact hgs u v
      · exact hms u v
    have hh : y ∈ ((step x).bind (run g m w)).support := by cases a <;> exact hy
    obtain ⟨z, hz, hz'⟩ := (PMF.mem_support_bind_iff _ _ _).mp hh
    rcases hs x z hz with hd | hp
    · rw [run_stuck (hg z hd) (hm z hd)] at hz'
      exact Or.inl (((PMF.mem_support_pure_iff z y).mp hz').symm ▸ hd)
    · exact (ih z hz').imp_right (fastPath_append hp)

def allowedStep (edge : ℝ → S → S → Prop) (ds : List ℝ) (x y : S) : Prop :=
  ∃ d ∈ ds, edge d x y

theorem observe_support {dead : S → Prop} {edge : ℝ → S → S → Prop}
    (clock : ℝ → ℝ≥0) (mark : ℝ → S → PMF S)
    (h : ∀ d x, dead x → mark d x = PMF.pure x)
    (hstep : ∀ d x y, y ∈ (mark d x).support → dead y ∨ x = y ∨ edge d x y)
    (ds : List ℝ) (ν : ℝ≥0) (x y : S) (hy : y ∈ (observe clock mark ds ν x).support) :
    dead y ∨ FastPath (allowedStep edge ds) x y := by
  classical
  induction ds generalizing ν x y with
  | nil =>
    have he : y = x := (PMF.mem_support_pure_iff x y).mp hy
    subst y
    exact Or.inr (.nil _)
  | cons d ds ih =>
    by_cases hp : raceShare (clock d) ν < 1
    · simp only [observe, dif_pos hp, sampled] at hy
      obtain ⟨n, _, hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
      refine run_path_support (w := rankRounds n ++ [.gap]) (x := x) (y := y) ?_ ?_ ?_ ?_ hn
      · exact fun z hd => observe_stuck h ds (clock d + ν) hd
      · exact h d
      · intro u v hv
        exact (ih _ u v hv).imp_right (fastPath_mono fun _ _ ⟨b, hb, he⟩ =>
          ⟨b, List.mem_cons_of_mem _ hb, he⟩)
      · intro u v hv
        rcases hstep d u v hv with hd | rfl | he
        · exact Or.inl hd
        · exact Or.inr (.nil _)
        · exact Or.inr (.cons ⟨d, List.mem_cons_self, he⟩ (.nil _))
    · simp only [observe, dif_neg hp] at hy
      have he := (PMF.mem_support_pure_iff x y).mp hy
      subst y
      exact Or.inr (.nil _)

end AIM272.RankedRace
