import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Weak reversibility and absolute concentration robustness

The uniform steady-state bounds and the rate/point scaling argument are proved
for finite mass-action networks over the real numbers. The final theorems take
the positive steady-state existence theorem of Boros (2019, Theorem 1,
DOI 10.1137/17M115534X) as an explicit hypothesis.

In a mathlib v4.19.0 project, run: lake env lean /path/to/WACR.lean
-/

open scoped BigOperators Topology
open Filter

noncomputable section

namespace WACR

abbrev Point (n : ℕ) := Fin n → ℝ

def Positive {n : ℕ} (x : Point n) : Prop := ∀ i, 0 < x i

def monomial {n : ℕ} (x : Point n) (y : Fin n → ℕ) : ℝ :=
  ∏ i, x i ^ y i

private theorem monomial_pos {n : ℕ} {x : Point n} (hx : Positive x)
    (y : Fin n → ℕ) : 0 < monomial x y :=
  Finset.prod_pos fun i _ => pow_pos (hx i) _

def dot {n : ℕ} (u : Point n) : Point n →ₗ[ℝ] ℝ where
  toFun x := ∑ i, u i * x i
  map_add' x y := by simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

private theorem dot_apply {n : ℕ} (u x : Point n) :
    dot u x = ∑ i, u i * x i := rfl

private theorem continuous_dot_left {n : ℕ} (x : Point n) :
    Continuous (fun u : Point n => dot u x) := by
  simp only [dot_apply]
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const

private theorem monomial_exp {n : ℕ} (a : ℝ) (u : Point n) (y : Fin n → ℕ) :
    monomial (fun i => Real.exp (a * u i)) y =
      Real.exp (a * dot u (fun i => (y i : ℝ))) := by
  rw [dot_apply, Finset.mul_sum, Real.exp_sum]
  unfold monomial
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Complexes, reactions and linkage classes are indexed by finite types.
Each reaction connects two complexes in the same linkage class. -/
structure Network (n c r l : ℕ) where
  complex : Fin c → Fin n → ℕ
  source : Fin r → Fin c
  target : Fin r → Fin c
  linkage : Fin c → Fin l
  sameLink : ∀ q, linkage (source q) = linkage (target q)

namespace Network

variable {n c r l : ℕ} (N : Network n c r l)

def Edge (a b : Fin c) : Prop :=
  ∃ q, N.source q = a ∧ N.target q = b

/-- The graph induced by each linkage class is strongly connected. -/
def WeaklyReversible : Prop :=
  ∀ a b, N.linkage a = N.linkage b → Relation.ReflTransGen N.Edge a b

def reactionClass (q : Fin r) : Fin l := N.linkage (N.source q)

def reactionsIn (k : Fin l) : Finset (Fin r) :=
  Finset.univ.filter (fun q => N.reactionClass q = k)

private theorem mem_reactionsIn {k : Fin l} {q : Fin r} :
    q ∈ N.reactionsIn k ↔ N.reactionClass q = k := by
  simp [reactionsIn]

def complexVector (a : Fin c) : Point n := fun i => N.complex a i

def change (q : Fin r) : Point n :=
  N.complexVector (N.target q) - N.complexVector (N.source q)

def stoich : Submodule ℝ (Point n) := Submodule.span ℝ (Set.range N.change)

def compatible (b x : Point n) : Prop := Positive x ∧ x - b ∈ N.stoich

def classField (κ : Fin r → ℝ) (k : Fin l) (x : Point n) : Point n :=
  ∑ q ∈ N.reactionsIn k, (κ q * monomial x (N.complex (N.source q))) • N.change q

def field (κ : Fin r → ℝ) (x : Point n) : Point n :=
  ∑ k, N.classField κ k x

/-- The grouping by linkage class agrees with the ordinary mass-action sum. -/
theorem field_eq_sum (κ : Fin r → ℝ) (x : Point n) :
    N.field κ x =
      ∑ q, (κ q * monomial x (N.complex (N.source q))) • N.change q := by
  unfold field classField reactionsIn
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

def scaleRates (κ : Fin r → ℝ) (α : Fin l → ℝ) (q : Fin r) : ℝ :=
  α (N.reactionClass q) * κ q

private theorem classField_scale (κ : Fin r → ℝ) (α : Fin l → ℝ)
    (k : Fin l) (x : Point n) :
    N.classField (N.scaleRates κ α) k x = α k • N.classField κ k x := by
  unfold classField
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [N.mem_reactionsIn] at hq
  simp only [scaleRates, hq, mul_assoc, mul_smul]

def height (u : Point n) (a : Fin c) : ℝ := dot u (N.complexVector a)

private theorem dot_change (u : Point n) (q : Fin r) :
    dot u (N.change q) = N.height u (N.target q) - N.height u (N.source q) :=
  (dot u).map_sub _ _

private theorem dot_classField (κ : Fin r → ℝ) (u : Point n) (k : Fin l)
    (x : Point n) :
    dot u (N.classField κ k x) =
      ∑ q ∈ N.reactionsIn k,
        κ q * monomial x (N.complex (N.source q)) * dot u (N.change q) := by
  simp [classField, map_sum, smul_eq_mul]

def ClassFlat (u : Point n) (k : Fin l) : Prop :=
  ∀ a b, N.linkage a = k → N.linkage b = k → N.height u a = N.height u b

private theorem dot_change_of_flat {u : Point n} {k : Fin l} (h : N.ClassFlat u k)
    {q : Fin r} (hq : q ∈ N.reactionsIn k) : dot u (N.change q) = 0 := by
  have hs := (N.mem_reactionsIn.mp hq)
  have ht : N.linkage (N.target q) = k := (N.sameLink q).symm.trans hs
  rw [N.dot_change, h _ _ ht hs, sub_self]

private theorem edge_exits {a b : Fin c} (p : Relation.ReflTransGen N.Edge a b)
    (low : Fin c → Prop) (ha : low a) :
    ¬ low b → ∃ q, low (N.source q) ∧ ¬ low (N.target q) := by
  induction p with
  | refl => exact fun h => (h ha).elim
  | @tail v w _ edge ih =>
    intro hw
    by_cases hv : low v
    · obtain ⟨q, hqv, hqw⟩ := edge
      exact ⟨q, hqv ▸ hv, hqw ▸ hw⟩
    · exact ih hv

/-- A nonconstant linkage class has an ascending reaction out of its minimum
height level. Every descending reaction in that class starts higher. -/
private theorem ascending_minimum (wr : N.WeaklyReversible) (u : Point n) (k : Fin l)
    (hf : ¬ N.ClassFlat u k) :
    ∃ q₀ ∈ N.reactionsIn k, 0 < dot u (N.change q₀) ∧
      ∀ q ∈ N.reactionsIn k, dot u (N.change q) < 0 →
        N.height u (N.source q₀) < N.height u (N.source q) := by
  classical
  unfold ClassFlat at hf
  push_neg at hf
  obtain ⟨a, b, ha, hb, hab⟩ := hf
  let nodes := Finset.univ.filter (fun v => N.linkage v = k)
  have hn : ∀ v : Fin c, v ∈ nodes ↔ N.linkage v = k := by
    intro v
    simp [nodes]
  obtain ⟨v₀, hv₀, hmin⟩ :=
    Finset.exists_min_image nodes (N.height u) ⟨a, (hn a).mpr ha⟩
  let low := fun v => N.linkage v = k ∧ N.height u v = N.height u v₀
  have hvLow : low v₀ := ⟨(hn v₀).mp hv₀, rfl⟩
  have hex : ∃ v, N.linkage v = k ∧ ¬ low v := by
    by_cases h : low a
    · exact ⟨b, hb, fun h' => hab (h.2.trans h'.2.symm)⟩
    · exact ⟨a, ha, h⟩
  obtain ⟨v, hv, hvHigh⟩ := hex
  obtain ⟨q₀, hs₀, ht₀⟩ :=
    N.edge_exits (wr _ _ (hvLow.1.trans hv.symm)) low hvLow hvHigh
  have hqt : N.linkage (N.target q₀) = k := (N.sameLink q₀).symm.trans hs₀.1
  have hgt : N.height u v₀ < N.height u (N.target q₀) :=
    lt_of_le_of_ne (hmin _ ((hn _).mpr hqt)) (fun eq => ht₀ ⟨hqt, eq.symm⟩)
  refine ⟨q₀, N.mem_reactionsIn.mpr hs₀.1, ?_, ?_⟩
  · rw [N.dot_change, hs₀.2]
    exact sub_pos.mpr hgt
  · intro q hq hneg
    have ht : N.linkage (N.target q) = k :=
      (N.sameLink q).symm.trans (N.mem_reactionsIn.mp hq)
    rw [N.dot_change] at hneg
    rw [hs₀.2]
    exact lt_of_le_of_lt (hmin _ ((hn _).mpr ht)) (sub_neg.mp hneg)

private theorem monomial_ratio_tendsto_zero
    {x u : ℕ → Point n} {L : ℕ → ℝ} {v : Point n}
    (hx : ∀ j i, x j i = Real.exp (-L j * u j i))
    (hL : Tendsto L atTop atTop) (hu : Tendsto u atTop (𝓝 v))
    {a b : Fin c} (hab : N.height v b < N.height v a) :
    Tendsto (fun j => monomial (x j) (N.complex a) /
      monomial (x j) (N.complex b)) atTop (𝓝 0) := by
  have hh (w : Fin c) :
      Tendsto (fun j => N.height (u j) w) atTop (𝓝 (N.height v w)) :=
    ((continuous_dot_left (N.complexVector w)).tendsto v).comp hu
  have hd := (hh a).sub (hh b)
  have hinf := hL.atTop_mul_pos (sub_pos.mpr hab) hd
  have hdec := tendsto_neg_atTop_atBot.comp hinf
  have hexp := Real.tendsto_exp_atBot.comp hdec
  convert hexp using 1
  ext j
  have hxj : x j = fun i => Real.exp (-L j * u j i) := funext (hx j)
  simp only [Function.comp_apply, hxj, monomial_exp]
  change Real.exp (-L j * N.height (u j) a) / Real.exp (-L j * N.height (u j) b) =
    Real.exp (-(L j * (N.height (u j) a - N.height (u j) b)))
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Positive projections in the escaping logarithmic direction persist under
any positive class multipliers, since the proof compares terms within a class. -/
private theorem eventually_positive_class
    (wr : N.WeaklyReversible) {κ : Fin r → ℝ} (hκ : ∀ q, 0 < κ q)
    {x u : ℕ → Point n} {L : ℕ → ℝ} {v : Point n}
    (hx : ∀ j i, x j i = Real.exp (-L j * u j i))
    (hL : Tendsto L atTop atTop) (hu : Tendsto u atTop (𝓝 v))
    (k : Fin l) (hf : ¬ N.ClassFlat v k) :
    ∀ᶠ j in atTop, 0 < dot v (N.classField κ k (x j)) := by
  classical
  obtain ⟨q₀, hq₀, hqpos, hmin⟩ := N.ascending_minimum wr v k hf
  let d (q : Fin r) := dot v (N.change q)
  let weight (j : ℕ) (q : Fin r) := monomial (x j) (N.complex (N.source q))
  let term (j : ℕ) (q : Fin r) := κ q * (weight j q / weight j q₀) * d q
  let desc := (N.reactionsIn k).filter (fun q => d q < 0)
  let rest := (N.reactionsIn k).filter (fun q => ¬ d q < 0)
  have hw (j q) : 0 < weight j q :=
    monomial_pos (fun i => hx j i ▸ Real.exp_pos _) _
  have hterm₀ (j) : term j q₀ = κ q₀ * d q₀ := by
    simp [term, (hw j q₀).ne']
  have hdesc : Tendsto (fun j => ∑ q ∈ desc, term j q) atTop (𝓝 0) := by
    have h (q : Fin r) (hq : q ∈ desc) : Tendsto (fun j => term j q) atTop (𝓝 0) := by
      obtain ⟨hqk, hqd⟩ := Finset.mem_filter.mp hq
      have hratio := N.monomial_ratio_tendsto_zero hx hL hu (hmin q hqk hqd)
      simpa [term, weight] using ((hratio.const_mul (κ q)).mul_const (d q))
    simpa using tendsto_finset_sum desc h
  have hconst : 0 < κ q₀ * d q₀ := mul_pos (hκ q₀) hqpos
  have hlimit :
      Tendsto (fun j => κ q₀ * d q₀ + ∑ q ∈ desc, term j q)
        atTop (𝓝 (κ q₀ * d q₀)) := by
    simpa using hdesc.const_add (κ q₀ * d q₀)
  filter_upwards [hlimit.eventually (lt_mem_nhds hconst)] with j hj
  have hrest (q) (hq : q ∈ rest) : 0 ≤ term j q := by
    have hqd := le_of_not_gt (Finset.mem_filter.mp hq).2
    exact mul_nonneg (mul_nonneg (hκ q).le (div_nonneg (hw j q).le (hw j q₀).le)) hqd
  have hqrest : q₀ ∈ rest := Finset.mem_filter.mpr ⟨hq₀, not_lt.mpr hqpos.le⟩
  have hlower := Finset.single_le_sum (f := term j) hrest hqrest
  rw [hterm₀] at hlower
  have hsplit :
      (∑ q ∈ desc, term j q) + (∑ q ∈ rest, term j q) =
        ∑ q ∈ N.reactionsIn k, term j q :=
    Finset.sum_filter_add_sum_filter_not (N.reactionsIn k) (fun q => d q < 0) (term j)
  have hnorm : (∑ q ∈ N.reactionsIn k, term j q) =
      dot v (N.classField κ k (x j)) / weight j q₀ := by
    rw [N.dot_classField]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q _
    simp only [term, weight, d, div_eq_mul_inv]
    ring
  have hpos : 0 < dot v (N.classField κ k (x j)) / weight j q₀ := by
    rw [← hnorm, ← hsplit]
    exact lt_of_lt_of_le (show 0 < κ q₀ * d q₀ + ∑ q ∈ desc, term j q from hj)
      (by linarith)
  exact (div_pos_iff_of_pos_right (hw j q₀)).mp hpos

private theorem no_escaping_steady_sequence
    (wr : N.WeaklyReversible) {κ : Fin r → ℝ} (hκ : ∀ q, 0 < κ q)
    {b : Point n} (hb : Positive b)
    {α : ℕ → Fin l → ℝ} {x u : ℕ → Point n} {L : ℕ → ℝ} {v : Point n}
    (hα : ∀ j k, 0 < α j k) (hcompat : ∀ j, N.compatible b (x j))
    (hsteady : ∀ j, N.field (N.scaleRates κ (α j)) (x j) = 0)
    (hx : ∀ j i, x j i = Real.exp (-L j * u j i))
    (hL : Tendsto L atTop atTop) (hu : Tendsto u atTop (𝓝 v)) (hv : ‖v‖ = 1) :
    False := by
  classical
  have hproj (k : Fin l) : ∀ᶠ j in atTop,
      0 ≤ dot v (N.classField κ k (x j)) ∧
        (¬ N.ClassFlat v k → 0 < dot v (N.classField κ k (x j))) := by
    by_cases hf : N.ClassFlat v k
    · apply Eventually.of_forall
      intro j
      have hzero : dot v (N.classField κ k (x j)) = 0 := by
        rw [N.dot_classField]
        apply Finset.sum_eq_zero
        intro q hq
        rw [N.dot_change_of_flat hf hq, mul_zero]
      exact ⟨hzero.ge, fun hn => (hn hf).elim⟩
    · filter_upwards [N.eventually_positive_class wr hκ hx hL hu k hf] with j hj
      exact ⟨hj.le, fun _ => hj⟩
  have hall : ∀ᶠ j in atTop, ∀ k,
      0 ≤ dot v (N.classField κ k (x j)) ∧
        (¬ N.ClassFlat v k → 0 < dot v (N.classField κ k (x j))) :=
    Filter.eventually_all.mpr hproj
  obtain ⟨j, hj⟩ := hall.exists
  have hz :
      (∑ k, α j k * dot v (N.classField κ k (x j))) = 0 := by
    simpa [field, N.classField_scale, smul_eq_mul] using congrArg (dot v) (hsteady j)
  have hflat (k : Fin l) : N.ClassFlat v k := by
    by_contra hn
    have hpos : 0 < ∑ t, α j t * dot v (N.classField κ t (x j)) :=
      Finset.sum_pos' (fun t _ => mul_nonneg (hα j t).le (hj t).1)
        ⟨k, Finset.mem_univ _, mul_pos (hα j k) ((hj k).2 hn)⟩
    exact hpos.ne' hz
  have hker : N.stoich ≤ LinearMap.ker (dot v) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact LinearMap.mem_ker.mpr
      (N.dot_change_of_flat (hflat (N.reactionClass q)) (N.mem_reactionsIn.mpr rfl))
  have hz' (j : ℕ) : (∑ i, v i * (x j i - b i)) = 0 := by
    simpa only [dot_apply, Pi.sub_apply] using
      LinearMap.mem_ker.mp (hker (hcompat j).2)
  have hfactor (i : Fin n) : ∀ᶠ j in atTop,
      v i * (x j i - b i) ≤ 0 ∧ (v i ≠ 0 → v i * (x j i - b i) < 0) := by
    have hui : Tendsto (fun j => u j i) atTop (𝓝 (v i)) :=
      ((continuous_apply i).tendsto v).comp hu
    rcases lt_trichotomy (v i) 0 with hneg | heq | hpos
    · have hm := hL.atTop_mul_neg hneg hui
      have hxTop : Tendsto (fun j => x j i) atTop atTop := by
        convert Real.tendsto_exp_atTop.comp (tendsto_neg_atBot_atTop.comp hm) using 1
        ext j
        simp [hx, Function.comp_apply, neg_mul]
      filter_upwards [hxTop.eventually_gt_atTop (b i)] with j hj
      have hh := mul_neg_of_neg_of_pos hneg (sub_pos.mpr hj)
      exact ⟨hh.le, fun _ => hh⟩
    · exact Eventually.of_forall fun _ => by simp [heq]
    · have hm := hL.atTop_mul_pos hpos hui
      have hx0 : Tendsto (fun j => x j i) atTop (𝓝 0) := by
        convert Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hm) using 1
        ext j
        simp [hx, Function.comp_apply, neg_mul]
      filter_upwards [hx0.eventually (gt_mem_nhds (hb i))] with j hj
      have hh := mul_neg_of_pos_of_neg hpos (sub_neg.mpr hj)
      exact ⟨hh.le, fun _ => hh⟩
  have hall' : ∀ᶠ j in atTop, ∀ i,
      v i * (x j i - b i) ≤ 0 ∧ (v i ≠ 0 → v i * (x j i - b i) < 0) :=
    Filter.eventually_all.mpr hfactor
  obtain ⟨j', hj'⟩ := hall'.exists
  have hnz : ∃ i, v i ≠ 0 := by
    by_contra hn
    have heq : v = 0 := by
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    simp [heq] at hv
  obtain ⟨i, hi⟩ := hnz
  have hsum : (∑ i, v i * (x j' i - b i)) < 0 :=
    Finset.sum_neg' (fun k _ => (hj' k).1) ⟨i, Finset.mem_univ _, (hj' i).2 hi⟩
  exact hsum.ne (hz' j')

private theorem uniform_log_bound
    (wr : N.WeaklyReversible) {κ : Fin r → ℝ} (hκ : ∀ q, 0 < κ q)
    {b : Point n} (hb : Positive b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (α : Fin l → ℝ), (∀ k, 0 < α k) →
      ∀ x, N.compatible b x → N.field (N.scaleRates κ α) x = 0 →
        ‖fun i => Real.log (x i)‖ ≤ B := by
  classical
  by_contra h
  have unbounded (j : ℕ) : ∃ (α : Fin l → ℝ) (x : Point n), (∀ k, 0 < α k) ∧
      N.compatible b x ∧ N.field (N.scaleRates κ α) x = 0 ∧
      (j : ℝ) + 1 < ‖fun i => Real.log (x i)‖ := by
    by_contra! hj
    exact h ⟨(j : ℝ) + 1, by positivity, fun α ha x hc hs => hj α x ha hc hs⟩
  choose α x hα hc hs hlarge using unbounded
  let logX (j : ℕ) : Point n := fun i => Real.log (x j i)
  let L (j : ℕ) : ℝ := ‖logX j‖
  have hLpos (j : ℕ) : 0 < L j := lt_trans (by positivity) (hlarge j)
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_mono (fun j => le_trans (by linarith : (j : ℝ) ≤ (j : ℝ) + 1)
      (hlarge j).le) tendsto_natCast_atTop_atTop
  let u (j : ℕ) : Point n := (-(L j)⁻¹) • logX j
  have hnorm (j : ℕ) : ‖u j‖ = 1 := by
    change ‖(-(L j)⁻¹) • logX j‖ = 1
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hLpos j))]
    exact inv_mul_cancel₀ (hLpos j).ne'
  have hexp (j : ℕ) (i : Fin n) : x j i = Real.exp (-L j * u j i) := by
    have hlog : -L j * u j i = Real.log (x j i) := by
      change -L j * (-(L j)⁻¹ * Real.log (x j i)) = Real.log (x j i)
      field_simp [(hLpos j).ne']
    rw [hlog, Real.exp_log ((hc j).1 i)]
  have hSphere (j : ℕ) : u j ∈ Metric.sphere (0 : Point n) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hnorm j
  obtain ⟨v, hv, subseq, hmono, hu⟩ := (isCompact_sphere (0 : Point n) 1).tendsto_subseq hSphere
  have hv' : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hv
  exact N.no_escaping_steady_sequence wr hκ hb
    (α := α ∘ subseq) (x := x ∘ subseq) (u := u ∘ subseq) (L := L ∘ subseq)
    (fun j => hα (subseq j)) (fun j => hc (subseq j)) (fun j => hs (subseq j))
    (fun j => hexp (subseq j)) (hL.comp hmono.tendsto_atTop) hu hv'

/-- In a fixed positive compatibility class, the same strict positive lower
bound and finite upper bound work for all positive class multipliers. -/
theorem uniformSteadyBounds
    (wr : N.WeaklyReversible) {κ : Fin r → ℝ} (hκ : ∀ q, 0 < κ q)
    {b : Point n} (hb : Positive b) :
    ∃ m M : ℝ, 0 < m ∧ m < M ∧
      ∀ (α : Fin l → ℝ), (∀ k, 0 < α k) → ∀ x, N.compatible b x →
        N.field (N.scaleRates κ α) x = 0 → ∀ i, m ≤ x i ∧ x i ≤ M := by
  obtain ⟨B, hB, hbds⟩ := N.uniform_log_bound wr hκ hb
  refine ⟨Real.exp (-(B + 1)), Real.exp (B + 1), Real.exp_pos _,
    Real.exp_lt_exp.mpr (by linarith), ?_⟩
  intro α hα x hx hs i
  have hh := (norm_le_pi_norm (fun i => Real.log (x i)) i).trans (hbds α hα x hx hs)
  rw [Real.norm_eq_abs, abs_le] at hh
  have hxi := Real.exp_log (hx.1 i)
  constructor
  · simpa only [hxi] using (Real.exp_le_exp.mpr (show -(B + 1) ≤ Real.log (x i) by linarith))
  · simpa only [hxi] using (Real.exp_le_exp.mpr (show Real.log (x i) ≤ B + 1 by linarith))

def basisPoint (i : Fin n) : Point n := Pi.single i 1

private theorem dual_as_dot (f : Point n →ₗ[ℝ] ℝ) (x : Point n) :
    dot (fun j => f (basisPoint j)) x = f x := by
  have hx : (∑ j, x j • basisPoint j) = x := by
    ext j
    simp [basisPoint, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
  calc
    dot (fun j => f (basisPoint j)) x = f (∑ j, x j • basisPoint j) := by
      simp [dot_apply, smul_eq_mul, mul_comm]
    _ = f x := by rw [hx]

private theorem direction_of_basis_not_mem (i : Fin n) (hi : basisPoint i ∉ N.stoich) :
    ∃ ψ : Point n, ψ i = 1 ∧ ∀ q, dot ψ (N.change q) = 0 := by
  obtain ⟨f, hf, hmap⟩ := N.stoich.exists_dual_map_eq_bot_of_nmem hi inferInstance
  let g := (f (basisPoint i))⁻¹ • f
  refine ⟨fun j => g (basisPoint j), ?_, ?_⟩
  · change g (basisPoint i) = 1
    simp [g, hf]
  · intro q
    rw [dual_as_dot]
    have hq : N.change q ∈ N.stoich := Submodule.subset_span ⟨q, rfl⟩
    have hfq : f (N.change q) = 0 := by
      have hm : f (N.change q) ∈ N.stoich.map f := ⟨N.change q, hq, rfl⟩
      simpa [hmap] using hm
    simp [g, hfq]

private theorem height_eq_of_path {ψ : Point n} (hψ : ∀ q, dot ψ (N.change q) = 0)
    {a b : Fin c} (p : Relation.ReflTransGen N.Edge a b) :
    N.height ψ a = N.height ψ b := by
  induction p with
  | refl => rfl
  | tail _ edge ih =>
    obtain ⟨q, hs, ht⟩ := edge
    have h := hψ q
    rw [N.dot_change, hs, ht] at h
    exact ih.trans (sub_eq_zero.mp h).symm

private theorem class_heights (wr : N.WeaklyReversible) {ψ : Point n}
    (hψ : ∀ q, dot ψ (N.change q) = 0) :
    ∃ w : Fin l → ℝ, ∀ a, N.height ψ a = w (N.linkage a) := by
  classical
  have h (k : Fin l) : ∃ v : ℝ, ∀ a, N.linkage a = k → N.height ψ a = v := by
    by_cases hnonempty : ∃ a, N.linkage a = k
    · obtain ⟨b, hb⟩ := hnonempty
      exact ⟨N.height ψ b, fun a ha => N.height_eq_of_path hψ (wr a b (ha.trans hb.symm))⟩
    · exact ⟨0, fun a ha => (hnonempty ⟨a, ha⟩).elim⟩
  choose w hw using h
  exact ⟨w, fun a => hw (N.linkage a) a rfl⟩

def scalePoint (t : ℝ) (ψ x : Point n) : Point n :=
  fun i => Real.exp (t * ψ i) * x i

private theorem monomial_scalePoint (t : ℝ) (ψ x : Point n) (y : Fin n → ℕ) :
    monomial (scalePoint t ψ x) y =
      Real.exp (t * dot ψ (fun i => (y i : ℝ))) * monomial x y := by
  calc
    monomial (scalePoint t ψ x) y =
        monomial (fun i => Real.exp (t * ψ i)) y * monomial x y := by
      simp [scalePoint, monomial, mul_pow, Finset.prod_mul_distrib]
    _ = _ := by rw [monomial_exp]

/-- Scaling concentrations along a direction constant on each class is
equivalent to multiplying every rate in each class by the same factor. -/
theorem rate_point_duality (κ : Fin r → ℝ) (t : ℝ) (ψ x : Point n)
    (w : Fin l → ℝ) (hw : ∀ a, N.height ψ a = w (N.linkage a)) :
    N.field κ (scalePoint t ψ x) =
      N.field (N.scaleRates κ (fun k => Real.exp (t * w k))) x := by
  rw [N.field_eq_sum, N.field_eq_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [monomial_scalePoint]
  have hh : dot ψ (fun i => (N.complex (N.source q) i : ℝ)) = w (N.reactionClass q) :=
    hw (N.source q)
  rw [hh]
  unfold scaleRates
  congr 1
  ring

def IsPositiveSteady (κ : Fin r → ℝ) (x : Point n) : Prop :=
  Positive x ∧ N.field κ x = 0

def HasACR (κ : Fin r → ℝ) (i : Fin n) : Prop :=
  (∃ x, N.IsPositiveSteady κ x) ∧
    ∃ a : ℝ, 0 < a ∧ ∀ x, N.IsPositiveSteady κ x → x i = a

/-- Boros (2019, Theorem 1) supplied as a hypothesis for the fixed weakly
reversible network. -/
def BorosExistence : Prop :=
  ∀ (κ : Fin r → ℝ), (∀ q, 0 < κ q) → ∀ b, Positive b →
    ∃ x, N.compatible b x ∧ N.field κ x = 0

/-- For the original fixed rates, the positive steady-state coordinate has
infimum zero and is unbounded above when the standard basis vector lies
outside the stoichiometric subspace. -/
theorem steadyStates_approach_zero_and_unbounded (wr : N.WeaklyReversible)
    (existence : N.BorosExistence) {κ : Fin r → ℝ} (hκ : ∀ q, 0 < κ q)
    (i : Fin n) (hi : basisPoint i ∉ N.stoich) :
    (∀ ε : ℝ, 0 < ε → ∃ x, N.IsPositiveSteady κ x ∧ x i < ε) ∧
      (∀ A : ℝ, ∃ x, N.IsPositiveSteady κ x ∧ A < x i) := by
  obtain ⟨ψ, hψi, hψ⟩ := N.direction_of_basis_not_mem i hi
  obtain ⟨w, hw⟩ := N.class_heights wr hψ
  let b : Point n := fun _ => 1
  have hb : Positive b := fun _ => zero_lt_one
  obtain ⟨m, M, hm, hmM, bounds⟩ := N.uniformSteadyBounds wr hκ hb
  have hM := hm.trans hmM
  have scaledSteady (a : ℝ) (ha : 0 < a) :
      ∃ z, N.IsPositiveSteady κ z ∧ a * m ≤ z i ∧ z i ≤ a * M := by
    let t := Real.log a
    let α (k : Fin l) := Real.exp (t * w k)
    have hα (k : Fin l) : 0 < α k := Real.exp_pos _
    obtain ⟨x, hx, hs⟩ := existence (N.scaleRates κ α)
      (fun q => mul_pos (hα (N.reactionClass q)) (hκ q)) b hb
    obtain ⟨hlo, hhi⟩ := bounds α hα x hx hs i
    refine ⟨scalePoint t ψ x, ⟨fun j => mul_pos (Real.exp_pos _) (hx.1 j), ?_⟩, ?_⟩
    · rw [N.rate_point_duality κ t ψ x w hw]
      exact hs
    · have hcoord : (scalePoint t ψ x) i = a * x i := by
        simp [scalePoint, hψi, t, Real.exp_log ha]
      rw [hcoord]
      exact ⟨mul_le_mul_of_nonneg_left hlo ha.le, mul_le_mul_of_nonneg_left hhi ha.le⟩
  constructor
  · intro ε hε
    let a := ε / (M + 1)
    have hM1 : 0 < M + 1 := by linarith
    have ha : 0 < a := div_pos hε hM1
    obtain ⟨z, hz, _, hup⟩ := scaledSteady a ha
    refine ⟨z, hz, hup.trans_lt ?_⟩
    calc
      a * M < a * (M + 1) := mul_lt_mul_of_pos_left (by linarith) ha
      _ = ε := div_mul_cancel₀ _ hM1.ne'
  · intro A
    let a := (max A 0 + 1) / m
    have ha : 0 < a := div_pos (by linarith [le_max_right A 0]) hm
    obtain ⟨z, hz, hlo, _⟩ := scaledSteady a ha
    refine ⟨z, hz, lt_of_lt_of_le ?_ hlo⟩
    calc
      A < max A 0 + 1 := by linarith [le_max_left A 0]
      _ = a * m := (div_mul_cancel₀ _ hm.ne').symm

/-- Weak reversibility excludes ACR of any species that occurs in a
conservation law. This theorem includes the dependent-linkage-class case. -/
theorem acr_implies_basis_mem (wr : N.WeaklyReversible) (existence : N.BorosExistence)
    {κ : Fin r → ℝ} (hκ : ∀ q, 0 < κ q) (i : Fin n) (hacr : N.HasACR κ i) :
    basisPoint i ∈ N.stoich := by
  by_contra hi
  obtain ⟨_, a, ha, hac⟩ := hacr
  obtain ⟨z, hz, hlt⟩ := (N.steadyStates_approach_zero_and_unbounded wr existence hκ i hi).1 a ha
  exact hlt.ne (hac z hz)

end Network
end WACR

#print axioms WACR.Network.uniformSteadyBounds
#print axioms WACR.Network.steadyStates_approach_zero_and_unbounded
#print axioms WACR.Network.acr_implies_basis_mem
