import Mathlib

set_option warningAsError true

/-!
# AIM 272: the affine approximation lemma with a margin (paper, Section 8)

Minimum form. For `h ∈ (0,1)` and `q : ι → ℝ`, a face `f` with slope `f.r`
and offset `f.c` has value `∑ i, f.r i * h ^ q i + f.c h`. A face is
*near-active* if its value is within `gap h = (log h)^2` of every face of the
family. `Small c a` means `c(h) = o(h^a)` as `h → 0⁺`.

The main theorem `exists_good_family` says: for every finite index type `ι`,
every `A < B ≤ 0` and every positive tolerance `E` (not necessarily continuous)
there is a finite face family with slopes in `[A,B]^ι` and offsets `o(h^A)` such
that, at every point `p` of the cube, a face whose slope is at distance
`≥ E(slope)` from `p` is not near-active for all `(h,q)` close to `(0,p)`.
`uniform_property` turns this into the statement used in the paper.
-/

open Real Filter Topology Set

set_option linter.unusedSectionVars false

noncomputable section

namespace AIM272Affine

/-! ## Asymptotic toolkit as `h → 0⁺` -/

/-- `c(h) = o(h^a)` as `h → 0⁺`. -/
def Small (c : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ h in 𝓝 (0 : ℝ), 0 < h → |c h| ≤ ε * h ^ a

/-- The margin `(log h)^2`. -/
def gap (h : ℝ) : ℝ := (Real.log h) ^ 2

theorem gap_nonneg (h : ℝ) : 0 ≤ gap h := sq_nonneg _

theorem eventually_lt_one : ∀ᶠ h in 𝓝 (0 : ℝ), h < 1 :=
  eventually_lt_nhds (by norm_num)

/-- `h^γ → 0` as `h → 0` for `γ > 0`. -/
theorem eventually_rpow_le {γ ε : ℝ} (hγ : 0 < γ) (hε : 0 < ε) :
    ∀ᶠ h in 𝓝 (0 : ℝ), 0 < h → h ^ γ ≤ ε := by
  have hc : Tendsto (fun h : ℝ => h ^ γ) (𝓝 0) (𝓝 ((0 : ℝ) ^ γ)) :=
    (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto
  rw [Real.zero_rpow hγ.ne'] at hc
  filter_upwards [hc.eventually (ge_mem_nhds hε)] with h hh _ using hh

theorem small_zero (a : ℝ) : Small (fun _ => 0) a := by
  intro ε hε
  filter_upwards with h hh
  simp only [abs_zero]
  exact mul_nonneg hε.le (Real.rpow_nonneg hh.le _)

theorem Small.add {c d : ℝ → ℝ} {a : ℝ} (hc : Small c a) (hd : Small d a) :
    Small (fun h => c h + d h) a := by
  intro ε hε
  filter_upwards [hc (ε / 2) (by positivity), hd (ε / 2) (by positivity)] with h h1 h2 hh
  calc |c h + d h| ≤ |c h| + |d h| := abs_add_le _ _
    _ ≤ ε / 2 * h ^ a + ε / 2 * h ^ a := add_le_add (h1 hh) (h2 hh)
    _ = ε * h ^ a := by ring

theorem Small.neg {c : ℝ → ℝ} {a : ℝ} (hc : Small c a) : Small (fun h => - c h) a := by
  intro ε hε
  filter_upwards [hc ε hε] with h h1 hh
  rw [abs_neg]; exact h1 hh

/-- A function that is `o(h^a')` is `o(h^a)` for every `a ≤ a'`. -/
theorem Small.mono {c : ℝ → ℝ} {a a' : ℝ} (hc : Small c a') (haa : a ≤ a') : Small c a := by
  intro ε hε
  filter_upwards [hc ε hε, eventually_lt_one] with h h1 h2 hh
  calc |c h| ≤ ε * h ^ a' := h1 hh
    _ ≤ ε * h ^ a := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hh h2.le haa) hε.le

/-- `h^b = o(h^a)` when `a < b`. -/
theorem small_rpow {a b : ℝ} (hab : a < b) : Small (fun h => h ^ b) a := by
  intro ε hε
  filter_upwards [eventually_rpow_le (sub_pos.mpr hab) hε] with h h1 hh
  rw [abs_of_nonneg (Real.rpow_nonneg hh.le _)]
  calc h ^ b = h ^ (b - a) * h ^ a := by rw [← Real.rpow_add hh]; ring_nf
    _ ≤ ε * h ^ a := mul_le_mul_of_nonneg_right (h1 hh) (Real.rpow_nonneg hh.le _)

/-- `(log h)^2 = o(h^β)` for `β < 0`. -/
theorem small_gap {β : ℝ} (hβ : β < 0) : Small gap β := by
  intro ε hε
  set r := -β / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have ht := tendsto_log_mul_rpow_nhdsGT_zero hr0
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), |Real.log h * h ^ r| ≤ Real.sqrt ε := by
    have : Tendsto (fun h => |Real.log h * h ^ r|) (𝓝[>] 0) (𝓝 0) := by
      simpa using ht.abs
    exact this.eventually (ge_mem_nhds (Real.sqrt_pos.mpr hε))
  rw [eventually_nhdsWithin_iff] at hev
  filter_upwards [hev] with h h1 hh
  have h1 := h1 hh
  unfold gap
  rw [abs_of_nonneg (sq_nonneg _)]
  have hsq : (Real.log h * h ^ r) ^ 2 ≤ ε := by
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [sq_abs, Real.sq_sqrt hε.le] at this
  have hsplit : Real.log h ^ 2 = (Real.log h * h ^ r) ^ 2 * h ^ β := by
    have e : (h ^ r) ^ 2 * h ^ β = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hh.le, ← Real.rpow_add hh]
      rw [show r * ((2 : ℕ) : ℝ) + β = 0 by rw [hr]; push_cast; ring, Real.rpow_zero]
    calc Real.log h ^ 2 = Real.log h ^ 2 * ((h ^ r) ^ 2 * h ^ β) := by rw [e, mul_one]
      _ = (Real.log h * h ^ r) ^ 2 * h ^ β := by ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hh.le _)

/-! ### Lifting to the product filter at `(0, p)` -/

variable {ι : Type} [Fintype ι]

theorem Small.lift {c : ℝ → ℝ} {a : ℝ} (hc : Small c a) (p : ι → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p), 0 < z.1 → |c z.1| ≤ ε * z.1 ^ a :=
  (continuous_fst.tendsto ((0 : ℝ), p)).eventually (hc ε hε)

theorem eventually_fst {P : ℝ → Prop} (hP : ∀ᶠ h in 𝓝 (0 : ℝ), P h) (p : ι → ℝ) :
    ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p), P z.1 :=
  (continuous_fst.tendsto ((0 : ℝ), p)).eventually hP

theorem eventually_coord_gt {p : ι → ℝ} {i : ι} {b : ℝ} (hb : b < p i) :
    ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p), b < z.2 i := by
  have hc : Continuous fun z : ℝ × (ι → ℝ) => z.2 i := (continuous_apply i).comp continuous_snd
  exact (hc.tendsto ((0 : ℝ), p)).eventually (eventually_gt_nhds hb)

theorem eventually_coord_lt {p : ι → ℝ} {i : ι} {b : ℝ} (hb : p i < b) :
    ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p), z.2 i < b := by
  have hc : Continuous fun z : ℝ × (ι → ℝ) => z.2 i := (continuous_apply i).comp continuous_snd
  exact (hc.tendsto ((0 : ℝ), p)).eventually (eventually_lt_nhds hb)

/-- If `p i > β`, then `h^(q i) = o(h^β)` near `(0,p)`. -/
theorem eventually_pow_small {p : ι → ℝ} {i : ι} {β ε : ℝ} (hp : β < p i) (hε : 0 < ε) :
    ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p), 0 < z.1 → z.1 ^ z.2 i ≤ ε * z.1 ^ β := by
  set γ := (p i - β) / 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  filter_upwards [eventually_coord_gt (show β + γ < p i by rw [hγ]; linarith),
    eventually_fst (eventually_rpow_le hγ0 hε) p, eventually_fst eventually_lt_one p]
    with z hq h1 h2 hz
  have hle : z.1 ^ (z.2 i - β) ≤ z.1 ^ γ :=
    Real.rpow_le_rpow_of_exponent_ge hz h2.le (by linarith)
  calc z.1 ^ z.2 i = z.1 ^ (z.2 i - β) * z.1 ^ β := by rw [← Real.rpow_add hz]; ring_nf
    _ ≤ ε * z.1 ^ β := mul_le_mul_of_nonneg_right (hle.trans (h1 hz))
        (Real.rpow_nonneg hz.le _)

/-- If `p i < β`, then `h^(q i) / h^β → ∞` near `(0,p)`. -/
theorem eventually_pow_big {p : ι → ℝ} {i : ι} {β : ℝ} (hp : p i < β) (M : ℝ) :
    ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p), 0 < z.1 → M * z.1 ^ β ≤ z.1 ^ z.2 i := by
  set γ := (β - p i) / 2 with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hM : (0 : ℝ) < 1 / (|M| + 1) := by positivity
  filter_upwards [eventually_coord_lt (show p i < β - γ by rw [hγ]; linarith),
    eventually_fst (eventually_rpow_le hγ0 hM) p, eventually_fst eventually_lt_one p]
    with z hq h1 h2 hz
  have hpos : 0 < z.1 ^ γ := Real.rpow_pos_of_pos hz _
  -- `h^(-γ) ≥ |M| + 1`
  have hinv : |M| + 1 ≤ z.1 ^ (-γ) := by
    rw [Real.rpow_neg hz.le]
    have := h1 hz
    rw [le_div_iff₀ (by positivity)] at this
    rw [le_inv_comm₀ (by positivity) hpos]
    rw [div_eq_mul_inv, one_mul] at *
    calc z.1 ^ γ ≤ 1 / (|M| + 1) := by
          rw [le_div_iff₀ (by positivity)]; linarith
      _ = (|M| + 1)⁻¹ := one_div _
  have hle : z.1 ^ (-γ) ≤ z.1 ^ (z.2 i - β) :=
    Real.rpow_le_rpow_of_exponent_ge hz h2.le (by linarith)
  have hβ : 0 < z.1 ^ β := Real.rpow_pos_of_pos hz _
  calc M * z.1 ^ β ≤ (|M| + 1) * z.1 ^ β :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self M]) hβ.le
    _ ≤ z.1 ^ (z.2 i - β) * z.1 ^ β := mul_le_mul_of_nonneg_right (hinv.trans hle) hβ.le
    _ = z.1 ^ z.2 i := by rw [← Real.rpow_add hz]; ring_nf

/-! ## Faces, families and the property to be proved -/

/-- A face: slope `r` and offset `c`. -/
structure Face (ι : Type) where
  r : ι → ℝ
  c : ℝ → ℝ

/-- Value of a face at `(h, q)`. -/
def val (f : Face ι) (h : ℝ) (q : ι → ℝ) : ℝ := (∑ i, f.r i * h ^ q i) + f.c h

/-- `f` is within the margin `gap h` of every face of `F`. -/
def NearActive (F : List (Face ι)) (f : Face ι) (h : ℝ) (q : ι → ℝ) : Prop :=
  ∀ f' ∈ F, val f h q ≤ val f' h q + gap h

def InCube (A B : ℝ) (p : ι → ℝ) : Prop := ∀ i, p i ∈ Icc A B

/-- `f` is not near-active for all `(h, q)` close to `(0, p)` with `h > 0`. -/
def Excluded (F : List (Face ι)) (f : Face ι) (p : ι → ℝ) : Prop :=
  ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p), 0 < z.1 → ¬ NearActive F f z.1 z.2

/-- The conclusion of the affine approximation lemma for a family `F`. -/
structure Good (A B : ℝ) (E : (ι → ℝ) → ℝ) (F : List (Face ι)) : Prop where
  ne : F ≠ []
  slope : ∀ f ∈ F, InCube A B f.r
  small : ∀ f ∈ F, Small f.c A
  valid : ∀ f ∈ F, ∀ p, InCube A B p → E f.r ≤ dist p f.r → Excluded F f p

/-- A face that is beaten by a member of the family by more than the margin,
eventually near `(0,p)`, is excluded. -/
theorem excluded_of_beaten {F : List (Face ι)} {f f' : Face ι} {p : ι → ℝ} (hf' : f' ∈ F)
    (hb : ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p), 0 < z.1 →
      val f' z.1 z.2 + gap z.1 < val f z.1 z.2) : Excluded F f p := by
  filter_upwards [hb] with z hz hpos hna
  exact absurd (hna f' hf') (not_le.mpr (hz hpos))

/-! ## Embedding coordinate subsets -/

section Embed

variable [DecidableEq ι]

/-- Extend a slope on `U` by the constant `t` off `U`. -/
def embed (U : Finset ι) (t : ℝ) (ρ : {i // i ∈ U} → ℝ) : ι → ℝ :=
  fun i => if h : i ∈ U then ρ ⟨i, h⟩ else t

def restrict (U : Finset ι) (q : ι → ℝ) : {i // i ∈ U} → ℝ := fun j => q j

theorem continuous_restrict (U : Finset ι) : Continuous (restrict U) :=
  continuous_pi fun j => continuous_apply (j : ι)

/-- A face of type `k`: the lift of a face on `U`, with the extra offset `-h^β`. -/
def lift (U : Finset ι) (t β : ℝ) (f : Face {i // i ∈ U}) : Face ι :=
  ⟨embed U t f.r, fun h => - h ^ β + f.c h⟩

/-- The face of type `0`. -/
def type0 (t : ℝ) : Face ι := ⟨fun _ => t, fun _ => 0⟩

theorem sum_embed (U : Finset ι) (t : ℝ) (ρ : {i // i ∈ U} → ℝ) (w : ι → ℝ) :
    ∑ i, (embed U t ρ i - t) * w i = ∑ j : {i // i ∈ U}, (ρ j - t) * w j := by
  rw [← Finset.sum_subset (Finset.subset_univ U)]
  · rw [← Finset.sum_coe_sort U]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [embed, j.2]
  · intro i _ hi
    simp [embed, hi]

theorem val_lift_sub_type0 (U : Finset ι) (t β : ℝ) (f : Face {i // i ∈ U}) (h : ℝ)
    (q : ι → ℝ) :
    val (lift U t β f) h q - val (type0 t) h q =
      (∑ j : {i // i ∈ U}, (f.r j - t) * h ^ q j) - h ^ β + f.c h := by
  have := sum_embed U t f.r (fun i => h ^ q i)
  simp only [val, lift, type0]
  rw [← this, add_zero]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem val_lift_sub_lift (U : Finset ι) (t β : ℝ) (f f' : Face {i // i ∈ U}) (h : ℝ)
    (q : ι → ℝ) :
    val (lift U t β f) h q - val (lift U t β f') h q =
      val f h (restrict U q) - val f' h (restrict U q) := by
  have e1 := val_lift_sub_type0 U t β f h q
  have e2 := val_lift_sub_type0 U t β f' h q
  have e3 : val (lift U t β f) h q - val (lift U t β f') h q =
      (val (lift U t β f) h q - val (type0 t) h q) -
        (val (lift U t β f') h q - val (type0 t) h q) := by ring
  rw [e3, e1, e2]
  simp only [val, restrict, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Near-activity of a lifted face in a family containing all lifts of `G`
implies near-activity in `G`. -/
theorem nearActive_restrict {F : List (Face ι)} {U : Finset ι} {t β : ℝ}
    {G : List (Face {i // i ∈ U})} (hG : ∀ g ∈ G, lift U t β g ∈ F) {f : Face {i // i ∈ U}}
    {h : ℝ} {q : ι → ℝ} (hna : NearActive F (lift U t β f) h q) :
    NearActive G f h (restrict U q) := by
  intro g hg
  have h1 := hna _ (hG g hg)
  have h2 := val_lift_sub_lift U t β f g h q
  linarith

end Embed

/-! ## The local family at a fixed limiting minimal exponent `t` (paper, Section 8.3) -/

section Local

variable [DecidableEq ι] (B t : ℝ) (E : (ι → ℝ) → ℝ)
  (IH : ∀ U : Finset ι, U.card < Fintype.card ι → ∀ a, a < B →
    ∃ F : List (Face {i // i ∈ U}), Good a B (fun ρ => E (embed U t ρ)) F)

/-- The family on `U` given by the induction hypothesis on `[a, B]^U`. -/
def fam (U : Finset ι) (a : ℝ) : List (Face {i // i ∈ U}) :=
  if h : U.card < Fintype.card ι ∧ a < B then Classical.choose (IH U h.1 a h.2) else []

theorem fam_good {U : Finset ι} {a : ℝ} (h : U.card < Fintype.card ι ∧ a < B) :
    Good a B (fun ρ => E (embed U t ρ)) (fam B t E IH U a) := by
  unfold fam; rw [dif_pos h]; exact Classical.choose_spec (IH U h.1 a h.2)

theorem fam_cond {U : Finset ι} {a : ℝ} {ρ : Face {i // i ∈ U}} (hρ : ρ ∈ fam B t E IH U a) :
    U.card < Fintype.card ι ∧ a < B := by
  unfold fam at hρ
  split_ifs at hρ with h
  · exact h
  · simp at hρ

/-- The minimum of the tolerances of a list of faces (and `1`). -/
def minTol (L : List (Face ι)) : ℝ := L.foldr (fun f m => min (E f.r) m) 1

theorem minTol_pos (hE : ∀ r, 0 < E r) (L : List (Face ι)) : 0 < minTol E L := by
  induction L with
  | nil => simp [minTol]
  | cons f L ih => exact lt_min (hE _) ih

theorem minTol_le {L : List (Face ι)} {f : Face ι} (hf : f ∈ L) : minTol E L ≤ E f.r := by
  induction L with
  | nil => simp at hf
  | cons g L ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hf)

/-- The faces of type `k` at level `b`. -/
def typesAt (k : ℕ) (b : ℝ) : List (Face ι) :=
  (Finset.univ.powersetCard k).toList.flatMap fun U => (fam B t E IH U b).map (lift U t b)

theorem mem_typesAt {k : ℕ} {b : ℝ} {f : Face ι} :
    f ∈ typesAt B t E IH k b ↔
      ∃ U : Finset ι, U.card = k ∧ ∃ ρ ∈ fam B t E IH U b, lift U t b ρ = f := by
  simp [typesAt, List.mem_flatMap, Finset.mem_powersetCard]

/-- Levels `β_k` and the faces of type `k`, built recursively. -/
def stage : ℕ → ℝ × List (Face ι)
  | 0 => (B, [type0 t])
  | k + 1 =>
    let b := t + min (minTol E (stage k).2) ((stage k).1 - t) / 2
    (b, typesAt B t E IH (k + 1) b)

def beta (k : ℕ) : ℝ := (stage B t E IH k).1

def T (k : ℕ) : List (Face ι) := (stage B t E IH k).2

theorem beta_zero : beta B t E IH 0 = B := rfl

theorem T_zero : T B t E IH 0 = [type0 t] := rfl

theorem beta_succ (k : ℕ) :
    beta B t E IH (k + 1) = t + min (minTol E (T B t E IH k)) (beta B t E IH k - t) / 2 := rfl

theorem T_succ (k : ℕ) : T B t E IH (k + 1) = typesAt B t E IH (k + 1) (beta B t E IH (k + 1)) :=
  rfl

/-- The local family: faces of type `0, 1, …, |ι|`. -/
def LF : List (Face ι) := (List.range (Fintype.card ι + 1)).flatMap (T B t E IH)

theorem mem_LF {f : Face ι} :
    f ∈ LF B t E IH ↔ ∃ k, k ≤ Fintype.card ι ∧ f ∈ T B t E IH k := by
  simp [LF, List.mem_flatMap, Nat.lt_succ_iff]

theorem type0_mem_LF : (type0 t : Face ι) ∈ LF B t E IH :=
  (mem_LF B t E IH).mpr ⟨0, Nat.zero_le _, by simp [T_zero]⟩

theorem beta_gt (hE : ∀ r, 0 < E r) (htB : t < B) : ∀ k, t < beta B t E IH k
  | 0 => htB
  | k + 1 => by
    rw [beta_succ]
    have h1 := minTol_pos E hE (T B t E IH k)
    have h2 := beta_gt hE htB k
    have : 0 < min (minTol E (T B t E IH k)) (beta B t E IH k - t) := lt_min h1 (by linarith)
    linarith

theorem beta_succ_lt (hE : ∀ r, 0 < E r) (htB : t < B) (k : ℕ) :
    beta B t E IH (k + 1) < beta B t E IH k := by
  rw [beta_succ]
  have h2 := beta_gt B t E IH hE htB k
  have : min (minTol E (T B t E IH k)) (beta B t E IH k - t) ≤ beta B t E IH k - t :=
    min_le_right _ _
  linarith

theorem beta_anti (hE : ∀ r, 0 < E r) (htB : t < B) {k m : ℕ} (hkm : k < m) :
    beta B t E IH m < beta B t E IH k := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hkm with h | rfl
    · exact (beta_succ_lt B t E IH hE htB m).trans (ih h)
    · exact beta_succ_lt B t E IH hE htB k

theorem beta_le (hE : ∀ r, 0 < E r) (htB : t < B) (k : ℕ) : beta B t E IH k ≤ B := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact le_of_eq (beta_zero B t E IH)
  · exact (beta_anti B t E IH hE htB hk).le

theorem beta_tol (hE : ∀ r, 0 < E r) {k : ℕ} {f : Face ι} (hf : f ∈ T B t E IH k)
    (htB : t < B) : beta B t E IH (k + 1) - t < E f.r := by
  rw [beta_succ]
  have h1 := minTol_le E hf
  have h0 := minTol_pos E hE (T B t E IH k)
  have h2 := beta_gt B t E IH hE htB k
  have : min (minTol E (T B t E IH k)) (beta B t E IH k - t) ≤ minTol E (T B t E IH k) :=
    min_le_left _ _
  have : 0 < min (minTol E (T B t E IH k)) (beta B t E IH k - t) := lt_min h0 (by linarith)
  linarith

/-- If `t = B` there are no faces of positive type. -/
theorem T_succ_eq_nil (hE : ∀ r, 0 < E r) (htB : t = B) (k : ℕ) : T B t E IH (k + 1) = [] := by
  have hb : ∀ k, beta B t E IH k = B := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [beta_succ, ih]
      have h0 : B - t = 0 := by linarith
      have := minTol_pos E hE (T B t E IH k)
      rw [h0, min_eq_right this.le]; linarith
  rw [T_succ, hb]
  simp only [typesAt]
  apply List.flatMap_eq_nil_iff.mpr
  intro U _
  simp [fam]

theorem lift_mem_LF {k : ℕ} (hk : k + 1 ≤ Fintype.card ι) {U : Finset ι} (hUc : U.card = k + 1)
    {g : Face {i // i ∈ U}} (hg : g ∈ fam B t E IH U (beta B t E IH (k + 1))) :
    lift U t (beta B t E IH (k + 1)) g ∈ LF B t E IH :=
  (mem_LF B t E IH).mpr ⟨k + 1, hk, by rw [T_succ]; exact (mem_typesAt B t E IH).mpr ⟨U, hUc, g, hg, rfl⟩⟩

/-- A face of the next type beats the face of type `0` by `h^β'/2` plus the margin,
when all coordinates of its support exceed `β'`. -/
theorem upper_face (hE : ∀ r, 0 < E r) (hB : B ≤ 0) (htB : t < B) {p : ι → ℝ} {U : Finset ι}
    {j : ι} (hj : j ∉ U) (hk : U.card + 1 < Fintype.card ι)
    (hpU : ∀ i ∈ U, beta B t E IH (U.card + 1) < p i) (hpj : beta B t E IH (U.card + 1) < p j) :
    ∃ f' ∈ LF B t E IH, ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p), 0 < z.1 →
      val f' z.1 z.2 + gap z.1 + z.1 ^ (beta B t E IH (U.card + 1)) / 2 ≤
        val (type0 t) z.1 z.2 := by
  set β' := beta B t E IH (U.card + 1) with hβ'
  set U' := insert j U with hU'
  have hU'c : U'.card = U.card + 1 := Finset.card_insert_of_notMem hj
  have hβ'B : β' < B := by
    have := beta_anti B t E IH hE htB (show 0 < U.card + 1 by omega)
    rwa [beta_zero] at this
  have hβ'0 : β' < 0 := lt_of_lt_of_le hβ'B hB
  have cond : U'.card < Fintype.card ι ∧ β' < B := ⟨by omega, hβ'B⟩
  have good := fam_good B t E IH cond
  obtain ⟨ρ', hρ'⟩ := List.exists_mem_of_ne_nil _ good.ne
  refine ⟨lift U' t β' ρ', lift_mem_LF B t E IH (by omega) hU'c hρ', ?_⟩
  set N : ℝ := (Fintype.card ι : ℝ)
  set D : ℝ := B - t
  have hD : 0 < D := by simp only [D]; linarith
  have hN : 0 ≤ N := by positivity
  set ε : ℝ := 1 / (4 * (N * D + 2)) with hεdef
  have hε : 0 < ε := by positivity
  have hεeq : ε * (N * D + 2) = 1 / 4 := by rw [hεdef]; field_simp
  have hpU' : ∀ i : {i // i ∈ U'}, β' < p i := by
    intro i
    rcases Finset.mem_insert.mp i.2 with h | h
    · rw [h]; exact hpj
    · exact hpU _ h
  have hall : ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p),
      ∀ i : {i // i ∈ U'}, 0 < z.1 → z.1 ^ z.2 i ≤ ε * z.1 ^ β' :=
    Filter.eventually_all.mpr fun i => eventually_pow_small (hpU' i) hε
  filter_upwards [hall, (good.small ρ' hρ').lift p hε, (small_gap hβ'0).lift p hε]
    with z h1 h2 h3 hpos
  have hX : 0 < z.1 ^ β' := Real.rpow_pos_of_pos hpos _
  have hdiff := val_lift_sub_type0 U' t β' ρ' z.1 z.2
  have hsum : (∑ i : {i // i ∈ U'}, (ρ'.r i - t) * z.1 ^ z.2 i) ≤ N * D * ε * z.1 ^ β' := by
    calc (∑ i : {i // i ∈ U'}, (ρ'.r i - t) * z.1 ^ z.2 i)
        ≤ ∑ _i : {i // i ∈ U'}, D * (ε * z.1 ^ β') := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hs := good.slope ρ' hρ' i
          have hq : 0 ≤ z.1 ^ z.2 i := Real.rpow_nonneg hpos.le _
          have hβt := beta_gt B t E IH hE htB (U.card + 1)
          exact mul_le_mul (by simp only [D]; linarith [hs.2]) (h1 i hpos) hq hD.le
      _ = (U'.card : ℝ) * (D * (ε * z.1 ^ β')) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ ≤ N * (D * (ε * z.1 ^ β')) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simp only [N]; exact_mod_cast Finset.card_le_univ U'
      _ = N * D * ε * z.1 ^ β' := by ring
  have hc := h2 hpos
  have hg := h3 hpos
  rw [abs_of_nonneg (gap_nonneg _)] at hg
  have hcle : ρ'.c z.1 ≤ ε * z.1 ^ β' := (le_abs_self _).trans hc
  have key : N * D * ε * z.1 ^ β' + ε * z.1 ^ β' + ε * z.1 ^ β' = z.1 ^ β' / 4 := by
    linear_combination z.1 ^ β' * hεeq
  linarith

/-- **Local lemma (paper, Lemma 8.2).** At a point whose minimal coordinate is `t`,
a face of the local family that violates its tolerance is excluded. -/
theorem local_excluded (hE : ∀ r, 0 < E r) (hB : B ≤ 0) (htB : t ≤ B) {p : ι → ℝ}
    (hpB : ∀ i, p i ≤ B) (hmin : ∀ i, t ≤ p i) (hatt : ∃ i, p i = t) {f : Face ι}
    (hf : f ∈ LF B t E IH) (htol : E f.r ≤ dist p f.r) : Excluded (LF B t E IH) f p := by
  by_contra hne
  apply absurd htol
  push_neg
  obtain ⟨k, hk, hfk⟩ := (mem_LF B t E IH).mp hf
  rcases htB.lt_or_eq with htB' | htB'
  swap
  · have hp : ∀ i, p i = t := fun i => le_antisymm (by linarith [hpB i]) (hmin i)
    cases k with
    | zero =>
      rw [T_zero, List.mem_singleton] at hfk
      subst hfk
      have : dist p (type0 t : Face ι).r = 0 := by
        rw [dist_eq_zero]; funext i; simp [type0, hp i]
      rw [this]; exact hE _
    | succ k =>
      rw [T_succ_eq_nil B t E IH hE htB'] at hfk; simp at hfk
  -- from now on `t < B`
  suffices key : ∀ i, |p i - f.r i| < E f.r by
    exact (dist_pi_lt_iff (hE _)).mpr fun i => by rw [Real.dist_eq]; exact key i
  cases k with
  | zero =>
    rw [T_zero, List.mem_singleton] at hfk
    subst hfk
    intro i
    simp only [type0]
    rw [abs_of_nonneg (by linarith [hmin i])]
    by_cases hk2 : (∅ : Finset ι).card + 1 < Fintype.card ι
    · have hle : p i ≤ beta B t E IH 1 := by
        by_contra hlt
        push_neg at hlt
        obtain ⟨f', hf', hev⟩ := upper_face B t E IH hE hB htB' (U := ∅) (j := i)
          (Finset.notMem_empty i) hk2 (by simp) (by simpa using hlt)
        apply hne
        apply excluded_of_beaten hf'
        filter_upwards [hev] with z hz hpos
        have := hz hpos
        have hX : 0 < z.1 ^ beta B t E IH ((∅ : Finset ι).card + 1) := Real.rpow_pos_of_pos hpos _
        linarith
      have := beta_tol B t E IH hE (k := 0) (f := type0 t) (by simp [T_zero]) htB'
      simp only [type0] at this
      linarith
    · obtain ⟨i0, hi0⟩ := hatt
      have : i = i0 := Fintype.card_le_one_iff.mp (by simp at hk2; omega) i i0
      subst this
      rw [hi0, sub_self]; exact hE _
  | succ k =>
    rw [T_succ, mem_typesAt] at hfk
    obtain ⟨U, hUc, ρ, hρ, rfl⟩ := hfk
    have cond := fam_cond B t E IH hρ
    have good := fam_good B t E IH cond
    set β := beta B t E IH (k + 1) with hβ
    have hβt : t < β := beta_gt B t E IH hE htB' (k + 1)
    have hβ0 : β < 0 := lt_of_lt_of_le cond.2 hB
    -- (i) the coordinates in `U` are at least `β`
    have hU : ∀ i ∈ U, β ≤ p i := by
      intro i hi
      by_contra hlt
      push_neg at hlt
      apply hne
      apply excluded_of_beaten (type0_mem_LF B t E IH)
      filter_upwards [eventually_pow_big hlt (3 / (β - t)), (good.small ρ hρ).lift p one_pos,
        (small_gap hβ0).lift p (by norm_num : (0 : ℝ) < 1 / 2)] with z h1 h2 h3 hpos
      have hX : 0 < z.1 ^ β := Real.rpow_pos_of_pos hpos _
      have hdiff := val_lift_sub_type0 U t β ρ z.1 z.2
      have hnn : ∀ j : {i // i ∈ U}, 0 ≤ (ρ.r j - t) * z.1 ^ z.2 j := fun j =>
        mul_nonneg (by linarith [(good.slope ρ hρ j).1]) (Real.rpow_nonneg hpos.le _)
      have hsingle : (ρ.r ⟨i, hi⟩ - t) * z.1 ^ z.2 i ≤
          ∑ j : {i // i ∈ U}, (ρ.r j - t) * z.1 ^ z.2 j :=
        Finset.single_le_sum (f := fun j : {i // i ∈ U} => (ρ.r j - t) * z.1 ^ z.2 j)
          (fun j _ => hnn j) (Finset.mem_univ (⟨i, hi⟩ : {i // i ∈ U}))
      have hρi : β ≤ ρ.r ⟨i, hi⟩ := (good.slope ρ hρ ⟨i, hi⟩).1
      have hbig := h1 hpos
      have hprod : 3 * z.1 ^ β ≤ (ρ.r ⟨i, hi⟩ - t) * z.1 ^ z.2 i := by
        have e : (β - t) * (3 / (β - t) * z.1 ^ β) = 3 * z.1 ^ β := by
          have hne0 : β - t ≠ 0 := by linarith
          field_simp
        calc 3 * z.1 ^ β = (β - t) * (3 / (β - t) * z.1 ^ β) := e.symm
          _ ≤ (β - t) * z.1 ^ z.2 i := mul_le_mul_of_nonneg_left hbig (by linarith)
          _ ≤ (ρ.r ⟨i, hi⟩ - t) * z.1 ^ z.2 i :=
              mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hpos.le _)
      have hc := h2 hpos
      have hg := h3 hpos
      rw [abs_of_nonneg (gap_nonneg _)] at hg
      have hcle : -(1 * z.1 ^ β) ≤ ρ.c z.1 := by
        have := neg_abs_le (ρ.c z.1); linarith
      show val (type0 t) z.1 z.2 + gap z.1 < val (lift U t β ρ) z.1 z.2
      linarith
    -- (i') the coordinates in `U` are within tolerance
    have hdistU : dist (restrict U p) ρ.r < E (embed U t ρ.r) := by
      by_contra hge
      push_neg at hge
      have hcube : InCube β B (restrict U p) := fun i => ⟨hU i i.2, hpB i⟩
      have ex := good.valid ρ hρ (restrict U p) hcube hge
      apply hne
      have hΦ : Tendsto (fun z : ℝ × (ι → ℝ) => (z.1, restrict U z.2)) (𝓝 ((0 : ℝ), p))
          (𝓝 ((0 : ℝ), restrict U p)) :=
        (continuous_fst.prodMk ((continuous_restrict U).comp continuous_snd)).tendsto _
      filter_upwards [hΦ.eventually ex] with z hz hpos hna
      exact hz hpos (nearActive_restrict
        (fun g hg => lift_mem_LF B t E IH hk hUc hg) hna)
    -- (ii) the other coordinates
    have hout : ∀ j, j ∉ U → p j - t < E (embed U t ρ.r) := by
      intro j hj
      by_cases hk2 : U.card + 1 < Fintype.card ι
      · have hβ'β : beta B t E IH (U.card + 1) < β := by
          rw [hβ, hUc]; exact beta_succ_lt B t E IH hE htB' (k + 1)
        have hle : p j ≤ beta B t E IH (U.card + 1) := by
          by_contra hlt
          push_neg at hlt
          obtain ⟨f', hf', hev⟩ := upper_face B t E IH hE hB htB' hj hk2
            (fun i hi => lt_of_lt_of_le hβ'β (hU i hi)) hlt
          apply hne
          apply excluded_of_beaten hf'
          filter_upwards [hev, (good.small ρ hρ).lift p one_pos,
            (small_rpow hβ'β).lift p (by norm_num : (0 : ℝ) < 1 / 8)] with z h1 h2 h3 hpos
          have hX : 0 < z.1 ^ beta B t E IH (U.card + 1) := Real.rpow_pos_of_pos hpos _
          have hdiff := val_lift_sub_type0 U t β ρ z.1 z.2
          have hnn : 0 ≤ ∑ j : {i // i ∈ U}, (ρ.r j - t) * z.1 ^ z.2 j :=
            Finset.sum_nonneg fun j _ =>
              mul_nonneg (by linarith [(good.slope ρ hρ j).1]) (Real.rpow_nonneg hpos.le _)
          have hc := h2 hpos
          have hcle : -(1 * z.1 ^ β) ≤ ρ.c z.1 := by
            have := neg_abs_le (ρ.c z.1); linarith
          have hs := h3 hpos
          rw [abs_of_nonneg (Real.rpow_nonneg hpos.le _)] at hs
          have := h1 hpos
          show val f' z.1 z.2 + gap z.1 < val (lift U t β ρ) z.1 z.2
          linarith
        have htol' := beta_tol B t E IH hE (k := k + 1) (f := lift U t β ρ)
          (by rw [T_succ, mem_typesAt]; exact ⟨U, hUc, ρ, hρ, rfl⟩) htB'
        rw [← hUc] at htol'
        simp only [lift] at htol'
        linarith
      · obtain ⟨i0, hi0⟩ := hatt
        have hi0U : i0 ∉ U := fun h => by linarith [hU i0 h]
        have : j = i0 := by
          by_contra hne'
          have h1 : (insert j (insert i0 U)).card = U.card + 2 := by
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem hi0U]
            simp only [Finset.mem_insert, not_or]; exact ⟨hne', hj⟩
          have h2 := Finset.card_le_univ (insert j (insert i0 U))
          have h3 := cond.1
          omega
        subst this
        rw [hi0, sub_self]; exact hE _
    intro i
    show |p i - embed U t ρ.r i| < E (embed U t ρ.r)
    by_cases hi : i ∈ U
    · have e : embed U t ρ.r i = ρ.r ⟨i, hi⟩ := by simp [embed, hi]
      rw [e]
      have := dist_le_pi_dist (restrict U p) ρ.r ⟨i, hi⟩
      rw [Real.dist_eq] at this
      exact lt_of_le_of_lt this hdistU
    · have e : embed U t ρ.r i = t := by simp [embed, hi]
      rw [e, abs_of_nonneg (by linarith [hmin i])]
      exact hout i hi

/-- Slopes of the local family lie in `[t, B]`. -/
theorem LF_slope (hE : ∀ r, 0 < E r) (htB : t ≤ B) {f : Face ι} (hf : f ∈ LF B t E IH) (i : ι) :
    t ≤ f.r i ∧ f.r i ≤ B := by
  obtain ⟨k, _, hfk⟩ := (mem_LF B t E IH).mp hf
  cases k with
  | zero =>
    rw [T_zero, List.mem_singleton] at hfk; subst hfk; exact ⟨le_rfl, htB⟩
  | succ k =>
    rw [T_succ, mem_typesAt] at hfk
    obtain ⟨U, _, ρ, hρ, rfl⟩ := hfk
    have cond := fam_cond B t E IH hρ
    have good := fam_good B t E IH cond
    rcases htB.lt_or_eq with htB' | htB'
    · have hβt := beta_gt B t E IH hE htB' (k + 1)
      by_cases hi : i ∈ U
      · have e : (lift U t (beta B t E IH (k + 1)) ρ).r i = ρ.r ⟨i, hi⟩ := by
          simp [lift, embed, hi]
        rw [e]
        have := good.slope ρ hρ ⟨i, hi⟩
        exact ⟨by linarith [this.1], this.2⟩
      · have e : (lift U t (beta B t E IH (k + 1)) ρ).r i = t := by simp [lift, embed, hi]
        rw [e]; exact ⟨le_rfl, htB⟩
    · exfalso
      have := T_succ_eq_nil B t E IH hE htB' k
      rw [T_succ] at this
      have hmem : lift U t (beta B t E IH (k + 1)) ρ ∈
          typesAt B t E IH (k + 1) (beta B t E IH (k + 1)) :=
        (mem_typesAt B t E IH).mpr ⟨U, ‹_›, ρ, hρ, rfl⟩
      rw [this] at hmem; simp at hmem

/-- Offsets of the local family are `o(h^s)` for every `s` below all levels used. -/
theorem LF_small (hE : ∀ r, 0 < E r) (htB : t ≤ B) {s : ℝ}
    (hs : t < B → ∀ k, 1 ≤ k → k ≤ Fintype.card ι → s < beta B t E IH k)
    {f : Face ι} (hf : f ∈ LF B t E IH) : Small f.c s := by
  obtain ⟨k, hk, hfk⟩ := (mem_LF B t E IH).mp hf
  cases k with
  | zero =>
    rw [T_zero, List.mem_singleton] at hfk; subst hfk; exact small_zero s
  | succ k =>
    rw [T_succ, mem_typesAt] at hfk
    obtain ⟨U, _, ρ, hρ, rfl⟩ := hfk
    have cond := fam_cond B t E IH hρ
    have good := fam_good B t E IH cond
    rcases htB.lt_or_eq with htB' | htB'
    · have hsβ := hs htB' (k + 1) (by omega) hk
      exact (small_rpow hsβ).neg.add ((good.small ρ hρ).mono hsβ.le)
    · exfalso
      have := T_succ_eq_nil B t E IH hE htB' k
      rw [T_succ] at this
      have hmem : lift U t (beta B t E IH (k + 1)) ρ ∈
          typesAt B t E IH (k + 1) (beta B t E IH (k + 1)) :=
        (mem_typesAt B t E IH).mpr ⟨U, ‹_›, ρ, hρ, rfl⟩
      rw [this] at hmem; simp at hmem

end Local

/-! ## Finite minima -/

theorem exists_pos_le_all {α : Type*} (L : List α) (P : α → ℝ → Prop)
    (hmono : ∀ a m m', m' ≤ m → 0 < m' → P a m → P a m')
    (h : ∀ a ∈ L, ∃ m > 0, P a m) : ∃ m > 0, ∀ a ∈ L, P a m := by
  induction L with
  | nil => exact ⟨1, one_pos, by simp⟩
  | cons a L ih =>
    obtain ⟨m₁, hm₁, h₁⟩ := h a (by simp)
    obtain ⟨m₂, hm₂, h₂⟩ := ih fun b hb => h b (by simp [hb])
    refine ⟨min m₁ m₂, lt_min hm₁ hm₂, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hmono _ _ _ (min_le_left _ _) (lt_min hm₁ hm₂) h₁
    · exact hmono _ _ _ (min_le_right _ _) (lt_min hm₁ hm₂) (h₂ b hb)

/-! ## The minimal coordinate -/

/-- The minimal coordinate of `p`. -/
def mn [Nonempty ι] (p : ι → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty p

theorem mn_le [Nonempty ι] (p : ι → ℝ) (i : ι) : mn p ≤ p i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem exists_eq_mn [Nonempty ι] (p : ι → ℝ) : ∃ i, p i = mn p := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := ι)) p
  exact ⟨i, hi.symm⟩

theorem continuous_mn [Nonempty ι] : Continuous (mn : (ι → ℝ) → ℝ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have := ContinuousAt.finset_inf'_apply (s := Finset.univ) (f := fun i (p : ι → ℝ) => p i)
    (x := x) Finset.univ_nonempty (fun i _ => (continuous_apply i).continuousAt)
  exact this

theorem isCompact_cube (A B : ℝ) : IsCompact {p : ι → ℝ | InCube A B p} := by
  have : {p : ι → ℝ | InCube A B p} = Set.pi Set.univ fun _ => Icc A B := by
    ext p
    simp only [InCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem isClosed_not_excluded (F : List (Face ι)) (f : Face ι) :
    IsClosed {p : ι → ℝ | ¬ Excluded F f p} := by
  have ho : IsOpen {x : ℝ × (ι → ℝ) | ∀ᶠ z in 𝓝 x, 0 < z.1 → ¬ NearActive F f z.1 z.2} :=
    isOpen_setOf_eventually_nhds
  have hc : Continuous fun p : ι → ℝ => ((0 : ℝ), p) := continuous_const.prodMk continuous_id
  exact (ho.preimage hc).isClosed_compl

/-! ## Extending the local family to a neighbourhood of `t` (paper, Lemma 8.3) -/

section Nbhd

variable [DecidableEq ι] (B t : ℝ) (E : (ι → ℝ) → ℝ)
  (IH : ∀ U : Finset ι, U.card < Fintype.card ι → ∀ a, a < B →
    ∃ F : List (Face {i // i ∈ U}), Good a B (fun ρ => E (embed U t ρ)) F)

theorem local_nbhd [Nonempty ι] (A : ℝ) (hE : ∀ r, 0 < E r) (hB : B ≤ 0) (htB : t ≤ B) :
    ∃ ρ > 0, (t < B → ∀ k, 1 ≤ k → k ≤ Fintype.card ι → t + ρ < beta B t E IH k) ∧
      ∀ f ∈ LF B t E IH, ∀ p, InCube A B p → |mn p - t| < ρ → E f.r ≤ dist p f.r →
        Excluded (LF B t E IH) f p := by
  -- a radius for each face
  have hface : ∀ f ∈ LF B t E IH, ∃ m > 0, ∀ p, InCube A B p → |mn p - t| < m →
      E f.r ≤ dist p f.r → Excluded (LF B t E IH) f p := by
    intro f hf
    set K := {p : ι → ℝ | InCube A B p} ∩ {p | E f.r ≤ dist p f.r} ∩
      {p | ¬ Excluded (LF B t E IH) f p}
    have hKc : IsCompact K := by
      refine (isCompact_cube A B).inter_right ?_ |>.inter_right (isClosed_not_excluded _ _)
      exact isClosed_le continuous_const (continuous_id.dist continuous_const)
    by_cases hKe : K.Nonempty
    · obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKe
        ((continuous_mn.sub continuous_const).abs.continuousOn)
      have hpos : 0 < |mn p₀ - t| := by
        rcases eq_or_ne (mn p₀) t with h | h
        · exfalso
          obtain ⟨⟨hcube, htol⟩, hnex⟩ := hp₀
          apply hnex
          obtain ⟨i₀, hi₀⟩ := exists_eq_mn p₀
          exact local_excluded B t E IH hE hB htB (fun i => (hcube i).2)
            (fun i => h ▸ mn_le p₀ i) ⟨i₀, hi₀.trans h⟩ hf htol
        · exact abs_pos.mpr (sub_ne_zero.mpr h)
      refine ⟨|mn p₀ - t|, hpos, fun p hp hlt htol => ?_⟩
      by_contra hnex
      have hpK : p ∈ K := ⟨⟨hp, htol⟩, hnex⟩
      have := hmin hpK
      simp only [Set.mem_setOf_eq] at this
      linarith
    · refine ⟨1, one_pos, fun p hp _ htol => ?_⟩
      by_contra hnex
      exact hKe ⟨p, ⟨hp, htol⟩, hnex⟩
  obtain ⟨m, hm, hall⟩ := exists_pos_le_all (LF B t E IH)
    (fun f m => ∀ p, InCube A B p → |mn p - t| < m → E f.r ≤ dist p f.r →
      Excluded (LF B t E IH) f p)
    (fun f m m' hle _ h p hp hlt => h p hp (lt_of_lt_of_le hlt hle)) hface
  -- also keep below all levels
  by_cases htB' : t < B
  · set m₂ := (beta B t E IH (Fintype.card ι) - t) / 2
    have hm₂ : 0 < m₂ := by
      simp only [m₂]; linarith [beta_gt B t E IH hE htB' (Fintype.card ι)]
    refine ⟨min m m₂, lt_min hm hm₂, fun _ k hk1 hk => ?_, fun f hf p hp hlt htol =>
      hall f hf p hp (lt_of_lt_of_le hlt (min_le_left _ _)) htol⟩
    have h1 : beta B t E IH (Fintype.card ι) ≤ beta B t E IH k := by
      rcases hk.lt_or_eq with h | h
      · exact (beta_anti B t E IH hE htB' h).le
      · rw [h]
    have h2 : min m m₂ ≤ m₂ := min_le_right _ _
    simp only [m₂] at h2
    linarith [beta_gt B t E IH hE htB' (Fintype.card ι)]
  · exact ⟨m, hm, fun h => absurd h htB', hall⟩

end Nbhd

/-! ## Chains of intervals covering `[A, B]` (paper, Section 8.5, steps (1)–(2)) -/

/-- Centers `tc 1 < … < tc m` in `[A,B]` and cut points `A = q 0 < q 1 < … < q m`
with `[q (j-1), q j]` inside the interval of radius `ρ (tc j)` around `tc j`, and
`tc j < q j < tc (j+1)`. -/
def IsChain (A B : ℝ) (ρ : ℝ → ℝ) (m : ℕ) (tc q : ℕ → ℝ) : Prop :=
  1 ≤ m ∧ q 0 = A ∧
    (∀ j, 1 ≤ j → j ≤ m → (A ≤ tc j ∧ tc j ≤ B) ∧ |q (j - 1) - tc j| < ρ (tc j) ∧
      |q j - tc j| < ρ (tc j) ∧ q (j - 1) < q j) ∧
    (∀ j, 1 ≤ j → j < m → tc j < q j ∧ q j < tc (j + 1))

theorem IsChain.prev_le {A B : ℝ} {ρ : ℝ → ℝ} {m : ℕ} {tc q : ℕ → ℝ}
    (h : IsChain A B ρ m tc q) : q (m - 1) ≤ tc m := by
  obtain ⟨hm, hq0, h1, h2⟩ := h
  rcases Nat.lt_or_ge 1 m with hlt | hle
  · have := (h2 (m - 1) (by omega) (by omega)).2
    rw [show m - 1 + 1 = m by omega] at this
    exact this.le
  · have hm1 : m = 1 := by omega
    subst hm1
    simpa [hq0] using (h1 1 le_rfl le_rfl).1.1

/-- Move the last cut point. -/
theorem IsChain.retarget {A B : ℝ} {ρ : ℝ → ℝ} {m : ℕ} {tc q : ℕ → ℝ}
    (h : IsChain A B ρ m tc q) {s : ℝ} (hs1 : q (m - 1) < s) (hs2 : |s - tc m| < ρ (tc m)) :
    IsChain A B ρ m tc (fun j => if j = m then s else q j) := by
  obtain ⟨hm, hq0, h1, h2⟩ := h
  refine ⟨hm, by simp [show (0 : ℕ) ≠ m by omega, hq0], fun j hj1 hjm => ?_, fun j hj1 hjm => ?_⟩
  · have := h1 j hj1 hjm
    have hjm' : j - 1 ≠ m := by omega
    rcases hjm.lt_or_eq with hlt | rfl
    · simpa [show j ≠ m by omega, hjm'] using this
    · simp only [hjm', if_false, if_true]
      exact ⟨this.1, this.2.1, hs2, hs1⟩
  · simpa [show j ≠ m by omega] using h2 j hj1 hjm

/-- Append a new last center. -/
theorem IsChain.append {A B : ℝ} {ρ : ℝ → ℝ} {m : ℕ} {tc q : ℕ → ℝ}
    (h : IsChain A B ρ m tc q) {s q' : ℝ} (hsA : A ≤ s) (hsB : s ≤ B)
    (h1 : tc m < q') (h2 : q' < tc m + ρ (tc m)) (h3 : s - ρ s < q') (h4 : q' < s)
    (hρs : 0 < ρ s) :
    IsChain A B ρ (m + 1) (fun j => if j = m + 1 then s else tc j)
      (fun j => if j = m + 1 then s else if j = m then q' else q j) := by
  have hprev := h.prev_le
  obtain ⟨hm, hq0, hc1, hc2⟩ := h
  refine ⟨by omega, by simp [show (0 : ℕ) ≠ m by omega, hq0],
    fun j hj1 hjm => ?_, fun j hj1 hjm => ?_⟩
  · rcases hjm.lt_or_eq with hlt | rfl
    · rcases (Nat.lt_succ_iff.mp hlt).lt_or_eq with hlt' | rfl
      · have := hc1 j hj1 hlt'.le
        simpa [show j ≠ m + 1 by omega, show j ≠ m by omega, show j - 1 ≠ m + 1 by omega,
          show j - 1 ≠ m by omega] using this
      · have := hc1 j hj1 le_rfl
        simp only [show j ≠ j + 1 by omega, show j - 1 ≠ j + 1 by omega, show j - 1 ≠ j by omega,
          if_false, if_true]
        refine ⟨this.1, this.2.1, ?_, by linarith⟩
        rw [abs_lt]; constructor <;> linarith
    · simp only [if_true, show m + 1 - 1 = m by omega, show m ≠ m + 1 by omega, if_false]
      refine ⟨⟨hsA, hsB⟩, ?_, by simpa using hρs, h4⟩
      rw [abs_lt]; constructor <;> linarith
  · rcases (Nat.lt_succ_iff.mp hjm).lt_or_eq with hlt | rfl
    · have := hc2 j hj1 hlt
      simpa [show j ≠ m + 1 by omega, show j ≠ m by omega, show j + 1 ≠ m + 1 by omega] using this
    · simp only [show j ≠ j + 1 by omega, if_false, if_true]
      exact ⟨h1, h4⟩

/-- Every positive radius function gives a chain covering `[A, B]`. -/
theorem exists_chain {A B : ℝ} (hAB : A < B) (ρ : ℝ → ℝ) (hρ : ∀ t, 0 < ρ t) :
    ∃ m tc q, IsChain A B ρ m tc q ∧ q m = B := by
  classical
  set S := {s : ℝ | A < s ∧ s ≤ B ∧ ∃ m tc q, IsChain A B ρ m tc q ∧ q m = s}
  -- a first element
  set s₀ := min B (A + ρ A / 2)
  have hs₀ : s₀ ∈ S := by
    have hρA := hρ A
    refine ⟨lt_min hAB (by linarith), min_le_left _ _, 1, fun _ => A,
      fun j => if j = 0 then A else s₀, ⟨le_rfl, by simp, fun j hj1 hjm => ?_, fun j hj1 hjm => ?_⟩,
      by simp⟩
    · have hj : j = 1 := by omega
      subst hj
      simp only [Nat.sub_self, if_true, one_ne_zero, if_false, sub_self, abs_zero]
      refine ⟨⟨le_rfl, hAB.le⟩, hρA, ?_, lt_min hAB (by linarith)⟩
      have h1 : A < s₀ := lt_min hAB (by linarith)
      have h2 : s₀ ≤ A + ρ A / 2 := min_le_right _ _
      rw [abs_lt]; constructor <;> linarith
    · omega
  have hne : S.Nonempty := ⟨s₀, hs₀⟩
  have hbdd : BddAbove S := ⟨B, fun s hs => hs.2.1⟩
  set s' := sSup S
  have hs'B : s' ≤ B := csSup_le hne fun s hs => hs.2.1
  have hs₀s' : s₀ ≤ s' := le_csSup hbdd hs₀
  have hAs' : A < s' := lt_of_lt_of_le hs₀.1 hs₀s'
  -- `s'` itself belongs to `S`
  have hs'S : s' ∈ S := by
    obtain ⟨s, hsS, hss⟩ := exists_lt_of_lt_csSup hne (show s' - ρ s' < s' by linarith [hρ s'])
    have hss' : s ≤ s' := le_csSup hbdd hsS
    obtain ⟨hAs, hsB, m, tc, q, hch, hqm⟩ := hsS
    have hprev := hch.prev_le
    have hseg := (hch.2.2.1 m hch.1 le_rfl)
    rw [hqm] at hseg
    obtain ⟨_, _, hlast, hlt⟩ := hseg
    rw [abs_lt] at hlast
    by_cases hcase : s' < tc m + ρ (tc m)
    · refine ⟨hAs', hs'B, m, tc, _, hch.retarget (s := s') (by linarith) ?_, by simp⟩
      rw [abs_lt]; constructor <;> linarith
    · push_neg at hcase
      set q' := (max (tc m) (s' - ρ s') + (tc m + ρ (tc m))) / 2
      have hmax1 : tc m ≤ max (tc m) (s' - ρ s') := le_max_left _ _
      have hmax2 : s' - ρ s' ≤ max (tc m) (s' - ρ s') := le_max_right _ _
      have hmaxlt : max (tc m) (s' - ρ s') < tc m + ρ (tc m) :=
        max_lt (by linarith [hρ (tc m)]) (by linarith)
      refine ⟨hAs', hs'B, m + 1, _, _, hch.append (s := s') (q' := q') hAs'.le hs'B ?_ ?_ ?_ ?_
        (hρ s'), by simp⟩
      · simp only [q']; linarith
      · simp only [q']; linarith
      · simp only [q']; linarith
      · simp only [q']; linarith
  -- and `s' = B`
  have hs'eq : s' = B := by
    by_contra hneq
    have hlt : s' < B := lt_of_le_of_ne hs'B hneq
    obtain ⟨_, _, m, tc, q, hch, hqm⟩ := hs'S
    have hseg := hch.2.2.1 m hch.1 le_rfl
    rw [hqm] at hseg
    obtain ⟨_, _, hlast, hlt2⟩ := hseg
    rw [abs_lt] at hlast
    set s'' := min B ((s' + (tc m + ρ (tc m))) / 2)
    have h1 : s' < s'' := lt_min hlt (by linarith)
    have h2 : s'' ≤ (s' + (tc m + ρ (tc m))) / 2 := min_le_right _ _
    have hmem : s'' ∈ S := by
      refine ⟨by linarith, min_le_left _ _, m, tc, _, hch.retarget (s := s'') (by linarith) ?_,
        by simp⟩
      rw [abs_lt]; constructor <;> linarith
    have := le_csSup hbdd hmem
    linarith
  rw [hs'eq] at hs'S
  obtain ⟨_, _, m, tc, q, hch, hqm⟩ := hs'S
  exact ⟨m, tc, q, hch, hqm⟩

theorem IsChain.q_gt {A B : ℝ} {ρ : ℝ → ℝ} {m : ℕ} {tc q : ℕ → ℝ}
    (h : IsChain A B ρ m tc q) : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ m → A < q ℓ := by
  intro ℓ hℓ1 hℓm
  induction ℓ with
  | zero => omega
  | succ ℓ ih =>
    have hstep := (h.2.2.1 (ℓ + 1) (by omega) hℓm).2.2.2
    simp only [Nat.add_sub_cancel] at hstep
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · rw [h.2.1] at hstep; exact hstep
    · exact (ih hpos (by omega)).trans hstep

/-! ## Gluing (paper, Section 8.5, step (3) and the proof of the sequential property) -/

/-- Shift the offset of a face. -/
def shift (f : Face ι) (s : ℝ → ℝ) : Face ι := ⟨f.r, fun h => f.c h - s h⟩

theorem val_shift (f : Face ι) (s : ℝ → ℝ) (h : ℝ) (q : ι → ℝ) :
    val (shift f s) h q = val f h q - s h := by
  simp only [val, shift]; ring

theorem small_sum {α : Type*} (s : Finset α) (f : α → ℝ → ℝ) {a : ℝ}
    (hf : ∀ ℓ ∈ s, Small (f ℓ) a) : Small (fun h => ∑ ℓ ∈ s, f ℓ h) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using small_zero a
  | insert x s hx ih =>
    have h1 := hf x (Finset.mem_insert_self x s)
    have h2 := ih fun ℓ hℓ => hf ℓ (Finset.mem_insert_of_mem hℓ)
    have := h1.add h2
    simpa [Finset.sum_insert hx] using this

theorem val_type0_diff (f : Face ι) (t : ℝ) (h : ℝ) (q : ι → ℝ) :
    val f h q - val (type0 t) h q = (∑ i, (f.r i - t) * h ^ q i) + f.c h := by
  simp only [val, type0, sub_mul, Finset.sum_sub_distrib]; ring

/-- **The affine approximation lemma (paper, Proposition 8.1).** -/
theorem exists_good_family : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
    Fintype.card ι = n → ∀ A B : ℝ, A < B → B ≤ 0 → ∀ E : (ι → ℝ) → ℝ, (∀ r, 0 < E r) →
      ∃ F : List (Face ι), Good A B E F := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hcard A B hAB hB E hE
  have IHt : ∀ t : ℝ, ∀ U : Finset ι, U.card < Fintype.card ι → ∀ a, a < B →
      ∃ F : List (Face {i // i ∈ U}), Good a B (fun ρ => E (embed U t ρ)) F :=
    fun t U hU a ha => ih U.card (hcard ▸ hU) {i // i ∈ U} (Fintype.card_coe U) a B ha hB _
      (fun ρ => hE _)
  -- the empty index type
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨[type0 A], by simp, fun f hf i => isEmptyElim i, fun f hf => ?_, fun f hf p _ htol => ?_⟩
    · rw [List.mem_singleton] at hf; subst hf; exact small_zero A
    · exfalso
      have : dist p f.r = 0 := by rw [dist_eq_zero]; funext i; exact isEmptyElim i
      linarith [hE f.r]
  -- radii from the neighbourhood lemma
  classical
  have hnb : ∀ t : ℝ, t ≤ B → ∃ ρ > 0,
      (t < B → ∀ k, 1 ≤ k → k ≤ Fintype.card ι → t + ρ < beta B t E (IHt t) k) ∧
      ∀ f ∈ LF B t E (IHt t), ∀ p, InCube A B p → |mn p - t| < ρ → E f.r ≤ dist p f.r →
        Excluded (LF B t E (IHt t)) f p :=
    fun t htB => local_nbhd B t E (IHt t) A hE hB htB
  set ρf : ℝ → ℝ := fun t => if h : t ≤ B then Classical.choose (hnb t h) else 1
  have hρpos : ∀ t, 0 < ρf t := by
    intro t; simp only [ρf]; split_ifs with h
    · exact (Classical.choose_spec (hnb t h)).1
    · exact one_pos
  have hρspec : ∀ t (h : t ≤ B),
      (t < B → ∀ k, 1 ≤ k → k ≤ Fintype.card ι → t + ρf t < beta B t E (IHt t) k) ∧
      ∀ f ∈ LF B t E (IHt t), ∀ p, InCube A B p → |mn p - t| < ρf t → E f.r ≤ dist p f.r →
        Excluded (LF B t E (IHt t)) f p := by
    intro t h
    have := (Classical.choose_spec (hnb t h)).2
    simp only [ρf, dif_pos h]; exact this
  obtain ⟨m, tc, q, hch, hqm⟩ := exists_chain hAB ρf hρpos
  obtain ⟨hm, hq0, hseg, hord⟩ := hch
  have hqA : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ m → A < q ℓ :=
    (show IsChain A B ρf m tc q from ⟨hm, hq0, hseg, hord⟩).q_gt
  -- the glued family
  set Lj : ℕ → List (Face ι) := fun j => LF B (tc j) E (IHt (tc j))
  set σ : ℕ → ℝ → ℝ := fun j h => ∑ ℓ ∈ Finset.Ico 1 j, h ^ q ℓ
  have hσ : ∀ j, 1 ≤ j → ∀ h, σ (j + 1) h = σ j h + h ^ q j := by
    intro j hj h; simp only [σ]; rw [Finset.sum_Ico_succ_top hj]
  set G : List (Face ι) :=
    (List.range m).flatMap fun j0 => (Lj (j0 + 1)).map fun f => shift f (σ (j0 + 1))
  have memG : ∀ g, g ∈ G ↔ ∃ j, 1 ≤ j ∧ j ≤ m ∧ ∃ f ∈ Lj j, shift f (σ j) = g := by
    intro g
    simp only [G, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨j0, hj0, f, hf, rfl⟩; exact ⟨j0 + 1, by omega, by omega, f, hf, rfl⟩
    · rintro ⟨j, hj1, hjm, f, hf, rfl⟩
      refine ⟨j - 1, by omega, f, ?_, ?_⟩ <;> rw [show j - 1 + 1 = j by omega]
      · exact hf
  have htc : ∀ j, 1 ≤ j → j ≤ m → A ≤ tc j ∧ tc j ≤ B := fun j h1 h2 => (hseg j h1 h2).1
  have type0G : ∀ j, 1 ≤ j → j ≤ m → shift (type0 (tc j)) (σ j) ∈ G := fun j h1 h2 =>
    (memG _).mpr ⟨j, h1, h2, _, type0_mem_LF B (tc j) E (IHt (tc j)), rfl⟩
  -- smallness of local offsets below `tc j + ρ`
  have hsmallLoc : ∀ j, 1 ≤ j → j ≤ m → ∀ f ∈ Lj j, ∀ s, s ≤ tc j + ρf (tc j) → Small f.c s := by
    intro j h1 h2 f hf s hs
    have hspec := hρspec (tc j) (htc j h1 h2).2
    apply LF_small B (tc j) E (IHt (tc j)) hE (htc j h1 h2).2 _ hf
    intro htB k hk1 hk
    exact lt_of_le_of_lt hs (hspec.1 htB k hk1 hk)
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro hG
    have := type0G 1 le_rfl hm
    rw [hG] at this; simp at this
  · intro g hg i
    obtain ⟨j, h1, h2, f, hf, rfl⟩ := (memG g).mp hg
    have := LF_slope B (tc j) E (IHt (tc j)) hE (htc j h1 h2).2 hf i
    exact ⟨(htc j h1 h2).1.trans this.1, this.2⟩
  · intro g hg
    obtain ⟨j, h1, h2, f, hf, rfl⟩ := (memG g).mp hg
    have hfA : Small f.c A :=
      hsmallLoc j h1 h2 f hf A (by linarith [(htc j h1 h2).1, hρpos (tc j)])
    have hσA : Small (σ j) A := small_sum _ _ fun ℓ hℓ => by
      rw [Finset.mem_Ico] at hℓ
      exact small_rpow (hqA ℓ hℓ.1 (by omega))
    exact hfA.add hσA.neg
  · intro g hg p hp htol
    obtain ⟨j, h1, h2, f, hf, rfl⟩ := (memG g).mp hg
    have htol' : E f.r ≤ dist p f.r := htol
    set τ := mn p
    obtain ⟨i₀, hi₀⟩ := exists_eq_mn p
    have hcj := hseg j h1 h2
    rw [abs_lt, abs_lt] at hcj
    have hspec := hρspec (tc j) (htc j h1 h2).2
    set N : ℝ := (Fintype.card ι : ℝ)
    have hN : 0 ≤ N := by positivity
    by_cases ha : j < m ∧ q j < τ
    · -- (a) beaten by the type-0 face of the next family
      have hqj0 : q j < 0 := lt_of_lt_of_le (hord j h1 ha.1).2 ((htc (j + 1) (by omega) ha.1).2.trans hB)
      set W : ℝ := B - A
      have hW : 0 < W := by simp only [W]; linarith
      set ε : ℝ := 1 / (2 * (N * W + 2)) with hεdef
      have hε : 0 < ε := by positivity
      have hεeq : ε * (N * W + 2) = 1 / 2 := by rw [hεdef]; field_simp
      apply excluded_of_beaten (type0G (j + 1) (by omega) ha.1)
      have hall : ∀ᶠ z : ℝ × (ι → ℝ) in 𝓝 ((0 : ℝ), p),
          ∀ i : ι, 0 < z.1 → z.1 ^ z.2 i ≤ ε * z.1 ^ q j :=
        Filter.eventually_all.mpr fun i =>
          eventually_pow_small (lt_of_lt_of_le ha.2 (mn_le p i)) hε
      have hfs : Small f.c (q j) := hsmallLoc j h1 h2 f hf (q j) (by linarith [hcj.2.2])
      filter_upwards [hall, hfs.lift p hε, (small_gap hqj0).lift p hε] with z hz hc hg hpos
      have hX : 0 < z.1 ^ q j := Real.rpow_pos_of_pos hpos _
      rw [val_shift, val_shift, hσ j h1]
      have hd := val_type0_diff f (tc (j + 1)) z.1 z.2
      have hsl : ∀ i, |f.r i - tc (j + 1)| ≤ W := by
        intro i
        have hs := LF_slope B (tc j) E (IHt (tc j)) hE (htc j h1 h2).2 hf i
        have ht1 := htc (j + 1) (by omega) ha.1
        have ht0 := htc j h1 h2
        rw [abs_le]; simp only [W]; constructor <;> linarith
      have hsum : -(N * W * ε * z.1 ^ q j) ≤ ∑ i, (f.r i - tc (j + 1)) * z.1 ^ z.2 i := by
        have hb : ∀ i, -(W * (ε * z.1 ^ q j)) ≤ (f.r i - tc (j + 1)) * z.1 ^ z.2 i := by
          intro i
          have hq := Real.rpow_nonneg hpos.le (z.2 i)
          have h1' := hz i hpos
          have := abs_le.mp (hsl i)
          have hprod : |(f.r i - tc (j + 1)) * z.1 ^ z.2 i| ≤ W * (ε * z.1 ^ q j) := by
            rw [abs_mul, abs_of_nonneg hq]
            exact mul_le_mul (hsl i) h1' hq hW.le
          linarith [neg_abs_le ((f.r i - tc (j + 1)) * z.1 ^ z.2 i)]
        calc -(N * W * ε * z.1 ^ q j) = ∑ _i : ι, -(W * (ε * z.1 ^ q j)) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
          _ ≤ _ := Finset.sum_le_sum fun i _ => hb i
      have hc' := hc hpos
      have hg' := hg hpos
      rw [abs_of_nonneg (gap_nonneg _)] at hg'
      have hcle : -(ε * z.1 ^ q j) ≤ f.c z.1 := by linarith [neg_abs_le (f.c z.1)]
      have key : N * W * ε * z.1 ^ q j + ε * z.1 ^ q j + ε * z.1 ^ q j = z.1 ^ q j / 2 := by
        linear_combination z.1 ^ q j * hεeq
      linarith
    by_cases hb : 1 < j ∧ τ < q (j - 1)
    · -- (b) beaten by the type-0 face of the previous family
      have hj1 : 1 ≤ j - 1 := by omega
      have hord' := hord (j - 1) hj1 (by omega)
      rw [show j - 1 + 1 = j by omega] at hord'
      have hδ : 0 < tc j - tc (j - 1) := by linarith [hord'.1, hord'.2]
      have hqj0 : q (j - 1) < 0 := lt_of_lt_of_le hord'.2 ((htc j h1 h2).2.trans hB)
      apply excluded_of_beaten (type0G (j - 1) hj1 (by omega))
      have hfs : Small f.c (q (j - 1)) :=
        hsmallLoc j h1 h2 f hf (q (j - 1)) (by linarith [hcj.1.2])
      have hlt : p i₀ < q (j - 1) := by rw [hi₀]; exact hb.2
      filter_upwards [eventually_pow_big hlt (4 / (tc j - tc (j - 1))), hfs.lift p one_pos,
        (small_gap hqj0).lift p one_pos] with z hz hc hg hpos
      have hX : 0 < z.1 ^ q (j - 1) := Real.rpow_pos_of_pos hpos _
      rw [val_shift, val_shift]
      have hσj : σ j z.1 = σ (j - 1) z.1 + z.1 ^ q (j - 1) := by
        have := hσ (j - 1) hj1 z.1
        rwa [show j - 1 + 1 = j by omega] at this
      rw [hσj]
      have hd := val_type0_diff f (tc (j - 1)) z.1 z.2
      have hcoef : ∀ i, tc j - tc (j - 1) ≤ f.r i - tc (j - 1) := by
        intro i
        have := LF_slope B (tc j) E (IHt (tc j)) hE (htc j h1 h2).2 hf i
        linarith [this.1]
      have hnn : ∀ i, 0 ≤ (f.r i - tc (j - 1)) * z.1 ^ z.2 i := fun i =>
        mul_nonneg (by linarith [hcoef i]) (Real.rpow_nonneg hpos.le _)
      have hsingle : (f.r i₀ - tc (j - 1)) * z.1 ^ z.2 i₀ ≤
          ∑ i, (f.r i - tc (j - 1)) * z.1 ^ z.2 i :=
        Finset.single_le_sum (f := fun i => (f.r i - tc (j - 1)) * z.1 ^ z.2 i)
          (fun i _ => hnn i) (Finset.mem_univ i₀)
      have hbig := hz hpos
      have hprod : 4 * z.1 ^ q (j - 1) ≤ (f.r i₀ - tc (j - 1)) * z.1 ^ z.2 i₀ := by
        have e : (tc j - tc (j - 1)) * (4 / (tc j - tc (j - 1)) * z.1 ^ q (j - 1)) =
            4 * z.1 ^ q (j - 1) := by
          have hne0 : tc j - tc (j - 1) ≠ 0 := hδ.ne'
          field_simp
        calc 4 * z.1 ^ q (j - 1)
            = (tc j - tc (j - 1)) * (4 / (tc j - tc (j - 1)) * z.1 ^ q (j - 1)) := e.symm
          _ ≤ (tc j - tc (j - 1)) * z.1 ^ z.2 i₀ := mul_le_mul_of_nonneg_left hbig hδ.le
          _ ≤ (f.r i₀ - tc (j - 1)) * z.1 ^ z.2 i₀ :=
              mul_le_mul_of_nonneg_right (hcoef i₀) (Real.rpow_nonneg hpos.le _)
      have hc' := hc hpos
      have hg' := hg hpos
      rw [abs_of_nonneg (gap_nonneg _)] at hg'
      have hcle : -(1 * z.1 ^ q (j - 1)) ≤ f.c z.1 := by linarith [neg_abs_le (f.c z.1)]
      linarith
    · -- (c) the local lemma applies
      have hlo : q (j - 1) ≤ τ := by
        by_cases hj : 1 < j
        · push_neg at hb; exact hb hj
        · have : j = 1 := by omega
          subst this
          simp only [Nat.sub_self, hq0]
          have := (hp i₀).1
          rw [hi₀] at this; exact this
      have hhi : τ ≤ q j := by
        by_cases hj : j < m
        · push_neg at ha; exact ha hj
        · have : j = m := by omega
          subst this
          rw [hqm]
          have := (hp i₀).2
          rw [hi₀] at this; exact this
      have hτ : |mn p - tc j| < ρf (tc j) := by
        rw [abs_lt]; constructor <;> linarith [hcj.1.1, hcj.2.2]
      have hex := hspec.2 f hf p hp hτ htol'
      filter_upwards [hex] with z hz hpos hna
      apply hz hpos
      intro f'' hf''
      have h1' := hna _ ((memG _).mpr ⟨j, h1, h2, f'', hf'', rfl⟩)
      rw [val_shift, val_shift] at h1'
      linarith

/-! ## The uniform statement used in the paper -/

theorem eventually_forall_list {α : Type*} (L : List α) {P : α → ℝ → Prop}
    (h : ∀ a ∈ L, ∀ᶠ x in 𝓝 (0 : ℝ), P a x) : ∀ᶠ x in 𝓝 (0 : ℝ), ∀ a ∈ L, P a x := by
  induction L with
  | nil => exact Eventually.of_forall fun _ a ha => by simp at ha
  | cons b L ih =>
    filter_upwards [h b (by simp), ih fun a ha => h a (by simp [ha])] with x h1 h2 a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h1
    · exact h2 a ha

/-- **Uniform form.** There is `h₀ > 0` such that for `0 < h < h₀`, every point of
the cube, and every face that is near-active there, the slope is within
tolerance. -/
theorem uniform_property_nonempty {ι : Type} [Fintype ι] [DecidableEq ι] {A B : ℝ} (hAB : A < B)
    (hB : B ≤ 0) (E : (ι → ℝ) → ℝ) (hE : ∀ r, 0 < E r) :
    ∃ F : List (Face ι), F ≠ [] ∧ (∀ f ∈ F, InCube A B f.r) ∧ (∀ f ∈ F, Small f.c A) ∧
      ∀ᶠ h in 𝓝 (0 : ℝ), ∀ f ∈ F, ∀ p, InCube A B p → 0 < h → NearActive F f h p →
        dist p f.r < E f.r := by
  obtain ⟨F, hF⟩ := exists_good_family _ ι rfl A B hAB hB E hE
  refine ⟨F, hF.ne, hF.slope, hF.small, ?_⟩
  have hface : ∀ f ∈ F, ∀ᶠ h in 𝓝 (0 : ℝ), ∀ p ∈ {p : ι → ℝ | InCube A B p ∧ E f.r ≤ dist p f.r},
      0 < h → ¬ NearActive F f h p := by
    intro f hf
    have hK : IsCompact {p : ι → ℝ | InCube A B p ∧ E f.r ≤ dist p f.r} :=
      (isCompact_cube A B).inter_right
        (isClosed_le continuous_const (continuous_id.dist continuous_const))
    exact hK.eventually_forall_of_forall_eventually fun p hp =>
      hF.valid f hf p hp.1 hp.2
  have hall : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ f ∈ F, ∀ p ∈ {p : ι → ℝ | InCube A B p ∧ E f.r ≤ dist p f.r},
      0 < h → ¬ NearActive F f h p := by
    exact eventually_forall_list F hface
  filter_upwards [hall] with h hh f hf p hp hpos hna
  by_contra hge
  push_neg at hge
  exact hh f hf p ⟨hp, hge⟩ hpos hna

theorem uniform_property {ι : Type} [Fintype ι] [DecidableEq ι] {A B : ℝ} (hAB : A < B)
    (hB : B ≤ 0) (E : (ι → ℝ) → ℝ) (hE : ∀ r, 0 < E r) :
    ∃ F : List (Face ι), (∀ f ∈ F, InCube A B f.r) ∧ (∀ f ∈ F, Small f.c A) ∧
      ∀ᶠ h in 𝓝 (0 : ℝ), ∀ f ∈ F, ∀ p, InCube A B p → 0 < h → NearActive F f h p →
        dist p f.r < E f.r := by
  obtain ⟨F, _, h₁, h₂, h₃⟩ := uniform_property_nonempty hAB hB E hE
  exact ⟨F, h₁, h₂, h₃⟩

end AIM272Affine


end

#print axioms AIM272Affine.local_excluded
#print axioms AIM272Affine.local_nbhd
#print axioms AIM272Affine.exists_chain
#print axioms AIM272Affine.exists_good_family
#print axioms AIM272Affine.uniform_property
