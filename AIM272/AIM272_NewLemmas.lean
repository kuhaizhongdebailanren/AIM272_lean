import Std

/-!
# AIM 272 — conditional check of the new proof

Lean 4 core and Std only. Run with `lean --no-sorries AIM272_NewLemmas.lean`
on a Lean version that supports that flag, or with `lean AIM272_NewLemmas.lean`
and inspect the `#print axioms` output. All mathematical interfaces are explicit
theorem arguments. No network-specific conclusion is declared as an axiom.

The file checks the new path transformations, the path conditions at a rank
clock, and the finite-horizon estimate obtained from the gluing inequalities.
It takes the finite-basis property, the variational characterization of the
layer, and the analytic estimates at the indicated interfaces.
-/

set_option warningAsError true

namespace AIM272

/- The height laws used here hold on ℝ. Giving the laws explicitly keeps the
   first check independent of Mathlib and does not quantize the heights. -/
structure HeightLaws (H : Type u) [Add H] [LE H] : Prop where
  refl : ∀ x : H, x ≤ x
  trans : ∀ {x y z : H}, x ≤ y → y ≤ z → x ≤ z
  addRight : ∀ {x y : H}, x ≤ y → ∀ d : H, x + d ≤ y + d

section Words

variable {H : Type u} {Phase : Type v} {Label : Type w} [Add H] [LE H]

/-- A path in the auxiliary graph. `guard r` is minus the source height.
    The phase transition may inspect the phase but cannot inspect `H`. -/
inductive WordUnder (step : Label → Phase → Phase → Prop)
    (delta guard : Label → H) (cap : H) : Phase → H → List Label → Phase → H → Prop
  | nil (phase : Phase) (height : H) : WordUnder step delta guard cap phase height [] phase height
  | cons {r phase next endPhase height endHeight tail} :
      step r phase next → height + guard r ≤ cap →
      WordUnder step delta guard cap next (height + delta r) tail endPhase endHeight →
      WordUnder step delta guard cap phase height (r :: tail) endPhase endHeight

/-- Height after a word. Read from left to right at the actual current height. -/
def advance (delta : Label → H) (height : H) : List Label → H
  | [] => height
  | r :: tail => advance delta (height + delta r) tail

variable {step : Label → Phase → Phase → Prop} {delta guard : Label → H} {cap : H}

theorem WordUnder.endHeight_eq {p q : Phase} {x y : H} {w : List Label}
    (h : WordUnder step delta guard cap p x w q y) : y = advance delta x w := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => exact ih

theorem WordUnder.append {p q r : Phase} {x y z : H} {u v : List Label}
    (left : WordUnder step delta guard cap p x u q y)
    (right : WordUnder step delta guard cap q y v r z) :
    WordUnder step delta guard cap p x (u ++ v) r z := by
  induction left with
  | nil => exact right
  | cons he hc _ ih => exact .cons he hc (ih right)

theorem advance_mono (laws : HeightLaws H) (w : List Label) {x y : H}
    (h : x ≤ y) : advance delta x w ≤ advance delta y w := by
  induction w generalizing x y with
  | nil => exact h
  | cons r tail ih => exact ih (laws.addRight h (delta r))

theorem WordUnder.lowerStart (laws : HeightLaws H) {p q : Phase} {x y : H} {w : List Label}
    (h : WordUnder step delta guard cap p x w q y) {x' : H} (hle : x' ≤ x) :
    WordUnder step delta guard cap p x' w q (advance delta x' w) := by
  induction h generalizing x' with
  | nil => exact .nil _ _
  | @cons r _ _ _ _ _ _ he hc _ ih =>
    exact .cons he (laws.trans (laws.addRight hle (guard r)) hc)
      (ih (laws.addRight hle (delta r)))

theorem WordUnder.raiseCap (laws : HeightLaws H) {p q : Phase} {x y : H} {w : List Label}
    (h : WordUnder step delta guard cap p x w q y) {upper : H} (hcap : cap ≤ upper) :
    WordUnder step delta guard upper p x w q y := by
  induction h with
  | nil => exact .nil _ _
  | cons he hc _ ih => exact .cons he (laws.trans hc hcap) ih

/-- Discard a closed phase segment with nonnegative net displacement. The
    suffix is feasible under the original cap and its endpoint moves down. -/
theorem deleteNonnegativeLoop (laws : HeightLaws H)
    {p mid q : Phase} {x h h' y : H} {stem cycle suffix : List Label}
    (hp : WordUnder step delta guard cap p x stem mid h)
    (_hc : WordUnder step delta guard cap mid h cycle mid h')
    (hs : WordUnder step delta guard cap mid h' suffix q y)
    (hmon : h ≤ h') :
    WordUnder step delta guard cap p x (stem ++ suffix) q (advance delta h suffix) ∧
      advance delta h suffix ≤ y := by
  refine ⟨hp.append (hs.lowerStart laws hmon), ?_⟩
  rw [hs.endHeight_eq]
  exact advance_mono laws suffix hmon

/-- The labels produced by repeating the same phase loop `count` times. -/
def repeatWord (w : List Label) : Nat → List Label
  | 0 => []
  | n + 1 => repeatWord w n ++ w

/-- The exact real-valued counterpart is the iterate of addition by the loop
    displacement. The Archimedean estimate enters as a separate hypothesis. -/
def repeatHeight (delta : Label → H) (w : List Label) (start : H) : Nat → H
  | 0 => start
  | n + 1 => advance delta (repeatHeight delta w start n) w

theorem repeatNonpositiveLoop (laws : HeightLaws H) {p : Phase} {x y : H} {w : List Label}
    (hw : WordUnder step delta guard cap p x w p y) (hdown : y ≤ x) (n : Nat) :
    WordUnder step delta guard cap p x (repeatWord w n) p (repeatHeight delta w x n) ∧
      repeatHeight delta w x n ≤ x := by
  induction n with
  | zero => exact ⟨.nil _ _, laws.refl x⟩
  | succ n ih =>
    have hm : advance delta (repeatHeight delta w x n) w ≤ y := by
      rw [hw.endHeight_eq]
      exact advance_mono laws w ih.2
    exact ⟨ih.1.append (hw.lowerStart laws ih.2), laws.trans hm hdown⟩

theorem pumpToTarget (laws : HeightLaws H) {p : Phase} {x y target : H} {w : List Label}
    (hw : WordUnder step delta guard cap p x w p y) (hdown : y ≤ x)
    (iterates : ∃ n, repeatHeight delta w x n ≤ target) :
    ∃ path endpoint, WordUnder step delta guard cap p x path p endpoint ∧ endpoint ≤ target := by
  obtain ⟨n, hn⟩ := iterates
  exact ⟨repeatWord w n, repeatHeight delta w x n, (repeatNonpositiveLoop laws hw hdown n).1, hn⟩

/-- Restore a coordinate that was temporarily omitted from the phase. -/
def restoreCoordinate (step : Label → Phase → Phase → Prop) (consume produce : Label → Nat)
    (r : Label) (p q : Phase × Nat) : Prop :=
  step r p.1 q.1 ∧ consume r ≤ p.2 ∧ q.2 = p.2 - consume r + produce r

theorem WordUnder.liftWithStock {p q : Phase} {x y : H} {w : List Label}
    (path : WordUnder step delta guard cap p x w q y) (consume produce : Label → Nat)
    (limit : Nat) (bounded : ∀ r, consume r ≤ limit) (stock : Nat)
    (sufficient : limit * w.length ≤ stock) :
    ∃ remaining, WordUnder (restoreCoordinate step consume produce) delta guard cap
      (p, stock) x w (q, remaining) y := by
  induction path generalizing stock with
  | nil => exact ⟨stock, .nil _ _⟩
  | @cons r phase next endPhase height endHeight tail he hc _ ih =>
    have enough : limit * tail.length + limit ≤ stock := by
      simpa only [List.length_cons, Nat.mul_succ] using sufficient
    have take : consume r ≤ stock := by have := bounded r; omega
    have keep : limit * tail.length ≤ stock - consume r + produce r := by
      have := bounded r
      omega
    obtain ⟨remaining, rest⟩ := ih _ keep
    exact ⟨remaining, .cons ⟨he, take, rfl⟩ hc rest⟩

/-- Cap-feasible reachability to every lower height. -/
def escapesBelow (step : Label → Phase → Phase → Prop) (delta guard : Label → H)
    (cap : H) (p : Phase) (height : H) : Prop :=
  ∀ floor, ∃ word finish endpoint,
    WordUnder step delta guard cap p height word finish endpoint ∧ endpoint ≤ floor

/-- The variational layer is transported along a path whose copies lie
    under the given cap. The existence and attainment of the layer are inputs. -/
theorem layerBoundAlongWord (laws : HeightLaws H) (layer : Phase → H → H)
    (layerSpec : ∀ p height upper,
      layer p height ≤ upper ↔ escapesBelow step delta guard upper p height)
    {p q : Phase} {x y upper : H} {w : List Label}
    (path : WordUnder step delta guard cap p x w q y)
    (capBound : cap ≤ upper) (destination : layer q y ≤ upper) :
    layer p x ≤ upper := by
  apply (layerSpec p x upper).mpr
  intro floor
  obtain ⟨tail, finish, endpoint, continuation, lower⟩ :=
    (layerSpec q y upper).mp destination floor
  exact ⟨w ++ tail, finish, endpoint, (path.raiseCap laws capBound).append continuation, lower⟩

/-- A return word under the same cap bounds the level of the forward
    destination. For a strictly faster copy the two levels agree. -/
theorem fastCopyPreservesLayer [LT H] (laws : HeightLaws H) (layer : Phase → H → H)
    (layerSpec : ∀ p height upper,
      layer p height ≤ upper ↔ escapesBelow step delta guard upper p height)
    (ltLe : ∀ {a b : H}, a < b → a ≤ b)
    (ltNotLe : ∀ {a b : H}, a < b → ¬ b ≤ a)
    (total : ∀ a b : H, a ≤ b ∨ b ≤ a)
    (antisymm : ∀ {a b : H}, a ≤ b → b ≤ a → a = b)
    {p q : Phase} {x y : H} {outbound back : List Label}
    (forward : WordUnder step delta guard cap p x outbound q y)
    (returnWord : WordUnder step delta guard cap q y back p x)
    (faster : cap < layer p x) : layer q y = layer p x := by
  have below := layerBoundAlongWord laws layer layerSpec returnWord
    (ltLe faster) (laws.refl (layer p x))
  have above : layer p x ≤ layer q y := by
    rcases total cap (layer q y) with allowed | tooLow
    · exact layerBoundAlongWord laws layer layerSpec forward allowed (laws.refl (layer q y))
    · have impossible := layerBoundAlongWord laws layer layerSpec forward
        (laws.refl cap) tooLow
      exact (ltNotLe faster impossible).elim
  exact antisymm below above

end Words

section FiniteBasis

variable {State : Type u}

/-- Uniformize witness lengths using the finite basis supplied by Dickson's
    lemma. Both the basis coverage and preservation under translation are
    explicit inputs. Read the witness parameter as an upper bound on length,
    so a translated word may stop earlier. -/
theorem boundedWitnessFromFiniteBasis {above : State → State → Prop}
    {reachable : State → Prop} {witness : State → Nat → Prop} (basis : List State)
    (covers : ∀ x, reachable x → ∃ b, b ∈ basis ∧ above b x)
    (chooseSeed : ∀ b, b ∈ basis → ∃ n, witness b n)
    (translate : ∀ {b x n}, above b x → witness b n → witness x n) :
    ∃ bound, ∀ x, reachable x → ∃ n, n ≤ bound ∧ witness x n := by
  have finiteBound : ∃ bound, ∀ b, b ∈ basis → ∃ n, n ≤ bound ∧ witness b n := by
    clear covers translate
    induction basis with
    | nil =>
      exact ⟨0, fun _ h => (List.not_mem_nil h).elim⟩
    | cons b tail ih =>
      obtain ⟨k, hk⟩ := chooseSeed b (by simp)
      obtain ⟨bound, hbound⟩ := ih (fun c hc => chooseSeed c (List.mem_cons_of_mem _ hc))
      refine ⟨max k bound, fun c hc => ?_⟩
      rcases List.mem_cons.mp hc with rfl | ht
      · exact ⟨k, Nat.le_max_left _ _, hk⟩
      · obtain ⟨n, hn, hw⟩ := hbound c ht
        exact ⟨n, Nat.le_trans hn (Nat.le_max_right _ _), hw⟩
  obtain ⟨bound, hbound⟩ := finiteBound
  refine ⟨bound, fun x hx => ?_⟩
  obtain ⟨b, hb, hbx⟩ := covers x hx
  obtain ⟨n, hn, hw⟩ := hbound b hb
  exact ⟨n, hn, translate hbx hw⟩

end FiniteBasis

section Ranks

variable {State : Type u}

/-- Traversal of the strictly faster ranks. -/
inductive FastPath (fast : State → State → Prop) : State → State → Prop
  | nil (x) : FastPath fast x x
  | cons {x y z} : fast x y → FastPath fast y z → FastPath fast x z

/-- A traversal with an exact count of the current rank's genuine edges. -/
inductive CountedPath (fast current : State → State → Prop) : State → State → Nat → Prop
  | nil (x) : CountedPath fast current x x 0
  | fastStep {x y z n} : fast x y → CountedPath fast current y z n → CountedPath fast current x z n
  | currentStep {x y z n} : current x y → CountedPath fast current y z n →
      CountedPath fast current x z (n + 1)

def canReachWithin (fast current : State → State → Prop) (target : State → Prop)
    (x : State) (budget : Nat) : Prop :=
  ∃ y n, target y ∧ CountedPath fast current x y n ∧ n ≤ budget

theorem CountedPath.append {fast current : State → State → Prop} {x y z : State} {n m : Nat}
    (left : CountedPath fast current x y n) (right : CountedPath fast current y z m) :
    CountedPath fast current x z (n + m) := by
  induction left with
  | nil => simpa only [Nat.zero_add] using right
  | fastStep he _ ih => exact .fastStep he (ih right)
  | currentStep he _ ih =>
    simpa only [Nat.succ_add] using CountedPath.currentStep he (ih right)

theorem FastPath.prependCharged {fast current : State → State → Prop} {x y z : State} {n : Nat}
    (hp : FastPath fast x y) (tail : CountedPath fast current y z n) : CountedPath fast current x z n := by
  induction hp with
  | nil => exact tail
  | cons h _ ih => exact .fastStep h (ih tail)

/-- Exact use of weak reversibility. A faster move transports every budget
    certificate in both directions, even if the reverse is a whole word. -/
theorem budgetInvariantAlongFast {fast current : State → State → Prop} {target : State → Prop}
    {x y : State} {budget : Nat} (forward : FastPath fast x y) (back : FastPath fast y x) :
    canReachWithin fast current target x budget ↔ canReachWithin fast current target y budget := by
  constructor
  · rintro ⟨z, n, hz, hp, hn⟩
    exact ⟨z, n, hz, back.prependCharged hp, hn⟩
  · rintro ⟨z, n, hz, hp, hn⟩
    exact ⟨z, n, hz, forward.prependCharged hp, hn⟩

/-- The clock proof leaves the prefix before the last B rings unrestricted.
    Over that prefix, every allowed move can return or reach the target on
    its way back. This preserves unbounded reachability, allowing the new
    starting state's finite-basis bound to be used just before the last rings. -/
theorem reachableAfterUnrestrictedPrefix {fast current : State → State → Prop}
    {target : State → Prop}
    (returnOrTarget : ∀ x y, fast x y ∨ current x y →
      (∃ n, CountedPath fast current y x n) ∨
        (∃ n, canReachWithin fast current target y n))
    {x y : State} {n : Nat} (path : CountedPath fast current x y n)
    (reachable : ∃ b, canReachWithin fast current target x b) :
    ∃ b, canReachWithin fast current target y b := by
  have atNext : ∀ {u v}, fast u v ∨ current u v →
      (∃ b, canReachWithin fast current target u b) →
        ∃ b, canReachWithin fast current target v b := by
    rintro u v edge start
    rcases returnOrTarget u v edge with ⟨k, back⟩ | reached
    · obtain ⟨_, z, m, hz, rest, _⟩ := start
      exact ⟨k + m, z, k + m, hz, back.append rest, Nat.le_refl _⟩
    · exact reached
  induction path with
  | nil => exact reachable
  | fastStep he _ ih => exact ih (atNext (.inl he) reachable)
  | currentStep he _ ih => exact ih (atNext (.inr he) reachable)

/-- Before the first positively charged edge there is a path using only
    faster edges. Landing after that edge reduces the certified count by one. -/
theorem firstChargedEdge {fast current : State → State → Prop} {x z : State} {n : Nat}
    (hp : CountedPath fast current x z n) (npos : 0 < n) :
    ∃ u v k, FastPath fast x u ∧ current u v ∧ CountedPath fast current v z k ∧ n = k + 1 := by
  induction hp with
  | nil => omega
  | fastStep hf _ ih =>
    obtain ⟨u, v, k, hprefix, he, hsuffix, hcount⟩ := ih npos
    exact ⟨u, v, k, .cons hf hprefix, he, hsuffix, hcount⟩
  | currentStep he htail =>
    exact ⟨_, _, _, .nil _, he, htail, rfl⟩

/-- Finite-budget form of the target passed to the faster-rank sampler. -/
theorem fastReachableReducingGate {fast current : State → State → Prop} {target : State → Prop}
    {x : State} {n : Nat} (possible : canReachWithin fast current target x (n + 1))
    (minimal : ¬ canReachWithin fast current target x n) :
    ∃ u v, FastPath fast x u ∧ current u v ∧ canReachWithin fast current target v n := by
  obtain ⟨z, k, hz, hw, hk⟩ := possible
  have hmin : n < k := by
    by_cases h : n < k
    · exact h
    · exact (minimal ⟨z, k, hz, hw, by omega⟩).elim
  obtain ⟨u, v, l, hprefix, he, hsuffix, hcount⟩ := firstChargedEdge hw (by omega)
  exact ⟨u, v, hprefix, he, ⟨z, l, hz, hsuffix, by omega⟩⟩

/-- At a favorable current-rank ring, a fast gap precedes an accepted edge
    or a null mark. Both alternatives can be used at a fixed ring budget. -/
inductive FavorableRings (fast current : State → State → Prop) : Nat → State → State → Prop
  | nil (x) : FavorableRings fast current 0 x x
  | cons {n x gate y z} : FastPath fast x gate → (gate = y ∨ current gate y) →
      FavorableRings fast current n y z → FavorableRings fast current (n + 1) x z

theorem CountedPath.zeroImpliesFast {fast current : State → State → Prop}
    {x z : State} {n : Nat} (path : CountedPath fast current x z n) (zero : n = 0) :
    FastPath fast x z := by
  induction path with
  | nil => exact .nil _
  | fastStep h _ ih => exact .cons h (ih zero)
  | currentStep => omega

/-- End the fixed ring sequence with one fast gap. A state from which the
    target needs zero further current-rank edges need not already be a target. -/
theorem finishAfterFavorableRings {fast current : State → State → Prop} {target : State → Prop}
    {x : State} {n : Nat} (possible : canReachWithin fast current target x n) :
    ∃ y z, FavorableRings fast current n x y ∧ FastPath fast y z ∧ target z := by
  classical
  induction n generalizing x with
  | zero =>
    obtain ⟨z, l, hz, path, hl⟩ := possible
    exact ⟨x, z, .nil x, path.zeroImpliesFast (by omega), hz⟩
  | succ n ih =>
    by_cases cheaper : canReachWithin fast current target x n
    · obtain ⟨y, z, rings, gap, hz⟩ := ih cheaper
      exact ⟨y, z, .cons (.nil x) (.inl rfl) rings, gap, hz⟩
    · obtain ⟨gate, v, gap, edge, cheaper⟩ := fastReachableReducingGate possible cheaper
      obtain ⟨y, z, rings, lastGap, hz⟩ := ih cheaper
      exact ⟨y, z, .cons gap (.inr edge) rings, lastGap, hz⟩

end Ranks

section ClockBounds

variable {Weight : Type u} [OfNat Weight 1] [Mul Weight] [LE Weight]

def prefixProduct (part : Nat → Weight) : Nat → Weight
  | 0 => 1
  | n + 1 => prefixProduct part n * part n

/-- Conditional lower bounds compose even when the successive probabilities
    are different. For the clock argument the ordered weights are in [0, ∞).
    The factorization of prefix probabilities is supplied by the clock model. -/
theorem conditionedAttemptsLowerBound
    (refl : ∀ a : Weight, a ≤ a)
    (monoMul : ∀ {a b c d : Weight}, a ≤ b → c ≤ d → a * c ≤ b * d)
    (mass lower actual : Nat → Weight) (initial : mass 0 = 1)
    (conditionalBound : ∀ n, lower n ≤ actual n)
    (next : ∀ n, mass (n + 1) = mass n * actual n) (n : Nat) :
    prefixProduct lower n ≤ mass n := by
  induction n with
  | zero =>
    rw [initial]
    exact refl _
  | succ n ih =>
    rw [next n]
    exact monoMul ih (conditionalBound n)

end ClockBounds

section Boundaries

/-- A copy of height at most the starting layer cannot create an upward
    exit. An upward exit at a higher copy is bounded by that copy's height. -/
theorem upwardEdgeUsesItsOwnRank {H : Type u} [LE H] [LT H]
    (noCycle : ∀ {a b : H}, a < b → ¬ b ≤ a)
    (total : ∀ a b : H, a ≤ b ∨ b ≤ a) {before after rank : H}
    (forward : (rank ≤ before → after ≤ before) ∧ (before ≤ rank → after ≤ rank))
    (up : before < after) : ¬ rank ≤ before ∧ after ≤ rank := by
  have hr : ¬ rank ≤ before := fun h => noCycle up (forward.1 h)
  exact ⟨hr, forward.2 ((total rank before).resolve_left hr)⟩

/- These laws hold for real expectations. The sign of the local drift, the
   bounds on the leakage, and the passage to an infinite horizon are inputs. -/
structure AdditiveBudgetLaws (H : Type u) [Zero H] [Add H] [LE H] : Prop where
  order : HeightLaws H
  comm : ∀ x y : H, x + y = y + x
  assoc : ∀ x y z : H, (x + y) + z = x + (y + z)
  zeroRight : ∀ x : H, x + 0 = x

variable {H : Type u} [Zero H] [Add H] [LE H]

theorem AdditiveBudgetLaws.addLeft (laws : AdditiveBudgetLaws H)
    {x y : H} (h : x ≤ y) (d : H) : d + x ≤ d + y := by
  rw [laws.comm d x, laws.comm d y]
  exact laws.order.addRight h d

def prefixReward (debit : Nat → H) : Nat → H
  | 0 => 0
  | n + 1 => prefixReward debit n + debit n

/-- Finite telescoping after stopping. In probability, `mass` is the expected
    terminal value at the stopped horizon and `debit` an expected visit reward. -/
theorem truncatedRewardBound (laws : AdditiveBudgetLaws H) (mass debit : Nat → H)
    (drift : ∀ n, mass (n + 1) + debit n ≤ mass n) (n : Nat) :
    mass n + prefixReward debit n ≤ mass 0 := by
  induction n with
  | zero =>
    rw [prefixReward, laws.zeroRight]
    exact laws.order.refl _
  | succ n ih =>
    have grouped : mass (n + 1) + prefixReward debit (n + 1) =
        (mass (n + 1) + debit n) + prefixReward debit n := by
      rw [prefixReward, laws.comm (prefixReward debit n) (debit n), laws.assoc]
    rw [grouped]
    exact laws.order.trans (laws.order.addRight (drift n) _) ih

theorem absorbLeakageAndCharge (laws : AdditiveBudgetLaws H) {active other leak debit : H}
    (activeDrift : (active + leak) + debit ≤ 0) (otherDrift : other ≤ leak) :
    (active + other) + debit ≤ 0 := by
  exact laws.order.trans (laws.order.addRight (laws.addLeft otherDrift active) debit) activeDrift

/-- Add the bounds before and after the first outer exit. -/
theorem splitExcursionBound (laws : AdditiveBudgetLaws H)
    {total before after entranceBudget farBudget : H}
    (split : total = before + after) (localBound : before ≤ entranceBudget)
    (returnBound : after ≤ farBudget) : total ≤ entranceBudget + farBudget := by
  rw [split]
  exact laws.order.trans (laws.order.addRight localBound after) (laws.addLeft returnBound entranceBudget)

end Boundaries

#print axioms deleteNonnegativeLoop
#print axioms pumpToTarget
#print axioms WordUnder.liftWithStock
#print axioms boundedWitnessFromFiniteBasis
#print axioms layerBoundAlongWord
#print axioms fastCopyPreservesLayer
#print axioms budgetInvariantAlongFast
#print axioms reachableAfterUnrestrictedPrefix
#print axioms fastReachableReducingGate
#print axioms finishAfterFavorableRings
#print axioms conditionedAttemptsLowerBound
#print axioms upwardEdgeUsesItsOwnRank
#print axioms truncatedRewardBound
#print axioms absorbLeakageAndCharge
#print axioms splitExcursionBound

end AIM272
