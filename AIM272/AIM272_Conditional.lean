import AIM272_NewLemmas

/-!
# AIM 272: a conditional proof of the new estimates and the return criterion

The imported file supplies the previous path and finite-horizon lemmas.
Here probability laws are expressed as interfaces for nonnegative real
quantities. The order, kernel composition, and passage to the supremum are
explicit hypotheses, so no probability space is postulated as a Lean axiom.
-/

set_option warningAsError true

namespace AIM272

section WitnessWindow

variable {H : Type u} {Phase : Type v} {Label : Type w} [Add H] [LE H]
variable {step : Label → Phase → Phase → Prop} {delta guard : Label → H} {cap : H}

/-- The recorded points are the origins of the edges in a cap-feasible word. -/
inductive WordTrace (step : Label → Phase → Phase → Prop) (delta guard : Label → H) (cap : H) :
    Phase × H → List (Phase × H) → Phase × H → Prop
  | nil (x) : WordTrace step delta guard cap x [] x
  | cons {r p next h trail endPoint} : step r p next → h + guard r ≤ cap →
      WordTrace step delta guard cap (next, h + delta r) trail endPoint →
      WordTrace step delta guard cap (p, h) ((p, h) :: trail) endPoint

theorem WordUnder.toTrace {p q : Phase} {x y : H} {w : List Label}
    (path : WordUnder step delta guard cap p x w q y) :
    ∃ points, points.length = w.length ∧ WordTrace step delta guard cap (p, x) points (q, y) := by
  induction path with
  | nil => exact ⟨[], rfl, .nil _⟩
  | cons edge bounded _ ih =>
    obtain ⟨points, size, trace⟩ := ih
    exact ⟨_ :: points, congrArg (· + 1) size, .cons edge bounded trace⟩

theorem WordTrace.toWord {initial final : Phase × H} {points : List (Phase × H)}
    (trace : WordTrace step delta guard cap initial points final) :
    ∃ word, word.length = points.length ∧
      WordUnder step delta guard cap initial.1 initial.2 word final.1 final.2 := by
  induction trace with
  | nil => exact ⟨[], rfl, .nil _ _⟩
  | cons edge bounded _ ih =>
    obtain ⟨word, size, tail⟩ := ih
    exact ⟨_ :: word, congrArg (· + 1) size, .cons edge bounded tail⟩

theorem WordTrace.split {p q : Phase × H} {stem tail : List (Phase × H)}
    (trace : WordTrace step delta guard cap p (stem ++ tail) q) :
    ∃ mid, WordTrace step delta guard cap p stem mid ∧ WordTrace step delta guard cap mid tail q := by
  induction stem generalizing p with
  | nil => exact ⟨p, .nil p, trace⟩
  | cons v stem ih =>
    cases trace with
    | cons reaction enabled rest =>
      obtain ⟨mid, left, right⟩ := ih rest
      exact ⟨mid, .cons reaction enabled left, right⟩

theorem WordTrace.splitAtPoint {p q v : Phase × H} {stem tail : List (Phase × H)}
    (trace : WordTrace step delta guard cap p (stem ++ v :: tail) q) :
    WordTrace step delta guard cap p stem v ∧ WordTrace step delta guard cap v (v :: tail) q := by
  obtain ⟨mid, left, right⟩ := trace.split
  have here : v = mid := by cases right; rfl
  cases here
  exact ⟨left, right⟩

private theorem distinctStatesFit {A : Type v} (states pool : List A)
    (inside : ∀ a ∈ states, a ∈ pool) (distinct : states.Nodup) : states.length ≤ pool.length := by
  classical
  induction states generalizing pool with
  | nil => simp
  | cons x rest ih =>
    obtain ⟨new, nodup⟩ := List.nodup_cons.mp distinct
    have member := inside x (by simp)
    have tailInside : ∀ a ∈ rest, a ∈ pool.erase x := by
      intro a ha
      have ne : a ≠ x := by
        intro eq
        subst a
        exact new ha
      exact (List.mem_erase_of_ne ne).2 (inside a (List.mem_cons_of_mem _ ha))
    have h := ih (pool.erase x) tailInside nodup
    rw [List.length_erase_of_mem member] at h
    have positive : 0 < pool.length := by
      cases pool with
      | nil => simp at member
      | cons a tl => simp
    simp only [List.length_cons]
    omega

private theorem repeatedValue {A : Type u} {B : Type v} (f : A → B) (xs : List A)
    (repeatExists : ¬ (xs.map f).Nodup) :
    ∃ stem a between b tail, xs = stem ++ a :: between ++ b :: tail ∧ f a = f b := by
  classical
  induction xs with
  | nil => simp at repeatExists
  | cons a rest ih =>
    by_cases found : f a ∈ rest.map f
    · obtain ⟨b, member, hb⟩ := List.mem_map.mp found
      obtain ⟨between, tail, parts⟩ := List.append_of_mem member
      exact ⟨[], a, between, b, tail, by simp [parts], hb.symm⟩
    · have repeats : ¬ (rest.map f).Nodup := fun h => repeatExists (List.nodup_cons.mpr ⟨found, h⟩)
      obtain ⟨s, b, between, c, t, parts, same⟩ := ih repeats
      exact ⟨a :: s, b, between, c, t, by simp [parts], same⟩

/-- A window of length |cube|+1 either sees an exterior point or contains
    two occurrences of a phase. The two times need not have equal heights. -/
theorem finitePhaseWindow {V : Type u} (phase : V → Phase) (nodes : List V) (cube : List Phase)
    (long : cube.length < nodes.length) :
    (∃ v, v ∈ nodes ∧ phase v ∉ cube) ∨
      ∃ stem a between b tail, nodes = stem ++ a :: between ++ b :: tail ∧ phase a = phase b := by
  classical
  by_cases outside : ∃ v, v ∈ nodes ∧ phase v ∉ cube
  · exact .inl outside
  · apply Or.inr
    apply repeatedValue phase nodes
    intro distinct
    have fits := distinctStatesFit (nodes.map phase) cube (fun value occurs => by
      obtain ⟨v, member, rfl⟩ := List.mem_map.mp occurs
      by_cases included : phase v ∈ cube
      · exact included
      · exact (outside ⟨v, member, included⟩).elim) distinct
    rw [List.length_map] at fits
    exact (Nat.not_lt_of_ge fits) long

/-- The bounded-witness scan. Its exterior continuation is the
    lower-dimensional inductive hypothesis after stock restoration.
    The pump budget uses the least downward displacement among the finite
    short words and the Archimedean estimate on heights. -/
theorem shortenToFiniteWindow (laws : HeightLaws H) (cube : List Phase) (outsideBound pumpBound : Nat)
    {p : Phase} {x target : H}
    (continueOutside : ∀ {mid : Phase} {h : H} {stem : List Label},
      WordUnder step delta guard cap p x stem mid h → mid ∉ cube →
      ∀ {tail : List Label} {q : Phase} {y : H},
        WordUnder step delta guard cap mid h tail q y → y ≤ target →
        ∃ w q' y', w.length ≤ outsideBound ∧ WordUnder step delta guard cap mid h w q' y' ∧ y' ≤ target)
    (pumpShort : ∀ {mid : Phase} {h h' : H} {stem cycle : List Label},
      WordUnder step delta guard cap p x stem mid h →
      WordUnder step delta guard cap mid h cycle mid h' →
      cycle.length ≤ cube.length + 1 → ¬ h ≤ h' →
      ∃ w y', w.length ≤ pumpBound ∧ WordUnder step delta guard cap mid h w mid y' ∧ y' ≤ target)
    {initial : List Label} {finish : Phase} {z : H}
    (feasible : WordUnder step delta guard cap p x initial finish z) (hit : z ≤ target) :
    ∃ w q y, w.length ≤ cube.length + 1 + max outsideBound pumpBound ∧
      WordUnder step delta guard cap p x w q y ∧ y ≤ target := by
  classical
  let windowSize := cube.length + 1
  have shorten : ∀ n (word : List Label) (q : Phase) (y : H),
      word.length = n → WordUnder step delta guard cap p x word q y → y ≤ target →
      ∃ w q' y', w.length ≤ windowSize + max outsideBound pumpBound ∧
        WordUnder step delta guard cap p x w q' y' ∧ y' ≤ target := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro word q y len path found
      by_cases short : word.length ≤ windowSize
      · exact ⟨word, q, y, Nat.le_trans short (Nat.le_add_right _ _), path, found⟩
      obtain ⟨trace, traceLen, recorded⟩ := path.toTrace
      let scanned := trace.take windowSize
      let later := trace.drop windowSize
      have whole : trace = scanned ++ later := (List.take_append_drop _ _).symm
      have nScan : scanned.length = windowSize := List.length_take_of_le (by omega)
      have big : cube.length < scanned.length := by simp [nScan, windowSize]
      by_cases early : ∃ v ∈ scanned, v.2 ≤ target
      · obtain ⟨v, member, lower⟩ := early
        obtain ⟨stem, tail, parts⟩ := List.append_of_mem member
        have split : trace = stem ++ v :: (tail ++ later) := by
          simpa only [parts, List.append_assoc, List.cons_append] using whole
        rw [split] at recorded
        obtain ⟨w, size, prefixPath⟩ := recorded.splitAtPoint.1.toWord
        have stemBound := congrArg List.length parts
        simp only [List.length_append, List.length_cons, nScan] at stemBound
        exact ⟨w, v.1, v.2, by omega, prefixPath, lower⟩
      rcases finitePhaseWindow Prod.fst scanned cube big with outside | repeated
      · obtain ⟨v, member, exterior⟩ := outside
        obtain ⟨stem, tail, parts⟩ := List.append_of_mem member
        have split : trace = stem ++ v :: (tail ++ later) := by
          simpa only [parts, List.append_assoc, List.cons_append] using whole
        rw [split] at recorded
        obtain ⟨left, right⟩ := recorded.splitAtPoint
        obtain ⟨w, size, prefixPath⟩ := left.toWord
        obtain ⟨_, _, suffixPath⟩ := right.toWord
        obtain ⟨v', q', y', n', finishPath, below⟩ :=
          continueOutside prefixPath exterior suffixPath found
        have stemBound := congrArg List.length parts
        simp only [List.length_append, List.length_cons, nScan] at stemBound
        exact ⟨w ++ v', q', y', by simp only [List.length_append]; omega,
          prefixPath.append finishPath, below⟩
      · obtain ⟨stem, a, cycle, b, tail, parts, same⟩ := repeated
        have split : trace = stem ++ a :: (cycle ++ b :: (tail ++ later)) := by
          simpa only [parts, List.append_assoc, List.cons_append] using whole
        rw [split] at recorded
        obtain ⟨left, middle⟩ := recorded.splitAtPoint
        have between : WordTrace step delta guard cap a ((a :: cycle) ++ b :: (tail ++ later)) (q, y) :=
          middle
        obtain ⟨loop, remaining⟩ := between.splitAtPoint
        obtain ⟨u, nu, startPath⟩ := left.toWord
        obtain ⟨v, nv, loopPath⟩ := loop.toWord
        obtain ⟨w, nw, tailPath⟩ := remaining.toWord
        have cyclePath : WordUnder step delta guard cap a.1 a.2 v a.1 b.2 := by
          simpa only [← same] using loopPath
        have afterPath : WordUnder step delta guard cap a.1 b.2 w q y := by
          simpa only [← same] using tailPath
        by_cases nonnegative : a.2 ≤ b.2
        · obtain ⟨shorter, lower⟩ :=
            deleteNonnegativeLoop laws startPath cyclePath afterPath nonnegative
          have full := congrArg List.length split
          simp only [List.length_append, List.length_cons, traceLen, len] at full
          have less : (u ++ w).length < n := by
            simp only [List.length_cons, List.length_append] at nw
            simp only [List.length_append]
            omega
          exact ih _ less _ _ _ rfl shorter (laws.trans lower found)
        · have pieces := congrArg List.length parts
          simp only [List.length_append, List.length_cons, nScan] at pieces nv
          have cycleSize : v.length ≤ cube.length + 1 := by
            dsimp [windowSize] at pieces
            omega
          obtain ⟨repeatWord, endpoint, size, descend, reached⟩ :=
            pumpShort startPath cyclePath cycleSize nonnegative
          exact ⟨u ++ repeatWord, a.1, endpoint, by simp only [List.length_append]; omega,
            startPath.append descend, reached⟩
  exact shorten _ _ _ _ rfl feasible hit

end WitnessWindow

section Arithmetic

variable {W : Type u} [Zero W] [OfNat W 1] [Add W] [Mul W] [LE W] [LT W]

/-- The required laws on nonnegative reals. The finite-horizon proofs use
    multiplication only on nonnegative quantities, with no subtraction. -/
structure NonnegativeLaws (W : Type u) [Zero W] [OfNat W 1] [Add W] [Mul W] [LE W] [LT W] :
    Prop where
  additive : AdditiveBudgetLaws W
  nonneg : ∀ w : W, 0 ≤ w
  mulRight : ∀ {a b : W}, a ≤ b → ∀ c, a * c ≤ b * c
  mulComm : ∀ a b : W, a * b = b * a
  mulAssoc : ∀ a b c : W, (a * b) * c = a * (b * c)
  mulOne : ∀ a : W, a * 1 = a
  mulPos : ∀ {a b : W}, 0 < a → 0 < b → 0 < a * b
  addMul : ∀ a b c : W, (a + b) * c = a * c + b * c
  cancelRight : ∀ {a b c : W}, 0 < c → a * c ≤ b * c → a ≤ b

namespace NonnegativeLaws

theorem mulLeft (laws : NonnegativeLaws W) {a b : W} (h : a ≤ b) (c : W) : c * a ≤ c * b := by
  rw [laws.mulComm c a, laws.mulComm c b]
  exact laws.mulRight h c

theorem addBoth (laws : NonnegativeLaws W) {a b c d : W} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a + c ≤ b + d :=
  laws.additive.order.trans (laws.additive.order.addRight h₁ c) (laws.additive.addLeft h₂ b)

theorem mulBoth (laws : NonnegativeLaws W) {a b c d : W} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a * c ≤ b * d :=
  laws.additive.order.trans (laws.mulRight h₁ c) (laws.mulLeft h₂ b)

theorem leftLeAdd (laws : NonnegativeLaws W) (a b : W) : a ≤ a + b := by
  have h := laws.additive.addLeft (laws.nonneg b) a
  rwa [laws.additive.zeroRight] at h

theorem rightLeAdd (laws : NonnegativeLaws W) (a b : W) : b ≤ a + b := by
  rw [laws.additive.comm a b]
  exact laws.leftLeAdd b a

theorem mulSum (laws : NonnegativeLaws W) (a b c : W) : a * (b + c) = a * b + a * c := by
  rw [laws.mulComm a (b + c), laws.addMul, laws.mulComm a b, laws.mulComm a c]

theorem prefixReward_mono (laws : NonnegativeLaws W) {f g : Nat → W}
    (lower : ∀ n, f n ≤ g n) (n : Nat) : prefixReward f n ≤ prefixReward g n := by
  induction n with
  | zero => exact laws.additive.order.refl 0
  | succ n ih => exact laws.addBoth ih (lower n)

end NonnegativeLaws

/-- An observed limit is the supremum of its finite-horizon approximations,
    as far as upper bounds are concerned. For event and reward counts this
    interface is discharged by monotone convergence. -/
def limitPreservesUpper (approximants : Nat → W) (limit : W) : Prop :=
  ∀ upper, (∀ n, approximants n ≤ upper) → limit ≤ upper

/-- Summing the reward over successive epochs gives a uniform finite-horizon
    estimate. The lost fraction and the surviving ratio sum to one. -/
theorem epochRewardBound (laws : NonnegativeLaws W) {ratio loss price : W}
    (total : loss + ratio = 1) (live reward : Nat → W)
    (contract : ∀ n, live (n + 1) ≤ ratio * live n)
    (inEpoch : ∀ n, reward n ≤ price * live n) (n : Nat) :
    prefixReward (fun i => loss * reward i) n ≤ price * live 0 := by
  have drift : ∀ i, price * live (i + 1) + loss * reward i ≤ price * live i := by
    intro i
    have step := laws.addBoth (laws.mulLeft (contract i) price) (laws.mulLeft (inEpoch i) loss)
    have collect : price * (ratio * live i) + loss * (price * live i) = price * live i := by
      rw [← laws.mulAssoc price ratio, laws.mulComm price ratio, laws.mulAssoc ratio price,
        laws.additive.comm, ← laws.addMul, total, laws.mulComm 1, laws.mulOne]
    rwa [collect] at step
  have h := truncatedRewardBound laws.additive (fun i => price * live i)
    (fun i => loss * reward i) drift n
  exact laws.additive.order.trans (laws.rightLeAdd _ _) h

/-- Terminal exit mass and cumulative visits are both payable from a stopped
    entrance budget. The price can differ for the boundary and for each state. -/
structure ShellObservations (W : Type u) where
  terminal : Nat → W
  debit : Nat → W
  exitBefore : Nat → W
  visitsBefore : Nat → W
  exitProbability : W
  visitsBeforeExit : W
  entranceBudget : W
  exitPrice : W
  visitPrice : W

structure ShellLaws (s : ShellObservations W) : Prop where
  initial : s.terminal 0 ≤ s.entranceBudget
  drift : ∀ n, s.terminal (n + 1) + s.debit n ≤ s.terminal n
  actualExit : ∀ n, s.exitBefore n * s.exitPrice ≤ s.terminal n
  visitCharge : ∀ n, s.visitsBefore n * s.visitPrice ≤ prefixReward s.debit n
  exitLimit : limitPreservesUpper s.exitBefore s.exitProbability
  visitLimit : limitPreservesUpper s.visitsBefore s.visitsBeforeExit
  exitPricePos : 0 < s.exitPrice
  visitPricePos : 0 < s.visitPrice

theorem stoppedShellEstimates (laws : NonnegativeLaws W) {s : ShellObservations W}
    (shell : ShellLaws s) {exitCap visitCap : W}
    (exitBudget : s.entranceBudget ≤ exitCap * s.exitPrice)
    (visitBudget : s.entranceBudget ≤ visitCap * s.visitPrice) :
    s.exitProbability ≤ exitCap ∧ s.visitsBeforeExit ≤ visitCap := by
  have finite : ∀ n, s.terminal n + prefixReward s.debit n ≤ s.entranceBudget :=
    fun n => laws.additive.order.trans
      (truncatedRewardBound laws.additive s.terminal s.debit shell.drift n) shell.initial
  constructor
  · apply shell.exitLimit
    intro n
    apply laws.cancelRight shell.exitPricePos
    exact laws.additive.order.trans (shell.actualExit n)
      (laws.additive.order.trans (laws.leftLeAdd _ _)
        (laws.additive.order.trans (finite n) exitBudget))
  · apply shell.visitLimit
    intro n
    apply laws.cancelRight shell.visitPricePos
    exact laws.additive.order.trans (shell.visitCharge n)
      (laws.additive.order.trans (laws.rightLeAdd _ _)
        (laws.additive.order.trans (finite n) visitBudget))

private theorem normalizeVisitBound (laws : NonnegativeLaws W)
    {visits factorial q rateFloor occupancy growthCap : W}
    (physicalTime : visits = q * occupancy) (uniformRate : rateFloor ≤ q)
    (positiveFloor : 0 < rateFloor) (scaled : visits * factorial ≤ growthCap * rateFloor) :
    occupancy * factorial ≤ growthCap := by
  apply laws.cancelRight positiveFloor
  have scaledTime : (occupancy * factorial) * q = visits * factorial := by
    rw [physicalTime, laws.mulAssoc q, laws.mulComm q]
  have h := laws.mulLeft uniformRate (occupancy * factorial)
  rw [scaledTime] at h
  exact laws.additive.order.trans h scaled

/-- Normalize visit counts by the actual holding rates, after adding the
    strong Markov contribution from after the first outer exit. -/
theorem factorialOccupancyBound (laws : NonnegativeLaws W) {s : ShellObservations W}
    (shell : ShellLaws s) {exitCap visitCap returnBudget visitsAfter visits : W}
    {factorial q rateFloor occupancy growthCap : W}
    (exitBudget : s.entranceBudget ≤ exitCap * s.exitPrice)
    (visitBudget : s.entranceBudget ≤ visitCap * s.visitPrice)
    (lateVisits : visitsAfter ≤ s.exitProbability * returnBudget)
    (split : visits = s.visitsBeforeExit + visitsAfter)
    (physicalTime : visits = q * occupancy)
    (uniformRate : rateFloor ≤ q) (positiveFloor : 0 < rateFloor)
    (sizeBudget : (visitCap + exitCap * returnBudget) * factorial ≤ growthCap * rateFloor) :
    visits * factorial ≤ growthCap * rateFloor ∧ occupancy * factorial ≤ growthCap := by
  obtain ⟨exitEstimate, preEstimate⟩ := stoppedShellEstimates laws shell exitBudget visitBudget
  have lateEstimate := laws.additive.order.trans lateVisits (laws.mulRight exitEstimate returnBudget)
  have sumEstimate := splitExcursionBound laws.additive split preEstimate lateEstimate
  have scaled := laws.additive.order.trans (laws.mulRight sumEstimate factorial) sizeBudget
  exact ⟨scaled, normalizeVisitBound laws physicalTime uniformRate positiveFloor scaled⟩

end Arithmetic

section RankRace

variable {State : Type u} {W : Type v}
  [Zero W] [OfNat W 1] [Add W] [Mul W] [LE W] [LT W]

inductive RaceAction
  | gap
  | ring

def rankRounds : Nat → List RaceAction
  | 0 => []
  | n + 1 => [.gap, .ring] ++ rankRounds n

theorem rankRounds_add (n m : Nat) : rankRounds (n + m) = rankRounds n ++ rankRounds m := by
  induction n with
  | zero => simp [rankRounds]
  | succ n ih => simp [Nat.succ_add, rankRounds, ih]

def finalBlockLower (fastLower markLower : W) : Nat → W
  | 0 => fastLower
  | n + 1 => (fastLower * markLower) * finalBlockLower fastLower markLower n

def gateWithin (below : State → Prop) (fast charged : State → State → Prop)
    (target : State → Prop) (n : Nat) (x : State) : Prop :=
  below x ∨ ∃ y, charged x y ∧ canReachWithin fast charged target y n

/-- Probability of a conditioned program of faster gaps and current-rank
    marks, together with the elementary support and conditioning laws. -/
structure RankKernel (fast charged : State → State → Prop) (killed : State → Prop) where
  probability : List RaceAction → State → (State → Prop) → W
  enlarge : ∀ {prog x p q}, (∀ y, p y → q y) → probability prog x p ≤ probability prog x q
  compose : ∀ {first rest x event success a b}, a ≤ probability first x event →
    (∀ y, event y → b ≤ probability rest y success) →
    a * b ≤ probability (first ++ rest) x success
  stuck : ∀ {prog x} {goal : State → Prop}, killed x → 1 ≤ probability prog x (fun y => killed y ∨ goal y)
  gapSupport : ∀ x, 1 ≤ probability [.gap] x (fun y => killed y ∨ FastPath fast x y)
  roundsSupport : ∀ n x, 1 ≤ probability (rankRounds n) x
    (fun y => killed y ∨ ∃ count, CountedPath fast charged x y count)

/-- The previous rank is applied to the target and to the finitely many gate
    predicates of budgets below B. One common lower bound suffices. -/
structure RankSamplingInputs
    (fast charged : State → State → Prop) (below killed target : State → Prop)
    (kernel : RankKernel (W := W) fast charged killed) (B : Nat)
    (fastLower markLower : W) : Prop where
  fastPos : 0 < fastLower
  fastLeOne : fastLower ≤ 1
  markPos : 0 < markLower
  markLeOne : markLower ≤ 1
  belowKilled : ∀ x, below x → killed x
  reverseFast : ∀ {x y}, FastPath fast x y → FastPath fast y x
  returnOrTarget : ∀ x y, fast x y ∨ charged x y →
    (∃ n, CountedPath fast charged y x n) ∨ (∃ n, canReachWithin fast charged target y n)
  budget : ∀ x, (∃ n, canReachWithin fast charged target x n) →
    canReachWithin fast charged target x B
  nullMark : ∀ x, markLower ≤ kernel.probability [.ring] x (fun y => killed y ∨ y = x)
  labeledMark : ∀ {x y}, charged x y →
    markLower ≤ kernel.probability [.ring] x (fun z => killed z ∨ z = y)
  sampleTarget : ∀ {x y}, FastPath fast x y → target y →
    fastLower ≤ kernel.probability [.gap] x (fun z => killed z ∨ target z)
  sampleGate : ∀ {n x y}, n < B → FastPath fast x y → gateWithin below fast charged target n y →
    fastLower ≤ kernel.probability [.gap] x
      (fun z => killed z ∨ gateWithin below fast charged target n z)

theorem finalBlockLower_pos (laws : NonnegativeLaws W) {a b : W}
    (ap : 0 < a) (bp : 0 < b) (n : Nat) : 0 < finalBlockLower a b n := by
  induction n with
  | zero => exact ap
  | succ n ih => exact laws.mulPos (laws.mulPos ap bp) ih

theorem finalBlockLower_le_one (laws : NonnegativeLaws W) {a b : W}
    (a1 : a ≤ 1) (b1 : b ≤ 1) (n : Nat) : finalBlockLower a b n ≤ 1 := by
  induction n with
  | zero => exact a1
  | succ n ih =>
    have ab := laws.mulBoth a1 b1
    rw [laws.mulOne] at ab
    have h := laws.mulBoth ab ih
    rwa [laws.mulOne] at h

/-- Given a remaining budget, a real mark can reduce it after a faster
    sample to the gate. A null mark is sufficient when the budget is slack. -/
theorem oneRoundDecreasesBudget (laws : NonnegativeLaws W) {fast charged : State → State → Prop}
    {below killed target : State → Prop} {kernel : RankKernel (W := W) fast charged killed}
    {B n : Nat} {fastLower markLower : W}
    (inputs : RankSamplingInputs fast charged below killed target kernel B fastLower markLower)
    (small : n < B) {x : State} (possible : canReachWithin fast charged target x (n + 1)) :
    fastLower * markLower ≤ kernel.probability [.gap, .ring] x
      (fun y => killed y ∨ canReachWithin fast charged target y n) := by
  classical
  by_cases cheaper : canReachWithin fast charged target x n
  · have gap : fastLower ≤ kernel.probability [.gap] x
        (fun y => killed y ∨ canReachWithin fast charged target y n) := by
      apply laws.additive.order.trans inputs.fastLeOne
      apply laws.additive.order.trans (kernel.gapSupport x)
      apply kernel.enlarge
      rintro y (dead | path)
      · exact .inl dead
      · exact .inr ((budgetInvariantAlongFast path (inputs.reverseFast path)).mp cheaper)
    have mark : ∀ y, (killed y ∨ canReachWithin fast charged target y n) →
        markLower ≤ kernel.probability [.ring] y (fun z => killed z ∨ canReachWithin fast charged target z n) := by
      rintro y (dead | within)
      · exact laws.additive.order.trans inputs.markLeOne (kernel.stuck dead)
      · apply laws.additive.order.trans (inputs.nullMark y)
        apply kernel.enlarge
        rintro z (doneHere | rfl)
        · exact .inl doneHere
        · exact .inr within
    exact kernel.compose gap mark
  · obtain ⟨u, v, way, mark, cheaperAfter⟩ := fastReachableReducingGate possible cheaper
    have gap := inputs.sampleGate small way (Or.inr ⟨v, mark, cheaperAfter⟩)
    have marked : ∀ y, (killed y ∨ gateWithin below fast charged target n y) →
        markLower ≤ kernel.probability [.ring] y (fun z => killed z ∨ canReachWithin fast charged target z n) := by
      rintro y (dead | (down | ⟨z, edge, within⟩))
      · exact laws.additive.order.trans inputs.markLeOne (kernel.stuck dead)
      · exact laws.additive.order.trans inputs.markLeOne (kernel.stuck (inputs.belowKilled y down))
      · apply laws.additive.order.trans (inputs.labeledMark edge)
        apply kernel.enlarge
        rintro a (doneHere | rfl)
        · exact .inl doneHere
        · exact .inr within
    exact kernel.compose gap marked

theorem finalRankBlock (laws : NonnegativeLaws W) {fast charged : State → State → Prop}
    {below killed target : State → Prop} {kernel : RankKernel (W := W) fast charged killed}
    {B : Nat} {fastLower markLower : W}
    (inputs : RankSamplingInputs fast charged below killed target kernel B fastLower markLower)
    (n : Nat) (small : n ≤ B) :
    ∀ x, killed x ∨ canReachWithin fast charged target x n →
      finalBlockLower fastLower markLower n ≤ kernel.probability (rankRounds n ++ [.gap]) x
        (fun y => killed y ∨ target y) := by
  induction n with
  | zero =>
    rintro x (dead | ⟨y, c, goal, path, count⟩)
    · exact laws.additive.order.trans inputs.fastLeOne (kernel.stuck dead)
    · exact inputs.sampleTarget (path.zeroImpliesFast (by omega)) goal
  | succ n ih =>
    rintro x (dead | possible)
    · exact laws.additive.order.trans
        (finalBlockLower_le_one laws inputs.fastLeOne inputs.markLeOne (n + 1)) (kernel.stuck dead)
    · have round := oneRoundDecreasesBudget laws inputs (by omega) possible
      have follow := kernel.compose round (ih (by omega))
      simpa only [rankRounds, List.append_assoc] using follow

/-- Conditioned on N current-rank marks before observation, leave the first
    N - B marks unrestricted. Only the final B and the final fast gap cost a
    success factor. The raw race law then removes the count conditioning. -/
theorem rankedClockLowerBound (laws : NonnegativeLaws W) {fast charged : State → State → Prop}
    {below killed target : State → Prop} {kernel : RankKernel (W := W) fast charged killed}
    {B : Nat} {fastLower markLower countLower : W}
    (inputs : RankSamplingInputs fast charged below killed target kernel B fastLower markLower)
    (countPos : 0 < countLower) {x : State} (start : ∃ n, canReachWithin fast charged target x n)
    (sampled : W)
    (raceMixture : ∀ p, (∀ n, B ≤ n →
        p ≤ kernel.probability (rankRounds n ++ [.gap]) x (fun y => killed y ∨ target y)) →
      countLower * p ≤ sampled) :
    0 < countLower * finalBlockLower fastLower markLower B ∧
    countLower * finalBlockLower fastLower markLower B ≤ sampled := by
  refine ⟨laws.mulPos countPos (finalBlockLower_pos laws inputs.fastPos inputs.markPos B), ?_⟩
  apply raceMixture
  intro n enough
  have support := kernel.roundsSupport (n - B) x
  have prefixBudget : 1 ≤ kernel.probability (rankRounds (n - B)) x
      (fun y => killed y ∨ canReachWithin fast charged target y B) := by
    apply laws.additive.order.trans support
    apply kernel.enlarge
    rintro y (dead | ⟨_, path⟩)
    · exact .inl dead
    · exact .inr (inputs.budget y (reachableAfterUnrestrictedPrefix inputs.returnOrTarget path start))
  have result := kernel.compose prefixBudget (finalRankBlock laws inputs B (Nat.le_refl B))
  rw [laws.mulComm 1, laws.mulOne, ← List.append_assoc, ← rankRounds_add,
    Nat.sub_add_cancel enough] at result
  exact result

end RankRace

section ReturnCriterion

variable {State : Type u} {Boundary : Type v} {W : Type w}
  [Zero W] [OfNat W 1] [Add W] [Mul W] [LE W] [LT W]

/-- An enumeration of the countable class is supplied by the stochastic model. -/
def finiteVisitMass (stateAt : Nat → State) (visits : State → W) : Prop :=
  ∃ bound, ∀ n, prefixReward (fun i => visits (stateAt i)) n ≤ bound

structure ExcursionData (State : Type u) (W : Type w) where
  stateAt : Nat → State
  exceptions : List State
  factorial : State → W
  rate : State → W
  visits : State → W
  occupancy : State → W
  growthCap : State → W
  summableEnvelope : State → W
  rateFloor : W

/-- For each state, the annulus is chosen at the desired factorial tolerance.
    The analytic inputs supply the size comparison and the strong Markov
    estimate. The exit and visit estimates are derived in the theorem. -/
structure ExcursionChecks (e : ExcursionData State W) : Prop where
  rateFloorPos : 0 < e.rateFloor
  rateLower : ∀ x, e.rateFloor ≤ e.rate x
  physicalTime : ∀ x, e.visits x = e.rate x * e.occupancy x
  factorialPos : ∀ x, 0 < e.factorial x
  occupancyPos : ∀ x, 0 < e.occupancy x
  envelopeSum : ∃ bound, ∀ n, prefixReward (fun i => e.summableEnvelope (e.stateAt i)) n ≤ bound
  envelopeDominates : ∀ x,
    e.growthCap x * e.rateFloor ≤ e.summableEnvelope x * e.factorial x
  finiteExceptions : ∀ x ∈ e.exceptions, e.visits x * e.factorial x ≤ e.growthCap x * e.rateFloor
  annulus : ∀ x, x ∉ e.exceptions → ∃ (s : ShellObservations W) (exitCap visitCap returnBudget visitsAfter : W),
    ShellLaws s ∧
    s.entranceBudget ≤ exitCap * s.exitPrice ∧
    s.entranceBudget ≤ visitCap * s.visitPrice ∧
    visitsAfter ≤ s.exitProbability * returnBudget ∧
    e.visits x = s.visitsBeforeExit + visitsAfter ∧
    (visitCap + exitCap * returnBudget) * e.factorial x ≤ e.growthCap x * e.rateFloor

/-- Standard excursion and interface identities. The incoming and outgoing
    functionals refer to physical occupancies and to the actual trace kernel. -/
structure ReturnBridge (e : ExcursionData State W) (Boundary : Type v) where
  nonexplosive : Prop
  positiveRecurrent : Prop
  stateAtBoundary : Boundary → State
  incoming : (State → W) → State → W
  outgoing : (State → W) → State → W
  traceIncoming : (Boundary → W) → Boundary → W
  traceOutgoing : (Boundary → W) → Boundary → W
  returnFromVisits : finiteVisitMass e.stateAt e.visits → nonexplosive ∧ positiveRecurrent
  balanceFromVisits : finiteVisitMass e.stateAt e.visits →
    ∀ x, incoming e.occupancy x = outgoing e.occupancy x
  eliminateBlocks : (∀ x, incoming e.occupancy x = outgoing e.occupancy x) →
    ∀ b, traceIncoming (e.occupancy ∘ stateAtBoundary) b =
      traceOutgoing (e.occupancy ∘ stateAtBoundary) b

/-- The end-to-end conditional conclusion. The interface weight is the
    restriction of the same excursion occupation used in the return proof. -/
theorem aim272Conditional (laws : NonnegativeLaws W) (e : ExcursionData State W)
    (checks : ExcursionChecks e) (bridge : ReturnBridge e Boundary) :
    finiteVisitMass e.stateAt e.visits ∧ bridge.nonexplosive ∧ bridge.positiveRecurrent ∧
    (∀ x, e.occupancy x * e.factorial x ≤ e.growthCap x) ∧
    ∃ nu : Boundary → W, (∀ b, nu b = e.occupancy (bridge.stateAtBoundary b)) ∧
      (∀ b, 0 < nu b) ∧
      (∀ b, bridge.traceIncoming nu b = bridge.traceOutgoing nu b) ∧
      (∀ b, nu b * e.factorial (bridge.stateAtBoundary b) ≤ e.growthCap (bridge.stateAtBoundary b)) := by
  classical
  have bounds : ∀ x, e.visits x * e.factorial x ≤ e.growthCap x * e.rateFloor ∧
      e.occupancy x * e.factorial x ≤ e.growthCap x := by
    intro x
    by_cases small : x ∈ e.exceptions
    · have fin := checks.finiteExceptions x small
      exact ⟨fin, normalizeVisitBound laws (checks.physicalTime x) (checks.rateLower x)
        checks.rateFloorPos fin⟩
    · obtain ⟨s, exitCap, visitCap, returnBudget, visitsAfter, shell, out, visits, late, split, size⟩ :=
        checks.annulus x small
      exact factorialOccupancyBound laws shell out visits late split
        (checks.physicalTime x) (checks.rateLower x) checks.rateFloorPos size
  have dominated : ∀ x, e.visits x ≤ e.summableEnvelope x := by
    intro x
    exact laws.cancelRight (checks.factorialPos x)
      (laws.additive.order.trans (bounds x).1 (checks.envelopeDominates x))
  obtain ⟨bound, sum⟩ := checks.envelopeSum
  have finite : finiteVisitMass e.stateAt e.visits := by
    refine ⟨bound, fun n => laws.additive.order.trans ?_ (sum n)⟩
    exact laws.prefixReward_mono (fun i => dominated (e.stateAt i)) n
  obtain ⟨nonexplosion, recurrence⟩ := bridge.returnFromVisits finite
  refine ⟨finite, nonexplosion, recurrence, fun x => (bounds x).2, e.occupancy ∘ bridge.stateAtBoundary,
    fun _ => rfl, fun b => checks.occupancyPos (bridge.stateAtBoundary b), ?_, ?_⟩
  · exact bridge.eliminateBlocks (bridge.balanceFromVisits finite)
  · exact fun b => (bounds (bridge.stateAtBoundary b)).2

end ReturnCriterion

#print axioms finitePhaseWindow
#print axioms shortenToFiniteWindow
#print axioms epochRewardBound
#print axioms stoppedShellEstimates
#print axioms factorialOccupancyBound
#print axioms oneRoundDecreasesBudget
#print axioms finalRankBlock
#print axioms rankedClockLowerBound
#print axioms aim272Conditional

end AIM272
