import Companion.Basic

/-!
# Courses, keepings and the premise

A course, A keeping, A held lapse, The premise and Claim 10 (Persistence). A course is one state obtaining at each step of an indefinite span, a point of `ℕ → S`, the states of `Process.overSpan ℕ` with the order of `ℕ`. A keeping is a quantity of the state, kept or lapsed, whose value at each step of a course is set by what its deciding processes respond at the step before. Nothing here generates a course: it is given, and `Upkeep.Runs` says when it runs a keeping. No law says how one state becomes another.

The premise says which courses and keepings a result speaks of, its first clause of a course and its second of a keeping and the accessible states. It is a hypothesis of each theorem that uses it and proved by nothing, and `lasts_without_range` and `lasts_without_occasion` show that neither clause can be dropped. `Persistence.lapse` follows from the premise in a few lines, and `Upkeep.occasions_iff_held` says what that comes to: given the run, the first clause and a keeping kept throughout, the second clause is equivalent to the conclusion. `Persistence.occurs` shows that premise and conclusion can hold of a keeping that lasts, `Persistence.cuts_unheld` that where the lapse is not held the keeping is cut, and `not_ranges_over_lapsed` why the first clause reads the states where the keeping is kept.
-/

namespace Companion

variable {S ι : Type}

/-! ## Courses and what is kept along them -/

/-- **A course.** A course: one state obtaining at each step of an indefinite span. It is a point of `ℕ → S`, the states of `Process.overSpan ℕ`, with the order of `ℕ`. A history stays which accessible state obtains at one step. -/
abbrev Course (S : Type) : Type :=
  ℕ → S

/-- A course read from a step on. -/
def Course.from (x : Course S) (n : ℕ) : Course S :=
  fun t => x (n + t)

/-- **A keeping, without its product.** Something an arrangement keeps or lets lapse: a quantity of the state, kept or lapsed; the positions that decide; and what their responses, read together, do to it, reading no other position. -/
structure Upkeep (A : Arrangement S ι) where
  /-- Whether it is kept at a state. -/
  kept : S → Prop
  /-- The deciding positions. -/
  deciding : Set ι
  /-- Whether the responses, read together, keep it. -/
  stays : (∀ i, (A.process i).Action) → Prop
  /-- That reads the deciding positions and no others. -/
  reads_deciding : ∀ r r' : (∀ i, (A.process i).Action), (∀ i ∈ deciding, r i = r' i) → (stays r ↔ stays r')

/-- **A keeping.** A keeping of an arrangement: an upkeep whose product depends on a forestalled state. `value` is the value of what it prevents, in a situation. -/
structure Keeping (A : Arrangement S ι) extends Upkeep A where
  /-- The values of what it prevents. -/
  Value : Type
  /-- The value of what it prevents, in a situation. -/
  value : Situation S → Value
  /-- Its product is a prevented failure. -/
  prevents : DependsOnForestalled value

variable {A : Arrangement S ι}

/-- **A keeping.** What the responses do to it at a state. -/
def Upkeep.decision (K : Upkeep A) (s : S) : Prop :=
  K.stays fun i => (A.process i).response s

/-- **A keeping.** A course runs it when its lapse at each step is set by responses at the step before: it is kept at the next step exactly when it is kept now and the responses keep it. All else about each step is free. -/
def Upkeep.Runs (K : Upkeep A) (x : Course S) : Prop :=
  ∀ t, K.kept (x (t + 1)) ↔ K.kept (x t) ∧ K.decision (x t)

/-- **A held lapse, a deciding process holding it.** A deciding process holds the quantity kept or lapsed. This much is a clause of what a relabelling carries, and it says nothing of what the decision reads. -/
def Upkeep.DecidingHolder (K : Upkeep A) (X : Accessible S) : Prop :=
  ∃ i ∈ K.deciding, (A.process i).Holds X K.kept

/-- **A held lapse, the tie.** The decision reads what position `i` responds to the lapse: at some accessible state where it is kept the responses keep it, and with that position's response at an accessible state where it has lapsed, every other response as it was, they do not. -/
def Upkeep.TiedTo (K : Upkeep A) (X : Accessible S) (i : ι) : Prop :=
  ∃ s ∈ X, ∃ t ∈ X, K.kept s ∧ ¬ K.kept t ∧ K.decision s ∧
    ∃ r : ∀ j, (A.process j).Action, (∀ j, j ≠ i → r j = (A.process j).response s) ∧ r i = (A.process i).response t ∧ ¬ K.stays r

/-- **A held lapse, at the decision.** A deciding process holds the quantity kept or lapsed, and the decision reads what it responds. -/
def Upkeep.HeldAtDecision (K : Upkeep A) (X : Accessible S) : Prop :=
  ∃ i ∈ K.deciding, (A.process i).Holds X K.kept ∧ K.TiedTo X i

/-- **A held lapse, through a join.** A process holds the quantity kept or lapsed, and a join passes what it makes to a deciding process:
what the join passes carries the holder's response, the taker's response follows the holder's across the accessible states, and the decision reads
what the taker responds. A taker told of the holder whose response does not follow it is not enough. -/
def Upkeep.HeldThroughJoin (K : Upkeep A) (X : Accessible S) : Prop :=
  ∃ j ∈ A.joins, j.taker ∈ K.deciding ∧ (A.process j.giver).Holds X K.kept ∧
    Carries ((A.process j.taker).grainings j.made) (A.process j.giver).response ∧
    Follows X (A.process j.taker).response (A.process j.giver).response ∧ K.TiedTo X j.taker

/-- **A held lapse.** The lapse is held across the accessible states when some process holds the quantity kept or lapsed and its response
reaches the decision: it is a deciding process the decision reads, or a join takes its response up into one. -/
def Upkeep.LapseHeld (K : Upkeep A) (X : Accessible S) : Prop :=
  K.HeldAtDecision X ∨ K.HeldThroughJoin X

/-- In an arrangement with no joins, a lapse is held only at the decision. -/
theorem Upkeep.LapseHeld.of_noJoins {K : Upkeep A} {X : Accessible S} (h : K.LapseHeld X) (hj : A.joins = ∅) : K.HeldAtDecision X := by
  rcases h with h | ⟨j, hj', -⟩
  · exact h
  · rw [hj] at hj'
    exact absurd hj' (Set.notMem_empty j)

/-- A response that follows a response that follows a quantity follows the quantity. -/
theorem Follows.trans {B C Q : Type} {X : Accessible S} {a : S → B} {b : S → C} {q : S → Q} (hab : Follows X a b) (hbq : Follows X b q) :
    Follows X a q := by
  refine ⟨fun s hs t ht hq => hab.1 s hs t ht (hbq.1 s hs t ht hq), ?_⟩
  obtain ⟨s, hs, t, ht, hb, ha⟩ := hab.2
  exact ⟨s, hs, t, ht, fun hq => hb (hbq.1 s hs t ht hq), ha⟩

/-- **Claim 10 (Persistence).** Where a lapse is held, some deciding process's response follows whether it is kept. -/
theorem Upkeep.LapseHeld.decidingFollows {K : Upkeep A} {X : Accessible S} (h : K.LapseHeld X) :
    ∃ i ∈ K.deciding, Follows X (A.process i).response K.kept := by
  rcases h with ⟨i, hi, hh, -⟩ | ⟨j, -, hj, hh, -, hf, -⟩
  · exact ⟨i, hi, hh.2⟩
  · exact ⟨j.taker, hj, hf.trans hh.2⟩

/-- **A held lapse, a holder that reaches the decision.** Some process holds the quantity kept or lapsed, and it decides or a join passes
what it makes to a deciding process. This much is a clause of what a relabelling carries. -/
def Upkeep.Holder (K : Upkeep A) (X : Accessible S) : Prop :=
  ∃ i, (A.process i).Holds X K.kept ∧ (i ∈ K.deciding ∨ ∃ j ∈ A.joins, j.giver = i ∧ j.taker ∈ K.deciding)

/-- A lapse held has a holder that reaches the decision. -/
theorem Upkeep.LapseHeld.holder {K : Upkeep A} {X : Accessible S} (h : K.LapseHeld X) : K.Holder X := by
  rcases h with ⟨i, hi, hh, -⟩ | ⟨j, hj, ht, hh, -⟩
  · exact ⟨i, hh, Or.inl hi⟩
  · exact ⟨j.giver, hh, Or.inr ⟨j, hj, rfl, ht⟩⟩

/-- **The premise, its first clause.** Over the course's whole span, what the deciding processes respond takes every value it has at the accessible states where the keeping is kept. -/
def Upkeep.Ranges (K : Upkeep A) (X : Accessible S) (x : Course S) : Prop :=
  ∀ s ∈ X, K.kept s → ∃ t, ∀ i ∈ K.deciding, (A.process i).response (x t) = (A.process i).response s

/-- **The premise, its second clause.** Where the lapse is not held, one of those values does not keep it. -/
def Upkeep.Occasions (K : Upkeep A) (X : Accessible S) : Prop :=
  ¬ K.LapseHeld X → ∃ s ∈ X, K.kept s ∧ ¬ K.decision s

/-- **The premise.** The premise, of a course and a set of accessible states, in its two clauses. It is proved by nothing, and a theorem that uses it takes it as a hypothesis. -/
structure Upkeep.Premise (K : Upkeep A) (X : Accessible S) (x : Course S) : Prop where
  /-- What the deciding responses do ranges over its values. -/
  ranges : K.Ranges X x
  /-- Where the lapse is not held, one of those values cuts it. -/
  occasions : K.Occasions X

/-- Two states with one value of each deciding response have one decision. -/
theorem Upkeep.decision_iff (K : Upkeep A) {s t : S} (h : ∀ i ∈ K.deciding, (A.process i).response s = (A.process i).response t) :
    K.decision s ↔ K.decision t :=
  K.reads_deciding _ _ h

/-- Once lapsed along a course that runs it, it stays lapsed. A course sets it from the step before, and nothing there brings it back. -/
theorem Upkeep.stays_lapsed (K : Upkeep A) {x : Course S} (hrun : K.Runs x) {n : ℕ} (h : ¬ K.kept (x n)) (m : ℕ) : ¬ K.kept (x (n + m)) := by
  induction m with
  | zero => exact h
  | succ m ih => exact fun hk => ih ((hrun (n + m)).mp hk).1

/-- A course read from a step on still runs it. -/
theorem Upkeep.Runs.from {K : Upkeep A} {x : Course S} (hrun : K.Runs x) (n : ℕ) : K.Runs (x.from n) :=
  fun t => by simpa [Course.from, Nat.add_assoc] using hrun (n + t)

/-- **Claim 10 (Persistence).** The theorem for anything kept along a course, whatever its product: it uses that the product is a prevented failure nowhere. -/
theorem Upkeep.held_of_kept (K : Upkeep A) (X : Accessible S) (x : Course S) (hrun : K.Runs x) (hp : K.Premise X x) (hkept : ∀ t, K.kept (x t)) :
    K.LapseHeld X := by
  by_contra hnot
  obtain ⟨s, hs, hks, hcut⟩ := hp.occasions hnot
  obtain ⟨t, ht⟩ := hp.ranges s hs hks
  exact hcut ((K.decision_iff ht).mp ((hrun t).mp (hkept (t + 1))).2)

/-- Under the premise, what is not held is cut at some step and stays cut. -/
theorem Upkeep.lapses (K : Upkeep A) (X : Accessible S) (x : Course S) (hrun : K.Runs x) (hp : K.Premise X x) (hnot : ¬ K.LapseHeld X) :
    ∃ n, ∀ m, ¬ K.kept (x (n + m)) := by
  by_contra hno
  have hkept : ∀ t, K.kept (x t) := fun t => by
    by_contra hk
    exact hno ⟨t, K.stays_lapsed hrun hk⟩
  exact hnot (K.held_of_kept X x hrun hp hkept)

/-- **Claim 10 (Persistence), what its strength comes to.** Given the run, the first clause and that it is kept throughout, the second clause is equivalent to the conclusion. -/
theorem Upkeep.occasions_iff_held (K : Upkeep A) (X : Accessible S) (x : Course S) (hrun : K.Runs x) (hr : K.Ranges X x) (hkept : ∀ t, K.kept (x t)) :
    K.Occasions X ↔ K.LapseHeld X := by
  constructor
  · intro ho
    by_contra hn
    obtain ⟨s, hs, hk, hcut⟩ := ho hn
    obtain ⟨t, ht⟩ := hr s hs hk
    exact hcut ((K.decision_iff ht).mp ((hrun t).mp (hkept (t + 1))).2)
  · exact fun h hn => absurd h hn

/-- **Claim 10 (Persistence).** Under the premise, a keeping kept at every step of a course that runs it has its lapse held. The conclusion is reached from the premise in a few lines, and `Upkeep.occasions_iff_held` says what that comes to. -/
theorem Persistence.lapse (K : Keeping A) (X : Accessible S) (x : Course S) (hrun : K.Runs x) (hp : K.Premise X x) (hkept : ∀ t, K.kept (x t)) :
    K.LapseHeld X :=
  K.toUpkeep.held_of_kept X x hrun hp hkept

/-- **Claim 10 (Persistence).** A course inside the accessible states that stays kept never takes the value a holder's response has where the keeping has lapsed. So were the first clause to read every accessible state, no keeping that lasts could have its lapse held, and with the second clause the premise would leave nothing kept along such a course, held or not. -/
theorem not_ranges_over_lapsed (K : Upkeep A) (X : Accessible S) (x : Course S) (hin : ∀ t, x t ∈ X) (hkept : ∀ t, K.kept (x t)) (hheld : K.LapseHeld X) :
    ¬ ∀ s ∈ X, ∃ t, ∀ i ∈ K.deciding, (A.process i).response (x t) = (A.process i).response s := by
  intro hall
  obtain ⟨i, hi, hfix, s, hs, u, hu, hne, hresp⟩ := hheld.decidingFollows
  have hlapsed : ¬ K.kept s ∨ ¬ K.kept u := by
    by_contra hcon
    push Not at hcon
    exact hne (propext ⟨fun _ => hcon.2, fun _ => hcon.1⟩)
  have hkeptSame : ∀ a ∈ X, K.kept a → ∀ t, (A.process i).response a = (A.process i).response (x t) := fun a ha hka t =>
    hfix a ha (x t) (hin t) (propext ⟨fun _ => hkept t, fun _ => hka⟩)
  rcases hlapsed with hl | hl
  · obtain ⟨t, ht⟩ := hall s hs
    have hk : K.kept u := by
      by_contra hku
      exact hne (propext ⟨fun h => absurd h hl, fun h => absurd h hku⟩)
    exact hresp ((ht i hi).symm.trans (hkeptSame u hu hk t).symm)
  · obtain ⟨t, ht⟩ := hall u hu
    have hk : K.kept s := by
      by_contra hks
      exact hne (propext ⟨fun h => absurd h hks, fun h => absurd h hl⟩)
    exact hresp ((hkeptSame s hs hk t).trans (ht i hi))

/-! ## Witnesses: the states are whether it is kept and whether the step is tight -/

/-- The states of the witnesses: whether it is kept, and whether the step is tight. -/
abbrev Two : Type :=
  Bool × Bool

/-- What would have obtained depends on a forestalled state, wherever a state has two others. -/
theorem wouldHave_depends {a b c : S} (hba : b ≠ a) (hca : c ≠ a) (hbc : b ≠ c) : DependsOnForestalled (Situation.wouldHave : Situation S → S) :=
  ⟨⟨a, b⟩, ⟨a, c⟩, hba, hca, rfl, hbc⟩

/-- On the witnesses' states, what would have obtained depends on a forestalled state. -/
theorem two_wouldHave_depends : DependsOnForestalled (Situation.wouldHave : Situation Two → Two) :=
  wouldHave_depends (a := (false, false)) (b := (false, true)) (c := (true, false)) (by decide) (by decide) (by decide)

/-- The arrangement of the witnesses: at `false` a process that reads whether the step is tight, at `true` one that reads whether it is kept. -/
def officeAndHolder : Arrangement Two Bool :=
  ⟨inferInstance, fun b => Process.reading (cond b Prod.fst Prod.snd), ∅⟩

/-- The keeping cut in a tight step, deciding by the process that reads whether the step is tight. No deciding process holds it. -/
def tightKeeping : Keeping officeAndHolder where
  kept := fun s => s.1 = true
  deciding := {false}
  stays := fun r => r false = false
  reads_deciding := fun r r' h => by rw [h false rfl]
  Value := Two
  value := Situation.wouldHave
  prevents := two_wouldHave_depends

/-- The same keeping with the holder deciding too: in a tight step it stays where the holder responds to its being kept. -/
def heldKeeping : Keeping officeAndHolder where
  kept := fun s => s.1 = true
  deciding := Set.univ
  stays := fun r => r false = false ∨ r true = true
  reads_deciding := fun r r' h => by rw [h false trivial, h true trivial]
  Value := Two
  value := Situation.wouldHave
  prevents := two_wouldHave_depends

/-- A keeping no response can cut, deciding by the process that reads whether the step is tight: a standing order. -/
def alwaysKeeping : Keeping officeAndHolder where
  kept := fun s => s.1 = true
  deciding := {false}
  stays := fun _ => True
  reads_deciding := fun _ _ _ => Iff.rfl
  Value := Two
  value := Situation.wouldHave
  prevents := two_wouldHave_depends

/-- A course of the witnesses: kept throughout, and tight at each step but the first. It takes both values of whether the step is tight. -/
def keptCourse : Course Two :=
  fun t => (true, decide (t ≠ 0))

/-- The process that reads whether the step is tight does not hold whether it is kept. -/
theorem tight_not_held (K : Upkeep officeAndHolder) (hd : K.deciding = {false}) (hk : ∀ s, K.kept s ↔ s.1 = true) (X : Accessible Two) (hX : ∃ b, (true, false) ∈ X ∧ (true, true) ∈ X ∧ (false, b) ∈ X) :
    ¬ K.LapseHeld X := by
  intro hl
  obtain ⟨i, hi, hfix, -⟩ := hl.decidingFollows
  rw [hd] at hi
  obtain rfl : i = false := hi
  obtain ⟨-, h0, h1, -⟩ := hX
  have hsame : (K.kept (true, false)) = (K.kept (true, true)) :=
    propext ⟨fun _ => (hk _).mpr rfl, fun _ => (hk _).mpr rfl⟩
  exact Bool.false_ne_true (hfix _ h0 _ h1 hsame)

/-- All the states of the witnesses, as accessible states, meet what `tight_not_held` asks. -/
theorem two_univ : ∃ b, ((true, false) : Two) ∈ (Set.univ : Accessible Two) ∧ ((true, true) : Two) ∈ (Set.univ : Accessible Two) ∧ ((false, b) : Two) ∈ (Set.univ : Accessible Two) :=
  ⟨false, trivial, trivial, trivial⟩

/-- `keptCourse` takes every value the deciding responses have at a kept state. -/
theorem keptCourse_ranges (K : Upkeep officeAndHolder) (hk : ∀ s, K.kept s ↔ s.1 = true) : K.Ranges Set.univ keptCourse := by
  rintro ⟨a, b⟩ - hs
  obtain rfl : a = true := (hk _).mp hs
  cases b
  · exact ⟨0, fun i _ => rfl⟩
  · exact ⟨1, fun i _ => rfl⟩

/-- **Claim 10 (Persistence), its hypotheses can hold.** A keeping kept at every step of a course inside the accessible states, which runs it and ranges, with the lapse held: the conclusion is met and the premise is not idle. -/
theorem Persistence.occurs :
    heldKeeping.Runs keptCourse ∧ heldKeeping.Premise Set.univ keptCourse ∧ (∀ t, heldKeeping.kept (keptCourse t)) ∧ heldKeeping.LapseHeld Set.univ := by
  have hheld : heldKeeping.LapseHeld Set.univ :=
    Or.inl ⟨true, trivial, ⟨⟨fun v => (v () : Bool) = true, rfl⟩, fun u _ v _ h => by
      have hu : (u.1 = true) ↔ (v.1 = true) := by simpa [heldKeeping] using h
      show u.1 = v.1
      cases hu1 : u.1 <;> cases hv1 : v.1 <;> simp_all, (true, false), trivial, (false, false), trivial,
      fun h => Bool.false_ne_true (Eq.mp h rfl), Bool.false_ne_true ∘ Eq.symm⟩,
      ⟨(true, true), trivial, (false, true), trivial, rfl, fun h => Bool.false_ne_true h, Or.inr rfl, fun j => cond j false true, fun j hj => by cases j; exact rfl; exact absurd rfl hj, rfl, by rintro (h | h); exact Bool.false_ne_true (Eq.symm h); exact Bool.false_ne_true h⟩⟩
  exact ⟨fun t => ⟨fun h => ⟨h, Or.inr rfl⟩, fun h => h.1⟩, ⟨keptCourse_ranges heldKeeping.toUpkeep fun _ => Iff.rfl, fun hn => absurd hheld hn⟩, fun _ => rfl, hheld⟩

/-- **Claim 10 (Persistence), what the premise does where no deciding process holds.** On the same arrangement and accessible states, deciding by the process that reads whether the step is tight: no deciding process holds the lapse, a value of what it responds cuts the keeping, `keptCourse` takes every such value, and any course that runs it and meets the premise cuts it, and it stays cut. -/
theorem Persistence.cuts_unheld :
    ¬ tightKeeping.LapseHeld Set.univ ∧ tightKeeping.Occasions Set.univ ∧ tightKeeping.Ranges Set.univ keptCourse ∧
      ∀ x : Course Two, tightKeeping.Runs x → tightKeeping.Premise Set.univ x → ∃ n, ∀ m, ¬ tightKeeping.kept (x (n + m)) := by
  have hnot : ¬ tightKeeping.LapseHeld Set.univ := tight_not_held tightKeeping.toUpkeep rfl (fun _ => Iff.rfl) _ two_univ
  refine ⟨hnot, fun _ => ⟨(true, true), trivial, rfl, fun h => Bool.false_ne_true (Eq.symm h)⟩, keptCourse_ranges tightKeeping.toUpkeep fun _ => Iff.rfl, fun x hrun hp => ?_⟩
  exact tightKeeping.toUpkeep.lapses Set.univ x hrun hp hnot

/-- **Claim 10 (Persistence).** A course that never meets a tight step keeps at every step a keeping no deciding process holds, though a tight step would cut it: the second clause holds and the first fails. -/
theorem lasts_without_range :
    ∃ x : Course Two, tightKeeping.Runs x ∧ (∀ t, tightKeeping.kept (x t)) ∧ ¬ tightKeeping.LapseHeld Set.univ ∧
      tightKeeping.Occasions Set.univ ∧ ¬ tightKeeping.Ranges Set.univ x := by
  refine ⟨fun _ => (true, false), fun _ => ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩, fun _ => rfl, tight_not_held tightKeeping.toUpkeep rfl (fun _ => Iff.rfl) _ two_univ,
    fun _ => ⟨(true, true), trivial, rfl, fun h => Bool.false_ne_true (Eq.symm h)⟩, fun h => ?_⟩
  obtain ⟨_, ht⟩ := h (true, true) trivial rfl
  exact Bool.false_ne_true (ht false rfl)

/-- **Claim 10 (Persistence).** A standing order keeps at every step a keeping no deciding process holds, over a course that ranges over everything the responses do: the first clause holds and the second fails. Holding plays no part in this, and what fails is the occasion. -/
theorem lasts_without_occasion :
    alwaysKeeping.Runs keptCourse ∧ (∀ t, alwaysKeeping.kept (keptCourse t)) ∧ ¬ alwaysKeeping.LapseHeld Set.univ ∧
      alwaysKeeping.Ranges Set.univ keptCourse ∧ ¬ alwaysKeeping.Occasions Set.univ := by
  have hnot : ¬ alwaysKeeping.LapseHeld Set.univ := tight_not_held alwaysKeeping.toUpkeep rfl (fun _ => Iff.rfl) _ two_univ
  refine ⟨fun _ => ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩, fun _ => rfl, hnot, keptCourse_ranges alwaysKeeping.toUpkeep fun _ => Iff.rfl, fun h => ?_⟩
  obtain ⟨_, -, -, hcut⟩ := h hnot
  exact hcut trivial

/-- A standing order with an idle reader among its deciding positions: nothing any process responds moves the decision. -/
def paddedStanding : Keeping officeAndHolder where
  kept := fun s => s.1 = true
  deciding := Set.univ
  stays := fun _ => True
  reads_deciding := fun _ _ _ => Iff.rfl
  Value := Two
  value := Situation.wouldHave
  prevents := two_wouldHave_depends

/-- **Claim 10 (Persistence).** A process among the deciding positions holds whether it is kept, and the decision reads no response, so the lapse is not held, and the second clause fails. So a held lapse is one the decision reads. -/
theorem standing_order_not_held :
    paddedStanding.DecidingHolder Set.univ ∧ ¬ paddedStanding.LapseHeld Set.univ ∧ ¬ paddedStanding.Occasions Set.univ := by
  have hnot : ¬ paddedStanding.LapseHeld Set.univ := by
    intro hl
    obtain ⟨_, -, -, _, -, _, -, -, -, -, _, -, -, hcut⟩ := hl.of_noJoins rfl
    exact hcut trivial
  refine ⟨⟨true, trivial, ⟨fun v => (v () : Bool) = true, rfl⟩, fun u _ v _ h => ?_, (true, false), trivial, (false, false), trivial,
    fun h => Bool.false_ne_true (Eq.mp h rfl), Bool.false_ne_true ∘ Eq.symm⟩, hnot, fun h => ?_⟩
  · have hu : (u.1 = true) ↔ (v.1 = true) := by simpa [paddedStanding] using h
    show u.1 = v.1
    cases hu1 : u.1 <;> cases hv1 : v.1 <;> simp_all
  · obtain ⟨_, -, -, hcut⟩ := h hnot
    exact hcut trivial

/-- A keeping both processes decide, kept only where the holder responds to it and the step is calm. -/
def heldAndOutvoted : Keeping officeAndHolder where
  kept := fun s => s.1 = true
  deciding := Set.univ
  stays := fun r => r true = true ∧ r false = false
  reads_deciding := fun r r' h => by rw [h true trivial, h false trivial]
  Value := Two
  value := Situation.wouldHave
  prevents := two_wouldHave_depends

/-- **Claim 10 (Persistence), only where.** A held lapse is no guarantee: a deciding process holds it and the decision reads it, the premise is met, and a tight step cuts the keeping, since another deciding process can cut it anyway. The theorem says that what lasts was held, and nothing of what is held. -/
theorem held_can_be_cut :
    heldAndOutvoted.Premise Set.univ keptCourse ∧ heldAndOutvoted.LapseHeld Set.univ ∧ ¬ heldAndOutvoted.decision (true, true) := by
  have hheld : heldAndOutvoted.LapseHeld Set.univ :=
    Or.inl ⟨true, trivial, ⟨⟨fun v => (v () : Bool) = true, rfl⟩, fun u _ v _ h => by
      have hu : (u.1 = true) ↔ (v.1 = true) := by simpa [heldAndOutvoted] using h
      show u.1 = v.1
      cases hu1 : u.1 <;> cases hv1 : v.1 <;> simp_all, (true, false), trivial, (false, false), trivial,
      fun h => Bool.false_ne_true (Eq.mp h rfl), Bool.false_ne_true ∘ Eq.symm⟩,
      ⟨(true, false), trivial, (false, false), trivial, rfl, fun h => Bool.false_ne_true h, ⟨rfl, rfl⟩, fun _ => false, fun j hj => by cases j; exact rfl; exact absurd rfl hj, rfl, fun h => Bool.false_ne_true h.1⟩⟩
  refine ⟨⟨?_, fun hn => absurd hheld hn⟩, hheld, fun h => Bool.false_ne_true (Eq.symm h.2)⟩
  rintro ⟨a, b⟩ - hs
  obtain rfl : a = true := hs
  cases b
  · exact ⟨0, fun i _ => by cases i <;> rfl⟩
  · exact ⟨1, fun i _ => by cases i <;> rfl⟩

/-- A course that is calm through step `n`, then tight, with whether it is kept set by the keeping cut in a tight step. -/
def lateCourse (n : ℕ) : Course Two :=
  fun t => (decide (t ≤ n + 1), decide (n < t))

/-- **Claim 10 (Persistence), a finite span says nothing.** For every length of span, a course meets the whole premise, and yet a keeping no deciding process holds stays kept through that span. It is cut, later. So the theorem rules out only that it lasts indefinitely. -/
theorem lasts_any_finite_span (n : ℕ) :
    tightKeeping.Runs (lateCourse n) ∧ tightKeeping.Premise Set.univ (lateCourse n) ∧ ¬ tightKeeping.LapseHeld Set.univ ∧
      (∀ t ≤ n, tightKeeping.kept (lateCourse n t)) ∧ ¬ tightKeeping.kept (lateCourse n (n + 2)) := by
  refine ⟨fun t => ?_, ⟨?_, fun _ => ⟨(true, true), trivial, rfl, fun h => Bool.false_ne_true (Eq.symm h)⟩⟩, tight_not_held tightKeeping.toUpkeep rfl (fun _ => Iff.rfl) _ two_univ, fun t ht => ?_, ?_⟩
  · change (decide (t + 1 ≤ n + 1) = true) ↔ (decide (t ≤ n + 1) = true) ∧ decide (n < t) = false
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · rintro ⟨a, b⟩ - -
    cases b
    · exact ⟨0, fun i hi => by
        obtain rfl : i = false := hi
        show decide (n < 0) = false
        simp⟩
    · exact ⟨n + 1, fun i hi => by
        obtain rfl : i = false := hi
        show decide (n < n + 1) = true
        simp⟩
  · change decide (t ≤ n + 1) = true
    simp only [decide_eq_true_eq]
    omega
  · change ¬ decide (n + 2 ≤ n + 1) = true
    simp

end Companion
