import Companion.Claims
import Companion.Time

/-!
# What the claims say over time

Each theorem here states one thing a claim of the Element says of a course, in the claim's own quantifiers, from `Persistence.lapse` and the theorems before it. Where a claim's strength lies in the premise of `Companion.Time`, the theorem takes the premise as a hypothesis and its docstring says so. A witness beside a theorem shows that its hypotheses can hold, or what is lost if one of them is dropped.
-/

namespace Companion

variable {S S' ι ι' κ : Type}

/-! ## Arrangements of readers, for the witnesses -/

/-- An arrangement in which each position reads a yes-or-no quantity and responds with it. -/
def readers [Finite ι] (g : ι → S → Bool) : Arrangement S ι :=
  ⟨inferInstance, fun i => Process.reading (g i), ∅⟩

/-- A reader of a quantity holds what that quantity says, across any states where it takes both values. -/
theorem readers_holds [Finite ι] (g : ι → S → Bool) (i : ι) (X : Accessible S) (k : S → Prop) (hk : ∀ s, k s ↔ g i s = true)
    (hs : ∃ s ∈ X, g i s = true) (ht : ∃ t ∈ X, g i t = false) : ((readers g).process i).Holds X k := by
  obtain ⟨s, hs, hgs⟩ := hs
  obtain ⟨t, ht, hgt⟩ := ht
  refine ⟨⟨fun v => (v () : Bool) = true, funext fun u => propext (hk u)⟩, fun u _ v _ h => ?_, s, hs, t, ht, fun h => ?_, ?_⟩
  · have huv : g i u = true ↔ g i v = true := by rw [← hk, ← hk, h]
    change g i u = g i v
    cases hu : g i u <;> cases hv : g i v <;> simp_all
  · have : g i t = true := (hk t).mp (h ▸ (hk s).mpr hgs)
    rw [hgt] at this
    exact Bool.false_ne_true this
  · change g i s ≠ g i t
    rw [hgs, hgt]
    decide

/-- A reader whose quantity takes one value across the states holds nothing there. -/
theorem readers_not_holds_of_const [Finite ι] (g : ι → S → Bool) (i : ι) (X : Accessible S) (hc : ∀ s ∈ X, ∀ t ∈ X, g i s = g i t) {Q : Type} (q : S → Q) :
    ¬ ((readers g).process i).Holds X q := by
  rintro ⟨-, -, s, hs, t, ht, -, ha⟩
  exact ha (hc s hs t ht)

/-- A reader whose quantity differs at two states where a quantity is one does not hold that quantity. -/
theorem readers_not_holds_of_differs [Finite ι] (g : ι → S → Bool) (i : ι) (X : Accessible S) {Q : Type} (q : S → Q) {s t : S} (hs : s ∈ X) (ht : t ∈ X)
    (hq : q s = q t) (hg : g i s ≠ g i t) : ¬ ((readers g).process i).Holds X q := by
  rintro ⟨-, hfix, -⟩
  exact hg (hfix s hs t ht hq)

/-! ## Persistence -/

variable {A : Arrangement S ι}

/-- **Claim 10 (Persistence), at a cut.** It holds of what a cut of a nested arrangement reads, with the premise as its hypothesis there, by instantiation, as `LawsAndResults` holds there. A course over a cut's states is a span read in order. -/
theorem Persistence.at_cut {τ : Type} (cut : Cut S τ) {n : Nested S} (h : cut.Stands n) (K : Keeping (cut.read h)) (X : Accessible _) (x : Course _) (hrun : K.Runs x) (hp : K.Premise X x)
    (hkept : ∀ t, K.kept (x t)) : K.LapseHeld X :=
  Persistence.lapse K X x hrun hp hkept

/-- **Claim 10 (Persistence), what a holder holds.** No process holds what a keeping prevents, across any set of situations, under any rule. So a holder of its lapse holds something else, and this is why the claim speaks of the lapse. -/
theorem Persistence.value_not_held (K : Keeping A) (i : ι) (W : Set (Situation S)) : ¬ (A.process i).HoldsOfSituation W K.value :=
  Response.holds_nothing_forestalled _ W K.prevents

/-- **Claim 10 (Persistence), what the decision reads.** Some two situations with one state that obtains give what a keeping prevents two values, and the decision one: it reads the state, and what it prevents does not reach it. -/
theorem Persistence.decision_reads_no_value (K : Keeping A) :
    ∃ w w' : Situation S, w.obtains = w'.obtains ∧ K.value w ≠ K.value w' ∧ (K.decision w.obtains ↔ K.decision w'.obtains) := by
  obtain ⟨w, w', -, -, ho, hv⟩ := K.prevents
  exact ⟨w, w', ho, hv, by rw [ho]⟩

/-! ## What lasts -/

/-- **Claim 13 (What lasts is what was held).** Across any family of keepings along one course, each under the premise, every one kept at every step has its lapse held. -/
theorem Persistence.what_lasts {J : Type} (K : J → Keeping A) (X : J → Accessible S) (x : Course S) (hrun : ∀ j, (K j).Runs x) (hp : ∀ j, (K j).Premise (X j) x) :
    ∀ j, (∀ t, (K j).kept (x t)) → (K j).LapseHeld (X j) :=
  fun j => Persistence.lapse (K j) (X j) x (hrun j) (hp j)

/-- **Claim 10 (Persistence), a chain.** Upkeeps along one course, the first under the premise with its lapse not held, and each later one up to the
`J`th with its lapse not held across the states at which the one before it has lapsed, meeting the premise there along the course from any step
on which that one stays lapsed: each of them is cut at some step and stays cut. A chain of holding lasts no longer than its first part that no one
holds. -/
theorem Persistence.chain (K : ℕ → Upkeep A) (X : Accessible S) (x : Course S) (J : ℕ) (hrun : ∀ j, (K j).Runs x) (hp : (K 0).Premise X x)
    (hnot : ¬ (K 0).LapseHeld X)
    (hnext : ∀ j < J, ∀ n, (∀ m, ¬ (K j).kept (x (n + m))) → (K (j + 1)).Premise {s | ¬ (K j).kept s} (x.from n))
    (hheld : ∀ j < J, ¬ (K (j + 1)).LapseHeld {s | ¬ (K j).kept s}) :
    ∀ j ≤ J, ∃ n, ∀ m, ¬ (K j).kept (x (n + m)) := by
  intro j hj
  induction j with
  | zero => exact (K 0).lapses X x (hrun 0) hp hnot
  | succ j ih =>
    have hjJ : j < J := Nat.lt_of_succ_le hj
    obtain ⟨n, hn⟩ := ih hjJ.le
    obtain ⟨n', hn'⟩ := (K (j + 1)).lapses _ (x.from n) ((hrun (j + 1)).from n) (hnext j hjJ n hn) (hheld j hjJ)
    exact ⟨n + n', fun m => by simpa [Course.from, Nat.add_assoc] using hn' m⟩

/-- **Claim 13 (What lasts is what was held), worth has no part.** Two upkeeps along one course, alike at the first step and alike in what their decisions do at each step, are alike at every step, whatever each is worth. -/
theorem Persistence.lasts_alike (K K' : Upkeep A) (x : Course S) (hrun : K.Runs x) (hrun' : K'.Runs x) (h0 : K.kept (x 0) ↔ K'.kept (x 0))
    (hd : ∀ t, K.decision (x t) ↔ K'.decision (x t)) (t : ℕ) : K.kept (x t) ↔ K'.kept (x t) := by
  induction t with
  | zero => exact h0
  | succ t ih => rw [hrun t, hrun' t, ih, hd t]

/-- The states of the witnesses with two things kept: whether the first is kept, whether the second is kept, and whether the step is tight. -/
abbrev Three : Type :=
  Bool × Bool × Bool

/-- Whether a collapse would have come. -/
def collapse (w : Situation Three) : ℕ :=
  if w.wouldHave.2.2 = true then 1 else 0

/-- What is worth `c` times a collapse depends on a forestalled state, for any positive `c`. -/
theorem collapse_depends {c : ℕ} (hc : 0 < c) : DependsOnForestalled fun w => c * collapse w := by
  refine ⟨⟨(true, true, true), (false, true, true)⟩, ⟨(true, true, true), (false, true, false)⟩, show ((false, true, true) : Three) ≠ (true, true, true) by decide, show ((false, true, false) : Three) ≠ (true, true, true) by decide, rfl, ?_⟩
  simpa [collapse] using hc.ne'

/-- What each position reads: at `false` whether the step is tight, and at `true` whether the second thing is kept. -/
def sieveGrain : Bool → Three → Bool :=
  fun b s => cond b s.2.1 s.2.2

/-- A process that reads whether the step is tight, and one that reads whether the second thing is kept. -/
def sieveReaders : Arrangement Three Bool :=
  readers sieveGrain

/-- The first thing: worth nine collapses, deciding by what reads whether the step is tight. -/
def cutWorthMore : Keeping sieveReaders where
  kept := fun s => s.1 = true
  deciding := {false}
  stays := fun r => r false = false
  reads_deciding := fun r r' h => by rw [h false rfl]
  Value := ℕ
  value := fun w => 9 * collapse w
  prevents := collapse_depends (by decide)

/-- The second thing: worth one collapse, with its holder deciding too. -/
def keptWorthLess : Keeping sieveReaders where
  kept := fun s => s.2.1 = true
  deciding := Set.univ
  stays := fun r => r false = false ∨ r true = true
  reads_deciding := fun r r' h => by rw [h false trivial, h true trivial]
  Value := ℕ
  value := fun w => 1 * collapse w
  prevents := collapse_depends (by decide)

/-- A course with a calm first step and tight steps after. -/
def sieveCourse : Course Three :=
  fun t => (decide (t ≤ 1), true, decide (t ≠ 0))

/-- **Claim 13 (What lasts is what was held), not the most valuable.** On one course, each under the premise, a keeping worth nine times another that no deciding process holds is cut, and the other, held, lasts at every step. -/
theorem Persistence.not_most_valuable :
    cutWorthMore.Runs sieveCourse ∧ keptWorthLess.Runs sieveCourse ∧ cutWorthMore.Premise Set.univ sieveCourse ∧ keptWorthLess.Premise Set.univ sieveCourse ∧
      ¬ cutWorthMore.LapseHeld Set.univ ∧ keptWorthLess.LapseHeld Set.univ ∧ ¬ cutWorthMore.kept (sieveCourse 2) ∧ (∀ t, keptWorthLess.kept (sieveCourse t)) ∧
      (∀ w, Nat.le (keptWorthLess.value w) (cutWorthMore.value w)) ∧ ∃ w, Nat.lt (keptWorthLess.value w) (cutWorthMore.value w) := by
  have hheld : keptWorthLess.LapseHeld Set.univ :=
    Or.inl ⟨true, trivial, readers_holds _ true _ _ (fun _ => Iff.rfl) ⟨(true, true, true), trivial, rfl⟩ ⟨(true, false, true), trivial, rfl⟩,
      (true, true, true), trivial, (true, false, true), trivial, rfl, fun h => Bool.false_ne_true h, Or.inr rfl, fun j => cond j false true, fun j hj => by cases j; exact rfl; exact absurd rfl hj, rfl, by
        rintro (h | h)
        · exact Bool.false_ne_true (Eq.symm h)
        · exact Bool.false_ne_true h⟩
  have hnot : ¬ cutWorthMore.LapseHeld Set.univ := by
    intro hl
    obtain ⟨i, hi, hh, -⟩ := hl.of_noJoins rfl
    obtain rfl : i = false := hi
    exact readers_not_holds_of_differs sieveGrain false Set.univ cutWorthMore.kept (s := (true, true, false)) (t := (true, true, true)) trivial trivial
      rfl (by decide) hh
  refine ⟨fun t => ?_, fun t => ⟨fun h => ⟨h, Or.inr rfl⟩, fun h => h.1⟩, ⟨?_, fun _ => ⟨(true, true, true), trivial, rfl, fun h => Bool.false_ne_true (Eq.symm h)⟩⟩, ⟨?_, fun hn => absurd hheld hn⟩, hnot, hheld, ?_, fun _ => rfl, fun w => ?_, ⟨(true, true, true), (false, true, true)⟩, ?_⟩
  · change (decide (t + 1 ≤ 1) = true) ↔ (decide (t ≤ 1) = true) ∧ decide (t ≠ 0) = false
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · rintro ⟨a, b, c⟩ - -
    cases c
    · exact ⟨0, fun i hi => by obtain rfl : i = false := hi; rfl⟩
    · exact ⟨1, fun i hi => by obtain rfl : i = false := hi; rfl⟩
  · rintro ⟨a, b, c⟩ - hk
    obtain rfl : b = true := hk
    cases c
    · exact ⟨0, fun i _ => by cases i <;> rfl⟩
    · exact ⟨1, fun i _ => by cases i <;> rfl⟩
  · exact fun h => Bool.false_ne_true h
  · change 1 * collapse w ≤ 9 * collapse w
    omega
  · change 1 * collapse ⟨(true, true, true), (false, true, true)⟩ < 9 * collapse ⟨(true, true, true), (false, true, true)⟩
    simp [collapse]

/-! ## What is kept, along a course -/

/-- **Claim 14 (What is kept), along a course.** Let the world's accessible states move along a course. Where a response told apart at one step what a quantity tells apart, and at a later step the accessible states hold a pair of the between that the quantity separates, then that pair was not accessible at the first step, and at the later step no rule of that position tells apart what the quantity tells apart. Nothing the arrangement registers has moved. -/
theorem Composition.kept_along (A : Arrangement S ι) (world : ℕ → Accessible S) {Q : Type} (q : S → Q) (i : ι) {n m : ℕ}
    (hhad : ∀ u ∈ world n, ∀ v ∈ world n, q u ≠ q v → (A.process i).response u ≠ (A.process i).response v) {s t : S} (hs : s ∈ world m) (ht : t ∈ world m)
    (hz : s(s, t) ∈ A.between) (hq : q s ≠ q t) :
    ¬ (s ∈ world n ∧ t ∈ world n) ∧ ∀ {B : Type} (r : (∀ k, (A.process i).Value k) → B),
      ¬ ∀ u ∈ world m, ∀ v ∈ world m, q u ≠ q v → ((A.process i).withRule r).response u ≠ ((A.process i).withRule r).response v :=
  have h := Composition.kept_and_lost A (world n) (world m) q i hhad hs ht hz hq
  ⟨h.1, fun r => h.2.2 r⟩

/-! ## What it is for -/

/-- A process's response tells apart, across the accessible states, what a quantity tells apart there. -/
def Process.TellsApart {Q : Type} (p : Process S) (X : Accessible S) (q : S → Q) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, q u ≠ q v → p.response u ≠ p.response v

/-- **Claim 15 (What it is for).** A correction is a keeping `K`, and an arrangement along a course `arr` changes only while `K` is kept. Under the premise, where `K`'s lapse is not held, it lapses at some step, and from there the arrangement stays as it was. If the world then brings in a pair of what lies between its processes, one the quantity it is for separates, no rule of a position tells apart there what that quantity tells apart. The arrangement continues, and what it was for does not. -/
theorem Composition.what_is_for {C : Arrangement S κ} (K : Keeping C) (Y : Accessible S) (x : Course S) (arr : ℕ → Arrangement S ι) (world : ℕ → Accessible S) {Q : Type} (q : S → Q) (i : ι)
    (hrun : K.Runs x) (hp : K.Premise Y x) (hnot : ¬ K.LapseHeld Y) (hacts : ∀ t, ¬ K.kept (x t) → arr (t + 1) = arr t)
    (hmoves : ∀ n, ¬ K.kept (x n) → ∃ m, n ≤ m ∧ ∃ s ∈ world m, ∃ t ∈ world m, s(s, t) ∈ (arr n).between ∧ q s ≠ q t) :
    ∃ n, (∀ m, arr (n + m) = arr n) ∧ ∃ m, n ≤ m ∧ ∀ {B : Type} (r : (∀ k, ((arr n).process i).Value k) → B),
      ¬ (((arr n).process i).withRule r).TellsApart (world m) q := by
  obtain ⟨n, hn⟩ := K.toUpkeep.lapses Y x hrun hp hnot
  have hstay : ∀ m, arr (n + m) = arr n := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [← Nat.add_assoc, hacts (n + m) (hn m), ih]
  have hlapsed : ¬ K.kept (x n) := hn 0
  obtain ⟨m, hm, s, hs, t, ht, hz, hq⟩ := hmoves n hlapsed
  refine ⟨n, hstay, m, hm, fun {B} r => ?_⟩
  have hG : ((arr n).process i).jointly s = ((arr n).process i).jointly t :=
    funext fun k => (mem_kernel _ s t).mp (mem_grainings_of_mem_constitution (hz.2 i) k)
  exact Response.design_cannot_run _ (world m) q hs ht hG hq r

/-- **Claim 15 (What it is for), only while.** Under the same hypotheses but that the lapse is not held, if at every step some rule of the arrangement standing there tells apart what the quantity tells apart, the correction's lapse is held. -/
theorem Composition.keeps_only_while_held {C : Arrangement S κ} (K : Keeping C) (Y : Accessible S) (x : Course S) (arr : ℕ → Arrangement S ι) (world : ℕ → Accessible S) {Q : Type} (q : S → Q) (i : ι)
    (hrun : K.Runs x) (hp : K.Premise Y x) (hacts : ∀ t, ¬ K.kept (x t) → arr (t + 1) = arr t)
    (hmoves : ∀ n, ¬ K.kept (x n) → ∃ m, n ≤ m ∧ ∃ s ∈ world m, ∃ t ∈ world m, s(s, t) ∈ (arr n).between ∧ q s ≠ q t)
    (hkeeps : ∀ m, ∃ (B : Type) (r : (∀ k, ((arr m).process i).Value k) → B), (((arr m).process i).withRule r).TellsApart (world m) q) :
    K.LapseHeld Y := by
  by_contra hnot
  obtain ⟨n, hstay, m, hm, hlost⟩ := Composition.what_is_for K Y x arr world q i hrun hp hnot hacts hmoves
  have hsame : arr m = arr n := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact hstay j
  have hk := hkeeps m
  rw [hsame] at hk
  obtain ⟨B, r, htells⟩ := hk
  exact hlost r htells

/-- The states of a witness of correction: whether it is kept, whether the step is tight, what the register reads, and what the arrangement is for. -/
abbrev Four : Type :=
  Bool × Bool × Bool × Bool

/-- What each position reads: at `false` whether the step is tight, at `true` whether the correction is kept. -/
def correctorGrain : Bool → Four → Bool :=
  fun b s => cond b s.1 s.2.1

/-- A process that reads whether the step is tight, and one that reads whether the correction is kept. -/
def correctors : Arrangement Four Bool :=
  readers correctorGrain

/-- What would have obtained depends on a forestalled state, on these states. -/
theorem four_wouldHave_depends : DependsOnForestalled (Situation.wouldHave : Situation Four → Four) :=
  wouldHave_depends (a := (false, false, false, false)) (b := (true, false, false, false)) (c := (false, true, false, false)) (by decide) (by decide) (by decide)

/-- A correction deciding by what reads whether the step is tight: no deciding process holds it. -/
def unheldCorrection : Keeping correctors where
  kept := fun s => s.1 = true
  deciding := {false}
  stays := fun r => r false = false
  reads_deciding := fun r r' h => by rw [h false rfl]
  Value := Four
  value := Situation.wouldHave
  prevents := four_wouldHave_depends

/-- A correction with its holder deciding too. -/
def heldCorrection : Keeping correctors where
  kept := fun s => s.1 = true
  deciding := Set.univ
  stays := fun r => r false = false ∨ r true = true
  reads_deciding := fun r r' h => by rw [h false trivial, h true trivial]
  Value := Four
  value := Situation.wouldHave
  prevents := four_wouldHave_depends

/-- One position, reading what the register reads. -/
def registerOf (e : Four → Bool) : Arrangement Four Unit :=
  readers fun _ => e

/-- The world: at first what the register reads moves with what the arrangement is for, and then the two come apart. -/
def movingWorld : ℕ → Accessible Four
  | 0 => {s | s.2.2.1 = s.2.2.2}
  | _ + 1 => Set.univ

/-- The arrangement a held correction brings: it reads what the register read, and from the next step on what the arrangement is for. -/
def correctedRegister : ℕ → Arrangement Four Unit
  | 0 => registerOf fun s => s.2.2.1
  | _ + 1 => registerOf fun s => s.2.2.2

/-- A course in which an unheld correction is cut at its first step. -/
def cutCourse : Course Four :=
  fun t => (decide (t = 0), true, false, false)

/-- A course kept throughout, calm at its first step and tight after. -/
def heldCourse : Course Four :=
  fun t => (true, decide (t ≠ 0), false, false)

/-- **Claim 15 (What it is for), both sides occur.** In one world moving one way, for one purpose and from one register. Where no deciding process holds the correction, the premise is met, it is cut, the register stays and what it is for is lost. Where the correction is held it stays kept at every step, the register pays to read what it is for, and at every step it tells apart what that quantity tells apart. -/
theorem Composition.what_is_for_occurs :
    (unheldCorrection.Runs cutCourse ∧ unheldCorrection.Premise {s | s.2.1 = true} cutCourse ∧ ¬ unheldCorrection.LapseHeld {s | s.2.1 = true} ∧
       ∃ m, ∀ {B : Type} (r : (∀ k, ((correctedRegister 0).process ()).Value k) → B),
         ¬ (((correctedRegister 0).process ()).withRule r).TellsApart (movingWorld m) (fun s => s.2.2.2)) ∧
    (heldCorrection.Runs heldCourse ∧ heldCorrection.Premise Set.univ heldCourse ∧ heldCorrection.LapseHeld Set.univ ∧ (∀ t, heldCorrection.kept (heldCourse t)) ∧
       (∀ m, ((correctedRegister m).process ()).TellsApart (movingWorld m) (fun s => s.2.2.2)) ∧
       s(((false, false, false, false) : Four), (false, false, false, true)) ∈ (correctedRegister 0).between ∧
       s(((false, false, false, false) : Four), (false, false, false, true)) ∉ (correctedRegister 1).between) := by
  refine ⟨?_, ?_⟩
  · have hrun : unheldCorrection.Runs cutCourse := fun t => by
      change (decide (t + 1 = 0) = true) ↔ (decide (t = 0) = true) ∧ (true : Bool) = false
      simp
    have hnot : ¬ unheldCorrection.LapseHeld {s | s.2.1 = true} := by
      intro hl
      obtain ⟨i, hi, hh, -⟩ := hl.of_noJoins rfl
      obtain rfl : i = false := hi
      refine readers_not_holds_of_const correctorGrain false _ ?_ _ hh
      intro s hs t ht
      exact (show s.2.1 = true from hs).trans (show t.2.1 = true from ht).symm
    have hp : unheldCorrection.Premise {s | s.2.1 = true} cutCourse :=
      ⟨fun s hs _ => ⟨0, fun i hi => by
          obtain rfl : i = false := hi
          exact (show s.2.1 = true from hs).symm⟩,
        fun _ => ⟨(true, true, false, false), rfl, rfl, fun h => Bool.false_ne_true (Eq.symm h)⟩⟩
    refine ⟨hrun, hp, hnot, ?_⟩
    obtain ⟨n, -, m, -, hlost⟩ := Composition.what_is_for (ι := Unit) unheldCorrection _ cutCourse (fun _ => correctedRegister 0) movingWorld (fun s => s.2.2.2) () hrun hp hnot (fun _ _ => rfl)
      (fun n _ => ⟨n + 1, Nat.le_succ n, (false, false, false, false), trivial, (false, false, false, true), trivial,
        ⟨by simp [Sym2.mk_isDiag_iff], fun _ => (mem_kernel _ _ _).mpr rfl⟩, by decide⟩)
    exact ⟨m, hlost⟩
  · have hheld : heldCorrection.LapseHeld Set.univ :=
      Or.inl ⟨true, trivial, readers_holds correctorGrain true _ _ (fun _ => Iff.rfl) ⟨(true, false, false, false), trivial, rfl⟩ ⟨(false, false, false, false), trivial, rfl⟩,
        (true, true, false, false), trivial, (false, true, false, false), trivial, rfl, fun h => Bool.false_ne_true h, Or.inr rfl, fun j => cond j false true, fun j hj => by cases j; exact rfl; exact absurd rfl hj, rfl, by
          rintro (h | h)
          · exact Bool.false_ne_true (Eq.symm h)
          · exact Bool.false_ne_true h⟩
    refine ⟨fun _ => ⟨fun h => ⟨h, Or.inr rfl⟩, fun h => h.1⟩, ⟨?_, fun hn => absurd hheld hn⟩, hheld, fun _ => rfl, ?_, ?_, ?_⟩
    · rintro ⟨a, b, c, d⟩ - hk
      obtain rfl : a = true := hk
      cases b
      · exact ⟨0, fun i _ => by cases i <;> rfl⟩
      · exact ⟨1, fun i _ => by cases i <;> rfl⟩
    · intro m u hu v hv hq he
      cases m with
      | zero =>
        have hu' : u.2.2.1 = u.2.2.2 := hu
        have hv' : v.2.2.1 = v.2.2.2 := hv
        have hsame : u.2.2.1 = v.2.2.1 := he
        exact hq (hu'.symm.trans (hsame.trans hv'))
      | succ m => exact hq he
    · exact ⟨by simp [Sym2.mk_isDiag_iff], fun _ => (mem_kernel _ _ _).mpr rfl⟩
    · rintro ⟨-, h⟩
      have := (mem_kernel _ _ _).mp (h ())
      exact Bool.false_ne_true this

/-! ## What gets built -/

/-- **Claim 18 (What gets built), a claim.** A claim of a position is a quantity it can be paid on: one its coarse-grainings carry. -/
def Arrangement.Claimable (A : Arrangement S ι) (i : ι) {Q : Type} (q : S → Q) : Prop :=
  (A.process i).Carries q

/-- **Claim 18 (What gets built), the second kind.** A product that depends on a forestalled state is paid on by no position, and held by none under any rule. Neither is a quantity that separates a pair of the between. -/
theorem Composition.second_kind_unclaimable (A : Arrangement S ι) :
    (∀ {Q : Type} (F : Situation S → Q), DependsOnForestalled F → ∀ i, ¬ CarriesOfSituation (A.process i).jointly F ∧ ∀ (W : Set (Situation S)) {B : Type} (r : (∀ j, (A.process i).Value j) → B), ¬ ((A.process i).withRule r).HoldsOfSituation W F) ∧
      ∀ {Q : Type} (q : S → Q) {z : Sym2 S}, z ∈ A.between → Separates q z → ∀ i, ¬ A.Claimable i q ∧ ∀ (X : Accessible S) {B : Type} (r : (∀ j, (A.process i).Value j) → B), ¬ ((A.process i).withRule r).Holds X q := by
  refine ⟨fun F hF i => ⟨Response.nonevent.1 _ F hF, fun W _ r => Response.holds_nothing_forestalled _ W hF⟩, fun q _ hz hq i => ?_⟩
  obtain ⟨-, hc, hr⟩ := Composition.one_shape A hz q hq
  exact ⟨hc i, fun X _ r => hr i X r⟩

/-- **Claim 18 (What gets built), a holder made.** The lapse is a quantity of the state, though what the keeping prevents is not. So where a position comes to carry whether it is kept, and that takes two values across the accessible states, some rule there holds the lapse, and still no rule holds what it prevents. -/
theorem Composition.holder_made (K : Keeping A) (X : Accessible S) (i : ι) (hk : A.Claimable i K.kept) (hkv : ∃ s ∈ X, ∃ t ∈ X, K.kept s ≠ K.kept t) :
    (∃ (B : Type) (r : (∀ j, (A.process i).Value j) → B), ((A.process i).withRule r).Holds X K.kept) ∧
      ∀ (W : Set (Situation S)) {B : Type} (r : (∀ j, (A.process i).Value j) → B), ¬ ((A.process i).withRule r).HoldsOfSituation W K.value :=
  ⟨(Process.holdable_iff _ X _).mpr ⟨hk, hkv⟩, fun W _ _ => Response.holds_nothing_forestalled _ W K.prevents⟩

/-- What each position reads in the witness of a holder made: at `none` whether the step is tight, at `some true` the first bit, at `some false` whether the keeping is kept. -/
def builtGrain : Option Bool → Three → Bool
  | none, s => s.2.2
  | some true, s => s.1
  | some false, s => s.2.1

/-- What reads whether the step is tight, a reader of the first bit, and a reader of the keeping. -/
def builtReaders : Arrangement Three (Option Bool) :=
  readers builtGrain

/-- A keeping decided by what reads whether the step is tight. -/
def preventedCut : Keeping builtReaders where
  kept := fun s => s.2.1 = true
  deciding := {none}
  stays := fun r => r none = false
  reads_deciding := fun r r' h => by rw [h none rfl]
  Value := ℕ
  value := fun w => 1 * collapse w
  prevents := collapse_depends (by decide)

/-- The same keeping with its reader deciding too. -/
def preventedHeld : Keeping builtReaders where
  kept := fun s => s.2.1 = true
  deciding := {none, some false}
  stays := fun r => r none = false ∨ r (some false) = true
  reads_deciding := fun r r' h => by rw [h none (Or.inl rfl), h (some false) (Or.inr rfl)]
  Value := ℕ
  value := fun w => 1 * collapse w
  prevents := collapse_depends (by decide)

/-- A course on which that keeping is cut at the first tight step. -/
def builtCourse : Course Three :=
  fun t => (true, decide (t ≤ 1), decide (t ≠ 0))

/-- A course on which it stays kept. -/
def builtHeldCourse : Course Three :=
  fun t => (true, true, decide (t ≠ 0))

/-- **Claim 18 (What gets built), what a holder made does.** On one arrangement, on tight steps, under the premise: a keeping no deciding process holds is cut. With the process that reads it among those that decide, and a decision that reads it, it lasts. The two differ only in who decides and what the decision reads. -/
theorem Composition.holder_made_occurs :
    (preventedCut.Runs builtCourse ∧ preventedCut.Premise Set.univ builtCourse ∧ ¬ preventedCut.LapseHeld Set.univ ∧ ¬ preventedCut.kept (builtCourse 2)) ∧
      (preventedHeld.Runs builtHeldCourse ∧ preventedHeld.Premise Set.univ builtHeldCourse ∧ preventedHeld.LapseHeld Set.univ ∧ ∀ t, preventedHeld.kept (builtHeldCourse t)) := by
  have hh : preventedHeld.LapseHeld Set.univ :=
    Or.inl ⟨some false, Or.inr rfl, readers_holds builtGrain (some false) _ _ (fun _ => Iff.rfl) ⟨(false, true, false), trivial, rfl⟩ ⟨(false, false, false), trivial, rfl⟩,
      (false, true, true), trivial, (false, false, true), trivial, rfl, fun h => Bool.false_ne_true h, Or.inr rfl, fun j => j.isNone, fun j hj => by
        match j, hj with
        | none, _ => rfl
        | some true, _ => rfl
        | some false, hj => exact absurd rfl hj, rfl, by
        rintro (h | h)
        · exact Bool.false_ne_true (Eq.symm h)
        · exact Bool.false_ne_true h⟩
  have hn : ¬ preventedCut.LapseHeld Set.univ := by
    intro hl
    obtain ⟨i, hi, hh', -⟩ := hl.of_noJoins rfl
    obtain rfl : i = none := hi
    exact readers_not_holds_of_differs builtGrain none Set.univ preventedCut.kept (s := (false, true, false)) (t := (false, true, true)) trivial trivial rfl (by decide) hh'
  refine ⟨⟨fun t => ?_, ⟨?_, fun _ => ⟨(false, true, true), trivial, rfl, fun h => Bool.false_ne_true (Eq.symm h)⟩⟩, hn, ?_⟩, ⟨fun _ => ⟨fun h => ⟨h, Or.inr rfl⟩, fun h => h.1⟩, ⟨?_, fun hc => absurd hh hc⟩, hh, fun _ => rfl⟩⟩
  · change (decide (t + 1 ≤ 1) = true) ↔ (decide (t ≤ 1) = true) ∧ decide (t ≠ 0) = false
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · rintro ⟨a, b, c⟩ - -
    cases c
    · exact ⟨0, fun i hi => by obtain rfl : i = none := hi; rfl⟩
    · exact ⟨1, fun i hi => by obtain rfl : i = none := hi; rfl⟩
  · exact fun h => Bool.false_ne_true h
  · rintro ⟨a, b, c⟩ - hk
    obtain rfl : b = true := hk
    cases c
    · refine ⟨0, fun i hi => ?_⟩
      rcases hi with rfl | rfl <;> rfl
    · refine ⟨1, fun i hi => ?_⟩
      rcases hi with rfl | rfl <;> rfl

/-! ## Removing a cause -/

/-- **Claim 20 (Removing a cause).** A cause is a value of what the deciding responses do, here their value at a state `c`. Removing it takes those states out of the accessible states, and nothing else moves. -/
def Upkeep.withoutCause (K : Upkeep A) (X : Accessible S) (c : S) : Accessible S :=
  {s | s ∈ X ∧ ¬ ∀ i ∈ K.deciding, (A.process i).response s = (A.process i).response c}

/-- **Claim 20 (Removing a cause).** Remove a cause and leave what each position holds of the lapse as it was. Nothing registered moves. Under the premise on the smaller set, one value it still holds cuts the keeping, and it is another value than the one removed, and a course that runs it and meets the premise cuts it. The strength lies in the premise, read on the smaller set. -/
theorem Persistence.removing_cause (K : Keeping A) (X : Accessible S) (c : S) (x : Course S) (hrun : K.Runs x) (hp : K.Premise (K.withoutCause X c) x)
    (hsame : K.LapseHeld (K.withoutCause X c) ↔ K.LapseHeld X) (hnot : ¬ K.LapseHeld X) :
    (let ch : Change S ι := ⟨A, A, X, K.withoutCause X c, Or.inr rfl⟩
     ch.after.between = ch.before.between ∧ (∀ j, ch.price j = ∅) ∧ ∀ j, ch.release j = ∅) ∧
      (∃ s ∈ X, K.kept s ∧ ¬ K.decision s ∧ ¬ ∀ i ∈ K.deciding, (A.process i).response s = (A.process i).response c) ∧
      ∃ n, ∀ m, ¬ K.kept (x (n + m)) := by
  have hnot' : ¬ K.LapseHeld (K.withoutCause X c) := fun h => hnot (hsame.mp h)
  obtain ⟨s, ⟨hs, hother⟩, hk, hcut⟩ := hp.occasions hnot'
  exact ⟨change_of_world_keeps_between ⟨A, A, X, K.withoutCause X c, Or.inr rfl⟩ rfl, ⟨s, hs, hk, hcut, hother⟩, K.toUpkeep.lapses _ x hrun hp hnot'⟩

/-- A process that reads two causes. -/
def causeReader : Arrangement Three Unit :=
  ⟨inferInstance, fun _ => Process.reading Prod.snd, ∅⟩

/-- A capacity cut wherever either of two causes arises. -/
def causedKeeping : Keeping causeReader where
  kept := fun s => s.1 = true
  deciding := Set.univ
  stays := fun r => r () = (false, false)
  reads_deciding := fun r r' h => by rw [h () trivial]
  Value := ℕ
  value := fun w => 1 * collapse w
  prevents := collapse_depends (by decide)

/-- A course meeting the second cause at its second step, and both after. -/
def causedCourse : Course Three
  | 0 => (true, false, false)
  | 1 => (true, false, true)
  | _ + 2 => (false, true, true)

/-- **Claim 20 (Removing a cause), it occurs, and where it stops.** Remove the first of two causes: the premise is met on the smaller set, no deciding process holds the lapse before or after, and the keeping is cut by the other. Remove every cause: nothing is left that cuts, the second clause fails, and the keeping lasts with no deciding process holding it. So the claim's "other causes" is the premise's. -/
theorem Persistence.removing_cause_occurs :
    (causedKeeping.Runs causedCourse ∧ causedKeeping.Premise (causedKeeping.withoutCause Set.univ (true, true, false)) causedCourse ∧
      (causedKeeping.LapseHeld (causedKeeping.withoutCause Set.univ (true, true, false)) ↔ causedKeeping.LapseHeld Set.univ) ∧ ¬ causedKeeping.LapseHeld Set.univ) ∧
    (causedKeeping.Runs (fun _ => (true, false, false)) ∧ causedKeeping.kept ((true, false, false) : Three) ∧ ¬ causedKeeping.LapseHeld {s | s.2 = (false, false)} ∧
      ¬ causedKeeping.Occasions {s | s.2 = (false, false)}) := by
  have hnotAt : ∀ X : Accessible Three, ((true, false, false) : Three) ∈ X → ((true, false, true) : Three) ∈ X → ¬ causedKeeping.LapseHeld X := by
    intro X h0 h1 hl
    obtain ⟨⟨⟩, -, ⟨-, hfix, -⟩, -⟩ := hl.of_noJoins rfl
    have : ((false, false) : Bool × Bool) = (false, true) := hfix _ h0 _ h1 (show causedKeeping.kept (true, false, false) = causedKeeping.kept (true, false, true) from rfl)
    exact absurd this (by decide)
  have hin : ∀ s : Three, s.2 ≠ (true, false) → s ∈ causedKeeping.withoutCause Set.univ (true, true, false) := fun s hs =>
    ⟨trivial, fun h => hs (h () trivial)⟩
  have hnotSmall := hnotAt _ (hin _ (by decide)) (hin _ (by decide))
  have hnotAll := hnotAt Set.univ trivial trivial
  have hconst : ¬ causedKeeping.LapseHeld {s | s.2 = (false, false)} := by
    intro hl
    obtain ⟨⟨⟩, -, ⟨-, -, s, hs, t, ht, -, ha⟩, -⟩ := hl.of_noJoins rfl
    exact ha ((show s.2 = (false, false) from hs).trans (show t.2 = (false, false) from ht).symm)
  refine ⟨⟨fun t => ?_, ⟨?_, fun _ => ⟨(true, false, true), hin _ (by decide), rfl, fun h => absurd (show ((false, true) : Bool × Bool) = (false, false) from h) (by decide)⟩⟩, ⟨fun h => absurd h hnotSmall, fun h => absurd h hnotAll⟩, hnotAll⟩,
    fun _ => ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩, rfl, hconst, fun h => ?_⟩
  · match t with
    | 0 => exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
    | 1 => exact ⟨fun h => absurd (show (false : Bool) = true from h) (by decide), fun h => absurd (show ((false, true) : Bool × Bool) = (false, false) from h.2) (by decide)⟩
    | _ + 2 => exact ⟨fun h => absurd (show (false : Bool) = true from h) (by decide), fun h => absurd (show (false : Bool) = true from h.1) (by decide)⟩
  · rintro ⟨a, b, c⟩ ⟨-, hother⟩ -
    match b, c with
    | false, false => exact ⟨0, fun i _ => rfl⟩
    | false, true => exact ⟨1, fun i _ => rfl⟩
    | true, true => exact ⟨2, fun i _ => rfl⟩
    | true, false => exact absurd (fun i _ => rfl) hother
  · obtain ⟨s, hs, -, hcut⟩ := h hconst
    exact hcut (show s.2 = (false, false) from hs)

/-- What the process of the next witness reads: one value where it is kept, another where it has lapsed in a calm step, and another where it has lapsed in a tight one. -/
def threeValues (s : Two) : ℕ :=
  if s.1 = true then 1 else if s.2 = true then 2 else 0

/-- A process reading those three values. -/
def threeValued : Arrangement Two Unit :=
  ⟨inferInstance, fun _ => Process.reading threeValues, ∅⟩

/-- An upkeep decided by that process. -/
def threeValuedKeeping : Upkeep threeValued where
  kept := fun s => s.1 = true
  deciding := Set.univ
  stays := fun r => @Eq ℕ (r ()) 1
  reads_deciding := fun r r' h => by rw [h () trivial]

/-- **Claim 20 (Removing a cause), what is held need not stay.** Taking states out of the accessible states can bring a holding that was not there: across all the states no deciding process holds the lapse, and with one value of the response removed its process does. So leaving what each party holds as it was is a real hypothesis of the claim. -/
theorem Persistence.removing_cause_can_make_holder :
    ¬ threeValuedKeeping.LapseHeld Set.univ ∧ threeValuedKeeping.LapseHeld (threeValuedKeeping.withoutCause Set.univ (false, true)) := by
  have hresp : ∀ s, (threeValued.process ()).response s = threeValues s := fun _ => rfl
  have hout : ∀ a b : Bool, threeValues (a, b) ≠ threeValues (false, true) → (a, b) ∈ threeValuedKeeping.withoutCause Set.univ (false, true) := fun a b h =>
    ⟨trivial, fun hall => h (hall () trivial)⟩
  refine ⟨?_, Or.inl ⟨(), trivial, ⟨⟨fun v => @Eq ℕ (v ()) 1, funext fun s => ?_⟩, ?_, (true, false), hout _ _ (by decide), (false, false), hout _ _ (by decide), ?_, ?_⟩, (true, false), hout _ _ (by decide), (false, false), hout _ _ (by decide), rfl, fun h => Bool.false_ne_true h, rfl, fun _ => (0 : ℕ), fun j hj => absurd rfl hj, rfl, fun h => absurd (show (0 : ℕ) = 1 from h) (by decide)⟩⟩
  · intro hl
    obtain ⟨⟨⟩, -, ⟨-, hfix, -⟩, -⟩ := hl.of_noJoins rfl
    have : threeValues (false, false) = threeValues (false, true) := hfix (false, false) trivial (false, true) trivial rfl
    exact absurd this (by decide)
  · rcases s with ⟨a, b⟩
    refine propext ?_
    change a = true ↔ threeValues (a, b) = 1
    cases a <;> cases b <;> decide
  · rintro ⟨a, b⟩ ⟨-, ha⟩ ⟨c, d⟩ ⟨-, hc⟩ h
    have ha' : threeValues (a, b) ≠ threeValues (false, true) := fun e => ha fun _ _ => e
    have hc' : threeValues (c, d) ≠ threeValues (false, true) := fun e => hc fun _ _ => e
    have hk : (a = true) = (c = true) := h
    change threeValues (a, b) = threeValues (c, d)
    revert ha' hc' hk
    cases a <;> cases b <;> cases c <;> cases d <;> simp [threeValues]
  · exact fun h => Bool.false_ne_true (Eq.mp (show ((true : Bool) = true) = ((false : Bool) = true) from h) rfl)
  · exact fun h => absurd (show threeValues (true, false) = threeValues (false, false) from h) (by decide)

/-! ## Shared shape, and what is learned about persistence -/

/-- **Claim 29 (Shared shape, shared lessons), about persistence.** Let a relabelling carry one setting to another, and let a keeping of each be matched: one is kept where the other is, under the states' bijection, and their deciding positions correspond. Whether a deciding process holds the lapse carries across. So what a course shows in one, that a keeping lasted under the premise and so was held, gives the other a deciding process holding its lapse. And where no deciding process holds the first, no course of the second that runs its keeping and meets the premise there keeps it. Nothing else of the two keepings need match, their rules and their values among them. The first line is a clause of what a relabelling is, and the other two are `Persistence.lapse` read through it. -/
theorem Relabelling.persistence_carried {A : Setting S ι} {B : Setting S' ι'} (r : Relabelling A B) (K : Keeping A.arrangement) (K' : Keeping B.arrangement)
    (hkept : K'.kept = K.kept ∘ r.states.symm) (hdec : K'.deciding = r.positions '' K.deciding) :
    (K.Holder A.accessible ↔ K'.Holder B.accessible) ∧
      (∀ x : Course S, K.Runs x → K.Premise A.accessible x → (∀ t, K.kept (x t)) → K'.Holder B.accessible) ∧
      (¬ K.Holder A.accessible → ∀ x' : Course S', K'.Runs x' → K'.Premise B.accessible x' → ∃ n, ∀ m, ¬ K'.kept (x' (n + m))) := by
  have hiff : K.Holder A.accessible ↔ K'.Holder B.accessible := by
    constructor
    · rintro ⟨i, hh, hi | ⟨j, hj, hg, ht⟩⟩
      · refine ⟨r.positions i, ?_, Or.inl (by rw [hdec]; exact ⟨i, hi, rfl⟩)⟩
        rw [hkept]
        exact (r.held i K.kept).mp hh
      · obtain ⟨j', hj', htk, hgv, -⟩ := r.joins j hj
        refine ⟨r.positions i, ?_, Or.inr ⟨j', hj', hgv.trans (congrArg r.positions hg), by rw [hdec]; exact ⟨j.taker, ht, htk.symm⟩⟩⟩
        rw [hkept]
        exact (r.held i K.kept).mp hh
    · rintro ⟨i', hh, hi' | ⟨j', hj', hg, ht⟩⟩
      · rw [hdec] at hi'
        obtain ⟨i, hi, rfl⟩ := hi'
        rw [hkept] at hh
        exact ⟨i, (r.held i K.kept).mpr hh, Or.inl hi⟩
      · obtain ⟨j, hj, htk, hgv, -⟩ := r.joins_onto j' hj'
        rw [hdec] at ht
        obtain ⟨k, hk, hkt⟩ := ht
        have hkj : k = j.taker := r.positions.injective (hkt.trans htk)
        subst hg
        rw [hgv, hkept] at hh
        exact ⟨j.giver, (r.held _ K.kept).mpr hh, Or.inr ⟨j, hj, rfl, hkj ▸ hk⟩⟩
  exact ⟨hiff, fun x hrun hp hk => hiff.mp (Persistence.lapse K _ x hrun hp hk).holder,
    fun hn x' hrun hp => K'.toUpkeep.lapses _ x' hrun hp fun h => hn (hiff.mpr h.holder)⟩

/-- **Claim 29 (Shared shape, shared lessons), at a cut.** Two settings share shape at a cut when what two cuts read, each with its accessible states,
have one content. Then what `Relabelling.persistence_carried` says carries across them, whatever the sizes of the two worlds: whether a holder
reaches each decision, and with it what the premise says where none does. It is that theorem read at the cuts. -/
theorem Relabelling.persistence_carried_at_cut {τ τ' : Type} (cut : Cut S τ) (cut' : Cut S' τ') {N : Nested S} {N' : Nested S'} (h : cut.Stands N)
    (h' : cut'.Stands N') {X : Accessible cut.States} {Y : Accessible cut'.States} (hX : X.Nonempty) (hY : Y.Nonempty)
    (r : Relabelling ⟨cut.read h, X, hX⟩ ⟨cut'.read h', Y, hY⟩) (K : Keeping (cut.read h)) (K' : Keeping (cut'.read h'))
    (hkept : K'.kept = K.kept ∘ r.states.symm) (hdec : K'.deciding = r.positions '' K.deciding) :
    (K.Holder X ↔ K'.Holder Y) ∧
      (∀ x : Course cut.States, K.Runs x → K.Premise X x → (∀ t, K.kept (x t)) → K'.Holder Y) ∧
      (¬ K.Holder X → ∀ x' : Course cut'.States, K'.Runs x' → K'.Premise Y x' → ∃ n, ∀ m, ¬ K'.kept (x' (n + m))) :=
  r.persistence_carried K K' hkept hdec

/-- The arrangement of `Companion.Time`'s witnesses, with what reads whether it is kept made to respond with nothing: one constitution at each position. -/
def quietHolder : Arrangement Two Bool :=
  ⟨inferInstance, fun b => (officeAndHolder.process b).withRule fun v => cond b false (v () : Bool), ∅⟩

/-- `Companion.Time`'s keeping decided by the same responses, on that arrangement. -/
def quietKeeping : Keeping quietHolder where
  kept := fun s => s.1 = true
  deciding := Set.univ
  stays := fun r => r false = false ∨ r true = true
  reads_deciding := fun r r' h => by rw [h false trivial, h true trivial]
  Value := Two
  value := Situation.wouldHave
  prevents := two_wouldHave_depends

/-- **Claim 29 (Shared shape, shared lessons), one content is needed.** Two settings over one set of positions, with the same constitutions at every position and no joins, are not of one content where one holds a lapse and the other does not. In the first a deciding process holds a keeping's lapse, and in the second, under the same words, none does, and the second clause gives a value that cuts it. So the lesson about persistence does not cross on what the two register alone. -/
theorem Persistence.needs_one_content :
    (∀ b, (quietHolder.process b).constitution = (officeAndHolder.process b).constitution) ∧
      ¬ OneContent (⟨officeAndHolder, Set.univ, ⟨(false, false), trivial⟩⟩ : Setting Two Bool) ⟨quietHolder, Set.univ, ⟨(false, false), trivial⟩⟩ ∧
      heldKeeping.LapseHeld Set.univ ∧ ¬ quietKeeping.LapseHeld Set.univ ∧ quietKeeping.Occasions Set.univ := by
  have hquiet : ∀ s t : Two, (quietHolder.process true).response s = (quietHolder.process true).response t := fun _ _ => rfl
  have hnot : ¬ quietKeeping.LapseHeld Set.univ := by
    intro hl
    obtain ⟨i, -, ⟨-, hfix, s, -, t, -, -, ha⟩, -⟩ := hl.of_noJoins rfl
    cases i
    · have : ((false : Bool)) = true := hfix (true, false) trivial (true, true) trivial rfl
      exact Bool.false_ne_true this
    · exact ha (hquiet s t)
  refine ⟨fun _ => rfl, ?_, Persistence.occurs.2.2.2, hnot, fun _ => ⟨(true, true), trivial, rfl, ?_⟩⟩
  · rintro ⟨r⟩
    obtain ⟨i, hi⟩ := r.positions.surjective true
    have hheld : (officeAndHolder.process i).Holds Set.univ (cond i Prod.fst Prod.snd : Two → Bool) := by
      refine ⟨⟨fun v => v (), rfl⟩, fun _ _ _ _ e => e, ?_⟩
      cases i
      · exact ⟨(false, false), trivial, (false, true), trivial, by decide, Bool.false_ne_true⟩
      · exact ⟨(false, false), trivial, (true, false), trivial, by decide, Bool.false_ne_true⟩
    have hb := (r.held i _).mp hheld
    rw [hi] at hb
    obtain ⟨-, -, s, -, t, -, -, ha⟩ := hb
    exact ha (hquiet s t)
  · rintro (h | h)
    · exact Bool.false_ne_true (Eq.symm h)
    · exact Bool.false_ne_true h

/-- **Claim 29 (Shared shape, shared lessons), lasting does not cross.** Two keepings of one setting, matched in what is kept and in who decides, each with its lapse held. Along a course that meets the premise one stays kept, and along no such course does the other. So one content carries whether a lapse is held, and not whether what is held lasts, since the rules that decide are no part of a content. -/
theorem Persistence.matched_do_not_behave_alike :
    OneContent (⟨officeAndHolder, Set.univ, ⟨(false, false), trivial⟩⟩ : Setting Two Bool) ⟨officeAndHolder, Set.univ, ⟨(false, false), trivial⟩⟩ ∧ heldAndOutvoted.kept = heldKeeping.kept ∧ heldAndOutvoted.deciding = heldKeeping.deciding ∧
      heldKeeping.LapseHeld Set.univ ∧ heldAndOutvoted.LapseHeld Set.univ ∧
      (heldKeeping.Runs keptCourse ∧ heldKeeping.Premise Set.univ keptCourse ∧ ∀ t, heldKeeping.kept (keptCourse t)) ∧
      ∀ x : Course Two, heldAndOutvoted.Runs x → heldAndOutvoted.Premise Set.univ x → ¬ ∀ t, heldAndOutvoted.kept (x t) := by
  refine ⟨⟨Relabelling.refl _⟩, rfl, rfl, Persistence.occurs.2.2.2, held_can_be_cut.2.1, ⟨Persistence.occurs.1, Persistence.occurs.2.1, Persistence.occurs.2.2.1⟩, fun x hrun hp hk => ?_⟩
  obtain ⟨t, ht⟩ := hp.ranges (true, true) trivial rfl
  exact held_can_be_cut.2.2 ((heldAndOutvoted.decision_iff ht).mp ((hrun t).mp (hk (t + 1))).2)

/-! ## What a fix leaves, and what decays -/

/-- **Claim 31 (What a fix leaves), a price can buy nothing new.** Fill an absent position with a copy of a process that already stands. That position pays for all that process tells apart, and the between stays as it was. -/
theorem Composition.fix_hires (A : Arrangement S ι) (k j : ι) (hk : A.process k = Process.absent) (X : Accessible S) :
    ∃ ch : Change S ι, ch.before = A ∧ ch.accessibleAfter = X ∧ ch.after.process k = A.process j ∧ (∀ i, i ≠ k → ch.after.process i = A.process i) ∧
      ch.after.between = A.between ∧ ch.price k = {z | z ∉ (A.process j).constitution} := by
  classical
  let A' : Arrangement S ι := ⟨A.finite, Function.update A.process k (A.process j), ∅⟩
  have hkk : A'.process k = A.process j := Function.update_self k _ A.process
  have hother : ∀ i, i ≠ k → A'.process i = A.process i := fun i hi => Function.update_of_ne hi _ A.process
  refine ⟨⟨A, A', X, X, Or.inl rfl⟩, rfl, rfl, hkk, hother, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨hd, hall⟩
      refine ⟨hd, fun i => ?_⟩
      by_cases hi : i = k
      · rw [hi, hk, constitution_absent]
        exact Set.mem_univ z
      · have := hall i
        rwa [hother i hi] at this
    · rintro ⟨hd, hall⟩
      refine ⟨hd, fun i => ?_⟩
      by_cases hi : i = k
      · rw [hi, hkk]
        exact hall j
      · rw [hother i hi]
        exact hall i
  · ext z
    constructor
    · rintro ⟨-, hout⟩ hin
      exact hout (show z ∈ (A'.process k).constitution by rw [hkk]; exact hin)
    · intro hout
      refine ⟨?_, fun hin => hout ?_⟩
      · change z ∈ (A.process k).constitution
        rw [hk, constitution_absent]
        exact Set.mem_univ z
      · have h : z ∈ (A'.process k).constitution := hin
        rwa [hkk] at h

/-- **Claim 31 (What a fix leaves), its decay.** Read a course from the step at which the event has faded. Where, across the states from there on, the lapse is not held, and the premise is met there, it is cut at some later step and stays cut. Its strength lies in the premise. -/
theorem Persistence.fades (K : Keeping A) (Y : Accessible S) (x : Course S) (n : ℕ) (hrun : K.Runs x) (hp : K.Premise Y (x.from n)) (hnot : ¬ K.LapseHeld Y) :
    ∃ m, ∀ j, ¬ K.kept (x (n + (m + j))) :=
  K.toUpkeep.lapses Y (x.from n) (hrun.from n) hp hnot

/-- **Claim 32 (Second-order reforms need holders of their own).** Under the premise, a keeping whose lapse is not held is cut at some step and stays cut, whatever else it does: this holds of any keeping, a reform's among them. Its strength lies in the premise. -/
theorem Persistence.decays (K : Keeping A) (X : Accessible S) (x : Course S) (hrun : K.Runs x) (hp : K.Premise X x) (hnot : ¬ K.LapseHeld X) :
    ∃ n, ∀ m, ¬ K.kept (x (n + m)) :=
  K.toUpkeep.lapses X x hrun hp hnot

/-- What each position of the witnesses of reform reads, as a pair. -/
def reformGrain : Option Bool → Three → Bool × Bool
  | none, s => (s.2.2, false)
  | some false, s => (s.1, s.2.1)
  | some true, s => (s.1, false)

/-- What each position does with what it reads: at `some false` it responds to the two together, and elsewhere to the first. -/
def reformRule : Option Bool → Bool × Bool → Bool
  | some false, v => v.1 && v.2
  | _, v => v.1

/-- Three positions: what reads whether the step is tight, a council that responds to a fix while attention or a reform stands, and what reads whether a reform stands. In each state the first entry says whether attention or a reform stands, the second whether the fix is kept, and the third whether the step is tight. -/
def council : Arrangement Three (Option Bool) :=
  ⟨inferInstance, fun i => (Process.reading (reformGrain i)).withRule fun v => reformRule i (v ()), ∅⟩

/-- A fix, kept in a tight step only where the council responds to it. -/
def councilFix : Keeping council where
  kept := fun s => s.2.1 = true
  deciding := {none, some false}
  stays := fun r => r none = false ∨ r (some false) = true
  reads_deciding := fun r r' h => by rw [h none (Or.inl rfl), h (some false) (Or.inr rfl)]
  Value := ℕ
  value := fun w => 1 * collapse w
  prevents := collapse_depends (by decide)

/-- A reform whose own lapse no deciding process holds. -/
def unheldReform : Keeping council where
  kept := fun s => s.1 = true
  deciding := {none}
  stays := fun r => r none = false
  reads_deciding := fun r r' h => by rw [h none rfl]
  Value := ℕ
  value := fun w => 1 * collapse w
  prevents := collapse_depends (by decide)

/-- The same reform with a holder of its own, who decides too. -/
def heldReform : Keeping council where
  kept := fun s => s.1 = true
  deciding := {none, some true}
  stays := fun r => r none = false ∨ r (some true) = true
  reads_deciding := fun r r' h => by rw [h none (Or.inl rfl), h (some true) (Or.inr rfl)]
  Value := ℕ
  value := fun w => 1 * collapse w
  prevents := collapse_depends (by decide)

/-- A course calm before step `n` and tight from there, on which the reform stands through step `n` and the fix one step more. -/
def fadingCourse (n : ℕ) : Course Three :=
  fun t => (decide (t ≤ n), decide (t ≤ n + 1), decide (n ≤ t))

/-- The accessible states where attention or a reform stands. -/
def whileStanding : Accessible Three :=
  {s | s.1 = true}

/-- The accessible tight states once attention or a reform has gone. -/
def onceGone : Accessible Three :=
  {s | s.1 = false ∧ s.2.2 = true}

/-- Whether a position is not the council. -/
def notCouncil : Option Bool → Bool
  | some false => false
  | _ => true

/-- The council holds the fix's lapse across the states where attention or a reform stands. -/
theorem council_holds_fix : councilFix.LapseHeld whileStanding := by
  refine Or.inl ⟨some false, Or.inr rfl, ⟨⟨fun v => (v () : Bool × Bool).2 = true, rfl⟩, ?_, (true, true, false), rfl, (true, false, false), rfl, ?_, ?_⟩,
    (true, true, true), rfl, (true, false, true), rfl, rfl, fun h => Bool.false_ne_true h, Or.inr rfl, fun j => notCouncil j, fun j hj => ?_, rfl, ?_⟩
  · rintro ⟨a, b, c⟩ ha ⟨a', b', c'⟩ ha' h
    obtain rfl : a = true := ha
    obtain rfl : a' = true := ha'
    have hb : (b = true) = (b' = true) := h
    change (true && b) = (true && b')
    cases b <;> cases b' <;> simp_all
  · exact fun h => Bool.false_ne_true (Eq.mp (show ((true : Bool) = true) = ((false : Bool) = true) from h) rfl)
  · exact fun h => absurd (show (true : Bool) = false from h) (by decide)
  · match j, hj with
    | none, _ => rfl
    | some true, _ => rfl
    | some false, hj => exact absurd rfl hj
  · rintro (h | h)
    · exact Bool.false_ne_true (Eq.symm h)
    · exact Bool.false_ne_true h

/-- No deciding process holds it across the tight states once that has gone. -/
theorem council_not_holds_fix_once_gone : ¬ councilFix.LapseHeld onceGone := by
  intro hl
  obtain ⟨i, hi, ⟨-, -, ⟨a, b, c⟩, ⟨ha, hc⟩, ⟨a', b', c'⟩, ⟨ha', hc'⟩, -, hne⟩, -⟩ := hl.of_noJoins rfl
  obtain rfl : a = false := ha
  obtain rfl : a' = false := ha'
  obtain rfl : c = true := hc
  obtain rfl : c' = true := hc'
  rcases hi with rfl | rfl
  · exact hne rfl
  · exact hne rfl

/-- **Claim 31 (What a fix leaves), it occurs.** For every step `n`, a fix stays kept through step `n + 1`, with its lapse held across the states where attention stands, and across the tight states after attention has gone no deciding process holds it, the premise is met on the course from there, and it is cut. Nothing in the arrangement changes along the course. -/
theorem Persistence.fades_occurs (n : ℕ) :
    councilFix.Runs (fadingCourse n) ∧ councilFix.LapseHeld whileStanding ∧ ¬ councilFix.LapseHeld onceGone ∧ councilFix.Premise onceGone ((fadingCourse n).from (n + 1)) ∧
      (∀ t ≤ n + 1, councilFix.kept (fadingCourse n t)) ∧ ¬ councilFix.kept (fadingCourse n (n + 2)) := by
  refine ⟨fun t => ?_, council_holds_fix, council_not_holds_fix_once_gone, ⟨?_, fun _ => ⟨(false, true, true), ⟨rfl, rfl⟩, rfl, ?_⟩⟩, fun t ht => ?_, ?_⟩
  · change (decide (t + 1 ≤ n + 1) = true) ↔ (decide (t ≤ n + 1) = true) ∧ (decide (n ≤ t) = false ∨ (decide (t ≤ n) && decide (t ≤ n + 1)) = true)
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.and_eq_true]
    omega
  · rintro ⟨a, b, c⟩ ⟨ha, hc⟩ hk
    obtain rfl : a = false := ha
    obtain rfl : c = true := hc
    obtain rfl : b = true := hk
    refine ⟨0, fun i hi => ?_⟩
    have h1 : decide (n + 1 + 0 ≤ n) = false := by simp
    have h2 : decide (n + 1 + 0 ≤ n + 1) = true := by simp
    have h3 : decide (n ≤ n + 1 + 0) = true := by simp
    rcases hi with rfl | rfl
    · show decide (n ≤ n + 1 + 0) = true
      exact h3
    · show (decide (n + 1 + 0 ≤ n) && decide (n + 1 + 0 ≤ n + 1)) = (false && true)
      rw [h1, h2]
  · rintro (h | h)
    · exact Bool.false_ne_true (Eq.symm h)
    · exact Bool.false_ne_true h
  · change decide (t ≤ n + 1) = true
    simpa using ht
  · change ¬ decide (n + 2 ≤ n + 1) = true
    simp

/-- **Claim 32 (Second-order reforms need holders of their own), it occurs.** A reform that gives a fix a holder, whose own lapse is not held: under the premise it is cut at step `n + 1`, and the fix, which held while the reform stood, is cut one step later. Holding what the reform provides does not hold the reform. -/
theorem Persistence.reform_decays (n : ℕ) :
    unheldReform.Runs (fadingCourse n) ∧ unheldReform.Premise {s | s.2.2 = true} (fadingCourse n) ∧ ¬ unheldReform.LapseHeld {s | s.2.2 = true} ∧
      (∀ t ≤ n, unheldReform.kept (fadingCourse n t)) ∧ ¬ unheldReform.kept (fadingCourse n (n + 1)) ∧
      councilFix.LapseHeld whileStanding ∧ councilFix.Runs (fadingCourse n) ∧ ¬ councilFix.kept (fadingCourse n (n + 2)) := by
  have hf := Persistence.fades_occurs n
  refine ⟨fun t => ?_, ⟨?_, fun _ => ⟨(true, true, true), rfl, rfl, fun h => Bool.false_ne_true (Eq.symm h)⟩⟩, ?_, fun t ht => ?_, ?_, hf.2.1, hf.1, hf.2.2.2.2.2⟩
  · change (decide (t + 1 ≤ n) = true) ↔ (decide (t ≤ n) = true) ∧ decide (n ≤ t) = false
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  · rintro ⟨a, b, c⟩ hc -
    obtain rfl : c = true := hc
    refine ⟨n, fun i hi => ?_⟩
    obtain rfl : i = none := hi
    show decide (n ≤ n) = true
    simp
  · intro hl
    obtain ⟨i, hi, ⟨-, -, s, hs, t, ht, -, hne⟩, -⟩ := hl.of_noJoins rfl
    obtain rfl : i = none := hi
    exact hne ((show s.2.2 = true from hs).trans (show t.2.2 = true from ht).symm)
  · change decide (t ≤ n) = true
    simpa using ht
  · change ¬ decide (n + 1 ≤ n) = true
    simp

/-- A course tight from its second step on, on which a held reform and the fix stay kept. -/
def standingCourse : Course Three :=
  fun t => (true, true, decide (t ≠ 0))

/-- **Claim 33 (The orders depend on each other), the second order makes the first last.** On a course tight from its second step, on that arrangement, with a holder of the reform's own lapse deciding too, the premise on the reform is met, the reform stays at every step, and so does the fix it stands behind. -/
theorem Persistence.held_reform_keeps_fix :
    heldReform.Runs standingCourse ∧ heldReform.Premise Set.univ standingCourse ∧ heldReform.LapseHeld Set.univ ∧ (∀ t, heldReform.kept (standingCourse t)) ∧
      councilFix.Runs standingCourse ∧ councilFix.LapseHeld whileStanding ∧ (∀ t, councilFix.kept (standingCourse t)) := by
  have hheld : heldReform.LapseHeld Set.univ := by
    refine Or.inl ⟨some true, Or.inr rfl, ⟨⟨fun v => (v () : Bool × Bool).1 = true, rfl⟩, ?_, (true, false, false), trivial, (false, false, false), trivial, ?_, ?_⟩,
      (true, false, true), trivial, (false, false, true), trivial, rfl, fun h => Bool.false_ne_true h, Or.inr rfl, fun j => j.isNone, fun j hj => ?_, rfl, ?_⟩
    · rintro ⟨a, b, c⟩ - ⟨a', b', c'⟩ - h
      have ha : (a = true) = (a' = true) := h
      change a = a'
      cases a <;> cases a' <;> simp_all
    · exact fun h => Bool.false_ne_true (Eq.mp (show ((true : Bool) = true) = ((false : Bool) = true) from h) rfl)
    · exact fun h => absurd (show (true : Bool) = false from h) (by decide)
    · match j, hj with
      | none, _ => rfl
      | some false, _ => rfl
      | some true, hj => exact absurd rfl hj
    · rintro (h | h)
      · exact Bool.false_ne_true (Eq.symm h)
      · exact Bool.false_ne_true h
  refine ⟨fun _ => ⟨fun h => ⟨h, Or.inr rfl⟩, fun h => h.1⟩, ⟨?_, fun hn => absurd hheld hn⟩, hheld, fun _ => rfl, fun _ => ⟨fun h => ⟨h, Or.inr rfl⟩, fun h => h.1⟩, council_holds_fix, fun _ => rfl⟩
  rintro ⟨a, b, c⟩ - ha
  obtain rfl : a = true := ha
  cases c
  · refine ⟨0, fun i hi => ?_⟩
    rcases hi with rfl | rfl <;> rfl
  · refine ⟨1, fun i hi => ?_⟩
    rcases hi with rfl | rfl <;> rfl

/-! ## What counts, and a remit -/

/-- **Claim 33 (The orders depend on each other), what counts.** A quantity counts for a process across the accessible states when something it makes moves with that quantity there: some carried quantity the quantity fixes, varying with it. -/
def Process.Counts {Q : Type} (p : Process S) (X : Accessible S) (q : S → Q) : Prop :=
  ∃ (V : Type) (b : S → V), p.Carries b ∧ Fixes X q b ∧ VariesWith X b q

/-- **Claim 33 (The orders depend on each other), a remit.** A remit for a quantity is a process whose coarse-grainings carry it. -/
def Process.RemitFor {Q : Type} (p : Process S) (q : S → Q) : Prop :=
  p.Carries q

/-- **Claim 33 (The orders depend on each other), a remit is built only for what counts.** A builder's decision to build for a quantity follows that quantity across the accessible states. Some rule of the builder does that exactly where the quantity counts for it. -/
theorem Composition.remit_for_what_counts (p : Process S) (X : Accessible S) {Q : Type} (q : S → Q) :
    (∃ (B : Type) (r : (∀ i, p.Value i) → B), Follows X (p.withRule r).response q) ↔ p.Counts X q :=
  Process.followable_iff p X q

/-- **Claim 33 (The orders depend on each other), the third order makes the second possible.** On two bits, a builder reading the first: the second bit does not count for it, and no rule of it builds for the second. After a change in what it reads the second bit counts, some rule builds for it, and a process that reads it is a remit for it. -/
theorem Composition.third_order_occurs :
    ¬ (Process.reading Prod.fst : Process (Bool × Bool)).Counts Set.univ (Prod.snd : Bool × Bool → Bool) ∧
      (¬ ∃ (B : Type) (r : (∀ i, (Process.reading Prod.fst : Process (Bool × Bool)).Value i) → B), Follows Set.univ ((Process.reading Prod.fst : Process (Bool × Bool)).withRule r).response (Prod.snd : Bool × Bool → Bool)) ∧
      (Process.reading Prod.snd : Process (Bool × Bool)).Counts Set.univ (Prod.snd : Bool × Bool → Bool) ∧
      (Process.reading Prod.snd : Process (Bool × Bool)).RemitFor (Prod.snd : Bool × Bool → Bool) := by
  have hnot : ¬ (Process.reading Prod.fst : Process (Bool × Bool)).Counts Set.univ (Prod.snd : Bool × Bool → Bool) := by
    rintro ⟨V, b, ⟨h, rfl⟩, hfix, s, -, t, -, -, hne⟩
    have key : ∀ a : Bool, ∀ c : Bool, (h ∘ (Process.reading Prod.fst : Process (Bool × Bool)).jointly) (a, c) = (h ∘ (Process.reading Prod.fst : Process (Bool × Bool)).jointly) (true, c) := fun a c =>
      hfix _ trivial _ trivial rfl
    have hindep : ∀ u v : Bool × Bool, (h ∘ (Process.reading Prod.fst : Process (Bool × Bool)).jointly) u = (h ∘ (Process.reading Prod.fst : Process (Bool × Bool)).jointly) v := by
      rintro ⟨a, c⟩ ⟨a', c'⟩
      have h1 : (h ∘ (Process.reading Prod.fst : Process (Bool × Bool)).jointly) (a, c) = (h ∘ (Process.reading Prod.fst : Process (Bool × Bool)).jointly) (a, c') := rfl
      exact h1.trans (key a c' |>.trans (key a' c').symm)
    exact hne (hindep s t)
  refine ⟨hnot, fun hex => hnot ((Composition.remit_for_what_counts _ _ _).mp hex), ⟨Bool, Prod.snd, ⟨fun v => v (), rfl⟩, fun _ _ _ _ e => e, (false, false), trivial, (false, true), trivial, by decide, by decide⟩, ⟨fun v => v (), rfl⟩⟩

/-! ## A remedy, and the distance -/

/-- **Claim 36 (The distance, bounded below), a remedy.** A remedy in the shape of `B`: a setting, before the remedy, with a relabelling onto `B`, a pair of its between, and one of the two routes for that pair. Nothing here says that the remedy has been applied anywhere, and the price route holds of every pair of every between. Either a change takes the pair out of the between, for a price. Or a position constituted to carry a quantity does not yet hold it, where a quantity separating the pair fixes it and it varies with that quantity: a rule would tie the two. -/
structure Remedy (B : Setting S' ι') : Type 1 where
  /-- The states of the setting it works in. -/
  States : Type
  /-- The positions of the setting it works in. -/
  Positions : Type
  /-- The setting it works in, before the remedy. -/
  source : Setting States Positions
  /-- It has the shape of `B`. -/
  shape : Relabelling source B
  /-- The pair it carries. -/
  pair : Sym2 States
  /-- That pair lies between the parties there. -/
  between : pair ∈ source.arrangement.between
  /-- A route: by a price, or by a tie. -/
  works : (∃ ch : Change States Positions, ch.before = source.arrangement ∧ pair ∉ ch.after.between) ∨
    ∃ (i : Positions) (Q L : Type) (q : States → Q) (l : States → L),
      (source.arrangement.process i).constitution ⊆ kernel l ∧ Fixes source.accessible q l ∧ VariesWith source.accessible l q ∧
        ¬ (source.arrangement.process i).Holds source.accessible l ∧ Separates q pair

/-- **Claim 36 (The distance, bounded below).** The pair a remedy would carry in `B`. -/
def Remedy.target {B : Setting S' ι'} (R : Remedy B) : Sym2 S' :=
  R.pair.map R.shape.states

/-- **Claim 36 (The distance, bounded below), the distance.** How far an arrangement is from what it could correct, in pairs: the size of its between, since each pair there can be carried at a price (`Composition.exact_in_kind`). -/
noncomputable def Setting.distance (B : Setting S' ι') : ℕ :=
  B.arrangement.residue

/-- **Claim 36 (The distance, bounded below), a tie carries across.** Let a position be constituted to carry a quantity it does not hold, where another quantity fixes it and it varies with that one. Under a relabelling its match does not hold the image either, so the tie is not in place there, and a process with the match's constitution holds the image and follows the other's image. This is why such a remedy is available in kind, and it uses that a relabelling carries constitutions and what is held. -/
theorem Relabelling.tie_carried {A : Setting S ι} {B : Setting S' ι'} (r : Relabelling A B) (i : ι) {Q L : Type} (q : S → Q) (l : S → L)
    (hc : (A.arrangement.process i).constitution ⊆ kernel l) (hfix : Fixes A.accessible q l) (hvar : VariesWith A.accessible l q)
    (hnot : ¬ (A.arrangement.process i).Holds A.accessible l) :
    ¬ (B.arrangement.process (r.positions i)).Holds B.accessible (l ∘ r.states.symm) ∧
      ∃ p' : Process S', p'.constitution = (B.arrangement.process (r.positions i)).constitution ∧ p'.Holds B.accessible (l ∘ r.states.symm) ∧
        Follows B.accessible p'.response (q ∘ r.states.symm) := by
  refine ⟨fun h => hnot ((r.held i l).mpr h), ?_⟩
  obtain ⟨b, -⟩ := B.nonempty
  have : Nonempty S' := ⟨b⟩
  have hsub : (B.arrangement.process (r.positions i)).constitution ⊆ kernel fun s => id ((l ∘ r.states.symm) s) := by
    intro z hz
    induction z with
    | _ u v =>
      have hin : s(r.states.symm u, r.states.symm v) ∈ (A.arrangement.process i).constitution := by
        refine (r.constitution i _).mpr ?_
        simpa using hz
      exact (mem_kernel _ u v).mpr ((mem_kernel l _ _).mp (hc hin))
  obtain ⟨f, hf⟩ := (exists_takeUp_iff (B.arrangement.process (r.positions i)) (l ∘ r.states.symm) id).mpr hsub
  let p' : Process S' := ((B.arrangement.process (r.positions i)).takeUp f).withRule fun v => v none
  have hresp : ∀ s, p'.response s = (l ∘ r.states.symm) s := hf
  have hacc : ∀ u ∈ B.accessible, r.states.symm u ∈ A.accessible := fun u hu => (r.accessible _).mpr (by simpa using hu)
  obtain ⟨s, hs, t, ht, hq, hl⟩ := hvar
  have hs' : r.states s ∈ B.accessible := (r.accessible s).mp hs
  have ht' : r.states t ∈ B.accessible := (r.accessible t).mp ht
  have hl0 : (l ∘ r.states.symm) (r.states s) ≠ (l ∘ r.states.symm) (r.states t) := by
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact hl
  have hq0 : (q ∘ r.states.symm) (r.states s) ≠ (q ∘ r.states.symm) (r.states t) := by
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact hq
  have hl' : p'.response (r.states s) ≠ p'.response (r.states t) := fun h => hl0 ((hresp _).symm.trans (h.trans (hresp _)))
  refine ⟨p', rfl, ⟨⟨fun v => v none, funext fun u => (hresp u).symm⟩, fun u _ v _ h => ?_, _, hs', _, ht', hl0, hl'⟩, fun u hu v hv h => ?_, _, hs', _, ht', hq0, hl'⟩
  · rw [hresp, hresp]
    exact h
  · rw [hresp, hresp]
    exact hfix _ (hacc u hu) _ (hacc v hv) h

/-- **Claim 36 (The distance, bounded below), a remedy is available.** The pair a remedy carries lies between the parties of `B`, so it has not been carried there at a price. At every position some change takes it out, for that price. -/
theorem Composition.remedy_carried {B : Setting S' ι'} (R : Remedy B) :
    R.target ∈ B.arrangement.between ∧
      ∀ i : ι', ∃ ch : Change S' ι', ch.before = B.arrangement ∧ R.target ∈ ch.price i ∧ R.target ∉ ch.after.between := by
  have ht : R.target ∈ B.arrangement.between := (R.shape.mem_between_iff R.pair).mp R.between
  refine ⟨ht, fun i => ?_⟩
  obtain ⟨ch, h1, -, h3, h4, -⟩ := (Composition.exact_in_kind B.arrangement ht).2.2.2 i B.accessible
  exact ⟨ch, h1, h3, h4⟩

/-- **Claim 36 (The distance, bounded below).** However many remedies lie in the shape of `B`, the pairs they would carry there are no more than `B`'s distance. The bound is in distinct pairs, since two remedies can carry one pair. -/
theorem Composition.distance_bounded_below [Fintype S'] (B : Setting S' ι') (Rs : Set (Remedy B)) :
    (Remedy.target '' Rs).ncard ≤ B.distance := by
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨R, -, rfl⟩
  exact (Composition.remedy_carried R).1

/-- **Claim 36 (The distance, bounded below), the bound is met.** The remedies a setting has at its own shape, one for each pair of its between, reach its distance. So a pair of a between is all a remedy's price route asks. -/
theorem Composition.distance_attained [Fintype S'] [Nonempty ι'] (B : Setting S' ι') :
    ∃ Rs : Set (Remedy B), (Remedy.target '' Rs).ncard = B.distance := by
  classical
  let make : {z // z ∈ B.arrangement.between} → Remedy B := fun z =>
    { States := S'
      Positions := ι'
      source := B
      shape := Relabelling.refl B
      pair := z.1
      between := z.2
      works := by
        obtain ⟨ch, h1, -, -, h4, -⟩ := (Composition.exact_in_kind B.arrangement z.2).2.2.2 (Classical.arbitrary ι') B.accessible
        exact Or.inl ⟨ch, h1, h4⟩ }
  refine ⟨Set.range make, ?_⟩
  have himage : Remedy.target '' Set.range make = B.arrangement.between := by
    ext y
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact (Composition.remedy_carried (make z)).1
    · intro hy
      refine ⟨make ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, ?_⟩
      change Sym2.map (Equiv.refl S') y = y
      simp
  rw [himage]
  rfl

/-! ## What it forbids -/

/-- **Claim 37 (What it forbids), its first sentence.** Where everything a process's coarse-grainings carry takes one value across the accessible states, its response follows nothing there. So a response cannot follow a difference through nothing its process registers. -/
theorem Response.no_channel (p : Process S) (X : Accessible S) (hnone : ∀ (V : Type) (b : S → V), p.Carries b → ∀ s ∈ X, ∀ t ∈ X, b s = b t) {Q : Type} (q : S → Q) :
    ¬ Follows X p.response q := by
  rintro ⟨-, s, hs, t, ht, -, ha⟩
  exact ha (hnone _ p.response (Law.factorization p) s hs t ht)

/-- **Claim 37 (What it forbids), its second sentence.** Under the premise no keeping is kept at every step of a course that runs it with no deciding process holding its lapse. This is `Persistence.lapse` read as a prohibition, and the premise carries it. -/
theorem Persistence.forbids (K : Keeping A) (X : Accessible S) (x : Course S) (hrun : K.Runs x) (hp : K.Premise X x) :
    ¬ ((∀ t, K.kept (x t)) ∧ ¬ K.LapseHeld X) :=
  fun h => h.2 (Persistence.lapse K X x hrun hp h.1)

/-- **Claim 37 (What it forbids), at one step.** Along a course that runs it, where the deciding responses at a step are those of a state at which the
decision does not keep it, it is not kept at the next step, whether or not that state is one at which it is kept. A finite record can show such a
step, as it cannot show being kept at every step. -/
theorem Persistence.forbids_at_step (K : Upkeep A) (x : Course S) (hrun : K.Runs x) (t : ℕ) (s : S) (hcut : ¬ K.decision s)
    (hresp : ∀ i ∈ K.deciding, (A.process i).response (x t) = (A.process i).response s) : ¬ K.kept (x (t + 1)) :=
  fun hk => hcut ((K.decision_iff hresp).mp ((hrun t).mp hk).2)

/-! ## Coordination -/

/-- **Claim 42 (Coordination across the between).** What is composed from the responses by one function, where it takes two values across the accessible states, is held by the composite. The composite registers what the processes do together. No process changed. -/
theorem Composition.coordination (A : Arrangement S ι) {D : Type} (h : (∀ i, (A.process i).Action) → D) (X : Accessible S)
    (hv : ∃ s ∈ X, ∃ t ∈ X, (A.composite h).response s ≠ (A.composite h).response t) : (A.composite h).Holds X (A.composite h).response := by
  obtain ⟨s, hs, t, ht, hne⟩ := hv
  exact ⟨Law.factorization _, fun _ _ _ _ e => e, s, hs, t, ht, hne, hne⟩

/-- A process reading the first of three bits, and one reading the second. -/
def twoReaders : Arrangement Three Bool :=
  readers fun b s => cond b s.1 s.2.1

/-- **Claim 42 (Coordination across the between), it occurs, and where it stops.** On three bits, two processes each read one of the first two. Whether those two differ is carried by neither, and neither holds it under any rule. The composite holds it. A pair that differs only in the third lies between them, and no function of their responses separates it: coordination reaches what no single process supplies, and what lies between stays until someone pays for it. -/
theorem Composition.coordination_occurs :
    let differ : (∀ i, (twoReaders.process i).Action) → Bool := fun r => xor (r false) (r true)
    (∀ i, ¬ (twoReaders.process i).Carries (twoReaders.composite differ).response) ∧
      (twoReaders.composite differ).Holds Set.univ (twoReaders.composite differ).response ∧
      s(((false, false, false) : Three), (false, false, true)) ∈ twoReaders.between ∧
      ¬ Separates (twoReaders.composite differ).response s(((false, false, false) : Three), (false, false, true)) := by
  intro differ
  have hz : s(((false, false, false) : Three), (false, false, true)) ∈ twoReaders.between :=
    ⟨by simp [Sym2.mk_isDiag_iff], fun _ => (mem_kernel _ _ _).mpr rfl⟩
  refine ⟨fun i ⟨h, hh⟩ => ?_, Composition.coordination _ _ _ ⟨(false, false, false), trivial, (true, false, false), trivial, fun he => Bool.false_ne_true he⟩, hz, fun hs => hs ((mem_kernel _ _ _).mpr rfl)⟩
  cases i
  · have hj : (twoReaders.process false).jointly (false, false, false) = (twoReaders.process false).jointly (true, false, false) := rfl
    have he : (twoReaders.composite differ).response (false, false, false) = (twoReaders.composite differ).response (true, false, false) :=
      (congrFun hh _).trans ((congrArg h hj).trans (congrFun hh _).symm)
    exact Bool.false_ne_true he
  · have hj : (twoReaders.process true).jointly (false, false, false) = (twoReaders.process true).jointly (false, true, false) := rfl
    have he : (twoReaders.composite differ).response (false, false, false) = (twoReaders.composite differ).response (false, true, false) :=
      (congrFun hh _).trans ((congrArg h hj).trans (congrFun hh _).symm)
    exact Bool.false_ne_true he

end Companion
