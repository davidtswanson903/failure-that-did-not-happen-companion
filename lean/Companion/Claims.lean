import Companion.AtCuts

/-!
# What the claims add

Each theorem here states one thing a claim of the book says, in the claim's own quantifiers, where a citation of the earlier theorems would say less. Most are a few lines on those theorems.
-/

namespace Companion

variable {S S' ι ι' : Type}

/-! ## Composition -/

/-- **Claim 1 (Inherited, not emergent).** What is composed from an arrangement's processes by a function `h` of their responses, as a process: it is constituted to make their joint coarse-graining, and it responds with `h`. -/
def Arrangement.composite (A : Arrangement S ι) {D : Type} (h : (∀ i, (A.process i).Action) → D) : Process S :=
  A.asProcess.withRule fun v => h (A.asProcess.rule v)

/-- **Claim 1 (Inherited, not emergent).** A response composed from the responses of an arrangement's processes, by any function of them, is itself the response of a process, constituted to make their joint coarse-graining. So a limit that holds of every process holds of it. -/
theorem Composition.inherited (A : Arrangement S ι) {D : Type} (h : (∀ i, (A.process i).Action) → D) (limit : Process S → Prop)
    (hlimit : ∀ p, limit p) :
    limit (A.composite h) ∧ (A.composite h).constitution = A.asProcess.constitution ∧
      (A.composite h).response = fun s => h fun i => (A.process i).response s :=
  ⟨hlimit _, rfl, rfl⟩

/-! ## The condition, and what follows from it -/

/-- **Claim 2 (The condition of response).** In every situation a response is a function of the value of the coarse-graining its process is constituted to make, read at the state that obtains. -/
theorem Response.condition (p : Process S) :
    ∃ h : p.constitutive.Value → p.Action, ∀ w : Situation S, evaluate p.response w = h (evaluate p.constitutive.map w) :=
  ⟨fun v => p.rule fun i => p.further i v, fun _ => rfl⟩

/-- **Claim 4 (No recovery).** Along a chain, no later step and no map of a later step's values separates a pair an earlier step identified. -/
theorem Regress.no_recovery (ch : Chain S) {m n : ℕ} (hmn : m ≤ n) {D : Type} (g : ch.Value n → D) :
    kernel (ch.map m) ⊆ kernel (g ∘ ch.map n) :=
  fun _ hz => kernel_subset_comp _ g (chain_kernel_monotone ch hmn hz)

/-- **Claim 4 (No recovery), describing more carefully.** A further map that keeps every value apart has the kernel of what it describes, so the finest description of a description tells apart what that description told apart and no more. -/
theorem Regress.careful {C D : Type} (c : S → C) (g : C → D) (hg : Function.Injective g) : kernel (g ∘ c) = kernel c := by
  ext z
  induction z with
  | _ s t => simp [mem_kernel, hg.eq_iff]

/-- **Claim 5 (The non-event), holding.** A process holds a quantity of situations when its coarse-grainings carry the quantity, as `CarriesOfSituation` reads carrying, and its response, read at the state that obtains, follows it across a set of situations. -/
def Process.HoldsOfSituation {Q : Type} (p : Process S) (W : Set (Situation S)) (F : Situation S → Q) : Prop :=
  CarriesOfSituation p.jointly F ∧ Follows W (evaluate p.response) F

/-- **Claim 5 (The non-event), holding.** On a quantity of the state that obtains, holding across the situations whose state is accessible is holding across the accessible states. -/
theorem Process.holdsOfSituation_iff {Q : Type} (p : Process S) (X : Accessible S) (q : S → Q) :
    p.HoldsOfSituation {w | w.obtains ∈ X} (fun w => q w.obtains) ↔ p.Holds X q := by
  constructor
  · rintro ⟨⟨h, hh⟩, hfix, w, hw, w', hw', hq, ha⟩
    exact ⟨⟨h, funext fun s => hh ⟨s, s⟩⟩, fun s hs t ht hst => hfix ⟨s, s⟩ hs ⟨t, t⟩ ht hst, w.obtains, hw, w'.obtains, hw', hq, ha⟩
  · rintro ⟨⟨h, hh⟩, hfix, s, hs, t, ht, hq, ha⟩
    refine ⟨⟨h, fun w => congrFun hh w.obtains⟩, fun w hw w' hw' hww => hfix _ hw _ hw' hww, ⟨s, s⟩, hs, ⟨t, t⟩, ht, hq, ha⟩

/-- **Claim 5 (The non-event).** No process holds a quantity that depends on a forestalled state, across any set of situations. -/
theorem Response.holds_nothing_forestalled {Q : Type} (p : Process S) (W : Set (Situation S)) {F : Situation S → Q}
    (hF : DependsOnForestalled F) : ¬ p.HoldsOfSituation W F :=
  fun h => Response.nonevent.1 _ F hF h.1

/-- **Claim 5 (The non-event), what stays open to a response.** A response can follow what would have obtained across a set of situations in which that moves with what obtains, and still no process holds it: this is what Claim 6 (Borrowing) leaves. -/
theorem Response.prevented_followed_not_held :
    DependsOnForestalled (Situation.wouldHave : Situation (Fin 3) → Fin 3) ∧
      ∃ (p : Process (Fin 3)) (W : Set (Situation (Fin 3))),
        Follows W (evaluate p.response) (Situation.wouldHave : Situation (Fin 3) → Fin 3) ∧
          ¬ p.HoldsOfSituation W (Situation.wouldHave : Situation (Fin 3) → Fin 3) := by
  have hdep : DependsOnForestalled (Situation.wouldHave : Situation (Fin 3) → Fin 3) :=
    ⟨⟨0, 1⟩, ⟨0, 2⟩, show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, rfl, show (1 : Fin 3) ≠ 2 by decide⟩
  refine ⟨hdep, Process.reading id, {⟨0, 1⟩, ⟨1, 2⟩}, ⟨?_, ?_⟩, Response.holds_nothing_forestalled _ _ hdep⟩
  · rintro w (rfl | rfl) w' (rfl | rfl) h
    · rfl
    · exact absurd (show (1 : Fin 3) = 2 from h) (by decide)
    · exact absurd (show (2 : Fin 3) = 1 from h) (by decide)
    · rfl
  · exact ⟨⟨0, 1⟩, Or.inl rfl, ⟨1, 2⟩, Or.inr rfl, show (1 : Fin 3) ≠ 2 by decide, show (0 : Fin 3) ≠ 1 by decide⟩

/-- **Claim 7 (Designs that cannot run).** Where two accessible states have one value under what a process makes and two under a quantity, no rule on what it makes gives a response that tells apart across those states what the quantity tells apart. -/
theorem Response.design_cannot_run (p : Process S) (X : Accessible S) {Q : Type} (q : S → Q) {s t : S} (hs : s ∈ X) (ht : t ∈ X)
    (hG : p.jointly s = p.jointly t) (hq : q s ≠ q t) {A : Type} (r : (∀ i, p.Value i) → A) :
    ¬ ∀ u ∈ X, ∀ v ∈ X, q u ≠ q v → (p.withRule r).response u ≠ (p.withRule r).response v :=
  fun h => h s hs t ht hq (congrArg r hG)

/-- **Claim 7 (Designs that cannot run), what it can be.** Such a requirement can be stated wherever a process identifies two distinct states: their marker is a quantity it does not carry. -/
theorem Response.requirement_can_be_written (p : Process S) {s t : S} (hne : s ≠ t) (hG : p.jointly s = p.jointly t) :
    ∃ q : S → Prop, ¬ p.Carries q := by
  refine ⟨fun x => x = s, ?_⟩
  rintro ⟨h, hh⟩
  have hs : (s = s) = h (p.jointly s) := congrFun hh s
  have ht : (t = s) = h (p.jointly t) := congrFun hh t
  rw [hG, ← ht] at hs
  exact hne (Eq.mp hs rfl).symm

/-- **Claim 7 (Designs that cannot run), what it does in operation.** Under any rule, across any accessible states, a response takes one value, and so responds to nothing, or its process holds that response, a quantity it carries. -/
theorem Response.runs_on_what_it_keeps (p : Process S) {A : Type} (r : (∀ i, p.Value i) → A) (Y : Accessible S) :
    (∀ u ∈ Y, ∀ v ∈ Y, (p.withRule r).response u = (p.withRule r).response v) ∨ (p.withRule r).Holds Y (p.withRule r).response := by
  by_cases h : ∀ u ∈ Y, ∀ v ∈ Y, (p.withRule r).response u = (p.withRule r).response v
  · exact Or.inl h
  · push Not at h
    obtain ⟨u, hu, v, hv, hne⟩ := h
    exact Or.inr ⟨Law.factorization _, fun _ _ _ _ e => e, u, hu, v, hv, hne, hne⟩

/-- **Claim 8 (Not supplied from outside).** A process told more, that is, making one more map of its constitutive values under its old rule, keeps its constitution and its response, and so follows what it followed. -/
theorem Response.told {V : Type} (p : Process S) (f : p.constitutive.Value → V) :
    (p.takeUp f).constitution = p.constitution ∧ (p.takeUp f).response = p.response ∧
      ∀ (X : Accessible S) {Q : Type} (q : S → Q), Follows X (p.takeUp f).response q ↔ Follows X p.response q :=
  ⟨rfl, rfl, fun _ _ _ => Iff.rfl⟩

/-- **Claim 8 (Not supplied from outside), what it can change.** Telling a process more can change what it holds, though neither its constitution nor its response moves, because holding asks that what it makes carry the quantity: what it followed by borrowing it then holds. -/
theorem Response.told_can_change_holding :
    ¬ tellsBothMakesFirst.Holds {s | s.1 = s.2} (Prod.snd : Bool × Bool → Bool) ∧
      (tellsBothMakesFirst.takeUp (Prod.snd : Bool × Bool → Bool)).Holds {s | s.1 = s.2} (Prod.snd : Bool × Bool → Bool) :=
  ⟨fun h => reading_keeps_a_borrowing.1 h.1, ⟨fun v => v none, rfl⟩, reading_keeps_a_borrowing.2.1⟩

/-- **Claim 8 (Not supplied from outside), once the rule uses it.** With a rule that uses what it is told, a process with the same constitution comes to follow what it did not. So the response stays only while the rule does. -/
theorem Response.told_and_acting_follows :
    (tellsBothMakesFirst.takeUp (Prod.snd : Bool × Bool → Bool)).constitution = tellsBothMakesFirst.constitution ∧
      ¬ Follows Set.univ tellsBothMakesFirst.response (Prod.snd : Bool × Bool → Bool) ∧
      Follows Set.univ ((tellsBothMakesFirst.takeUp (Prod.snd : Bool × Bool → Bool)).withRule fun v => v none).response (Prod.snd : Bool × Bool → Bool) := by
  refine ⟨rfl, fun hf => ?_, ⟨fun u _ v _ h => h, ⟨(false, false), trivial, (false, true), trivial, Bool.false_ne_true, Bool.false_ne_true⟩⟩⟩
  have : (false : Bool) = true := hf.1 (false, false) trivial (true, false) trivial rfl
  exact Bool.false_ne_true this

/-- **Claim 8 (Not supplied from outside), which losses can reach it.** Whatever a process holds once it makes one more map of its constitutive
values, the coarse-graining it is constituted to make already carries: telling it more adds no loss that can reach it. -/
theorem Response.told_holds_within {V : Type} (p : Process S) (f : p.constitutive.Value → V) (X : Accessible S) {Q : Type} (q : S → Q)
    (h : (p.takeUp f).Holds X q) : Carries p.constitutive q := by
  obtain ⟨g, hg⟩ := h.1
  exact ⟨fun v => g fun i => (p.takeUp f).further i v, hg⟩

/-! ## The between -/

/-- **Claim 9 (The between), when there is one.** An arrangement's between holds a pair exactly when its processes' constitutive maps, read together, do not tell every two states apart. -/
theorem between_nonempty_iff (A : Arrangement S ι) : A.between.Nonempty ↔ ¬ Function.Injective A.asProcess.constitutive.map := by
  constructor
  · rintro ⟨z, hd, hall⟩ hinj
    induction z with
    | _ s t =>
      have hin : s(s, t) ∈ A.asProcess.constitution := (mem_constitution_asProcess A _).mpr hall
      exact hd (Sym2.mk_isDiag_iff.mpr (hinj ((mem_kernel _ s t).mp hin)))
  · intro hnot
    obtain ⟨s, t, heq, hne⟩ : ∃ s t, A.asProcess.constitutive.map s = A.asProcess.constitutive.map t ∧ s ≠ t := by
      simpa [Function.Injective] using hnot
    exact ⟨s(s, t), by simpa [Sym2.mk_isDiag_iff] using hne, (mem_constitution_asProcess A _).mp ((mem_kernel _ s t).mpr heq)⟩

/-- **Claim 35 (Exact in kind), the limit is exact.** A pair of distinct states lies in the between exactly when no function of the processes' constitutive values separates it. -/
theorem between_exact (A : Arrangement S ι) {z : Sym2 S} (hz : ¬ z.IsDiag) :
    z ∈ A.between ↔ ∀ (D : Type) (h : (∀ i, (A.process i).constitutive.Value) → D), z ∈ kernel fun s => h fun i => (A.process i).constitutive.map s := by
  constructor
  · intro hin D h
    exact Composition.nesting (fun i => (A.process i).constitutive.map) h (Set.mem_iInter.mpr hin.2)
  · intro h
    exact ⟨hz, (mem_constitution_asProcess A z).mp (h _ id)⟩

/-- **Claim 11 (Change by refinement).** A pair of the between leaves it exactly when some process comes to tell it apart. -/
theorem Composition.leaves_iff (ch : Change S ι) {z : Sym2 S} (hz : z ∈ ch.before.between) :
    z ∉ ch.after.between ↔ ∃ i, z ∈ ch.price i :=
  ⟨fun h => Composition.payer ch z ⟨hz, h⟩, fun ⟨i, _, hout⟩ hin => hout (hin.2 i)⟩

/-- **Claim 12 (Change by attachment), tying to what is held.** What fixes a quantity a process holds drives that process's response: where a process holds a quantity and another quantity fixes it, across the accessible states, the response follows the other. -/
theorem Composition.tied_to_held {Q L : Type} (p : Process S) (X : Accessible S) (q : S → Q) (l : S → L) (hl : p.Holds X l) (hfix : Fixes X q l) :
    Follows X p.response q := by
  obtain ⟨-, hfl, s, hs, t, ht, hne, ha⟩ := hl
  exact ⟨fun u hu v hv huv => hfl u hu v hv (hfix u hu v hv huv), s, hs, t, ht, fun e => hne (hfix s hs t ht e), ha⟩

/-- **Claim 12 (Change by attachment), after the change.** The rule that gives a carried quantity makes the process hold it, wherever that quantity varies with anything across the accessible states. -/
theorem Composition.attached_holds {V Q : Type} (p : Process S) (X : Accessible S) (h : (∀ i, p.Value i) → V) (q : S → Q)
    (hvar : VariesWith X (h ∘ p.jointly) q) : (p.withRule h).Holds X (h ∘ p.jointly) := by
  obtain ⟨s, hs, t, ht, -, ha⟩ := hvar
  exact ⟨⟨h, rfl⟩, fun _ _ _ _ e => e, s, hs, t, ht, ha, ha⟩

/-- **Claim 12 (Change by attachment), what a party lumps together.** The states a process lumps together with some state of `N`: those at which its
coarse-grainings, read together, take the values they take at one of `N`. -/
def Process.lumpedWith (p : Process S) (N : Set S) : Set S :=
  {t | ∃ s ∈ N, p.jointly s = p.jointly t}

/-- **Claim 12 (Change by attachment), an act over the whole of what the party lumps together.** Give a process any rule that acts at every state of a
need `N`. Then it acts at every accessible state the process lumps together with one of `N`, so its act where it was not needed takes in every such state
outside `N`. The rule that acts where the process's values are those at some state of `N` meets the need, and its act where it was not needed is exactly
those states. -/
theorem Composition.act_over_lumped (p : Process S) (X : Accessible S) (N : Set S) :
    (∀ h : (∀ i, p.Value i) → Prop, (∀ s ∈ N, (p.withRule h).response s) →
      (p.lumpedWith N ∩ X) \ N ⊆ {t | t ∈ X ∧ (p.withRule h).response t} \ N) ∧
    (∀ s ∈ N, (p.withRule fun v => ∃ s ∈ N, p.jointly s = v).response s) ∧
    {t | t ∈ X ∧ (p.withRule fun v => ∃ s ∈ N, p.jointly s = v).response t} \ N = (p.lumpedWith N ∩ X) \ N := by
  refine ⟨fun h hN t ht => ?_, fun s hs => show ∃ s' ∈ N, p.jointly s' = p.jointly s from ⟨s, hs, rfl⟩, ?_⟩
  · obtain ⟨⟨⟨s, hs, hst⟩, htX⟩, htN⟩ := ht
    refine ⟨⟨htX, ?_⟩, htN⟩
    show h (p.jointly t)
    rw [← hst]
    exact hN s hs
  · ext t
    exact ⟨fun ⟨⟨htX, hlump⟩, htN⟩ => ⟨⟨hlump, htX⟩, htN⟩, fun ⟨⟨hlump, htX⟩, htN⟩ => ⟨⟨htX, hlump⟩, htN⟩⟩

/-- **Claim 12 (Change by attachment), its cost where a difference lies between.** Where a pair of the between has one state in a need and the other
accessible and outside it, every position lumps the two together. So at every position, an act that meets the need is taken at the second state, where it
was not needed. -/
theorem Composition.cost_of_between (A : Arrangement S ι) (X : Accessible S) (N : Set S) {s t : S} (hz : s(s, t) ∈ A.between)
    (hs : s ∈ N) (ht : t ∈ X) (htN : t ∉ N) (i : ι) : t ∈ ((A.process i).lumpedWith N ∩ X) \ N :=
  ⟨⟨⟨s, hs, (mem_kernel _ s t).1 (mem_kernel_jointly fun k => mem_grainings_of_mem_constitution (hz.2 i) k)⟩, ht⟩, htN⟩

/-- **Claim 12 (Change by attachment), the cost occurs.** On two bits, where the second can be set only where the first is, a process reads the first.
Where the need is the states with the second bit set, the act that meets it is taken at the state with only the first set, where it was not needed. -/
theorem cost_occurs :
    (true, false) ∈ ((Process.reading (Prod.fst : Bool × Bool → Bool)).lumpedWith {s | s.2 = true} ∩ {s | s.2 = true → s.1 = true}) \
      {s | s.2 = true} :=
  ⟨⟨⟨(true, true), rfl, rfl⟩, fun _ => rfl⟩, Bool.false_ne_true⟩

/-- **Claim 14 (What is kept), what a response following a between's difference comes to.** Take a pair of the between before a change, a quantity separating it, and a response after the change that follows the quantity. Either the pair has left the between, and some position paid for it. Or it is still there, and then that process does not carry the quantity and follows it through a carried quantity the quantity fixes. So such a response follows only by a price or by borrowing. -/
theorem Composition.routes (ch : Change S ι) {z : Sym2 S} (hz : z ∈ ch.before.between) {Q : Type} (q : S → Q) (hq : Separates q z) (i : ι) (X : Accessible S)
    (hf : Follows X (ch.after.process i).response q) :
    (z ∉ ch.after.between ∧ ∃ j, z ∈ ch.price j) ∨
      (z ∈ ch.after.between ∧ ¬ (ch.after.process i).Carries q ∧
        ∃ (V : Type) (b : S → V), (ch.after.process i).Carries b ∧ Carries b (ch.after.process i).response ∧ Fixes X q b ∧ VariesWith X b q ∧ ¬ Carries b q) := by
  by_cases h : z ∈ ch.after.between
  · have hnot := not_carries_of_separates ch.after i ⟨z, h, hq⟩
    exact Or.inr ⟨h, hnot, Response.borrowing _ X q hnot hf⟩
  · exact Or.inl ⟨h, Composition.payer ch z ⟨hz, h⟩⟩

/-! ## What is kept -/

/-- **Claim 14 (What is kept).** Let a response tell apart, across the accessible states, whatever a quantity tells apart there, and let a change of the world bring in two states whose difference lies between the processes and that the quantity separates. Those two were not both accessible before; the change moves nothing the arrangement registers; and under every rule, the position no longer tells apart across the new states what the quantity tells apart. -/
theorem Composition.kept_and_lost (A : Arrangement S ι) (X X' : Accessible S) {Q : Type} (q : S → Q) (i : ι)
    (hhad : ∀ u ∈ X, ∀ v ∈ X, q u ≠ q v → (A.process i).response u ≠ (A.process i).response v) {s t : S} (hs : s ∈ X') (ht : t ∈ X')
    (hz : s(s, t) ∈ A.between) (hq : q s ≠ q t) :
    ¬ (s ∈ X ∧ t ∈ X) ∧
      (let ch : Change S ι := ⟨A, A, X, X', Or.inr rfl⟩
       ch.after.between = ch.before.between ∧ (∀ j, ch.price j = ∅) ∧ ∀ j, ch.release j = ∅) ∧
      ∀ {B : Type} (r : (∀ k, (A.process i).Value k) → B),
        ¬ ∀ u ∈ X', ∀ v ∈ X', q u ≠ q v → ((A.process i).withRule r).response u ≠ ((A.process i).withRule r).response v := by
  have hG : (A.process i).jointly s = (A.process i).jointly t :=
    funext fun k => (mem_kernel _ s t).mp (mem_grainings_of_mem_constitution (hz.2 i) k)
  refine ⟨fun hin => hhad s hin.1 t hin.2 hq (congrArg (A.process i).rule hG), change_of_world_keeps_between ⟨A, A, X, X', Or.inr rfl⟩ rfl, fun r => ?_⟩
  exact Response.design_cannot_run (A.process i) X' q hs ht hG hq r

/-- **Claim 14 (What is kept), following can be lost too.** On two bits, a process reads the first and responds with it. Across the states where the bits agree its response tells apart what the second bit tells apart, and follows the second bit, which it does not carry. A change of the world, to all the states, leaves the arrangement, and under no rule does a response of that process follow the second bit. -/
theorem Composition.kept_and_lost_occurs :
    ∃ ch : Change (Bool × Bool) Unit,
      ch.before = ch.after ∧ ¬ (ch.before.process ()).Carries (Prod.snd : Bool × Bool → Bool) ∧
        (∀ u ∈ ch.accessibleBefore, ∀ v ∈ ch.accessibleBefore, u.2 ≠ v.2 → (ch.before.process ()).response u ≠ (ch.before.process ()).response v) ∧
        Follows ch.accessibleBefore (ch.before.process ()).response (Prod.snd : Bool × Bool → Bool) ∧
          ∀ {B : Type} (r : (∀ k, (ch.after.process ()).Value k) → B),
            ¬ Follows ch.accessibleAfter ((ch.after.process ()).withRule r).response (Prod.snd : Bool × Bool → Bool) := by
  let A : Arrangement (Bool × Bool) Unit := ⟨inferInstance, fun _ => Process.reading Prod.fst, ∅⟩
  refine ⟨⟨A, A, {s | s.1 = s.2}, Set.univ, Or.inr rfl⟩, rfl, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨h, hh⟩
    have h0 : (false : Bool) = h ((Process.reading Prod.fst : Process (Bool × Bool)).jointly (false, false)) := congrFun hh (false, false)
    have h1 : (true : Bool) = h ((Process.reading Prod.fst : Process (Bool × Bool)).jointly (false, true)) := congrFun hh (false, true)
    exact Bool.false_ne_true (h0.trans h1.symm)
  · rintro u hu v hv huv heq
    have hu' : u.1 = u.2 := hu
    have hv' : v.1 = v.2 := hv
    have hsame : u.1 = v.1 := heq
    exact huv (hu'.symm.trans (hsame.trans hv'))
  · rintro u hu v hv huv
    have hu' : u.1 = u.2 := hu
    have hv' : v.1 = v.2 := hv
    have huv' : u.2 = v.2 := huv
    exact hu'.trans (huv'.trans hv'.symm)
  · exact ⟨(false, false), rfl, (true, true), rfl, Bool.false_ne_true, Bool.false_ne_true⟩
  · intro B r
    rintro ⟨hfix, s, -, t, -, -, ha⟩
    have h : ((A.process ()).withRule r).response (false, false) = ((A.process ()).withRule r).response (true, false) := hfix _ trivial _ trivial rfl
    rcases s with ⟨a, _⟩
    rcases t with ⟨c, _⟩
    cases a <;> cases c
    · exact ha rfl
    · exact ha h
    · exact ha h.symm
    · exact ha rfl

/-- **Claim 16 (Drift has a direction).** Where no position pays, the between cannot shrink. -/
theorem Composition.drift (ch : Change S ι) (h : ∀ i, ch.price i = ∅) : ch.before.between ⊆ ch.after.between := by
  intro z hz
  by_contra hout
  obtain ⟨i, hi⟩ := Composition.payer ch z ⟨hz, hout⟩
  rw [h i] at hi
  exact hi

/-- **Claim 16 (Drift has a direction), it can grow.** On two states, a process that tells them apart comes to tell nothing apart: nothing is paid, and the between grows. -/
theorem Composition.drift_can_grow :
    ∃ ch : Change Bool Unit, (∀ i, ch.price i = ∅) ∧ ch.after.between ≠ ch.before.between := by
  let A : Arrangement Bool Unit := ⟨inferInstance, fun _ => Process.reading id, ∅⟩
  let A' : Arrangement Bool Unit := ⟨inferInstance, fun _ => Process.blank, ∅⟩
  refine ⟨⟨A, A', Set.univ, Set.univ, Or.inl rfl⟩, fun i => ?_, fun heq => ?_⟩
  · ext z
    constructor
    · rintro ⟨-, hout⟩
      exact absurd (mem_constitution_blank z) hout
    · exact fun h => absurd h (Set.notMem_empty _)
  · have hin : (s(false, true) : Sym2 Bool) ∈ A'.between :=
      ⟨by simp [Sym2.mk_isDiag_iff], fun _ => mem_constitution_blank _⟩
    have hin' : (s(false, true) : Sym2 Bool) ∈ A.between := heq ▸ hin
    exact Bool.false_ne_true ((mem_kernel id false true).mp (hin'.2 ()))

/-- **Claim 17 (Every level, every join).** What every process at a deeper level identifies, every process at a shallower level built from it identifies, and no response there separates. A level is built from the one below when each of its positions is an arrangement standing as the process there, no finer than its members together. -/
theorem Composition.no_level_recovers {n : Nested S} {d e : ℕ} (hde : d ≤ e) (hn : ∀ k, d ≤ k → k < e → ∀ m, n.AtDepth k m → m.EachPositionComposed)
    {z : Sym2 S} (hz : z ∈ n.betweenAt e) :
    z ∈ n.betweenAt d ∧ ∀ m, n.AtDepth d m → ∀ p, m.HoldsProcess p → ¬ Separates p.response z := by
  have hd := Nested.betweenAt_subset_of_le hde hn hz
  exact ⟨hd, fun m hm p hp hsep => hsep (mem_response_of_mem_constitution (hd.2 m hm p hp))⟩

/-! ## Accounts -/

/-- **Claim 19 (What accounts of agents leave out).** An account, any function of what the processes are constituted to make, separates no pair of the between, and so carries no quantity that separates one. -/
theorem Composition.account (A : Arrangement S ι) {D : Type} (h : (∀ i, (A.process i).constitutive.Value) → D) {z : Sym2 S} (hz : z ∈ A.between)
    {Q : Type} {q : S → Q} (hq : Separates q z) :
    ¬ Separates (fun s => h fun i => (A.process i).constitutive.map s) z ∧ ¬ Carries (fun s => h fun i => (A.process i).constitutive.map s) q := by
  have hin : z ∈ kernel fun s => h fun i => (A.process i).constitutive.map s :=
    Composition.nesting (fun i => (A.process i).constitutive.map) h (Set.mem_iInter.mpr hz.2)
  exact ⟨fun hs => hs hin, fun hc => hq (kernel_subset_of_carries hc hin)⟩

/-- **Claim 19 (What accounts of agents leave out), complete for every party.** The account that keeps what every process is constituted to make carries each of those maps and each response. -/
theorem Composition.account_complete (A : Arrangement S ι) (i : ι) :
    Carries A.asProcess.constitutive.map (A.process i).constitutive.map ∧ Carries A.asProcess.constitutive.map (A.process i).response :=
  ⟨⟨fun v => v i, rfl⟩, ⟨fun v => (A.process i).rule fun k => (A.process i).further k (v i), rfl⟩⟩

/-! ## Joint prohibition -/

/-- **Claim 25 (Joint prohibition), each forbids little.** For any number of states from two up, there is an arrangement of that many processes, each forbidding one state, that never reaches an outcome none of them excludes. -/
theorem Composition.prohibition_little (n : ℕ) (hn : 2 ≤ n) :
    ∃ (F : ForbidAllow (Fin n) (Fin n)) (O : Outcome (Fin n)),
      (∀ i s, F.responseAt i s = Verdict.forbid ↔ s = i) ∧ (∀ i, ¬ Excludes (F.responseAt i) O) ∧ ¬ F.Reaches O := by
  let F : ForbidAllow (Fin n) (Fin n) :=
    { finite := inferInstance
      process := fun i => Process.reading fun s => decide (s = i)
      joins := ∅
      verdict := fun _ a => cond a Verdict.forbid Verdict.allow }
  have hF : ∀ i s, F.responseAt i s = Verdict.forbid ↔ s = i := by
    intro i s
    change cond (decide (s = i)) Verdict.forbid Verdict.allow = Verdict.forbid ↔ s = i
    by_cases h : s = i <;> simp [h]
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  refine ⟨F, Set.univ, hF, fun i hex => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_ne i
    exact hs ((hF i s).mp (hex s trivial))
  · rintro ⟨s, -, hnone⟩
    exact hnone s ((hF s s).mpr rfl)

/-- **Claim 25 (Joint prohibition), the outcome.** The states of size at least 100 are the states raising at least five concerns. -/
theorem mem_witnessOutcome_iff (s : WitnessState) : s ∈ witnessOutcome ↔ 5 ≤ raised s := by
  change 100 ≤ 10 + 20 * raised s ↔ _
  omega

/-! ## One shape -/

/-- **Claim 26 (One shape, named separately), a difference no responsible party registers.** A pair of an arrangement's between, separated by a quantity. Under every choice of rules no response separates it, no process carries the quantity, and no process holds it under any rule. -/
theorem Composition.one_shape (A : Arrangement S ι) {z : Sym2 S} (hz : z ∈ A.between) {Q : Type} (q : S → Q) (hq : Separates q z) :
    (∀ (σ : A.Rules) (i : ι), ¬ Separates ((A.withRules σ).process i).response z) ∧ (∀ i, ¬ (A.process i).Carries q) ∧
      ∀ (i : ι) (X : Accessible S) {B : Type} (r : (∀ k, (A.process i).Value k) → B), ¬ ((A.process i).withRule r).Holds X q := by
  have hcarry : ∀ i, ¬ (A.process i).Carries q := fun i => not_carries_of_separates A i ⟨z, hz, hq⟩
  exact ⟨fun σ i hsep => hsep (mem_response_of_mem_constitution (p := (A.withRules σ).process i) (hz.2 i)), hcarry, fun i _ _ _ h => hcarry i h.1⟩

/-- A pair is separated exactly when its image under a bijection is separated by the quantity read at the old names. -/
theorem separates_map_iff (π : S ≃ S') {Q : Type} (q : S → Q) (z : Sym2 S) : Separates (q ∘ π.symm) (z.map π) ↔ Separates q z :=
  not_congr (pairsCarried_kernel π q z).symm

/-- **Claim 26 (One shape, named separately), whatever the field calls it.** A relabelling carries the shape: a quantity separates a pair of one between exactly when that quantity, read at the old names, separates a pair of the other. -/
theorem Relabelling.shape_iff {A : Setting S ι} {B : Setting S' ι'} (r : Relabelling A B) {Q : Type} (q : S → Q) :
    (∃ z ∈ A.arrangement.between, Separates q z) ↔ ∃ z ∈ B.arrangement.between, Separates (q ∘ r.states.symm) z := by
  constructor
  · rintro ⟨z, hz, hs⟩
    exact ⟨z.map r.states, (r.mem_between_iff z).mp hz, (separates_map_iff r.states q z).mpr hs⟩
  · rintro ⟨z, hz, hs⟩
    rw [r.between_eq_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, hy, (separates_map_iff r.states q y).mp hs⟩

/-- A situation with its states renamed by a bijection. -/
def Situation.relabel (π : S ≃ S') (w : Situation S) : Situation S' :=
  ⟨π w.obtains, π w.wouldHave⟩

/-- **Claim 26 (One shape, named separately), the prevented failure.** Renaming the states carries a quantity that depends on a forestalled state to one that does. -/
theorem dependsOnForestalled_relabel (π : S ≃ S') {Q : Type} {F : Situation S → Q} (hF : DependsOnForestalled F) :
    DependsOnForestalled (F ∘ Situation.relabel π.symm) := by
  obtain ⟨⟨o, h⟩, ⟨o', h'⟩, hf, hf', ho, hne⟩ := hF
  obtain rfl : o = o' := ho
  refine ⟨⟨π o, π h⟩, ⟨π o, π h'⟩, fun e => hf (π.injective e), fun e => hf' (π.injective e), rfl, ?_⟩
  simpa [Situation.relabel] using hne

/-! ## Shared shape, and what a design fails on -/

/-- **Claim 29 (Shared shape, shared lessons).** Two settings of one content: a relabelling carries the between onto the between, with its size, carries what each process holds onto what its match holds, and carries the quantities that separate a pair of the between. -/
theorem Relabelling.shared_lessons {A : Setting S ι} {B : Setting S' ι'} (r : Relabelling A B) :
    B.arrangement.between = Sym2.map r.states '' A.arrangement.between ∧ B.arrangement.residue = A.arrangement.residue ∧
      (∀ (i : ι) {Q : Type} (q : S → Q), (A.arrangement.process i).Holds A.accessible q ↔
        (B.arrangement.process (r.positions i)).Holds B.accessible (q ∘ r.states.symm)) ∧
      ∀ {Q : Type} (q : S → Q), (∃ z ∈ A.arrangement.between, Separates q z) ↔ ∃ z ∈ B.arrangement.between, Separates (q ∘ r.states.symm) z := by
  refine ⟨r.between_eq_image, ?_, fun i _ q => r.held i q, fun q => r.shape_iff q⟩
  change B.arrangement.between.ncard = A.arrangement.between.ncard
  rw [r.between_eq_image, Set.ncard_image_of_injective _ (Sym2.map.injective r.states.injective)]

/-- **Claim 34 (A limit, not a problem), a response.** Some rule on what a process makes gives a response following a quantity across the accessible states exactly when that quantity fixes a carried quantity that varies with it there. -/
theorem Process.followable_iff (p : Process S) (X : Accessible S) {Q : Type} (q : S → Q) :
    (∃ (B : Type) (r : (∀ i, p.Value i) → B), Follows X (p.withRule r).response q) ↔
      ∃ (V : Type) (c : S → V), p.Carries c ∧ Fixes X q c ∧ VariesWith X c q := by
  constructor
  · rintro ⟨B, r, hf⟩
    exact ⟨B, _, ⟨r, rfl⟩, hf.1, hf.2⟩
  · rintro ⟨V, _, ⟨h, rfl⟩, hfix, hvar⟩
    exact ⟨V, h, hfix, hvar⟩

/-- **Claim 34 (A limit, not a problem), a holder.** Some rule on what a process makes has it hold a quantity across the accessible states exactly when what it makes carries the quantity and the quantity takes two values there. -/
theorem Process.holdable_iff (p : Process S) (X : Accessible S) {Q : Type} (q : S → Q) :
    (∃ (B : Type) (r : (∀ i, p.Value i) → B), (p.withRule r).Holds X q) ↔ p.Carries q ∧ ∃ s ∈ X, ∃ t ∈ X, q s ≠ q t := by
  constructor
  · rintro ⟨B, r, hc, -, s, hs, t, ht, hq, -⟩
    exact ⟨hc, s, hs, t, ht, hq⟩
  · rintro ⟨⟨h, rfl⟩, s, hs, t, ht, hq⟩
    exact ⟨Q, h, ⟨h, rfl⟩, fun _ _ _ _ e => e, s, hs, t, ht, hq, hq⟩

/-- **Claim 34 (A limit, not a problem), the criteria sort no more than two requirements.** On two bits, under no rule does the reading of the first bit tell apart what the identity tells apart, though some rule has it follow the identity, and some rule has the reading of the identity hold it. -/
theorem Response.tells_apart_beyond_both :
    (∀ {B : Type} (r : (∀ k, (Process.reading (Prod.fst : Bool × Bool → Bool)).Value k) → B),
      ¬ ∀ u ∈ (Set.univ : Accessible (Bool × Bool)), ∀ v ∈ (Set.univ : Accessible (Bool × Bool)), (id u : Bool × Bool) ≠ id v →
        ((Process.reading (Prod.fst : Bool × Bool → Bool)).withRule r).response u ≠ ((Process.reading (Prod.fst : Bool × Bool → Bool)).withRule r).response v) ∧
      (∃ (B : Type) (r : (∀ i, (Process.reading (Prod.fst : Bool × Bool → Bool)).Value i) → B),
        Follows Set.univ ((Process.reading (Prod.fst : Bool × Bool → Bool)).withRule r).response (id : Bool × Bool → Bool × Bool)) ∧
      ∃ (B : Type) (r : (∀ i, (Process.reading (id : Bool × Bool → Bool × Bool)).Value i) → B),
        ((Process.reading (id : Bool × Bool → Bool × Bool)).withRule r).Holds Set.univ (id : Bool × Bool → Bool × Bool) := by
  refine ⟨fun {B} r => ?_, ?_, ?_⟩
  · exact Response.design_cannot_run _ Set.univ id (s := (false, false)) (t := (false, true)) trivial trivial (funext fun _ => rfl) (by decide) r
  · exact (Process.followable_iff _ Set.univ id).mpr
      ⟨Bool, Prod.fst, ⟨fun v => v (), rfl⟩, fun u _ v _ h => congrArg Prod.fst h, (false, false), trivial, (true, false), trivial, by decide, Bool.false_ne_true⟩
  · exact (Process.holdable_iff _ Set.univ id).mpr ⟨⟨fun v => v (), rfl⟩, (false, false), trivial, (false, true), trivial, by decide⟩

/-- **Claim 35 (Exact in kind), rules do less.** A rule reads what a process makes, not all it is constituted to make. On two bits, a process constituted to read both and making the first leaves a pair outside the between that no response of it separates, under any rule. -/
theorem Response.rule_short_of_between :
    let A : Arrangement (Bool × Bool) Unit := ⟨inferInstance, fun _ => tellsBothMakesFirst, ∅⟩
    let z : Sym2 (Bool × Bool) := s((false, false), (false, true))
    ¬ z.IsDiag ∧ z ∉ A.between ∧ ∀ (i : Unit) {B : Type} (r : (∀ k, (A.process i).Value k) → B), ¬ Separates ((A.process i).withRule r).response z := by
  intro A z
  refine ⟨by simp [z, Sym2.mk_isDiag_iff], ?_, fun i B r hsep => ?_⟩
  · rintro ⟨-, hall⟩
    have h : ((false, false) : Bool × Bool) = (false, true) := (mem_kernel id _ _).mp (hall ())
    exact absurd h (by decide)
  · exact hsep ((mem_kernel _ _ _).mpr (congrArg r (funext fun _ => rfl)))

/-- **Claim 35 (Exact in kind).** For a pair of the between: every process misses it and no response separates it; each join stands on both sides of it; a change removes it exactly when some position pays for it; such a change exists at every position; and at each position attachment has its exact condition. -/
theorem Composition.exact_in_kind (A : Arrangement S ι) {z : Sym2 S} (hz : z ∈ A.between) :
    (∀ i, z ∈ (A.process i).constitution ∧ ¬ Separates (A.process i).response z) ∧
      (∀ j : Join A.process, z ∈ kernel ((A.process j.giver).grainings j.source) ∧ z ∈ kernel ((A.process j.taker).grainings j.made)) ∧
      (∀ ch : Change S ι, ch.before = A → (z ∉ ch.after.between ↔ ∃ i, z ∈ ch.price i)) ∧
      (∀ (i : ι) (X : Accessible S), ∃ ch : Change S ι, ch.before = A ∧ ch.accessibleAfter = X ∧ z ∈ ch.price i ∧ z ∉ ch.after.between ∧
        ∀ j, j ≠ i → ch.after.process j = A.process j) := by
  classical
  refine ⟨fun i => ⟨hz.2 i, fun hsep => hsep (mem_response_of_mem_constitution (hz.2 i))⟩,
    fun j => ⟨mem_grainings_of_mem_constitution (hz.2 _) _, mem_grainings_of_mem_constitution (hz.2 _) _⟩, ?_, fun i X => ?_⟩
  · rintro ch rfl
    exact Composition.leaves_iff ch hz
  · let A' : Arrangement S ι := ⟨A.finite, Function.update A.process i Process.discrete, ∅⟩
    have hi : A'.process i = Process.discrete := Function.update_self i _ A.process
    have hout : z ∉ (A'.process i).constitution := by
      rw [hi]
      exact not_mem_constitution_discrete hz.1
    exact ⟨⟨A, A', X, X, Or.inl rfl⟩, rfl, rfl, ⟨hz.2 i, hout⟩, fun hin => hout (hin.2 i), fun j hj => Function.update_of_ne hj _ A.process⟩

/-- **Claim 35 (Exact in kind), where a join falls.** The pairs a join falls at: those neither of the two processes it connects is constituted to tell
apart. -/
def Arrangement.betweenAt (A : Arrangement S ι) (j : Join A.process) : Set (Sym2 S) :=
  {z | ¬ z.IsDiag ∧ z ∈ (A.process j.giver).constitution ∧ z ∈ (A.process j.taker).constitution}

/-- **Claim 35 (Exact in kind), the two parties of a join.** The arrangement of a join's giver and taker alone, with the join between them. -/
def Arrangement.atJoin (A : Arrangement S ι) (j : Join A.process) : Arrangement S Bool where
  finite := inferInstance
  process := fun b => cond b (A.process j.taker) (A.process j.giver)
  joins := {⟨true, false, Bool.false_ne_true, j.source, j.made, j.further, j.made_eq⟩}

/-- **Claim 35 (Exact in kind), the join it falls at.** The two parties of a join have for their between exactly the pairs the join falls at, and a pair
of the whole arrangement's between falls at every join. -/
theorem Composition.at_join (A : Arrangement S ι) (j : Join A.process) :
    (A.atJoin j).between = A.betweenAt j ∧ A.between ⊆ A.betweenAt j := by
  refine ⟨Set.ext fun z => ⟨fun hz => ⟨hz.1, hz.2 false, hz.2 true⟩, fun hz => ⟨hz.1, fun b => ?_⟩⟩, fun z hz => ⟨hz.1, hz.2 _, hz.2 _⟩⟩
  cases b
  · exact hz.2.1
  · exact hz.2.2

/-- **Claim 35 (Exact in kind), at a join.** For a pair a join falls at, the claim holds of the join's two parties: both miss it and no response of theirs
separates it; the join stands on both sides of it; a change removes it exactly when one of the two pays for it; and such a change exists at
either. -/
theorem Composition.exact_at_join (A : Arrangement S ι) (j : Join A.process) {z : Sym2 S} (hz : z ∈ A.betweenAt j) :
    (∀ b, z ∈ ((A.atJoin j).process b).constitution ∧ ¬ Separates ((A.atJoin j).process b).response z) ∧
      (∀ j' : Join (A.atJoin j).process, z ∈ kernel (((A.atJoin j).process j'.giver).grainings j'.source) ∧
        z ∈ kernel (((A.atJoin j).process j'.taker).grainings j'.made)) ∧
      (∀ ch : Change S Bool, ch.before = A.atJoin j → (z ∉ ch.after.between ↔ ∃ b, z ∈ ch.price b)) ∧
      (∀ (b : Bool) (X : Accessible S), ∃ ch : Change S Bool, ch.before = A.atJoin j ∧ ch.accessibleAfter = X ∧ z ∈ ch.price b ∧
        z ∉ ch.after.between ∧ ∀ b', b' ≠ b → ch.after.process b' = (A.atJoin j).process b') :=
  Composition.exact_in_kind (A.atJoin j) ((Composition.at_join A j).1 ▸ hz)

/-! ## What is forbidden, and which error is held -/

/-- **Claim 37 (What it forbids), its first sentence.** Whatever a response follows, it follows through a carried quantity: there is no process whose response follows a quantity through nothing its coarse-grainings carry. -/
theorem Response.follows_through_carried (p : Process S) (X : Accessible S) {Q : Type} (q : S → Q) (hf : Follows X p.response q) :
    ∃ (V : Type) (c : S → V), p.Carries c ∧ Carries c p.response ∧ Fixes X q c ∧ VariesWith X c q :=
  ⟨_, p.response, Law.factorization p, ⟨id, rfl⟩, hf.1, hf.2⟩

/-- **Claim 39 (Which error is held).** A quantity of situations a process holds is a quantity of the state that obtains, and does not depend on a forestalled state. -/
theorem Response.held_is_of_the_state {Q : Type} (p : Process S) (W : Set (Situation S)) {F : Situation S → Q} (hh : p.HoldsOfSituation W F) :
    (∃ e : S → Q, ∀ w, F w = e w.obtains) ∧ ¬ DependsOnForestalled F := by
  obtain ⟨⟨h, hF⟩, hf⟩ := hh
  exact ⟨⟨h ∘ p.jointly, hF⟩, fun hdep => Response.holds_nothing_forestalled p W hdep ⟨⟨h, hF⟩, hf⟩⟩

/-- **Claim 41 (Seeing is the first step).** A pair of the between, and a map separating it. Let a position that holds an absent process come to hold a process that reads that map, with a constant rule. The position pays for the pair, the pair leaves the between, nothing joins the between, every other position stays, and the new process holds nothing. -/
theorem Composition.seeing (A : Arrangement S ι) (k : ι) (hk : A.process k = Process.absent) (X : Accessible S) {V : Type} (e : S → V) {z : Sym2 S} (hz : z ∈ A.between) (hsep : Separates e z) :
    ∃ ch : Change S ι, ch.before = A ∧ ch.accessibleAfter = X ∧ z ∈ ch.price k ∧ z ∉ ch.after.between ∧ ch.after.between ⊆ A.between ∧
      (∀ j, j ≠ k → ch.after.process j = A.process j) ∧
      ∀ (Y : Accessible S) {Q : Type} (q : S → Q), ¬ (ch.after.process k).Holds Y q := by
  classical
  let reader : Process S := (Process.reading e).withRule fun _ => ()
  let A' : Arrangement S ι := ⟨A.finite, Function.update A.process k reader, ∅⟩
  have hkk : A'.process k = reader := Function.update_self k _ A.process
  have hother : ∀ j, j ≠ k → A'.process j = A.process j := fun j hj => Function.update_of_ne hj _ A.process
  have hout : z ∉ (A'.process k).constitution := by
    rw [hkk]
    exact hsep
  refine ⟨⟨A, A', X, X, Or.inl rfl⟩, rfl, rfl, ⟨hz.2 k, hout⟩, fun hin => hout (hin.2 k), fun w hw => ⟨hw.1, fun j => ?_⟩, hother, ?_⟩
  · by_cases hj : j = k
    · rw [hj, hk, constitution_absent]
      exact Set.mem_univ w
    · have h := hw.2 j
      rwa [hother j hj] at h
  · intro Y Q q hheld
    change (A'.process k).Holds Y q at hheld
    rw [hkk] at hheld
    obtain ⟨-, -, s, -, t, -, -, ha⟩ := hheld
    exact ha rfl

end Companion
