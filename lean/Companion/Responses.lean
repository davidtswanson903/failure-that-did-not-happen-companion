import Companion.Laws
import Mathlib.Data.Fintype.Card

/-!
# The responses

Claim 3 (Silence), Claim 5 (The non-event), Claim 6 (Borrowing) and Claim 8 (Not supplied from outside): what a response cannot do. It is constant where its coarse-grainings
are; no coarse-graining carries what depends on a state that does not obtain; it follows what its coarse-grainings do not carry only through what they do; and
what others make does not change what it is constituted to tell apart.

The route: `Law.factorization` writes the response as a function of its coarse-grainings' values, which gives silence, and makes the response itself a carried
quantity, which gives borrowing. `Law.obtains` makes every value a function of the state that obtains, so two situations with one state that obtains give one
value, which gives the non-event. And a constitution is read from the one coarse-graining a process is constituted to make, so taking up another's leaves it, and
by `Law.constitution` what is taken up identifies every pair it identifies. So another's coarse-graining supplies nothing a process was not constituted to tell apart, and what it can make of another's is settled by its own constitution.
-/

namespace Companion

variable {S : Type}

/-- **Claim 3 (Silence).** A response is constant on every pair of states that all its coarse-grainings identify. -/
theorem Response.silence (p : Process S) {s t : S} (h : ∀ i, p.grainings i s = p.grainings i t) :
    p.response s = p.response t := by
  obtain ⟨g, hg⟩ := Law.factorization p
  rw [hg]
  exact congrArg g (funext h)

/-- A coarse-graining carries a quantity of a situation when the quantity is a function of the value its evaluation gives
there. This is `Carries` for a quantity that takes the forestalled state as a second argument. -/
def CarriesOfSituation {C Q : Type} (c : S → C) (F : Situation S → Q) : Prop :=
  ∃ h : C → Q, ∀ w, F w = h (evaluate c w)

/-- The value of what was forestalled: a value `v` read at the state that obtains and at the one that would have. -/
def valueForestalled {Q : Type} (v : S → S → Q) : Situation S → Q :=
  fun w => v w.obtains w.wouldHave

/-- The first step of the non-event: by Claim 2 (The condition of response), two situations with one state that obtains give any coarse-graining
one value, so a quantity it carries has one value in them. -/
theorem carried_eq_of_obtains_eq {C Q : Type} {c : S → C} {F : Situation S → Q} (hc : CarriesOfSituation c F)
    {w w' : Situation S} (hw : w.obtains = w'.obtains) : F w = F w' := by
  obtain ⟨h, hh⟩ := hc
  rw [hh w, hh w', (Law.obtains c w').2 w hw]

/-- The second step of the non-event: a value that differs between two forestalled states for one state that obtains
depends on a forestalled state. -/
theorem valueForestalled_depends {Q : Type} (v : S → S → Q) (s t t' : S) (ht : t ≠ s) (ht' : t' ≠ s)
    (hv : v s t ≠ v s t') : DependsOnForestalled (valueForestalled v) :=
  ⟨⟨s, t⟩, ⟨s, t'⟩, ht, ht', rfl, hv⟩

/-- **Claim 5 (The non-event), in general.** No coarse-graining carries a quantity of a situation that takes two values at one state
that obtains, whether or not either situation has anything forestalled. -/
theorem not_carries_of_differs {C Q : Type} (c : S → C) (F : Situation S → Q)
    (hF : ∃ w w' : Situation S, w.obtains = w'.obtains ∧ F w ≠ F w') : ¬ CarriesOfSituation c F := by
  obtain ⟨w, w', hw, hne⟩ := hF
  exact fun hc => hne (carried_eq_of_obtains_eq hc hw)

/-- **Claim 5 (The non-event).** No coarse-graining carries a quantity that depends on a state that does not obtain, and the value
of what was forestalled is such a quantity, wherever that value differs between two forestalled states for one state that
obtains. The first clause is `not_carries_of_differs` with the forestalled hypotheses set aside. The second clause's hypotheses restate
its scope. -/
theorem Response.nonevent :
    (∀ {C Q : Type} (c : S → C) (F : Situation S → Q), DependsOnForestalled F → ¬ CarriesOfSituation c F) ∧
      ∀ {Q : Type} (v : S → S → Q) (s t t' : S), t ≠ s → t' ≠ s → v s t ≠ v s t' →
        DependsOnForestalled (valueForestalled v) := by
  refine ⟨fun c F hF => ?_, fun v s t t' ht ht' hv => valueForestalled_depends v s t t' ht ht' hv⟩
  obtain ⟨w, w', -, -, hw, hne⟩ := hF
  exact not_carries_of_differs c F ⟨w, w', hw, hne⟩

/-- **Claim 5 (The non-event), its reach on small `S`.** On at most two states no quantity depends on a forestalled state in the sense of
`DependsOnForestalled`, which needs two forestalled states beside the one that obtains. So the first clause of `Response.nonevent`
is empty there. -/
theorem not_dependsOnForestalled_of_card_le_two [Fintype S] (hS : Fintype.card S ≤ 2) {Q : Type} (F : Situation S → Q) :
    ¬ DependsOnForestalled F := by
  rintro ⟨w, w', hf, hf', ho, hne⟩
  have hdiff : w.wouldHave ≠ w'.wouldHave := fun heq => hne (congrArg F (Situation.ext ho heq))
  have hthree : 2 < Fintype.card S :=
    Fintype.two_lt_card_iff.mpr ⟨w.obtains, w.wouldHave, w'.wouldHave, Ne.symm hf, ho ▸ Ne.symm hf', hdiff⟩
  omega

/-- **Claim 5 (The non-event), its reach.** The general form reaches what `DependsOnForestalled` leaves out, and only through a situation with nothing forestalled. On two states, what would have obtained
differs between a situation with something forestalled and one with nothing forestalled. It does not depend on a forestalled state in the
sense of that definition, and still no coarse-graining carries it. Restricted to situations where something is forestalled, it is carried (`forestalled_value_carried_on_two_states`). -/
theorem nonevent_beyond_forestalled :
    ∃ F : Situation Bool → Bool, ¬ DependsOnForestalled F ∧ ∀ {C : Type} (c : Bool → C), ¬ CarriesOfSituation c F :=
  ⟨Situation.wouldHave, not_dependsOnForestalled_of_card_le_two (by simp) _, fun c =>
    not_carries_of_differs c _ ⟨⟨false, false⟩, ⟨false, true⟩, rfl, Bool.false_ne_true⟩⟩

/-- A step of borrowing: a quantity a carried one carries is carried too. -/
theorem Process.Carries.trans {p : Process S} {V Q : Type} {c : S → V} {q : S → Q} (hc : p.Carries c)
    (hq : Companion.Carries c q) : p.Carries q := by
  obtain ⟨g, rfl⟩ := hc
  obtain ⟨h, rfl⟩ := hq
  exact ⟨h ∘ g, rfl⟩

/-- **Claim 6 (Borrowing).** A response follows a quantity its coarse-grainings do not carry only through a carried quantity
that varies with it across the accessible states: there is a quantity `c` the coarse-grainings carry, which carries the
response, which the followed quantity fixes across them, which varies with it there, and which does not carry it. By
Claim 2 (The condition of response) the response itself is that quantity. -/
theorem Response.borrowing (p : Process S) (X : Accessible S) {Q : Type} (q : S → Q)
    (hq : ¬ p.Carries q) (hf : Follows X p.response q) :
    ∃ (V : Type) (c : S → V), p.Carries c ∧ Carries c p.response ∧ Fixes X q c ∧ VariesWith X c q ∧ ¬ Carries c q :=
  ⟨p.Action, p.response, Law.factorization p, ⟨id, rfl⟩, hf.1, hf.2, fun hc => hq ((Law.factorization p).trans hc)⟩

/-- **Claim 6 (Borrowing), for every carried quantity it passes through.** Where a response follows a quantity its coarse-grainings do not
carry, each carried quantity `c` that carries the response varies with the followed quantity across the accessible states, and does not
carry it. What the followed quantity fixes across them is what `c` passes on to the response, `h ∘ c`, and not in general `c` itself
(`borrowing_fixes_can_fail`). -/
theorem Response.borrowing_every (p : Process S) (X : Accessible S) {Q : Type} (q : S → Q)
    (hq : ¬ p.Carries q) (hf : Follows X p.response q) {V : Type} (c : S → V) (hc : p.Carries c) (hr : Carries c p.response) :
    VariesWith X c q ∧ ¬ Carries c q ∧ ∃ h : V → p.Action, p.response = h ∘ c ∧ Fixes X q (h ∘ c) := by
  obtain ⟨h, hh⟩ := hr
  obtain ⟨s, hs, t, ht, hqst, hne⟩ := hf.2
  refine ⟨⟨s, hs, t, ht, hqst, fun heq => hne ?_⟩, fun hcq => hq (hc.trans hcq), h, hh, hh ▸ hf.1⟩
  rw [hh]
  exact congrArg h heq

/-- **Claim 6 (Borrowing).** The followed quantity need not fix a carried quantity the response passes through. On three bits, a process
reads the first two and responds with the first, and across the states where the first and third bits agree its response follows the third, which it does
not carry. The third bit does not fix what the process reads, since the second bit is free. -/
theorem borrowing_fixes_can_fail :
    ∃ (S : Type) (_ : Fintype S) (p : Process S) (X : Accessible S) (Q V : Type) (q : S → Q) (c : S → V),
      ¬ p.Carries q ∧ Follows X p.response q ∧ p.Carries c ∧ Carries c p.response ∧ ¬ Fixes X q c := by
  let c : Bool × Bool × Bool → Bool × Bool := fun s => (s.1, s.2.1)
  let p : Process (Bool × Bool × Bool) := (Process.reading c).withRule fun v => (v ()).1
  let q : Bool × Bool × Bool → Bool := fun s => s.2.2
  let X : Accessible (Bool × Bool × Bool) := {s | s.1 = s.2.2}
  refine ⟨Bool × Bool × Bool, inferInstance, p, X, Bool, Bool × Bool, q, c, ?_, ⟨?_, ?_⟩, ⟨fun v => v (), rfl⟩, ⟨Prod.fst, rfl⟩, ?_⟩
  · rintro ⟨h, hh⟩
    have h0 : q (false, false, false) = h (p.jointly (false, false, false)) := congrFun hh _
    have h1 : q (false, false, true) = h (p.jointly (false, false, true)) := congrFun hh _
    exact Bool.false_ne_true (h0.trans h1.symm)
  · rintro s hs t ht hst
    have hs' : s.1 = s.2.2 := hs
    have ht' : t.1 = t.2.2 := ht
    have hst' : s.2.2 = t.2.2 := hst
    exact hs'.trans (hst'.trans ht'.symm)
  · exact ⟨(false, false, false), rfl, (true, false, true), rfl, Bool.false_ne_true, Bool.false_ne_true⟩
  · intro hfix
    have hsame : c (true, false, true) = c (true, true, true) := hfix _ rfl _ rfl rfl
    exact Bool.false_ne_true (congrArg Prod.snd hsame)

/-- The first step: by Claim 2 (The condition of response), a pair in a process's constitution is in the kernel of each of its
coarse-grainings. -/
theorem mem_grainings_of_mem_constitution {p : Process S} {z : Sym2 S} (hz : z ∈ p.constitution)
    (k : p.Index) : z ∈ kernel (p.grainings k) :=
  (Law.constitution p k).2 hz

/-- The second step: a pair all of a process's coarse-grainings identify, read together they identify. -/
theorem mem_kernel_jointly {p : Process S} {z : Sym2 S} (hz : ∀ k, z ∈ kernel (p.grainings k)) : z ∈ kernel p.jointly := by
  induction z with
  | _ s t =>
    exact (mem_kernel _ s t).mpr (funext fun k => (mem_kernel (p.grainings k) s t).mp (hz k))

/-- **Claim 3 (Silence).** The third step: by silence, a pair in a process's constitution is in the kernel of its response. -/
theorem mem_response_of_mem_constitution {p : Process S} {z : Sym2 S} (hz : z ∈ p.constitution) : z ∈ kernel p.response := by
  induction z with
  | _ s t =>
    refine (mem_kernel _ s t).mpr (Response.silence p fun k => ?_)
    exact (mem_kernel (p.grainings k) s t).mp (mem_grainings_of_mem_constitution hz k)

/-- A step of the unsupplied: by Claim 2 (The condition of response), what a process comes to make by a map `f` of its own constitutive values, equal to a map `h` of the
values of a coarse-graining `c` another makes, identifies every pair its constitution identifies. -/
theorem constitution_subset_of_takeUp {p : Process S} {C V : Type} {c : S → C} {h : C → V} {f : p.constitutive.Value → V}
    (hf : ∀ s, f (p.constitutive s) = h (c s)) : p.constitution ⊆ kernel (fun s => h (c s)) := by
  intro z
  induction z with
  | _ s t =>
    intro hz
    have hk : f (p.constitutive s) = f (p.constitutive t) :=
      (mem_kernel ((p.takeUp f).grainings none) s t).mp ((Law.constitution (p.takeUp f) none).2 hz)
    exact (mem_kernel _ s t).mpr ((hf s).symm.trans (hk.trans (hf t)))

/-- **Claim 8 (Not supplied from outside).** Coarse-grainings made by other processes do not change what a process is constituted to tell apart. For any map `f`, a process that comes
to make `f` keeps its constitution. And where `f` is a map `h` of the values of a coarse-graining `q` makes, nothing `p` then makes or responds to through it separates a pair in
`p`'s constitution, so the other's coarse-graining supplies `p` nothing it was not constituted to tell apart. -/
theorem Response.unsupplied (p q : Process S) (i : q.Index) {V : Type} (h : (q.grainings i).Value → V) :
    (∀ f : p.constitutive.Value → V, (p.takeUp f).constitution = p.constitution) ∧
      ∀ f : p.constitutive.Value → V, (∀ s, f (p.constitutive s) = h (q.grainings i s)) → ∀ z ∈ p.constitution,
        ¬ Separates (fun s => h (q.grainings i s)) z ∧
          ∀ {A : Type} (g : (∀ k, (p.takeUp f).Value k) → A), ¬ Separates ((p.takeUp f).withRule g).response z :=
  ⟨fun _ => rfl, fun _ hf _ hz => ⟨fun hsep => hsep (constitution_subset_of_takeUp hf hz),
    fun g hsep => hsep (mem_response_of_mem_constitution (p := (p.takeUp _).withRule g) hz)⟩⟩

/-- **Claim 8 (Not supplied from outside).** A process can make a map of the values of a coarse-graining from outside exactly where its constitution lies in that map's kernel, there being a state
for the map's values to come from. So whether another's coarse-graining reaches it is settled by what it is already constituted to tell apart. -/
theorem exists_takeUp_iff [Nonempty S] (p : Process S) {C V : Type} (c : S → C) (h : C → V) :
    (∃ f : p.constitutive.Value → V, ∀ s, f (p.constitutive s) = h (c s)) ↔ p.constitution ⊆ kernel (fun s => h (c s)) := by
  constructor
  · rintro ⟨f, hf⟩
    exact constitution_subset_of_takeUp hf
  · intro hsub
    obtain ⟨s₀⟩ := ‹Nonempty S›
    have hthrough : Function.FactorsThrough (fun s => h (c s)) p.constitutive.map := fun s t hst =>
      (mem_kernel _ s t).mp (hsub ((mem_kernel p.constitutive.map s t).mpr hst))
    exact ⟨Function.extend p.constitutive.map (fun s => h (c s)) (fun _ => h (c s₀)), fun s => hthrough.extend_apply _ s⟩

/-- **Claim 8 (Not supplied from outside).** What the taker of a join makes through the source, and its response, separate no pair in its constitution, whatever the giver tells apart:
at such a pair the join's map gives the source's two values one value. -/
theorem join_supplies_nothing {ι : Type} {process : ι → Process S} (j : Join process) :
    (∀ z ∈ (process j.taker).constitution,
      ¬ Separates ((process j.taker).grainings j.made) z ∧ ¬ Separates (process j.taker).response z) ∧
      ∀ s t, s(s, t) ∈ (process j.taker).constitution →
        j.further ((process j.giver).grainings j.source s) = j.further ((process j.giver).grainings j.source t) := by
  refine ⟨fun z hz => ⟨fun hsep => hsep (mem_grainings_of_mem_constitution hz j.made),
    fun hsep => hsep (mem_response_of_mem_constitution hz)⟩, fun s t hst => ?_⟩
  have hk := (mem_kernel _ s t).mp (mem_grainings_of_mem_constitution hst j.made)
  exact (j.made_eq s).symm.trans (hk.trans (j.made_eq t))

/-- **Claim 5 (The non-event), on two states.** On two states the value of what was forestalled is carried, on every situation where something is forestalled: there the state that would have obtained is the other state, a function of the state that obtains. So the form's second clause needs its condition, that the value changes while the state that obtains stays the same, and that condition asks for three states (`not_dependsOnForestalled_of_card_le_two`). -/
theorem forestalled_value_carried_on_two_states :
    ∃ F : Situation Bool → Bool, (∀ w, w.Forestalled → F w = w.wouldHave) ∧ CarriesOfSituation (id : Bool → Bool) F := by
  refine ⟨fun w => !w.obtains, ?_, ⟨fun b => !b, fun _ => rfl⟩⟩
  rintro ⟨o, h⟩ hf
  cases o <;> cases h <;> first | rfl | exact absurd rfl hf

/-- **Claim 5 (The non-event), on two states, of every value.** On at most two states every value of what was forestalled is carried, on every situation where something is forestalled: there the state that would have obtained is the other state, a function of the state that obtains, so the value is one too. `forestalled_value_carried_on_two_states` is one such value on `Bool`. -/
theorem every_forestalled_value_carried_on_two_states {a b : S} (hall : ∀ s, s = a ∨ s = b) {Q : Type} (v : S → S → Q) :
    ∃ F : Situation S → Q, (∀ w, w.Forestalled → F w = valueForestalled v w) ∧ CarriesOfSituation (id : S → S) F := by
  classical
  refine ⟨fun w => v w.obtains (if w.obtains = a then b else a), ?_, ⟨fun s => v s (if s = a then b else a), fun _ => rfl⟩⟩
  rintro ⟨o, h⟩ hf
  have hother : (if o = a then b else a) = h := by
    have hne : h ≠ o := hf
    rcases hall o with ho | ho <;> rcases hall h with hh | hh <;> simp_all
  exact congrArg (v o) hother

end Companion
