import Companion.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Relation

/-!
# Content, filing and invariance

The content, One setting of a content, A case's class under relabelling, Definition 4 (Invariance under redescription): an arrangement with its
accessible states, a relabelling of it, its content as its class under relabelling, a case as such an arrangement with the state that
obtains, a filing as a case's class under relabelling, invariance under a named kind of change, and what invariance under relabellings and under changes of history together come to.

The route of the split: both a relabelling alone and a change of history alone stay within one content, so a feature with one value across a
content is left as it was by each. And a case with the content of another is reached from it by one change of each kind, first the
relabelling, carrying the state that obtains, and then the change of history. So the two checks together are one value across a content, and
that is a function of the class.
-/

namespace Companion

variable {S S' S'' ι ι' ι'' : Type}

/-! ## An arrangement with its accessible states, and a case -/

/-- **The content, The accessible states.** An arrangement with its accessible states, which The content carries with it.
At least one state is accessible, since a state obtains in every case, and an arrangement with no state that can obtain has no history. What a
process holds is not stored: Definition 3 (Holding a loss) reads it from the arrangement and the accessible states (`Process.Holds`). -/
structure Setting (S ι : Type) where
  /-- The arrangement. -/
  arrangement : Arrangement S ι
  /-- Its accessible states. -/
  accessible : Accessible S
  /-- Some state can obtain. -/
  nonempty : accessible.Nonempty

/-- **A case's class under relabelling.** A case: an arrangement with its accessible states, and its history, which accessible state obtains. -/
structure Case (S ι : Type) extends Setting S ι where
  /-- Which state obtains. -/
  obtains : S
  /-- The state that obtains is accessible. -/
  obtains_mem : obtains ∈ accessible

/-! ## Relabelling and content -/

/-- A bijection of the states carries one set of pairs onto another when a pair lies in the first exactly when its image lies in the second. -/
def PairsCarried (π : S ≃ S') (X : Set (Sym2 S)) (Y : Set (Sym2 S')) : Prop :=
  ∀ z, z ∈ X ↔ z.map π ∈ Y

/-- **The content.** A relabelling carries a join onto another when it matches their takers and their givers, and carries what the source and
what is made identify. A join is read through kernels, as a constitution is: the two may differ in the names of their values. -/
def JoinCarried {process : ι → Process S} {process' : ι' → Process S'} (π : S ≃ S') (σ : ι ≃ ι') (j : Join process) (j' : Join process') : Prop :=
  j'.taker = σ j.taker ∧ j'.giver = σ j.giver ∧
    PairsCarried π (kernel ((process j.giver).grainings j.source)) (kernel ((process' j'.giver).grainings j'.source)) ∧
    PairsCarried π (kernel ((process j.taker).grainings j.made)) (kernel ((process' j'.taker).grainings j'.made))

/-- **Definition 4 (Invariance under redescription).** A relabelling: the processes matched one to one, and a bijection of the states that carries the accessible states, and each
process's constitution, held quantities and joins, onto those of its match. A quantity `q` goes to `q ∘ π⁻¹`. -/
structure Relabelling (A : Setting S ι) (B : Setting S' ι') where
  /-- The bijection of the states. -/
  states : S ≃ S'
  /-- The processes matched one to one. -/
  positions : ι ≃ ι'
  /-- It carries the accessible states. -/
  accessible : ∀ s, s ∈ A.accessible ↔ states s ∈ B.accessible
  /-- It carries each process's constitution. -/
  constitution : ∀ i, PairsCarried states (A.arrangement.process i).constitution (B.arrangement.process (positions i)).constitution
  /-- It carries what each process holds. -/
  held : ∀ i {Q : Type} (q : S → Q),
    (A.arrangement.process i).Holds A.accessible q ↔ (B.arrangement.process (positions i)).Holds B.accessible (q ∘ states.symm)
  /-- It carries each join into the other's. -/
  joins : ∀ j ∈ A.arrangement.joins, ∃ j' ∈ B.arrangement.joins, JoinCarried states positions j j'
  /-- And it carries the joins onto the other's. -/
  joins_onto : ∀ j' ∈ B.arrangement.joins, ∃ j ∈ A.arrangement.joins, JoinCarried states positions j j'

/-- A bijection carries a set of pairs onto itself under the identity. -/
theorem PairsCarried.refl (X : Set (Sym2 S)) : PairsCarried (Equiv.refl S) X X := by
  intro z
  induction z with
  | _ s t => exact Iff.rfl

/-- What a bijection carries, its inverse carries back. -/
theorem PairsCarried.symm {π : S ≃ S'} {X : Set (Sym2 S)} {Y : Set (Sym2 S')} (h : PairsCarried π X Y) : PairsCarried π.symm Y X := by
  intro z
  induction z with
  | _ s t =>
    have := h s(π.symm s, π.symm t)
    simpa using this.symm

/-- What two bijections carry in turn, their composite carries. -/
theorem PairsCarried.trans {π : S ≃ S'} {ρ : S' ≃ S''} {X : Set (Sym2 S)} {Y : Set (Sym2 S')} {Z : Set (Sym2 S'')}
    (h : PairsCarried π X Y) (k : PairsCarried ρ Y Z) : PairsCarried (π.trans ρ) X Z := by
  intro z
  induction z with
  | _ s t => exact (h s(s, t)).trans (k s(π s, π t))

/-- A join carried is carried back. -/
theorem JoinCarried.symm {process : ι → Process S} {process' : ι' → Process S'} {π : S ≃ S'} {σ : ι ≃ ι'} {j : Join process} {j' : Join process'}
    (h : JoinCarried π σ j j') : JoinCarried π.symm σ.symm j' j := by
  obtain ⟨ht, hg, hs, hm⟩ := h
  exact ⟨by rw [ht, Equiv.symm_apply_apply], by rw [hg, Equiv.symm_apply_apply], hs.symm, hm.symm⟩

/-- A join carried twice is carried by the composite. -/
theorem JoinCarried.trans {process : ι → Process S} {process' : ι' → Process S'} {process'' : ι'' → Process S''} {π : S ≃ S'} {ρ : S' ≃ S''}
    {σ : ι ≃ ι'} {τ : ι' ≃ ι''} {j : Join process} {j' : Join process'} {j'' : Join process''}
    (h : JoinCarried π σ j j') (k : JoinCarried ρ τ j' j'') : JoinCarried (π.trans ρ) (σ.trans τ) j j'' := by
  obtain ⟨ht, hg, hs, hm⟩ := h
  obtain ⟨kt, kg, ks, km⟩ := k
  exact ⟨by rw [kt, ht]; rfl, by rw [kg, hg]; rfl, hs.trans ks, hm.trans km⟩

/-- Every arrangement is a relabelling of itself, by the identity. -/
def Relabelling.refl (A : Setting S ι) : Relabelling A A where
  states := Equiv.refl S
  positions := Equiv.refl ι
  accessible := fun _ => Iff.rfl
  constitution := fun _ => PairsCarried.refl _
  held := fun _ _ _ => Iff.rfl
  joins := fun j hj => ⟨j, hj, rfl, rfl, PairsCarried.refl _, PairsCarried.refl _⟩
  joins_onto := fun j hj => ⟨j, hj, rfl, rfl, PairsCarried.refl _, PairsCarried.refl _⟩

/-- A relabelling is undone by the inverse bijections. -/
def Relabelling.symm {A : Setting S ι} {B : Setting S' ι'} (r : Relabelling A B) : Relabelling B A where
  states := r.states.symm
  positions := r.positions.symm
  accessible := fun s => by
    have := r.accessible (r.states.symm s)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  constitution := fun i => by
    have := r.constitution (r.positions.symm i)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  held := fun i {Q} q => by
    have := r.held (r.positions.symm i) (q ∘ r.states)
    rw [Equiv.apply_symm_apply] at this
    have hq : (q ∘ r.states) ∘ r.states.symm = q := by
      funext s
      simp
    rw [hq] at this
    exact this.symm
  joins := fun j' hj' => by
    obtain ⟨j, hj, hc⟩ := r.joins_onto j' hj'
    exact ⟨j, hj, hc.symm⟩
  joins_onto := fun j hj => by
    obtain ⟨j', hj', hc⟩ := r.joins j hj
    exact ⟨j', hj', hc.symm⟩

/-- Two relabellings in turn are a relabelling, by the composite bijections. -/
def Relabelling.trans {A : Setting S ι} {B : Setting S' ι'} {C : Setting S'' ι''} (r : Relabelling A B) (u : Relabelling B C) : Relabelling A C where
  states := r.states.trans u.states
  positions := r.positions.trans u.positions
  accessible := fun s => (r.accessible s).trans (u.accessible (r.states s))
  constitution := fun i => (r.constitution i).trans (u.constitution (r.positions i))
  held := fun i _ q => (r.held i q).trans (u.held (r.positions i) (q ∘ r.states.symm))
  joins := fun j hj => by
    obtain ⟨j', hj', hc⟩ := r.joins j hj
    obtain ⟨j'', hj'', hd⟩ := u.joins j' hj'
    exact ⟨j'', hj'', hc.trans hd⟩
  joins_onto := fun j'' hj'' => by
    obtain ⟨j', hj', hd⟩ := u.joins_onto j'' hj''
    obtain ⟨j, hj, hc⟩ := r.joins_onto j' hj'
    exact ⟨j, hj, hc.trans hd⟩

/-- **The content.** Two arrangements have one content when there is a relabelling between them. -/
def OneContent (A : Setting S ι) (B : Setting S' ι') : Prop :=
  Nonempty (Relabelling A B)

/-- **Definition 4 (Invariance under redescription).** Having one content is an equivalence on the arrangements over given states and positions. -/
def contentSetoid (S ι : Type) : Setoid (Setting S ι) where
  r := OneContent
  iseqv := ⟨fun A => ⟨Relabelling.refl A⟩, fun ⟨r⟩ => ⟨r.symm⟩, fun ⟨r⟩ ⟨u⟩ => ⟨r.trans u⟩⟩

/-- **The content.** The content of an arrangement is its class under relabelling. -/
def Content (S ι : Type) : Type 1 :=
  Quotient (contentSetoid S ι)

/-- **The content.** The map from each arrangement to its content. -/
def Setting.content (A : Setting S ι) : Content S ι :=
  Quotient.mk (contentSetoid S ι) A

/-- **One setting of a content.** A labelling of a content is one arrangement that has it. -/
def Setting.IsLabelling (A : Setting S ι) (κ : Content S ι) : Prop :=
  A.content = κ

/-- **One setting of a content.** Any two labellings of one content differ by a relabelling. -/
theorem Setting.IsLabelling.differ {A B : Setting S ι} {κ : Content S ι} (hA : A.IsLabelling κ) (hB : B.IsLabelling κ) : OneContent A B :=
  Quotient.exact (hA.trans hB.symm)

/-- The content of a case: the content of its arrangement. -/
def Case.content (C : Case S ι) : Content S ι :=
  C.toSetting.content

/-! ## Invariance -/

/-- **Definition 4 (Invariance under redescription).** A kind of change, on whatever it changes, is a relation: which things one change of that kind takes to which. A feature is invariant
under a kind of change when every change of that kind leaves it as it was. -/
def InvariantUnder {X V : Type*} (change : X → X → Prop) (f : X → V) : Prop :=
  ∀ a b, change a b → f a = f b

/-- **Definition 4 (Invariance under redescription).** A feature of an arrangement and the state that obtains. -/
abbrev Feature (S ι V : Type) : Type 1 :=
  Case S ι → V

/-- **Definition 4 (Invariance under redescription).** A relabelling alone: it takes a case to one whose arrangement is a relabelling of its own and whose state that obtains is the
image of its own. -/
def Case.Relabels (a b : Case S ι) : Prop :=
  ∃ r : Relabelling a.toSetting b.toSetting, r.states a.obtains = b.obtains

/-- **Definition 4 (Invariance under redescription).** A change of history alone: the same arrangement over the same accessible states, and any state that obtains. -/
def Case.HistoryChange (a b : Case S ι) : Prop :=
  a.toSetting = b.toSetting

/-- A case is a relabelling of itself. -/
theorem Case.Relabels.refl (C : Case S ι) : C.Relabels C :=
  ⟨Relabelling.refl C.toSetting, rfl⟩

/-- A relabelling alone is undone by a relabelling alone. -/
theorem Case.Relabels.symm {a b : Case S ι} : a.Relabels b → b.Relabels a := by
  rintro ⟨r, hr⟩
  refine ⟨r.symm, ?_⟩
  change r.states.symm b.obtains = a.obtains
  rw [← hr, Equiv.symm_apply_apply]

/-- Two relabellings alone in turn are a relabelling alone. -/
theorem Case.Relabels.trans {a b c : Case S ι} : a.Relabels b → b.Relabels c → a.Relabels c := by
  rintro ⟨r, hr⟩ ⟨u, hu⟩
  refine ⟨r.trans u, ?_⟩
  change u.states (r.states a.obtains) = c.obtains
  rw [hr, hu]

/-- **A case's class under relabelling.** Being related by a relabelling alone is an equivalence on the cases over given states and positions. -/
def caseSetoid (S ι : Type) : Setoid (Case S ι) where
  r := Case.Relabels
  iseqv := ⟨Case.Relabels.refl, Case.Relabels.symm, Case.Relabels.trans⟩

/-- **A case's class under relabelling.** A filing is a case's class under relabelling: its content and its history taken together. The state that obtains has a name only in a labelling, and the class has forgotten the labelling, so a filing holds the content, and the state only up to a relabelling of that setting onto itself (`Case.filing_eq_iff_of_historyChange`). Where such a relabelling moves a state, two cases of the setting have one filing (`one_filing_two_states`), and no map from filings gives the state (`filing_does_not_say_which`). The class stands because the pair fails both ways (`relabelling_can_move_pair`, `one_pair_two_filings`). -/
def Filing (S ι : Type) : Type 1 :=
  Quotient (caseSetoid S ι)

/-- **A case's class under relabelling.** The filing of a case. -/
def Case.filing (C : Case S ι) : Filing S ι :=
  Quotient.mk (caseSetoid S ι) C

/-- **A case's class under relabelling.** Two cases have one filing exactly when a relabelling takes one to the other, carrying the state that obtains. -/
theorem Case.filing_eq_iff {a b : Case S ι} : a.filing = b.filing ↔ a.Relabels b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- **A case's class under relabelling, its history up to a relabelling onto itself.** Two cases of one setting have one filing exactly when some relabelling of that setting onto itself carries the one state to the other. So a filing holds which state obtains up to such a relabelling and no more finely. -/
theorem Case.filing_eq_iff_of_historyChange {a b : Case S ι} (h : a.HistoryChange b) :
    a.filing = b.filing ↔ ∃ r : Relabelling a.toSetting a.toSetting, r.states a.obtains = b.obtains := by
  obtain ⟨A, s, hs⟩ := a
  obtain ⟨B, t, ht⟩ := b
  obtain rfl : A = B := h
  exact Case.filing_eq_iff

/-- **A case's class under relabelling.** A filing determines its content. -/
def Filing.content : Filing S ι → Content S ι :=
  Quotient.lift Case.content fun _ _ ⟨r, _⟩ => Quotient.sound ⟨r⟩

/-- **A case's class under relabelling.** The content of a case's filing is the case's content. So two cases of one filing have one content. -/
theorem Case.content_filing (C : Case S ι) : C.filing.content = C.content :=
  rfl

/-- **Definition 4 (Invariance under redescription).** A feature takes one value across every labelling and every history of one content. -/
def OneValueAcrossContent {V : Type} (f : Feature S ι V) : Prop :=
  ∀ a b : Case S ι, a.content = b.content → f a = f b

/-- **Definition 4 (Invariance under redescription), invariance composes.** A feature every change of a kind leaves as it was, any sequence of them leaves as it was. So taking each kind on its
own loses nothing. -/
theorem InvariantUnder.reflTransGen {X V : Type*} {change : X → X → Prop} {f : X → V} (h : InvariantUnder change f) :
    InvariantUnder (Relation.ReflTransGen change) f := by
  intro a b hab
  induction hab with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (h _ _ hstep)

/-! ## The split -/

/-- The first half of the split, forward: a case with the content of another is reached from it by a relabelling alone and then a change of history alone. -/
theorem oneValue_of_invariantUnder {V : Type} {f : Feature S ι V} (hr : InvariantUnder Case.Relabels f) (hh : InvariantUnder Case.HistoryChange f) :
    OneValueAcrossContent f := by
  intro a b hab
  obtain ⟨r⟩ : OneContent a.toSetting b.toSetting := Quotient.exact hab
  let m : Case S ι := ⟨b.toSetting, r.states a.obtains, (r.accessible _).mp a.obtains_mem⟩
  exact (hr a m ⟨r, rfl⟩).trans (hh m b rfl)

/-- The first half of the split, back: a relabelling alone and a change of history alone each stay within one content. -/
theorem invariantUnder_of_oneValue {V : Type} {f : Feature S ι V} (h : OneValueAcrossContent f) :
    InvariantUnder Case.Relabels f ∧ InvariantUnder Case.HistoryChange f := by
  refine ⟨fun a b ⟨r, _⟩ => h a b (Quotient.sound ⟨r⟩), fun a b hab => h a b ?_⟩
  exact congrArg Setting.content hab

/-- The second half of the split: one value across a content is a function of the content. The value at a content is the feature's at any case of it, there being one, since
some state is accessible. -/
theorem oneValue_iff_factors {V : Type} (f : Feature S ι V) :
    OneValueAcrossContent f ↔ ∃ g : Content S ι → V, ∀ C, f C = g C.content := by
  constructor
  · intro h
    let pick : Setting S ι → V := fun A => f ⟨A, A.nonempty.some, A.nonempty.some_mem⟩
    have hpick : ∀ A B : Setting S ι, OneContent A B → pick A = pick B := fun A B hAB => h _ _ (Quotient.sound hAB)
    refine ⟨Quotient.lift pick hpick, fun C => ?_⟩
    exact h C ⟨C.toSetting, C.toSetting.nonempty.some, C.toSetting.nonempty.some_mem⟩ rfl
  · rintro ⟨g, hg⟩ a b hab
    rw [hg a, hg b, hab]

/-- **Definition 4 (Invariance under redescription).** A feature of an arrangement and the state that obtains is invariant under relabellings and invariant under changes of history exactly when it takes one
value across every labelling and every history of one content, that is, when it factors through the map from each arrangement to its content. -/
theorem Invariance.split {V : Type} (f : Feature S ι V) :
    (InvariantUnder Case.Relabels f ∧ InvariantUnder Case.HistoryChange f ↔ OneValueAcrossContent f) ∧
      (OneValueAcrossContent f ↔ ∃ g : Content S ι → V, ∀ C, f C = g C.content) :=
  ⟨⟨fun h => oneValue_of_invariantUnder h.1 h.2, invariantUnder_of_oneValue⟩, oneValue_iff_factors f⟩

/-! ## The filing -/

/-- **A case's class under relabelling, a relabelling changes no filing.** It holds of the class. -/
theorem filing_invariant_under_relabels : InvariantUnder (@Case.Relabels S ι) Case.filing :=
  fun _ _ h => Case.filing_eq_iff.mpr h

/-- **Definition 4 (Invariance under redescription), its companion for the filing.** A feature is invariant under relabellings exactly when it factors through the filing, as a feature invariant under relabellings and under changes of history is one that factors through content. -/
theorem invariant_relabels_iff_factors_filing {V : Type} (f : Feature S ι V) :
    InvariantUnder Case.Relabels f ↔ ∃ g : Filing S ι → V, ∀ C, f C = g C.filing := by
  constructor
  · exact fun h => ⟨Quotient.lift f fun a b hab => h a b hab, fun _ => rfl⟩
  · rintro ⟨g, hg⟩ a b hab
    rw [hg a, hg b, Case.filing_eq_iff.mpr hab]

/-! ## A relabelling exists for every bijection -/

/-- **The content.** A process with its states renamed by a bijection: it reads the old name of each state, and all else about it stays. -/
def Process.relabel (π : S ≃ S') (p : Process S) : Process S' where
  constitutive := ⟨p.constitutive.Value, p.constitutive ∘ π.symm⟩
  Index := p.Index
  Value := p.Value
  further := p.further
  Action := p.Action
  rule := p.rule

/-- A join stands through a renaming of the states. -/
def Join.relabel {process : ι → Process S} (π : S ≃ S') (j : Join process) : Join (fun i => (process i).relabel π) where
  taker := j.taker
  giver := j.giver
  another := j.another
  source := j.source
  made := j.made
  further := j.further
  made_eq := fun s => j.made_eq (π.symm s)

/-- An arrangement with its states renamed. -/
def Arrangement.relabel (π : S ≃ S') (A : Arrangement S ι) : Arrangement S' ι where
  finite := A.finite
  process := fun i => (A.process i).relabel π
  joins := Join.relabel π '' A.joins

/-- **One setting of a content.** An arrangement with its accessible states, its states renamed: another labelling of its content (`Setting.relabelling`). -/
def Setting.relabel (π : S ≃ S') (A : Setting S ι) : Setting S' ι where
  arrangement := A.arrangement.relabel π
  accessible := π '' A.accessible
  nonempty := A.nonempty.image π

/-- A bijection carries the kernel of a coarse-graining onto that of the same coarse-graining read at the old names. -/
theorem pairsCarried_kernel {C : Type} (π : S ≃ S') (c : S → C) : PairsCarried π (kernel c) (kernel (c ∘ π.symm)) := by
  intro z
  induction z with
  | _ s t => simp [mem_kernel]

/-- What a process holds, its renaming holds, at the old names. -/
theorem holds_relabel (π : S ≃ S') (p : Process S) (X : Accessible S) {Q : Type} (q : S → Q) :
    p.Holds X q ↔ (p.relabel π).Holds (π '' X) (q ∘ π.symm) := by
  have hj : ∀ s, (p.relabel π).jointly (π s) = p.jointly s := fun s => funext fun k => by
    change p.further k (p.constitutive (π.symm (π s))) = p.further k (p.constitutive s)
    rw [π.symm_apply_apply]
  have hr : ∀ s, (p.relabel π).response (π s) = p.response s := fun s => congrArg p.rule (hj s)
  have hq : ∀ s t, (q ∘ π.symm) (π s) = (q ∘ π.symm) (π t) ↔ q s = q t := fun s t => by simp
  have hcarries : p.Carries q ↔ (p.relabel π).Carries (q ∘ π.symm) := by
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, hh⟩
      refine ⟨h, funext fun s => ?_⟩
      have hs : q s = (q ∘ π.symm) (π s) := by simp
      exact hs.trans ((congrFun hh (π s)).trans (congrArg h (hj s)))
  have hfixes : Fixes X q p.response ↔ Fixes (π '' X) (q ∘ π.symm) (p.relabel π).response := by
    constructor
    · rintro h _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst
      exact (hr s).trans ((h s hs t ht ((hq s t).mp hst)).trans (hr t).symm)
    · intro h s hs t ht hst
      exact (hr s).symm.trans ((h (π s) ⟨s, hs, rfl⟩ (π t) ⟨t, ht, rfl⟩ ((hq s t).mpr hst)).trans (hr t))
  have hvaries : VariesWith X p.response q ↔ VariesWith (π '' X) (p.relabel π).response (q ∘ π.symm) := by
    constructor
    · rintro ⟨s, hs, t, ht, hne, ha⟩
      exact ⟨π s, ⟨s, hs, rfl⟩, π t, ⟨t, ht, rfl⟩, fun e => hne ((hq s t).mp e), fun e => ha ((hr s).symm.trans (e.trans (hr t)))⟩
    · rintro ⟨_, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, hne, ha⟩
      exact ⟨s, hs, t, ht, fun e => hne ((hq s t).mpr e), fun e => ha ((hr s).trans (e.trans (hr t).symm))⟩
  exact and_congr hcarries (and_congr hfixes hvaries)

/-- **Definition 4 (Invariance under redescription).** Renaming the states by any bijection gives a relabelling, with the processes matched by position. -/
def Setting.relabelling (π : S ≃ S') (A : Setting S ι) : Relabelling A (A.relabel π) where
  states := π
  positions := Equiv.refl ι
  accessible := fun _ => π.injective.mem_set_image.symm
  constitution := fun i => pairsCarried_kernel π (A.arrangement.process i).constitutive
  held := fun i _ q => holds_relabel π (A.arrangement.process i) A.accessible q
  joins := fun j hj => ⟨Join.relabel π j, ⟨j, hj, rfl⟩, rfl, rfl, pairsCarried_kernel π _, pairsCarried_kernel π _⟩
  joins_onto := by
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl, rfl, pairsCarried_kernel π _, pairsCarried_kernel π _⟩

/-! ## The three features -/

/-- A pair lies in the between exactly when its image lies in the between of the relabelled arrangement. -/
theorem Relabelling.mem_between_iff {A : Setting S ι} {B : Setting S' ι'} (r : Relabelling A B) (z : Sym2 S) :
    z ∈ A.arrangement.between ↔ z.map r.states ∈ B.arrangement.between := by
  have hdiag : (z.map r.states).IsDiag ↔ z.IsDiag := by
    induction z with
    | _ s t => simp [Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨hd, hall⟩
    refine ⟨fun h => hd (hdiag.mp h), fun i => ?_⟩
    have := (r.constitution (r.positions.symm i) z).mp (hall _)
    rwa [Equiv.apply_symm_apply] at this
  · rintro ⟨hd, hall⟩
    exact ⟨fun h => hd (hdiag.mpr h), fun i => (r.constitution i z).mpr (hall _)⟩

/-- The between of a relabelled arrangement is the image of the between. -/
theorem Relabelling.between_eq_image {A : Setting S ι} {B : Setting S' ι'} (r : Relabelling A B) :
    B.arrangement.between = Sym2.map r.states '' A.arrangement.between := by
  ext z
  constructor
  · intro hz
    refine ⟨z.map r.states.symm, (r.mem_between_iff _).mpr ?_, ?_⟩
    · rw [Sym2.map_map]
      simpa using hz
    · rw [Sym2.map_map]
      simp
  · rintro ⟨y, hy, rfl⟩
    exact (r.mem_between_iff y).mp hy

/-- **Definition 4 (Invariance under redescription), the first feature.** The size of the between. -/
noncomputable def betweenSize (C : Case S ι) : ℕ :=
  C.arrangement.residue

/-- **Definition 4 (Invariance under redescription), the second feature.** Whether one named pair lies in the between. -/
def betweenPair (x : Sym2 S) (C : Case S ι) : Prop :=
  x ∈ C.arrangement.between

/-- **Definition 4 (Invariance under redescription), the third feature.** Whether some process identifies the state that obtains with another state. A relabelling may match the processes in any order, under which "first" would be a
labelling's word, so this reads some process. -/
def obtainsShared (C : Case S ι) : Prop :=
  ∃ i t, t ≠ C.obtains ∧ s(C.obtains, t) ∈ (C.arrangement.process i).constitution

/-- **Definition 4 (Invariance under redescription).** The size of the between is invariant under relabellings: a bijection of pairs carries one between onto the other. -/
theorem betweenSize_relabels : InvariantUnder (@Case.Relabels S ι) betweenSize := by
  rintro a b ⟨r, -⟩
  change a.arrangement.between.ncard = b.arrangement.between.ncard
  rw [r.between_eq_image, Set.ncard_image_of_injective _ (Sym2.map.injective r.states.injective)]

/-- Reading only the arrangement, a feature is invariant under changes of history. -/
theorem invariantUnder_history_of_arrangement {V : Type} (g : Arrangement S ι → V) :
    InvariantUnder (@Case.HistoryChange S ι) fun C => g C.arrangement := by
  intro a b hab
  exact congrArg (fun A : Setting S ι => g A.arrangement) hab

/-- **Definition 4 (Invariance under redescription).** Whether some process identifies the state that obtains with another is invariant under relabellings. -/
theorem obtainsShared_relabels : InvariantUnder (@Case.Relabels S ι) obtainsShared := by
  have forward : ∀ a b : Case S ι, a.Relabels b → obtainsShared a → obtainsShared b := by
    rintro a b ⟨r, hr⟩ ⟨i, t, ht, hin⟩
    refine ⟨r.positions i, r.states t, ?_, ?_⟩
    · rw [← hr]
      exact fun h => ht (r.states.injective h)
    · have := (r.constitution i _).mp hin
      rwa [Sym2.map_mk, hr] at this
  rintro a b ⟨r, hr⟩
  refine propext ⟨forward a b ⟨r, hr⟩, forward b a ⟨r.symm, ?_⟩⟩
  change r.states.symm b.obtains = a.obtains
  rw [← hr, Equiv.symm_apply_apply]

/-- The coarse-graining of the witnesses over four states: it identifies states 0 and 1, and tells the rest apart. -/
def splitMap : Fin 4 → Fin 3 :=
  ![0, 0, 1, 2]

/-- The arrangement of the witnesses: two processes, each reading `splitMap`, no joins, all states accessible. -/
def splitSetting : Setting (Fin 4) Bool where
  arrangement := ⟨inferInstance, fun _ => Process.reading splitMap, ∅⟩
  accessible := Set.univ
  nonempty := ⟨0, trivial⟩

/-- The bijection of the witnesses: it swaps states 1 and 2. -/
def splitSwap : Fin 4 ≃ Fin 4 :=
  Equiv.swap 1 2

/-- A case of `splitSetting`. -/
def splitCase (s : Fin 4) : Case (Fin 4) Bool :=
  ⟨splitSetting, s, trivial⟩

/-- The case after the relabelling of the witnesses. -/
def splitRelabelled (s : Fin 4) : Case (Fin 4) Bool :=
  ⟨splitSetting.relabel splitSwap, splitSwap s, ⟨s, trivial, rfl⟩⟩

/-- The witnesses' relabelling is a relabelling alone. -/
theorem splitCase_relabels (s : Fin 4) : (splitCase s).Relabels (splitRelabelled s) :=
  ⟨Setting.relabelling splitSwap splitSetting, rfl⟩

/-- The pair the witnesses name lies in the between before the relabelling, and not after. -/
theorem betweenPair_changes :
    betweenPair s((0 : Fin 4), (1 : Fin 4)) (splitCase 0) ∧ ¬ betweenPair s((0 : Fin 4), (1 : Fin 4)) (splitRelabelled 0) := by
  constructor
  · refine ⟨by rw [Sym2.mk_isDiag_iff]; decide, fun _ => (mem_kernel splitMap _ _).mpr (by decide)⟩
  · rintro ⟨-, hall⟩
    have : (splitMap ∘ splitSwap.symm) 0 = (splitMap ∘ splitSwap.symm) 1 := (mem_kernel _ _ _).mp (hall true)
    exact absurd this (by decide)

/-- The state 0 shares its coarse value and the state 2 does not. -/
theorem obtainsShared_changes : obtainsShared (splitCase 0) ∧ ¬ obtainsShared (splitCase 2) := by
  constructor
  · exact ⟨true, 1, by decide, (mem_kernel splitMap _ _).mpr (by decide)⟩
  · rintro ⟨i, t, ht, hin⟩
    have hk : splitMap 2 = splitMap t := (mem_kernel splitMap _ _).mp hin
    have hall : ∀ t : Fin 4, t ≠ 2 → splitMap 2 ≠ splitMap t := by decide
    exact hall t ht hk

/-- **Definition 4 (Invariance under redescription), the kinds are real.** Three features over four states. The size of the between is invariant under both kinds, so by the split it factors through content.
Whether a named pair lies in the between is changed by a relabelling alone and by no change of history. Whether some process identifies the state that obtains with another is
changed by a change of history alone and by no relabelling. -/
theorem Invariance.split_kinds :
    (InvariantUnder (@Case.Relabels (Fin 4) Bool) betweenSize ∧ InvariantUnder (@Case.HistoryChange (Fin 4) Bool) betweenSize ∧
        ∃ g : Content (Fin 4) Bool → ℕ, ∀ C, betweenSize C = g C.content) ∧
      (¬ InvariantUnder (@Case.Relabels (Fin 4) Bool) (betweenPair s(0, 1)) ∧
        InvariantUnder (@Case.HistoryChange (Fin 4) Bool) (betweenPair s(0, 1))) ∧
      (InvariantUnder (@Case.Relabels (Fin 4) Bool) obtainsShared ∧
        ¬ InvariantUnder (@Case.HistoryChange (Fin 4) Bool) obtainsShared) := by
  have hsize := invariantUnder_history_of_arrangement (S := Fin 4) (ι := Bool) fun A => A.residue
  refine ⟨⟨betweenSize_relabels, hsize, (Invariance.split betweenSize).2.mp ((Invariance.split betweenSize).1.mp ⟨betweenSize_relabels, hsize⟩)⟩,
    ⟨fun h => ?_, invariantUnder_history_of_arrangement fun A => s(0, 1) ∈ A.between⟩, ⟨obtainsShared_relabels, fun h => ?_⟩⟩
  · have hsame := h _ _ (splitCase_relabels 0)
    exact betweenPair_changes.2 (hsame ▸ betweenPair_changes.1)
  · have hsame := h (splitCase 0) (splitCase 2) rfl
    exact obtainsShared_changes.2 (hsame ▸ obtainsShared_changes.1)

/-- **A case's class under relabelling, a change of history can change it.** Two cases of one arrangement, with one state obtaining in one and another in the other, can have two filings: a relabelling would carry whether some process identifies the state that obtains with another, and that differs. -/
theorem history_can_change_filing : ∃ a b : Case (Fin 4) Bool, a.HistoryChange b ∧ a.filing ≠ b.filing := by
  refine ⟨splitCase 0, splitCase 2, rfl, fun heq => ?_⟩
  have hsame := obtainsShared_relabels _ _ (Case.filing_eq_iff.mp heq)
  exact obtainsShared_changes.2 (hsame ▸ obtainsShared_changes.1)

/-- **A case's class under relabelling, the pair is not the filing.** A case's content with the state that obtains, by its name in the case's own labelling. A filing could be written so, and it fails both ways: the first part forgets the labelling, and the second is a name in that labelling (`relabelling_can_move_pair`, `one_pair_two_filings`). -/
def Case.pair (C : Case S ι) : Content S ι × S :=
  (C.content, C.obtains)

/-- **A case's class under relabelling, what a relabelling keeps of the pair.** A relabelling alone keeps its first part, the content. Its second part it can move (`relabelling_can_move_pair`). -/
theorem pair_of_relabels {a b : Case S ι} (h : a.Relabels b) : a.pair.1 = b.pair.1 := by
  obtain ⟨r, -⟩ := h
  exact Quotient.sound ⟨r⟩

/-- **A case's class under relabelling, the pair's first failure.** The pair's name is in the case's own labelling, so a relabelling can move the pair while it changes no filing. -/
theorem relabelling_can_move_pair : ∃ a b : Case (Fin 4) Bool, a.Relabels b ∧ a.pair ≠ b.pair := by
  refine ⟨splitCase 1, splitRelabelled 1, splitCase_relabels 1, fun h => ?_⟩
  have : (1 : Fin 4) = splitSwap 1 := congrArg Prod.snd h
  exact absurd this (by decide)

/-- **A case's class under relabelling, the pair's second failure.** One pair can hold two cases no relabelling connects, and a feature invariant under relabellings can differ between them. So the pair does not say which state obtains: it names a state in a labelling it has dropped. -/
theorem one_pair_two_filings :
    ∃ a b : Case (Fin 4) Bool, a.pair = b.pair ∧ a.filing ≠ b.filing ∧ obtainsShared a ∧ ¬ obtainsShared b := by
  let a : Case (Fin 4) Bool := splitCase 1
  let b : Case (Fin 4) Bool := ⟨splitSetting.relabel splitSwap, 1, ⟨2, trivial, by decide⟩⟩
  have hshared : obtainsShared a := ⟨true, 0, by decide, (mem_kernel splitMap _ _).mpr (by decide)⟩
  have hnot : ¬ obtainsShared b := by
    rintro ⟨i, t, ht, hin⟩
    have hk : (splitMap ∘ splitSwap.symm) 1 = (splitMap ∘ splitSwap.symm) t := (mem_kernel _ _ _).mp hin
    have hall : ∀ t : Fin 4, t ≠ 1 → (splitMap ∘ splitSwap.symm) 1 ≠ (splitMap ∘ splitSwap.symm) t := by decide
    exact hall t ht hk
  refine ⟨a, b, ?_, fun heq => ?_, hshared, hnot⟩
  · have hc : a.content = b.content := Quotient.sound ⟨Setting.relabelling splitSwap splitSetting⟩
    exact Prod.ext hc rfl
  · have hsame := obtainsShared_relabels a b (Case.filing_eq_iff.mp heq)
    exact hnot (hsame ▸ hshared)

/-- The setting of the witnesses that a filing holds a state only up to relabelling: one process on two states, telling them apart and responding with which obtains, and both accessible. -/
def bitSetting : Setting Bool Unit :=
  ⟨⟨inferInstance, fun _ => Process.reading id, ∅⟩, Set.univ, ⟨false, trivial⟩⟩

/-- A case of `bitSetting`. -/
def bitCase (b : Bool) : Case Bool Unit :=
  ⟨bitSetting, b, trivial⟩

/-- What `bitSetting`'s process holds: exactly the quantities that tell the two states apart. -/
theorem bit_holds_iff {Q : Type} (q : Bool → Q) :
    (Process.reading (id : Bool → Bool)).Holds Set.univ q ↔ Function.Injective q := by
  constructor
  · rintro ⟨-, hfix, -⟩ s t hst
    exact hfix s trivial t trivial hst
  · intro hq
    refine ⟨⟨fun v => q (v ()), rfl⟩, fun s _ t _ hst => congrArg (Process.reading (id : Bool → Bool)).response (hq hst), false, trivial, true, trivial, fun h => Bool.false_ne_true (hq h), Bool.false_ne_true⟩

/-- **A case's class under relabelling, a relabelling of a setting onto itself.** The swap of the two states relabels `bitSetting` onto itself: a relabelling carries kernels and held quantities and not the names of values, and the swap keeps what the process identifies and holds. -/
def bitRelabelling : Relabelling bitSetting bitSetting where
  states := Equiv.swap false true
  positions := Equiv.refl Unit
  accessible := fun _ => Iff.rfl
  constitution := fun _ z => by
    induction z with
    | _ s t =>
      change s(s, t) ∈ kernel (id : Bool → Bool) ↔ s(Equiv.swap false true s, Equiv.swap false true t) ∈ kernel (id : Bool → Bool)
      rw [mem_kernel, mem_kernel]
      exact (Equiv.swap false true).injective.eq_iff.symm
  held := fun _ {Q} q => by
    change (Process.reading (id : Bool → Bool)).Holds Set.univ q ↔ (Process.reading (id : Bool → Bool)).Holds Set.univ (q ∘ (Equiv.swap false true).symm)
    rw [bit_holds_iff, bit_holds_iff]
    exact (Equiv.swap false true).symm.injective_comp q |>.symm
  joins := fun _ hj => hj.elim
  joins_onto := fun _ hj => hj.elim

/-- **A case's class under relabelling, one filing, two states.** Two cases of one setting, with two different states obtaining that its process tells apart, have one filing: a change of history that changes no filing. -/
theorem one_filing_two_states :
    (bitCase false).HistoryChange (bitCase true) ∧ (bitCase false).obtains ≠ (bitCase true).obtains ∧
      s((bitCase false).obtains, (bitCase true).obtains) ∉ ((bitCase false).arrangement.process ()).constitution ∧
      (bitCase false).filing = (bitCase true).filing :=
  ⟨rfl, Bool.false_ne_true, fun hin => Bool.false_ne_true ((mem_kernel id false true).mp hin),
    Case.filing_eq_iff.mpr ⟨bitRelabelling, rfl⟩⟩

/-- **A case's class under relabelling, it does not say which.** No map from filings gives the state that obtains, since one filing holds two cases with two states. -/
theorem filing_does_not_say_which :
    ¬ ∃ g : Filing Bool Unit → Bool, ∀ C : Case Bool Unit, g C.filing = C.obtains := by
  rintro ⟨g, hg⟩
  have h := one_filing_two_states.2.2.2
  have h0 := hg (bitCase false)
  have h1 := hg (bitCase true)
  rw [h] at h0
  exact Bool.false_ne_true (h0.symm.trans h1)

/-! ## What a content reads -/

/-- **Definition 4 (Invariance under redescription).** Two settings with one family of processes and one accessible set, differing in `joins` alone, are not of one content: a relabelling carries each join onto another, and on one side there is none. So `Arrangement.joins` is data a content reads. -/
theorem content_reads_joins :
    ∃ A B : Setting Bool Bool, A.arrangement.process = B.arrangement.process ∧ A.accessible = B.accessible ∧ ¬ OneContent A B := by
  let p : Process Bool := Process.reading id
  let j : Join (fun _ : Bool => p) := ⟨true, false, Bool.false_ne_true, (), (), id, fun _ => rfl⟩
  let A : Setting Bool Bool := ⟨⟨inferInstance, fun _ => p, {j}⟩, Set.univ, ⟨true, trivial⟩⟩
  let B : Setting Bool Bool := ⟨⟨inferInstance, fun _ => p, ∅⟩, Set.univ, ⟨true, trivial⟩⟩
  refine ⟨A, B, rfl, rfl, ?_⟩
  rintro ⟨r⟩
  obtain ⟨_, hj, _⟩ := r.joins j rfl
  exact hj

/-- **The content, positions count.** Two arrangements of one content have as many positions, matched one to one. -/
theorem OneContent.positions {A : Setting S ι} {B : Setting S' ι'} (h : OneContent A B) : Nonempty (ι ≃ ι') :=
  h.elim fun r => ⟨r.positions⟩

/-- **Definition 4 (Invariance under redescription).** A process alone, and the same process beside an absent one, are not of one content, though the absent one tells nothing apart: the positions are matched one to one, and there are one and two. -/
theorem absent_changes_content (p : Process S) (s : S) :
    ¬ OneContent (⟨⟨inferInstance, fun _ : Unit => p, ∅⟩, Set.univ, ⟨s, trivial⟩⟩ : Setting S Unit)
      (⟨⟨inferInstance, fun b : Bool => cond b p Process.absent, ∅⟩, Set.univ, ⟨s, trivial⟩⟩ : Setting S Bool) := fun h =>
  (OneContent.positions h).elim fun e => Bool.false_ne_true (e.symm.injective (Subsingleton.elim _ _))

/-- **Definition 4 (Invariance under redescription).** A process alone, and the same process held at two positions, are not of one content, as the positions are matched one to one. -/
theorem held_twice_changes_content (p : Process S) (s : S) :
    ¬ OneContent (⟨⟨inferInstance, fun _ : Unit => p, ∅⟩, Set.univ, ⟨s, trivial⟩⟩ : Setting S Unit)
      (⟨⟨inferInstance, fun _ : Bool => p, ∅⟩, Set.univ, ⟨s, trivial⟩⟩ : Setting S Bool) := fun h =>
  (OneContent.positions h).elim fun e => Bool.false_ne_true (e.symm.injective (Subsingleton.elim _ _))

/-- **An arrangement, a join is between positions.** `Join.another` says two positions, and they may hold one process: here one process held twice has a join of itself to itself, with a map that is not constant. -/
theorem join_of_one_process_held_twice :
    ∃ j : Join (fun _ : Bool => (Process.reading (id : Bool → Bool))), ∃ x y, j.further x ≠ j.further y :=
  ⟨⟨true, false, Bool.false_ne_true, (), (), id, fun _ => rfl⟩, false, true, Bool.false_ne_true⟩

end Companion
