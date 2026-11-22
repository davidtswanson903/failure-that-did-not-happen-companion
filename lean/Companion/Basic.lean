import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Sym.Sym2

/-!
# The objects

Every object the theorems name, defined once: the states and what obtains, a
coarse-graining with its kernel and what it carries, a process with its constitution and its response, an arrangement
with its joins and its between, a nested arrangement and its levels, a change with its price and its release, the
accessible states with following and holding, the forestalled state, and the outcome.

A pair of states is unordered, an element of `Sym2 S`, so that a size counts each pair once. A kernel holds the diagonal,
as the kernel of a function does, and `residue` and the between count only pairs of distinct states: eight states have
twenty-eight pairs. The values of a coarse-graining and of a quantity live in `Type`: on a finite `S` the kernels are the
content, and every kernel is that of a map into a type of `Type`.

The objects are built so that each law holds of them by construction. A coarse-graining a process makes is defined by composition with
the map it is constituted to make, its response by a rule on its coarse-grainings' values, and evaluation by reading the state that obtains. `Companion.Laws` states the three
laws as theorems, and each proof unfolds one of these definitions. That real arrangements are such objects is identification, which no definition or proof here touches.
-/

namespace Companion

variable {S : Type}

/-! ## States, and what obtains -/

/-- **The states, The forestalled state.** A situation over the states: the one state that obtains, and the
state that would have obtained. The states themselves are a type `S`, finite wherever a theorem uses that it is. -/
@[ext]
structure Situation (S : Type) where
  /-- The state that obtains. Exactly one obtains in a situation. -/
  obtains : S
  /-- The state that would have obtained. -/
  wouldHave : S

/-- **The forestalled state.** The state that would have obtained is forestalled when it does not obtain. -/
def Situation.Forestalled (w : Situation S) : Prop :=
  w.wouldHave ≠ w.obtains

/-- **The forestalled state.** A quantity of a situation depends on a forestalled state when its value changes with
that state while the state that obtains stays the same. -/
def DependsOnForestalled {Q : Type} (F : Situation S → Q) : Prop :=
  ∃ w w' : Situation S, w.Forestalled ∧ w'.Forestalled ∧ w.obtains = w'.obtains ∧ F w ≠ F w'

/-- **The states.** A coarse-graining is evaluated in a situation by reading it at the state that obtains. -/
def evaluate {C : Type} (c : S → C) (w : Situation S) : C :=
  c w.obtains

/-! ## Coarse-grainings, kernels and what they carry -/

/-- **Definition 2 (What a party registers).** The kernel of a coarse-graining `c : S → C` is the set of pairs of states it identifies:
`s(s, t) ∈ kernel c` exactly when `c s = c t` (`mem_kernel`). -/
def kernel {C : Type} (c : S → C) : Set (Sym2 S) :=
  {z | (z.map c).IsDiag}

/-- A pair is in the kernel exactly when the coarse-graining gives its two states one value. -/
@[simp]
theorem mem_kernel {C : Type} (c : S → C) (s t : S) : s(s, t) ∈ kernel c ↔ c s = c t :=
  Sym2.mk_isDiag_iff

/-- The kernel is Mathlib's kernel of a function, `Setoid.ker`, read on unordered pairs. -/
theorem mem_kernel_iff_ker {C : Type} (c : S → C) (s t : S) : s(s, t) ∈ kernel c ↔ Setoid.ker c s t :=
  mem_kernel c s t

/-- **Definition 2 (What a party registers).** A coarse-graining `c` carries a quantity `q` when `q` factors through it, `q = h ∘ c`. -/
def Carries {C Q : Type} (c : S → C) (q : S → Q) : Prop :=
  ∃ h : C → Q, q = h ∘ c

/-- A quantity separates a pair when it gives the pair's two states different values. -/
def Separates {Q : Type} (q : S → Q) (z : Sym2 S) : Prop :=
  z ∉ kernel q

/-- **Residue.** The pairs of distinct states in a set of pairs, the pairs a size counts. -/
def distinctPairs (X : Set (Sym2 S)) : Set (Sym2 S) :=
  {z | z ∈ X ∧ ¬ z.IsDiag}

/-- **Residue.** The size of residue for a coarse-graining: the number of pairs of distinct states in its
kernel. A size is `Set.ncard`, which is the count on a finite `S`. -/
noncomputable def residue {C : Type} (c : S → C) : ℕ :=
  (distinctPairs (kernel c)).ncard

/-- **Definition 2 (What a party registers).** A coarse-graining as a value: a map from the states with the type of its values, for a
process that makes several. -/
structure CoarseGraining (S : Type) where
  /-- The type of its values. -/
  Value : Type
  /-- The map from the states. -/
  map : S → Value

instance : CoeFun (CoarseGraining S) (fun c => S → c.Value) :=
  ⟨CoarseGraining.map⟩

/-! ## Processes and responses -/

/-- **Definition 1 (Party).** A process: the one coarse-graining it is constituted to make, each further
coarse-graining it makes, as a map of that one's values, and the rule by which its response is a function of those coarse-grainings' values.

"Its coarse-grainings" means one family here. A process that responds through a coarse-graining another makes has taken it up, and then makes
a coarse-graining of its values itself (`Join`), which is a map of its own constitutive values or it cannot make it. A process that only makes has a
constant response; one that only responds makes nothing but what it responds through. -/
structure Process (S : Type) where
  /-- The coarse-graining it is constituted to make. -/
  constitutive : CoarseGraining S
  /-- What indexes its coarse-grainings. -/
  Index : Type
  /-- The values of each of its coarse-grainings. -/
  Value : Index → Type
  /-- Each of its coarse-grainings, as a map of the values of the one it is constituted to make. -/
  further : ∀ i, constitutive.Value → Value i
  /-- The values of its response. -/
  Action : Type
  /-- Its response, as a function of its coarse-grainings' values. -/
  rule : (∀ i, Value i) → Action

/-- **Definition 1 (Party).** A coarse-graining a process makes: a further map composed with the one it is constituted to make. -/
def Process.grainings (p : Process S) (i : p.Index) : CoarseGraining S :=
  ⟨p.Value i, p.further i ∘ p.constitutive⟩

/-- **Definition 1 (Party).** The constitution of a process: the kernel of the coarse-graining it is constituted to
make, the pairs it is not constituted to tell apart. -/
def Process.constitution (p : Process S) : Set (Sym2 S) :=
  kernel p.constitutive

/-- **Definition 1 (Party).** All of a process's coarse-grainings read together: the tuple of their values. -/
def Process.jointly (p : Process S) : S → ∀ i, p.Value i :=
  fun s i => p.grainings i s

/-- **Definition 1 (Party).** The response of a process, a quantity belonging to it: its rule applied to the values of its coarse-grainings. -/
def Process.response (p : Process S) : S → p.Action :=
  fun s => p.rule (p.jointly s)

/-- **Definition 2 (What a party registers).** A process's coarse-grainings carry a quantity when it factors through them, read
together. -/
def Process.Carries {Q : Type} (p : Process S) (q : S → Q) : Prop :=
  Companion.Carries p.jointly q

/-- **A change.** A process absent from an arrangement tells nothing apart in it: every pair is in its
constitution (`constitution_absent`). It makes nothing and its response is constant, which the word "absent" asks for, and which Definition 1 (Party)'s "makes a coarse-graining, responds through one, or both" does not describe.
Every universal statement holds of such a process too, and no existence statement has one as its witness, except `absent_changes_content`, where the word is the point. -/
def Process.absent : Process S where
  constitutive := ⟨Unit, fun _ => ()⟩
  Index := Empty
  Value := Empty.elim
  further := fun e => e.elim
  Action := Unit
  rule := fun _ => ()

/-- An absent process's constitution is every pair. -/
theorem constitution_absent : (Process.absent : Process S).constitution = Set.univ := by
  ext z
  induction z with
  | _ s t => simp [Process.constitution, Process.absent]

/-- The same process making one more coarse-graining, a map `f` of the values of the one it is constituted to make, with nothing else about it
moved. A coarse-graining another process makes reaches it this way in this encoding, which is how the encoding is built: all a process makes is a map of its constitutive values. -/
def Process.takeUp {V : Type} (p : Process S) (f : p.constitutive.Value → V) : Process S where
  constitutive := p.constitutive
  Index := Option p.Index
  Value := fun o => match o with
    | none => V
    | some i => p.Value i
  further := fun o v => match o with
    | none => f v
    | some i => p.further i v
  Action := p.Action
  rule := fun v => p.rule fun i => v (some i)

/-- The same process with another rule, so another response: its constitution and its coarse-grainings stay, the change of
Claim 12 (Change by attachment). -/
def Process.withRule {A : Type} (p : Process S) (g : (∀ i, p.Value i) → A) : Process S where
  constitutive := p.constitutive
  Index := p.Index
  Value := p.Value
  further := p.further
  Action := A
  rule := g

/-- A process that makes one coarse-graining and is constituted to make it, and whose response is that coarse-graining's value. -/
def Process.reading {V : Type} (c : S → V) : Process S where
  constitutive := ⟨V, c⟩
  Index := Unit
  Value := fun _ => V
  further := fun _ => id
  Action := V
  rule := fun v => v ()

/-- Every pair is in the kernel of a constant map. -/
theorem mem_kernel_const {V : Type} (v : V) (z : Sym2 S) : z ∈ kernel (fun _ : S => v) := by
  induction z with
  | _ s t => exact (mem_kernel _ s t).mpr rfl

/-- A process that tells nothing apart: it makes one coarse-graining, a constant one, and responds through it. Unlike `Process.absent`, it makes something. -/
def Process.blank : Process S :=
  Process.reading fun _ => ()

/-- A process that tells nothing apart identifies every pair. -/
theorem mem_constitution_blank (z : Sym2 S) : z ∈ (Process.blank : Process S).constitution :=
  mem_kernel_const () z

/-! ## Arrangements, joins and the between -/

/-- **An arrangement.** A join: one process making a coarse-graining of the values of a coarse-graining that
another process makes. -/
structure Join {ι : Type} (process : ι → Process S) where
  /-- The process that makes the new coarse-graining, which takes the other's up. -/
  taker : ι
  /-- The process that makes the coarse-graining taken up. -/
  giver : ι
  /-- A join is between two processes. -/
  another : giver ≠ taker
  /-- The coarse-graining the giver makes. -/
  source : (process giver).Index
  /-- The coarse-graining the taker makes. -/
  made : (process taker).Index
  /-- The map from the source's values to the values of what the taker makes. -/
  further : ((process giver).grainings source).Value → ((process taker).grainings made).Value
  /-- What the taker makes is that map of the source's values. -/
  made_eq : ∀ s, (process taker).grainings made s = further ((process giver).grainings source s)

/-- **An arrangement.** An arrangement: a finite set of processes over the states, with its joins. The processes
are a family over a finite type of positions, so that one process can be followed through a change. -/
structure Arrangement (S ι : Type) where
  /-- The set of processes is finite. -/
  finite : Finite ι
  /-- The process at each position. A position may hold `Process.absent`. -/
  process : ι → Process S
  /-- Its joins. -/
  joins : Set (Join process)

/-- **Claim 9 (The between).** The between of an arrangement: the pairs of distinct states that no process in it is
constituted to tell apart. It reads the constitutions and ignores the joins. -/
def Arrangement.between {ι : Type} (A : Arrangement S ι) : Set (Sym2 S) :=
  {z | ¬ z.IsDiag ∧ ∀ i, z ∈ (A.process i).constitution}

/-- **Residue.** The size of residue for an arrangement: the size of its between. -/
noncomputable def Arrangement.residue {ι : Type} (A : Arrangement S ι) : ℕ :=
  A.between.ncard

/-- **A change.** A rule for each position of an arrangement, with the values it gives: what a change of responses alone chooses. -/
abbrev Arrangement.Rules {ι : Type} (A : Arrangement S ι) : Type 1 :=
  ∀ j, Σ B : Type, ((∀ k, (A.process j).Value k) → B)

/-- **An arrangement.** A join stands through a change of rules: it reads coarse-grainings only, and those stay. -/
def Join.withRules {ι : Type} {process : ι → Process S} (σ : ∀ j, Σ B : Type, ((∀ k, (process j).Value k) → B)) (j : Join process) :
    Join (fun k => (process k).withRule (σ k).2) where
  taker := j.taker
  giver := j.giver
  another := j.another
  source := j.source
  made := j.made
  further := j.further
  made_eq := j.made_eq

/-- **A change.** The same arrangement with new rules: at each position the same process with another response, its
constitution and its coarse-grainings staying, and the same joins. -/
def Arrangement.withRules {ι : Type} (A : Arrangement S ι) (σ : A.Rules) : Arrangement S ι where
  finite := A.finite
  process := fun j => (A.process j).withRule (σ j).2
  joins := Join.withRules σ '' A.joins

open Classical in
/-- **A change.** The rules that give one position the rule `g` and leave every other position its own. -/
noncomputable def Arrangement.rulesAt {ι : Type} (A : Arrangement S ι) (i : ι) {B : Type} (g : (∀ k, (A.process i).Value k) → B) : A.Rules :=
  Function.update (fun j => ⟨(A.process j).Action, (A.process j).rule⟩) i ⟨B, g⟩

/-! ## Nesting and levels -/

/-- **An arrangement.** A nested arrangement: an arrangement, the process it is as a member of the level above,
and, for each of its positions, the nested arrangement that position's process is, if it is one. An arrangement nests when
some of its processes are arrangements. The definition leaves open what constitution an arrangement has as a process, so
`self` is data, and whether it is composed from its members' is a hypothesis of the theorems that need it. -/
inductive Nested (S : Type) : Type 1
  /-- `self` is the arrangement as a process; `level` its processes and joins; `inner i` what position `i` is. -/
  | mk (self : Process S) {ι : Type} (level : Arrangement S ι) (inner : ι → Option (Nested S)) : Nested S

/-- The process a nested arrangement is at the level above. -/
def Nested.self : Nested S → Process S
  | .mk self _ _ => self

/-- The between of a nested arrangement, at its own level. -/
def Nested.between : Nested S → Set (Sym2 S)
  | .mk _ level _ => level.between

/-- **An arrangement.** Each depth of nesting is a level: `AtDepth n d m` says `m` is a nested arrangement at
depth `d` of `n`, with `n` itself at depth zero. -/
inductive Nested.AtDepth : Nested S → ℕ → Nested S → Prop
  /-- A nested arrangement is at depth zero of itself. -/
  | here (n : Nested S) : Nested.AtDepth n 0 n
  /-- What is at depth `d` of a member is at depth `d + 1` of the arrangement. -/
  | inside {self : Process S} {ι : Type} {level : Arrangement S ι} {inner : ι → Option (Nested S)} {i : ι}
      {member m : Nested S} {d : ℕ} (hi : inner i = some member) (hm : Nested.AtDepth member d m) :
      Nested.AtDepth (.mk self level inner) (d + 1) m

/-- A nested arrangement hangs together when each position that is a nested arrangement holds the process that arrangement is,
all the way in. -/
inductive Nested.Coherent : Nested S → Prop
  /-- Each inner arrangement is the process at its position, and hangs together. -/
  | mk {self : Process S} {ι : Type} {level : Arrangement S ι} {inner : ι → Option (Nested S)}
      (hself : ∀ i n, inner i = some n → n.self = level.process i)
      (hinner : ∀ i n, inner i = some n → Nested.Coherent n) :
      Nested.Coherent (.mk self level inner)

/-- A process stands at a nested arrangement's own level when some position there holds it. -/
def Nested.HoldsProcess : Nested S → Process S → Prop
  | .mk _ level _, q => ∃ i, level.process i = q

/-- **Claim 9 (The between), An arrangement.** The between at a level, each depth of nesting being a level: the pairs of
distinct states no process at that depth is constituted to tell apart, across every nested arrangement at that depth. -/
def Nested.betweenAt (n : Nested S) (d : ℕ) : Set (Sym2 S) :=
  {z | ¬ z.IsDiag ∧ ∀ m, n.AtDepth d m → ∀ p, m.HoldsProcess p → z ∈ p.constitution}

/-- **An arrangement.** A nested arrangement is composed from a member's coarse-graining when that member stands at its
own level and the arrangement, as a process, is constituted to tell apart exactly what the member is. The definition leaves open
what constitution an arrangement has as a process, so this is one way of fixing it, read through the kernel: the two coarse-grainings may differ in the
names of their values. -/
def Nested.ComposedFrom (n : Nested S) (p : Process S) : Prop :=
  n.HoldsProcess p ∧ n.self.constitution = p.constitution

/-- **An arrangement.** A nested arrangement is composed from a member's response when that member stands at its own
level and the arrangement, as a process, is constituted to tell apart exactly what the member's response tells apart. -/
def Nested.ComposedFromResponse (n : Nested S) (p : Process S) : Prop :=
  n.HoldsProcess p ∧ n.self.constitution = kernel p.response

/-- **An arrangement.** A nested arrangement is composed from all its members together when, as a process, it identifies
exactly the pairs every process at its own level is constituted to identify. -/
def Nested.ComposedFromAll : Nested S → Prop
  | .mk self level _ => ∀ z, z ∈ self.constitution ↔ ∀ i, z ∈ (level.process i).constitution

/-- **An arrangement.** A nested arrangement is composed from all its members' responses together when, as a process, it
identifies exactly the pairs no response at its own level separates. -/
def Nested.ComposedFromAllResponses : Nested S → Prop
  | .mk self level _ => ∀ z, z ∈ self.constitution ↔ ∀ i, z ∈ kernel (level.process i).response

/-! ## Accessible states, following, holding -/

/-- **The accessible states.** The accessible states: those that can obtain under the present constraints, as a set of
states. A statement made across them is quantified over them, and so says nothing of the other states. -/
abbrev Accessible (S : Type) : Type :=
  Set S

/-- **Definition 3 (Holding a loss).** Across the accessible states, the quantity `q` fixes the quantity `a`: states of `X` that `q`
gives one value, `a` gives one value. -/
def Fixes {Q A : Type} (X : Accessible S) (q : S → Q) (a : S → A) : Prop :=
  ∀ s ∈ X, ∀ t ∈ X, q s = q t → a s = a t

/-- **Definition 3 (Holding a loss).** Across the accessible states, `a` varies with `q`: at some two of them both differ. -/
def VariesWith {A Q : Type} (X : Accessible S) (a : S → A) (q : S → Q) : Prop :=
  ∃ s ∈ X, ∃ t ∈ X, q s ≠ q t ∧ a s ≠ a t

/-- **Definition 3 (Holding a loss).** A response follows a quantity across the accessible states when, across them, the quantity
fixes the response and the response varies with it. -/
def Follows {A Q : Type} (X : Accessible S) (a : S → A) (q : S → Q) : Prop :=
  Fixes X q a ∧ VariesWith X a q

/-- **Definition 3 (Holding a loss).** A process holds a quantity when its coarse-grainings carry the quantity and its response
follows it. It is stated without sign. -/
def Process.Holds {Q : Type} (p : Process S) (X : Accessible S) (q : S → Q) : Prop :=
  p.Carries q ∧ Follows X p.response q

/-! ## Changes, price and release -/

/-- **A change.** A change compares two arrangements over the same accessible states, or one arrangement over
two sets of accessible states, which is a change of the world. Both arrangements have the same positions, so that one
process is followed through the change, and a position may hold `Process.absent`. -/
structure Change (S ι : Type) where
  /-- The arrangement before. -/
  before : Arrangement S ι
  /-- The arrangement after. -/
  after : Arrangement S ι
  /-- The accessible states before. -/
  accessibleBefore : Accessible S
  /-- The accessible states after. -/
  accessibleAfter : Accessible S
  /-- Either the accessible states stay, or the arrangement stays. -/
  kind : accessibleBefore = accessibleAfter ∨ before = after

/-- **Claim 11 (Change by refinement).** The price of a change at a process: the set of pairs it comes to tell apart. -/
def Change.price {ι : Type} (ch : Change S ι) (i : ι) : Set (Sym2 S) :=
  {z | z ∈ (ch.before.process i).constitution ∧ z ∉ (ch.after.process i).constitution}

/-- **Claim 11 (Change by refinement).** The release of a change at a process: the set of pairs it stops telling apart. -/
def Change.release {ι : Type} (ch : Change S ι) (i : ι) : Set (Sym2 S) :=
  {z | z ∈ (ch.after.process i).constitution ∧ z ∉ (ch.before.process i).constitution}

/-- **A change.** A change that leaves every constitution: at every position the process identifies what it did, whatever else about it moves, the names of its values among them. -/
def Change.ConstitutionsStay {ι : Type} (ch : Change S ι) : Prop :=
  ∀ i, (ch.after.process i).constitution = (ch.before.process i).constitution

/-- **Claim 12 (Change by attachment).** A change of response only, none of a process's coarse-grainings changing: the accessible states
stay, and the arrangement after is the arrangement before with new rules. -/
def Change.ResponseOnly {ι : Type} (ch : Change S ι) : Prop :=
  ch.accessibleBefore = ch.accessibleAfter ∧ ∃ σ : ch.before.Rules, ch.after = ch.before.withRules σ

/-- **Claim 12 (Change by attachment).** The change of an arrangement that gives one position the rule `g`, over one set of accessible
states. -/
noncomputable def Change.ofRule {ι : Type} (A : Arrangement S ι) (i : ι) {B : Type} (g : (∀ k, (A.process i).Value k) → B)
    (X : Accessible S) : Change S ι where
  before := A
  after := A.withRules (A.rulesAt i g)
  accessibleBefore := X
  accessibleAfter := X
  kind := Or.inl rfl

/-! ## Outcomes -/

/-- **An outcome.** An outcome is a set of states. -/
abbrev Outcome (S : Type) : Type :=
  Set S

/-- **An outcome.** What a response that only forbids or allows does at a state. -/
inductive Verdict : Type
  /-- It forbids. -/
  | forbid
  /-- It allows. -/
  | allow
  deriving DecidableEq

/-- **An outcome.** A response excludes an outcome when it forbids at every state in it. -/
def Excludes (a : S → Verdict) (O : Outcome S) : Prop :=
  ∀ s ∈ O, a s = Verdict.forbid

/-- **An outcome.** An arrangement whose responses only forbid or allow: each value of each process's response
is read as one or the other. -/
structure ForbidAllow (S ι : Type) extends Arrangement S ι where
  /-- What each value of a process's response does. -/
  verdict : ∀ i, (process i).Action → Verdict

/-- The response of the process at a position, as forbidding or allowing. -/
def ForbidAllow.responseAt {ι : Type} (F : ForbidAllow S ι) (i : ι) : S → Verdict :=
  fun s => F.verdict i ((F.process i).response s)

/-- **An outcome.** An arrangement whose responses only forbid or allow reaches an outcome when at some state in
it none of its responses forbids. -/
def ForbidAllow.Reaches {ι : Type} (F : ForbidAllow S ι) (O : Outcome S) : Prop :=
  ∃ s ∈ O, ∀ i, F.responseAt i s ≠ Verdict.forbid

end Companion
