import Companion.Responses
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod

/-!
# The compositions

Claim 1 (Inherited, not emergent), Claim 9 (The between), Claim 11 (Change by refinement) and Claim 12 (Change by attachment): what
holds of a coarse-graining composed from others, of what no process in an arrangement tells apart, of a change of an
arrangement, and of a change of response alone.

The route: a function of values identifies what all those values identify, which is nesting. Every pair in the between lies
in each constitution, so by `Law.constitution` in each coarse-graining and by silence in each response, which is the first
half of the between. For the second, with the positions free, a pair of distinct states in a process's constitution either lies in the between, and a process that
tells everything apart set beside it takes the pair out, or does not, and the process standing alone puts it in. Balance is a statement
about sets: a pair of distinct states leaves the between only if it leaves some constitution, and enters only if it enters
one; no law is used. Attachment is `Law.factorization` read both ways: a response is a carried quantity, and a
carried quantity can be made the response, by a change that gives the process another rule and moves nothing else.
-/

namespace Companion

variable {S : Type}

/-! ## Nesting -/

/-- **Claim 1 (Inherited, not emergent).** A coarse-graining composed from finer coarse-grainings separates no pair that all of them
identify. -/
theorem Composition.nesting {κ : Type} {C : κ → Type} {D : Type} (cs : ∀ k, S → C k) (h : (∀ k, C k) → D) :
    (⋂ k, kernel (cs k)) ⊆ kernel (fun s => h (fun k => cs k s)) := by
  intro z hz
  induction z with
  | _ s t =>
    have hall : ∀ k, cs k s = cs k t := fun k => (mem_kernel (cs k) s t).mp (Set.mem_iInter.mp hz k)
    exact (mem_kernel _ s t).mpr (congrArg h (funext hall))

/-! ## The between -/

/-- **Claim 3 (Silence).** A process that tells every two states apart: it reads which state obtains, and responds with it. It is what shows that the between does not belong to any one process. -/
def Process.discrete : Process S :=
  Process.reading id

/-- **Claim 3 (Silence).** The constitution of the process that tells everything apart holds the diagonal alone. -/
theorem not_mem_constitution_discrete {z : Sym2 S} (hz : ¬ z.IsDiag) : z ∉ (Process.discrete : Process S).constitution := by
  induction z with
  | _ s t =>
    intro hin
    exact hz (Sym2.mk_isDiag_iff.mpr ((mem_kernel id s t).mp hin))

/-- The first step of the second clause: beside any process that stands, set the process that tells everything apart. Where the between was not
empty, the new arrangement has another between. -/
theorem exists_between_ne {ι : Type} (A : Arrangement S ι) {i j : ι} (hji : j ≠ i) (hne : A.between.Nonempty) :
    ∃ A' : Arrangement S ι, A'.process i = A.process i ∧ A'.between ≠ A.between := by
  classical
  obtain ⟨z, hz⟩ := hne
  let A' : Arrangement S ι := ⟨A.finite, Function.update A.process j Process.discrete, ∅⟩
  have hj : A'.process j = Process.discrete := Function.update_self j Process.discrete A.process
  have hk : ∀ k, k ≠ j → A'.process k = A.process k := fun k hk => Function.update_of_ne hk Process.discrete A.process
  refine ⟨A', hk i hji.symm, fun heq => ?_⟩
  have hz' : z ∈ A'.between := heq ▸ hz
  have hin := hz'.2 j
  rw [hj] at hin
  exact not_mem_constitution_discrete hz.1 hin

/-- The second step of the second clause: beside a process that stands, make every other tell nothing apart. A pair of distinct states in its constitution then
lies in the new between, so where it was not in the old between the new arrangement has another between. -/
theorem exists_between_ne_of_not_mem {ι : Type} (A : Arrangement S ι) {i : ι} {z : Sym2 S} (hd : ¬ z.IsDiag)
    (hin : z ∈ (A.process i).constitution) (hout : z ∉ A.between) :
    ∃ A' : Arrangement S ι, A'.process i = A.process i ∧ A'.between ≠ A.between := by
  classical
  let A' : Arrangement S ι := ⟨A.finite, Function.update (fun _ => Process.blank) i (A.process i), ∅⟩
  have hi : A'.process i = A.process i := Function.update_self i (A.process i) (fun _ => Process.blank)
  have hk : ∀ k, k ≠ i → A'.process k = Process.blank := fun k hk =>
    Function.update_of_ne hk (A.process i) (fun _ => Process.blank)
  refine ⟨A', hi, fun heq => hout (heq ▸ (⟨hd, fun k => ?_⟩ : z ∈ A'.between))⟩
  by_cases hki : k = i
  · subst hki
    rw [hi]
    exact hin
  · rw [hk k hki]
    exact mem_constitution_blank z

/-- **Claim 9 (The between).** The second clause does not need a between that is not empty: on two states, a process that tells
nothing apart stands beside one that tells them apart, so the between is empty, and another arrangement with the first process
standing has another between. -/
theorem exists_between_ne_of_empty :
    ∃ (S ι : Type) (_ : Fintype S) (A : Arrangement S ι) (i j : ι),
      j ≠ i ∧ A.between = ∅ ∧ ∃ A' : Arrangement S ι, A'.process i = A.process i ∧ A'.between ≠ A.between := by
  let A : Arrangement Bool Bool :=
    ⟨inferInstance, fun b => cond b (Process.reading fun _ => ()) (Process.reading id), ∅⟩
  have hd : ¬ (s(false, true) : Sym2 Bool).IsDiag := by simp [Sym2.mk_isDiag_iff]
  have hempty : A.between = ∅ := by
    ext z
    induction z with
    | _ s t =>
      constructor
      · rintro ⟨hz, hall⟩
        exact hz (Sym2.mk_isDiag_iff.mpr ((mem_kernel id s t).mp (hall false)))
      · exact fun h => absurd h (Set.notMem_empty _)
  refine ⟨Bool, Bool, inferInstance, A, true, false, Bool.false_ne_true, hempty, ?_⟩
  refine exists_between_ne_of_not_mem A (z := s(false, true)) hd ((mem_kernel (fun _ : Bool => ()) _ _).mpr rfl) ?_
  rw [hempty]
  exact Set.notMem_empty _

/-- **Claim 9 (The between), its second clause, the positions free.** Over any arrangement, some arrangement over some finite positions with the same process standing has another between, exactly when that process's constitution holds a pair of distinct states. So the only exception is a process that tells everything apart, which fixes the between, empty, in every arrangement that holds it. -/
theorem exists_between_ne_over_positions_iff {ι : Type} (A : Arrangement S ι) (i : ι) :
    (∃ (κ : Type) (A' : Arrangement S κ) (k : κ), A'.process k = A.process i ∧ A'.between ≠ A.between) ↔
      ∃ z, ¬ z.IsDiag ∧ z ∈ (A.process i).constitution := by
  constructor
  · rintro ⟨κ, A', k, hk, hne⟩
    by_contra hnone
    push Not at hnone
    have hA : A.between = ∅ := Set.eq_empty_of_forall_notMem fun z hz => hnone z hz.1 (hz.2 i)
    have hA' : A'.between = ∅ := Set.eq_empty_of_forall_notMem fun z hz => hnone z hz.1 (hk ▸ hz.2 k)
    exact hne (hA'.trans hA.symm)
  · rintro ⟨z, hd, hin⟩
    by_cases hz : z ∈ A.between
    · refine ⟨Bool, ⟨inferInstance, fun b => cond b (A.process i) Process.discrete, ∅⟩, true, rfl, fun heq => ?_⟩
      have hz' : z ∈ (⟨inferInstance, fun b => cond b (A.process i) Process.discrete, ∅⟩ : Arrangement S Bool).between := heq ▸ hz
      exact not_mem_constitution_discrete hd (hz'.2 false)
    · refine ⟨Unit, ⟨inferInstance, fun _ => A.process i, ∅⟩, (), rfl, fun heq => hz ?_⟩
      have hz' : z ∈ (⟨inferInstance, fun _ => A.process i, ∅⟩ : Arrangement S Unit).between := ⟨hd, fun _ => hin⟩
      exact heq ▸ hz'

/-- **Claim 9 (The between).** No response at an arrangement's own level separates a pair in its between, and the between belongs to the
arrangement, not to a process in it, unless that process tells every pair apart: some arrangement over some finite positions with that process standing has another between, exactly where its constitution holds a pair of distinct states. -/
theorem Composition.between {ι : Type} (A : Arrangement S ι) :
    (∀ i, ∀ z ∈ A.between, ¬ Separates (A.process i).response z) ∧
      ∀ i, (∃ (κ : Type) (A' : Arrangement S κ) (k : κ), A'.process k = A.process i ∧ A'.between ≠ A.between) ↔
        ∃ z, ¬ z.IsDiag ∧ z ∈ (A.process i).constitution :=
  ⟨fun i _ hz hsep => hsep (mem_response_of_mem_constitution (hz.2 i)), exists_between_ne_over_positions_iff A⟩

/-- **Claim 9 (The between), with the positions fixed.** Over the same positions, with another position beside it, a process leaves the between open to another arrangement exactly
where its constitution holds a pair of distinct states. -/
theorem exists_between_ne_iff {ι : Type} (A : Arrangement S ι) {i j : ι} (hji : j ≠ i) :
    (∃ A' : Arrangement S ι, A'.process i = A.process i ∧ A'.between ≠ A.between) ↔
      ∃ z, ¬ z.IsDiag ∧ z ∈ (A.process i).constitution := by
  constructor
  · rintro ⟨A', hi, hne⟩
    by_contra hnone
    push Not at hnone
    have hempty : ∀ B : Arrangement S ι, B.process i = A.process i → B.between = ∅ := fun B hB =>
      Set.eq_empty_of_forall_notMem fun z hz => hnone z hz.1 (hB ▸ hz.2 i)
    exact hne ((hempty A' hi).trans (hempty A rfl).symm)
  · rintro ⟨z, hd, hin⟩
    by_cases hz : z ∈ A.between
    · exact exists_between_ne A hji ⟨z, hz⟩
    · exact exists_between_ne_of_not_mem A hd hin hz

/-- **Claim 9 (The between), with the positions fixed at one.** Over one position, any arrangement over that one position with its process standing has its between. This comes from fixing the positions: over more, a lone process whose constitution holds a pair of distinct states has another between (`lone_process_other_positions`, `exists_between_ne_over_positions_iff`), so one position is no exception to the second clause. -/
theorem between_eq_of_subsingleton {ι : Type} [Subsingleton ι] (A A' : Arrangement S ι) {i : ι} (hi : A'.process i = A.process i) :
    A'.between = A.between := by
  ext z
  refine and_congr_right fun _ => forall_congr' fun k => ?_
  rw [Subsingleton.elim k i, hi]

/-! ## Balance -/

/-- A pair that enters the between enters some constitution: it is in that process's release. -/
theorem between_sdiff_subset_release {ι : Type} (ch : Change S ι) :
    ch.after.between \ ch.before.between ⊆ ⋃ i, ch.release i := by
  rintro z ⟨hafter, hbefore⟩
  have hout : ∃ i, z ∉ (ch.before.process i).constitution := by
    by_contra hall
    push Not at hall
    exact hbefore ⟨hafter.1, hall⟩
  obtain ⟨i, hi⟩ := hout
  exact Set.mem_iUnion.mpr ⟨i, hafter.2 i, hi⟩

/-- A pair that leaves the between leaves some constitution: it is in that process's price. -/
theorem between_sdiff_subset_price {ι : Type} (ch : Change S ι) :
    ch.before.between \ ch.after.between ⊆ ⋃ i, ch.price i := by
  rintro z ⟨hbefore, hafter⟩
  have hout : ∃ i, z ∉ (ch.after.process i).constitution := by
    by_contra hall
    push Not at hall
    exact hafter ⟨hbefore.1, hall⟩
  obtain ⟨i, hi⟩ := hout
  exact Set.mem_iUnion.mpr ⟨i, hbefore.2 i, hi⟩

/-- A set lying in another with the rest in a union over a finite family is no larger than the other and the family's
sizes added. It is the step from the inclusions of balance to its bounds. -/
theorem ncard_le_add_sum [Fintype S] {ι : Type} [Fintype ι] {X Y : Set (Sym2 S)} {U : ι → Set (Sym2 S)}
    (h : X \ Y ⊆ ⋃ i, U i) : X.ncard ≤ Y.ncard + ∑ i, (U i).ncard := by
  have hsub : X ⊆ Y ∪ ⋃ i, U i := fun z hz => by
    by_cases hy : z ∈ Y
    · exact Or.inl hy
    · exact Or.inr (h ⟨hz, hy⟩)
  calc X.ncard ≤ (Y ∪ ⋃ i, U i).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Y.ncard + (⋃ i, U i).ncard := Set.ncard_union_le _ _
    _ ≤ Y.ncard + ∑ i, (U i).ncard := Nat.add_le_add_left (Set.ncard_iUnion_le_of_fintype U) _

/-- **Claim 11 (Change by refinement).** The between grows by no more than the release and shrinks by no more than the price paid, for
any change: a pair enters only inside some process's release and leaves only inside some process's price, and the sizes
are bounded by their sums. -/
theorem Composition.balance [Fintype S] {ι : Type} [Fintype ι] (ch : Change S ι) :
    ch.after.between \ ch.before.between ⊆ ⋃ i, ch.release i ∧
      ch.before.between \ ch.after.between ⊆ ⋃ i, ch.price i ∧
      ch.after.between.ncard ≤ ch.before.between.ncard + ∑ i, (ch.release i).ncard ∧
      ch.before.between.ncard ≤ ch.after.between.ncard + ∑ i, (ch.price i).ncard :=
  ⟨between_sdiff_subset_release ch, between_sdiff_subset_price ch,
    ncard_le_add_sum (between_sdiff_subset_release ch), ncard_le_add_sum (between_sdiff_subset_price ch)⟩

/-- **Claim 11 (Change by refinement).** Every shrinkage of the between has a price that pays for it: a pair that leaves the between is
in the price of some process. -/
theorem Composition.payer {ι : Type} (ch : Change S ι) :
    ∀ z ∈ ch.before.between \ ch.after.between, ∃ i, z ∈ ch.price i :=
  fun _ hz => Set.mem_iUnion.mp (between_sdiff_subset_price ch hz)

/-- A change of the world keeps the between, with nothing paid or released: the arrangement stays, and the between reads no accessible set. -/
theorem change_of_world_keeps_between {ι : Type} (ch : Change S ι) (h : ch.before = ch.after) :
    ch.after.between = ch.before.between ∧ (∀ i, ch.price i = ∅) ∧ ∀ i, ch.release i = ∅ := by
  refine ⟨by rw [h], fun i => ?_, fun i => ?_⟩
  · ext z
    simp [Change.price, h]
  · ext z
    simp [Change.release, h]

/-- **Claim 11 (Change by refinement), a change of the world.** What a change of the world moves is what follows what, and not the between. On two states, one
arrangement over all the states and then over one: its between stays, with nothing paid or released, and its process's response follows a quantity across the
first set and not across the second. -/
theorem change_of_world_moves_following :
    ∃ (S ι : Type) (_ : Fintype S) (ch : Change S ι) (i : ι) (Q : Type) (q : S → Q),
      ch.before = ch.after ∧ ch.after.between = ch.before.between ∧ (∀ i, ch.price i = ∅) ∧ (∀ i, ch.release i = ∅) ∧
        Follows ch.accessibleBefore (ch.before.process i).response q ∧ ¬ Follows ch.accessibleAfter (ch.after.process i).response q := by
  let A : Arrangement Bool Unit := ⟨inferInstance, fun _ => Process.reading id, ∅⟩
  let ch : Change Bool Unit := ⟨A, A, Set.univ, {false}, Or.inr rfl⟩
  obtain ⟨hb, hp, hr⟩ := change_of_world_keeps_between ch rfl
  refine ⟨Bool, Unit, inferInstance, ch, (), Bool, id, rfl, hb, hp, hr, ⟨fun _ _ _ _ h => h, ?_⟩, ?_⟩
  · exact ⟨false, Set.mem_univ _, true, Set.mem_univ _, Bool.false_ne_true, Bool.false_ne_true⟩
  · rintro ⟨-, s, hs, t, ht, hst, -⟩
    exact hst (hs.trans ht.symm)

/-! ## Attachment -/

/-- A quantity that separates a pair in the between is not carried by any process's coarse-grainings: by
Claim 2 (The condition of response) they identify the pair, read together, and a quantity they carried would too. -/
theorem not_carries_of_separates {ι : Type} (A : Arrangement S ι) (i : ι)
    {Q : Type} {q : S → Q} (hq : ∃ z ∈ A.between, Separates q z) : ¬ (A.process i).Carries q := by
  obtain ⟨z, hz, hsep⟩ := hq
  intro hcarried
  exact hsep (kernel_subset_of_carries hcarried
    (mem_kernel_jointly fun k => mem_grainings_of_mem_constitution (hz.2 i) k))

/-- A change of response only is one that leaves every constitution. The converse does not hold: a change can leave every constitution and move what
else a process makes. -/
theorem Change.ResponseOnly.constitutionsStay {ι : Type} {ch : Change S ι} (h : ch.ResponseOnly) : ch.ConstitutionsStay := by
  obtain ⟨-, σ, hσ⟩ := h
  intro i
  rw [hσ]
  rfl

open Classical in
/-- At the position it names, the change of one rule puts that rule, with nothing else about the process moved. -/
theorem process_withRules_rulesAt_self {ι : Type} (A : Arrangement S ι) (i : ι) {B : Type} (g : (∀ k, (A.process i).Value k) → B) :
    (A.withRules (A.rulesAt i g)).process i = (A.process i).withRule g := by
  have h : A.rulesAt i g i = ⟨B, g⟩ := Function.update_self _ _ _
  change (A.process i).withRule (A.rulesAt i g i).2 = _
  rw [h]

open Classical in
/-- At every other position, the change of one rule leaves the process as it was. -/
theorem process_withRules_rulesAt_of_ne {ι : Type} (A : Arrangement S ι) {i j : ι} (hj : j ≠ i) {B : Type}
    (g : (∀ k, (A.process i).Value k) → B) : (A.withRules (A.rulesAt i g)).process j = A.process j := by
  have h : A.rulesAt i g j = ⟨(A.process j).Action, (A.process j).rule⟩ := Function.update_of_ne hj _ _
  change (A.process j).withRule (A.rulesAt i g j).2 = _
  rw [h]
  rfl

/-- **Claim 12 (Change by attachment).** A change of one rule is a change of response only: the accessible states stay, and the arrangement after is
the arrangement before with new rules, every coarse-graining of every process and every join standing. -/
theorem responseOnly_ofRule {ι : Type} (A : Arrangement S ι) (i : ι) {B : Type} (g : (∀ k, (A.process i).Value k) → B)
    (X : Accessible S) : (Change.ofRule A i g X).ResponseOnly :=
  ⟨rfl, A.rulesAt i g, rfl⟩

/-- **Claim 12 (Change by attachment).** A process's response can come to follow a quantity that separates pairs in the between, with
none of its coarse-grainings changing, exactly where, across the accessible states, that quantity fixes a quantity its
coarse-grainings carry and the carried one varies with it. Coming to follow is a change from the arrangement `A`, of response only, with every other
process staying. Such a quantity is itself not carried by the coarse-grainings. -/
theorem Composition.attachment {ι : Type} (A : Arrangement S ι) (i : ι)
    (X : Accessible S) {Q : Type} (q : S → Q) (hq : ∃ z ∈ A.between, Separates q z) :
    ¬ (A.process i).Carries q ∧
      ((∃ ch : Change S ι, ch.before = A ∧ ch.accessibleAfter = X ∧ ch.ResponseOnly ∧
          (∀ j, j ≠ i → ch.after.process j = ch.before.process j) ∧ Follows X (ch.after.process i).response q) ↔
        ∃ (V : Type) (c : S → V), (A.process i).Carries c ∧ Fixes X q c ∧ VariesWith X c q) := by
  refine ⟨not_carries_of_separates A i hq, ?_, ?_⟩
  · rintro ⟨ch, rfl, -, ⟨-, σ, hσ⟩, -, hf⟩
    rw [hσ] at hf
    exact ⟨(σ i).1, _, Law.factorization ((ch.before.process i).withRule (σ i).2), hf.1, hf.2⟩
  · rintro ⟨V, _, ⟨h, rfl⟩, hfix, hvar⟩
    refine ⟨Change.ofRule A i h X, rfl, rfl, responseOnly_ofRule A i h X, fun j hj => process_withRules_rulesAt_of_ne A hj h, ?_⟩
    change Follows X ((A.withRules (A.rulesAt i h)).process i).response q
    rw [process_withRules_rulesAt_self]
    exact ⟨hfix, hvar⟩

/-- **Claim 12 (Change by attachment).** A change that leaves every constitution leaves the between as it was: nothing is paid and nothing is
released. So does a change of response only (`Change.ResponseOnly.constitutionsStay`). -/
theorem attachment_leaves_between {ι : Type} (ch : Change S ι) (h : ch.ConstitutionsStay) :
    ch.after.between = ch.before.between ∧ (∀ i, ch.price i = ∅) ∧ ∀ i, ch.release i = ∅ := by
  have hsame : ∀ i, (ch.after.process i).constitution = (ch.before.process i).constitution := h
  refine ⟨?_, fun i => ?_, fun i => ?_⟩
  · ext z
    exact ⟨fun hz => ⟨hz.1, fun i => hsame i ▸ hz.2 i⟩, fun hz => ⟨hz.1, fun i => (hsame i).symm ▸ hz.2 i⟩⟩
  · ext z
    simp [Change.price, hsame i]
  · ext z
    simp [Change.release, hsame i]

/-- **Claim 12 (Change by attachment).** The case the theorem speaks of occurs, as a change. On two bits, a process is constituted to read the first bit and
has a constant response. The second bit separates a pair in the between. Across the states where the two bits agree, the second bit fixes the first, and the first
varies with it. The rule comes to give the first bit: the response goes from not following the second bit to following it, none of the process's coarse-grainings
changing, and the between stays. -/
theorem attachment_occurs :
    ∃ (S ι : Type) (_ : Fintype S) (ch : Change S ι) (i : ι) (X : Accessible S) (Q : Type) (q : S → Q),
      ch.accessibleBefore = X ∧ ch.ResponseOnly ∧ (∃ z ∈ ch.before.between, Separates q z) ∧
        (∃ (V : Type) (c : S → V), (ch.before.process i).Carries c ∧ Fixes X q c ∧ VariesWith X c q) ∧
        ¬ Follows X (ch.before.process i).response q ∧ Follows X (ch.after.process i).response q ∧
        ch.after.between = ch.before.between := by
  let p : Process (Bool × Bool) := (Process.reading Prod.fst).withRule fun _ => ()
  let A : Arrangement (Bool × Bool) Unit := ⟨inferInstance, fun _ => p, ∅⟩
  let X : Accessible (Bool × Bool) := {s | s.1 = s.2}
  let g : (∀ k, p.Value k) → Bool := fun v => v ()
  let ch := Change.ofRule A () g X
  have hfix : Fixes X Prod.snd Prod.fst := by
    rintro s hs t ht hst
    exact hs.trans (hst.trans ht.symm)
  have hvar : VariesWith X Prod.fst (Prod.snd : Bool × Bool → Bool) :=
    ⟨(false, false), rfl, (true, true), rfl, Bool.false_ne_true, Bool.false_ne_true⟩
  have hresponse : Follows X (ch.after.process ()).response (Prod.snd : Bool × Bool → Bool) := by
    change Follows X ((A.withRules (A.rulesAt () g)).process ()).response _
    rw [process_withRules_rulesAt_self]
    exact ⟨hfix, hvar⟩
  have hsep : ∃ z ∈ ch.before.between, Separates (Prod.snd : Bool × Bool → Bool) z := by
    refine ⟨s((false, false), (false, true)), ⟨?_, fun _ => ?_⟩, ?_⟩
    · simp [Sym2.mk_isDiag_iff]
    · exact (mem_kernel Prod.fst _ _).mpr rfl
    · intro hin
      exact Bool.false_ne_true ((mem_kernel Prod.snd _ _).mp hin)
  have hronly : ch.ResponseOnly := responseOnly_ofRule A () g X
  refine ⟨Bool × Bool, Unit, inferInstance, ch, (), X, Bool, Prod.snd, rfl, hronly, hsep,
    ⟨Bool, Prod.fst, ⟨fun v => v (), rfl⟩, hfix, hvar⟩, ?_, hresponse, (attachment_leaves_between ch hronly.constitutionsStay).1⟩
  rintro ⟨-, s, -, t, -, -, hne⟩
  exact hne rfl

/-- **Claim 9 (The between), over other positions.** A lone process whose constitution holds a pair of distinct states has another arrangement with it standing and another between, once the other arrangement may have other positions. On two states, a process that tells nothing apart stands alone, and beside a process that tells the states apart it stands in an arrangement with an empty between. -/
theorem lone_process_other_positions :
    ∃ (A : Arrangement Bool Unit) (A' : Arrangement Bool Bool),
      A'.process true = A.process () ∧ A'.between ≠ A.between := by
  let blank : Process Bool := Process.reading fun _ => ()
  let A : Arrangement Bool Unit := ⟨inferInstance, fun _ => blank, ∅⟩
  let A' : Arrangement Bool Bool := ⟨inferInstance, fun b => cond b blank (Process.reading id), ∅⟩
  refine ⟨A, A', rfl, fun heq => ?_⟩
  have hin : (s(false, true) : Sym2 Bool) ∈ A.between :=
    ⟨by simp [Sym2.mk_isDiag_iff], fun _ => (mem_kernel (fun _ : Bool => ()) _ _).mpr rfl⟩
  have hin' : (s(false, true) : Sym2 Bool) ∈ A'.between := heq ▸ hin
  exact Bool.false_ne_true ((mem_kernel id false true).mp (hin'.2 false))

end Companion
