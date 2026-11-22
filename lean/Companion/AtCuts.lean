import Companion.Cuts
import Companion.Invariance
import Companion.Uptake
import Companion.Witness

/-!
# The laws and results at a cut

Claim 17 (Every level, every join): each part of a cut yields an object the theorems already apply to (`Companion.Cuts`), and here each is applied. `LawsAndResults` is the list, one field for each law and derived result
proved of the objects, each field the statement of its theorem at an arrangement over any states.

What the invariance comes to, as a fact of the proof: every field holds by instantiation, because the theorems were stated for any states, so the list holds at any arrangement over any states, and a cut's reading is one. `Invariance.cuts` is one line at the total reading, and `Invariance.cuts_exactly` one line at the exact reading. What is not instantiation is that the reading at a scale exists, that it makes nothing up (the forward direction of `Process.mem_response_imageAtScale`, `value_least`), and when it is exact, which is `Process.imageAtScale`, `Cut.read` and what `Cut.ReadsExactly` asks of a scale, in `Companion.Cuts`. Invariance under changes of cut is then that the list is true at each reading (`Invariance.under_cuts`), and residue is a feature that moves (`residue_not_invariant_under_cuts`).

Three of the results say that some arrangement or coarse-graining does a thing, and an existence is not instantiated by being stated for any states: Claim 25 (Joint prohibition), Relocation and the "can grow" of Claim 4 (No recovery). Each is stated of the states a cut reads, and needs room there: where they hold two distinct states, some arrangement or coarse-graining over them does it (`exists_prohibition_of_ne`,
`exists_relocation_of_ne`, `exists_relocation_by_response_of_ne`, `residue_can_grow_of_ne`), and where they hold three, a relocation with an inner between that is not empty (`exists_relocation_nonempty_inner`, `exists_relocation_by_response_nonempty_inner`), which two cannot have (`not_relocation_nonempty_inner_of_card_le_two`). A scale that identifies everything leaves one coarse state and no room (`one_coarse_state`). The arrangement a cut itself reads need not: at depth zero it has one position (`level_zero_one_position`), and one position cannot prohibit (`not_prohibition_of_one_position`).
Claim 9 (The between)'s second clause also says some arrangement, and Claim 12 (Change by attachment) says "can", but each is an equivalence that holds as stated at an arrangement over any states, so it needs no such form.
-/

namespace Companion

variable {S ι τ : Type}

/-! ## The results that say some arrangement does a thing -/

open Classical in
/-- **Claim 25 (Joint prohibition), over any states.** Over any states that hold two distinct states, some arrangement never reaches an outcome that no response in it alone excludes: the outcome is the two, one process forbids the first alone, and the other the second alone. -/
theorem exists_prohibition_of_ne {T : Type} {a b : T} (h : a ≠ b) :
    ∃ (F : ForbidAllow T Bool) (O : Outcome T), (∀ i, ¬ Excludes (F.responseAt i) O) ∧ ¬ F.Reaches O := by
  let chi : Bool → T → Bool := fun i s => decide (s = cond i a b)
  let F : ForbidAllow T Bool :=
    { finite := inferInstance
      process := fun i => Process.reading (chi i)
      joins := ∅
      verdict := fun _ (v : Bool) => cond v Verdict.forbid Verdict.allow }
  have hforbid : ∀ i s, F.responseAt i s = Verdict.forbid ↔ s = cond i a b := by
    intro i s
    have hval : F.responseAt i s = cond (chi i s) Verdict.forbid Verdict.allow := rfl
    rw [hval]
    by_cases hs : s = cond i a b <;> simp [chi, hs]
  refine ⟨F, {a, b}, fun i hex => ?_, ?_⟩
  · cases i with
    | true =>
      have hb := (hforbid true b).mp (hex b (Or.inr rfl))
      exact h hb.symm
    | false =>
      have ha := (hforbid false a).mp (hex a (Or.inl rfl))
      exact h ha
  · rintro ⟨s, hs, hnone⟩
    rcases hs with rfl | rfl
    · exact hnone true ((hforbid true _).mpr rfl)
    · exact hnone false ((hforbid false _).mpr rfl)

/-- **Claim 25 (Joint prohibition), its bound in the states.** Over one state, an arrangement with at least one process prohibits nothing: every process allows the one state of an outcome no process excludes. With no process it can (`prohibition_of_no_process`), so the existence over a cut's states, with a process, needs two distinct states there. -/
theorem not_prohibition_of_subsingleton {T : Type} [Subsingleton T] [Nonempty ι] (F : ForbidAllow T ι) (O : Outcome T) :
    ¬ ((∀ i, ¬ Excludes (F.responseAt i) O) ∧ ¬ F.Reaches O) := by
  rintro ⟨hex, hreach⟩
  have hallow : ∀ i, ∃ s ∈ O, F.responseAt i s ≠ Verdict.forbid := by
    intro i
    by_contra hnone
    push Not at hnone
    exact hex i hnone
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨s, hs, -⟩ := hallow i
  refine hreach ⟨s, hs, fun j => ?_⟩
  obtain ⟨s', -, hj⟩ := hallow j
  rwa [Subsingleton.elim s s']

/-- **Claim 25 (Joint prohibition), its bound in the positions.** One position prohibits nothing: what the arrangement never reaches, its one process excludes. A cut at depth zero reads one position, so the arrangement it reads is no such case, though other arrangements over its states are. -/
theorem not_prohibition_of_one_position {T : Type} [Subsingleton ι] [Nonempty ι] (F : ForbidAllow T ι) (O : Outcome T) :
    ¬ ((∀ i, ¬ Excludes (F.responseAt i) O) ∧ ¬ F.Reaches O) := by
  rintro ⟨hex, hreach⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine hex i fun s hs => ?_
  by_contra hne
  exact hreach ⟨s, hs, fun j => by rwa [Subsingleton.elim j i]⟩

open Classical in
/-- **Relocation, over any states.** Over any states that hold two distinct states, a change of one process's constitution at one level leaves the between unchanged and enlarges the between at the level above. The member tells one state from the rest and comes to tell nothing apart, a sibling tells every state apart, and the inner arrangement as a process reads the member. -/
theorem exists_relocation_of_ne {T : Type} {a b : T} (h : a ≠ b) :
    ∃ p p' q : Process T, p.constitution ≠ p'.constitution ∧ (tower p q p.constitutive).Coherent ∧ (tower p' q p'.constitutive).Coherent ∧
      (towerInner p q p.constitutive).ComposedFrom p ∧ (towerInner p' q p'.constitutive).ComposedFrom p' ∧
      (tower p' q p'.constitutive).betweenAt 1 = (tower p q p.constitutive).betweenAt 1 ∧
      (tower p q p.constitutive).betweenAt 0 ⊂ (tower p' q p'.constitutive).betweenAt 0 := by
  let p : Process T := Process.reading fun s => decide (s = a)
  let p' : Process T := Process.reading fun _ => ()
  let q : Process T := Process.reading id
  have hkeep : ∀ z, ¬ z.IsDiag → z ∈ p'.constitution → z ∉ p.constitution → z ∉ q.constitution := by
    intro z
    induction z with
    | _ s t =>
      intro hd _ _ hq
      exact hd (Sym2.mk_isDiag_iff.mpr ((mem_kernel id s t).mp hq))
  have hd : ¬ (s(a, b) : Sym2 T).IsDiag := fun hd => h (Sym2.mk_isDiag_iff.mp hd)
  have hin : s(a, b) ∈ p'.constitution := mem_kernel_const () _
  have hout : s(a, b) ∉ p.constitution := by
    intro hmem
    have hval : decide (a = a) = decide (b = a) := (mem_kernel _ a b).mp hmem
    exact h (of_decide_eq_true (hval.symm.trans (decide_eq_true rfl))).symm
  have hall := tower_relocates (p := p) (p' := p') (q := q) (fun z _ => mem_kernel_const () z) hkeep hd hin hout
  exact ⟨p, p', q, fun heq => hout (heq ▸ hin), tower_coherent _ _ _, tower_coherent _ _ _, ⟨⟨true, rfl⟩, rfl⟩, ⟨⟨true, rfl⟩, rfl⟩, hall.2.1, hall.2.2⟩

open Classical in
/-- **Relocation, by response, over any states.** Over any states that hold two distinct states, a change of one process's response at one level leaves every constitution and the between unchanged, and enlarges the between at the level above. The member tells one state from the rest and its rule comes to give a constant; the inner arrangement as a process reads the member's response. -/
theorem exists_relocation_by_response_of_ne {T : Type} {a b : T} (h : a ≠ b) :
    ∃ p p' q : Process T, p'.constitution = p.constitution ∧ kernel p.response ≠ kernel p'.response ∧
      (tower p q p.response).Coherent ∧ (tower p' q p'.response).Coherent ∧
      (towerInner p' q p'.response).between = (towerInner p q p.response).between ∧
      (tower p q p.response).betweenAt 0 ⊂ (tower p' q p'.response).betweenAt 0 := by
  let r : Process T := Process.reading fun s => decide (s = a)
  let p : Process T := r
  let p' : Process T := r.withRule fun _ => ()
  let q : Process T := Process.reading id
  have hd : ¬ (s(a, b) : Sym2 T).IsDiag := fun hd => h (Sym2.mk_isDiag_iff.mp hd)
  have hin : s(a, b) ∈ kernel p'.response := mem_kernel_const () _
  have hout : s(a, b) ∉ kernel p.response := by
    intro hmem
    have hval : decide (a = a) = decide (b = a) := (mem_kernel _ a b).mp hmem
    exact h (of_decide_eq_true (hval.symm.trans (decide_eq_true rfl))).symm
  have hall := tower_relocates_by_response (p := p) (p' := p') (q := q) rfl (fun z _ => mem_kernel_const () z) hd hin hout
  exact ⟨p, p', q, rfl, fun heq => hout (heq ▸ hin), tower_coherent _ _ _, tower_coherent _ _ _, hall.1, hall.2.2⟩

open Classical in
/-- **Relocation, an inner between that is not empty, over any states.** Over any states that hold three distinct states, a change of one process's constitution at one level leaves the between unchanged and not empty, and enlarges the between at the level above. The member and a distinct sibling each tell the third state from the rest, so the inner between holds the first two, and the member comes to tell nothing apart. On exactly three states the sibling has to share the member's constitution, and `Composition.relocation` is the case on four where it does not. -/
theorem exists_relocation_nonempty_inner {T : Type} {a b c : T} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p p' q : Process T, p ≠ q ∧ p.constitution ≠ p'.constitution ∧ (tower p q p.constitutive).Coherent ∧ (tower p' q p'.constitutive).Coherent ∧
      (towerInner p q p.constitutive).ComposedFrom p ∧ (towerInner p' q p'.constitutive).ComposedFrom p' ∧
      (towerInner p q p.constitutive).between.Nonempty ∧
      (tower p' q p'.constitutive).betweenAt 1 = (tower p q p.constitutive).betweenAt 1 ∧
      (tower p q p.constitutive).betweenAt 0 ⊂ (tower p' q p'.constitutive).betweenAt 0 := by
  let χ : T → Bool := fun s => decide (s = c)
  let p : Process T := Process.reading χ
  let p' : Process T := Process.reading fun _ => ()
  let q : Process T := p.withRule fun _ => ()
  have hd : ¬ (s(a, c) : Sym2 T).IsDiag := fun hd => hac (Sym2.mk_isDiag_iff.mp hd)
  have hin : s(a, c) ∈ p'.constitution := mem_kernel_const () _
  have hval : χ a ≠ χ c := by simp [χ, hac]
  have hout : s(a, c) ∉ p.constitution := fun hmem => hval ((mem_kernel χ a c).mp hmem)
  have hall := tower_relocates (p := p) (p' := p') (q := q) (fun z _ => mem_kernel_const () z) (fun _ _ _ h => h) hd hin hout
  have hsame : s(a, b) ∈ kernel χ := (mem_kernel χ a b).mpr (by simp [χ, hac, hbc])
  have hne : p ≠ q := by
    intro heq
    have hsep : s(a, c) ∈ kernel p.response := heq.symm ▸ (mem_kernel_const () _ : s(a, c) ∈ kernel (fun _ : T => ()))
    exact hval ((mem_kernel p.response a c).mp hsep)
  refine ⟨p, p', q, hne, fun heq => hout (heq ▸ hin), tower_coherent _ _ _, tower_coherent _ _ _, ⟨⟨true, rfl⟩, rfl⟩, ⟨⟨true, rfl⟩, rfl⟩, ?_, hall.2.1, hall.2.2⟩
  exact ⟨s(a, b), (mem_between_towerInner p q _ _).mpr ⟨fun hdiag => hab (Sym2.mk_isDiag_iff.mp hdiag), hsame, hsame⟩⟩

open Classical in
/-- **Relocation, by response, an inner between that is not empty, over any states.** Over any states that hold three distinct states, a change of one process's response at one level leaves every constitution and the between unchanged and not empty, and enlarges the between at the level above. The member and its sibling each tell the third state from the rest, and the member's rule comes to give a constant. -/
theorem exists_relocation_by_response_nonempty_inner {T : Type} {a b c : T} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p p' q : Process T, p'.constitution = p.constitution ∧ kernel p.response ≠ kernel p'.response ∧
      (tower p q p.response).Coherent ∧ (tower p' q p'.response).Coherent ∧
      (towerInner p q p.response).between.Nonempty ∧
      (tower p' q p'.response).betweenAt 1 = (tower p q p.response).betweenAt 1 ∧
      (tower p q p.response).betweenAt 0 ⊂ (tower p' q p'.response).betweenAt 0 := by
  let χ : T → Bool := fun s => decide (s = c)
  let p : Process T := Process.reading χ
  let p' : Process T := p.withRule fun _ => ()
  have hd : ¬ (s(a, c) : Sym2 T).IsDiag := fun hd => hac (Sym2.mk_isDiag_iff.mp hd)
  have hin : s(a, c) ∈ kernel p'.response := mem_kernel_const () _
  have hval : χ a ≠ χ c := by simp [χ, hac]
  have hout : s(a, c) ∉ kernel p.response := fun hmem => hval ((mem_kernel χ a c).mp hmem)
  have hall := tower_relocates_by_response (p := p) (p' := p') (q := p) rfl (fun z _ => mem_kernel_const () z) hd hin hout
  have hsame : s(a, b) ∈ kernel χ := (mem_kernel χ a b).mpr (by simp [χ, hac, hbc])
  refine ⟨p, p', p, rfl, fun heq => hout (heq ▸ hin), tower_coherent _ _ _, tower_coherent _ _ _, ?_, hall.2.1, hall.2.2⟩
  exact ⟨s(a, b), (mem_between_towerInner p p _ _).mpr ⟨fun hdiag => hab (Sym2.mk_isDiag_iff.mp hdiag), hsame, hsame⟩⟩

/-- On at most two states, a pair of distinct states is the only one. -/
theorem eq_of_not_isDiag_of_card_le_two {T : Type} [Fintype T] (hT : Fintype.card T ≤ 2) {z w : Sym2 T} (hz : ¬ z.IsDiag) (hw : ¬ w.IsDiag) : w = z := by
  classical
  induction z with
  | _ x y =>
    induction w with
    | _ u v =>
      have hxy : x ≠ y := fun h => hz (Sym2.mk_isDiag_iff.mpr h)
      have huv : u ≠ v := fun h => hw (Sym2.mk_isDiag_iff.mpr h)
      have hone : ∀ t : T, t = x ∨ t = y := by
        intro t
        by_contra hnot
        push Not at hnot
        have hthree : 2 < Fintype.card T := Fintype.two_lt_card_iff.mpr ⟨x, y, t, hxy, Ne.symm hnot.1, Ne.symm hnot.2⟩
        omega
      rcases hone u with rfl | rfl <;> rcases hone v with rfl | rfl
      · exact absurd rfl huv
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl huv

/-- **Relocation, an inner between that is not empty, on two states.** It cannot be done on at most two states, by constitution or by response. An inner between that is not empty holds the one pair of distinct states, so the member's constitution holds it, and what the level above reads, composed from the member's coarse-graining or its response, identifies it already. The between above has nothing to gain. So the empty inner between of `exists_relocation_of_ne`, on two states, is unavoidable there and avoidable on three. -/
theorem not_relocation_nonempty_inner_of_card_le_two {T : Type} [Fintype T] (hT : Fintype.card T ≤ 2) {p p' q q' : Process T} {V V' : Type} {c : T → V} {c' : T → V'}
    (hc : p.constitution ⊆ kernel c) (hne : (towerInner p q c).between.Nonempty) : ¬ (tower p q c).betweenAt 0 ⊂ (tower p' q' c').betweenAt 0 := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨hd, hp, -⟩ := (mem_between_towerInner p q c z).mp hz
  rintro ⟨-, hnot⟩
  refine hnot fun w hw => ?_
  rw [Nested.betweenAt_zero] at hw ⊢
  have hwd : ¬ w.IsDiag := ((mem_between_tower _ _ _ w).mp hw).1
  exact (mem_between_tower _ _ _ w).mpr ⟨hwd, eq_of_not_isDiag_of_card_le_two hT hd hwd ▸ hc hp⟩

/-- **Claim 17 (Every level, every join), no room at one coarse state.** At a scale that identifies everything a cut's states are one, so no coarse-graining's residue grows and no nested arrangement's between enlarges: Claim 4 (No recovery)'s "can grow" and all of Relocation say nothing there, their fields in the list holding only because no two distinct states are there to meet their premise. -/
theorem one_coarse_state (cut : Cut S τ) (hc : ∀ s t, cut.scale s = cut.scale t) :
    Subsingleton cut.States ∧
      (¬ ∃ (C D : Type) (c : cut.States → C) (g : C → D), residue c < residue (g ∘ c)) ∧
      ¬ ∃ n n' : Nested cut.States, n.between ⊂ n'.between := by
  have hsub : Subsingleton cut.States := by
    refine ⟨fun x y => funext fun t => ?_⟩
    induction x t using Quotient.inductionOn with
    | _ a =>
      induction y t using Quotient.inductionOn with
      | _ b => exact Quotient.sound (s := Setoid.ker cut.scale) (hc a b)
  have hdiag : ∀ z : Sym2 cut.States, z.IsDiag := by
    intro z
    induction z with
    | _ a b => exact Sym2.mk_isDiag_iff.mpr (Subsingleton.elim a b)
  refine ⟨hsub, ?_, ?_⟩
  · rintro ⟨C, D, c, g, hlt⟩
    have hzero : ∀ {E : Type} (e : cut.States → E), residue e = 0 := by
      intro E e
      have : distinctPairs (kernel e) = ∅ := Set.eq_empty_of_forall_notMem fun z hz => hz.2 (hdiag z)
      unfold residue
      rw [this, Set.ncard_empty]
    rw [hzero, hzero] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨n, n', hss⟩
    have hempty : ∀ m : Nested cut.States, m.between = ∅ := fun m =>
      Set.eq_empty_of_forall_notMem fun z hz => (Nested.mem_between_iff.mp hz).1 (hdiag z)
    rw [hempty n, hempty n'] at hss
    exact hss.2 (Set.empty_subset _)

/-- **Claim 17 (Every level, every join), the arrangement a cut reads at depth zero.** It has one position, since one arrangement stands at depth zero. So what `not_prohibition_of_one_position` says reaches it, and an existence over a cut's states is not always of the arrangement the cut reads. -/
theorem level_zero_one_position (n : Nested S) : Nat.card {m // n.AtDepth 0 m} = 1 := by
  have : Unique {m // n.AtDepth 0 m} :=
    ⟨⟨⟨n, .here n⟩⟩, fun ⟨_, hm⟩ => Subtype.ext (Nested.eq_of_atDepth_zero hm)⟩
  exact Nat.card_unique

/-! ## The list -/

/-- **Claim 17 (Every level, every join), the list.** Every law and derived result, each field one theorem, at an arrangement `A` over any states `T`. Each field is that theorem at `A`'s processes, at any quantity or coarse-graining over `T`, by `type_of%`: the type of the theorem applied there, so a field cannot say other than the theorem says. Claim 17 (Every level, every join) is this list itself. -/
structure LawsAndResults {T ι : Type} (A : Arrangement T ι) : Prop where
  /-- **Claim 2 (The condition of response).** -/
  law_obtains : ∀ {C : Type} (c : T → C) (w : Situation T), type_of% (Law.obtains c w)
  /-- **Claim 2 (The condition of response).** -/
  law_constitution : ∀ i (k : (A.process i).Index), type_of% (Law.constitution (A.process i) k)
  /-- **Claim 2 (The condition of response).** -/
  law_factorization : ∀ i, type_of% (Law.factorization (A.process i))
  /-- **Claim 4 (No recovery).** -/
  regress_closure : ∀ {C D : Type} (c : T → C) (g : C → D) (w : Situation T), type_of% (Regress.closure c g w)
  /-- **Claim 4 (No recovery).** -/
  regress_monotonicity : (∀ [Fintype T] {C D : Type} (c : T → C) (g : C → D), type_of% (Regress.monotonicity c g)) ∧
    ∀ [Fintype T] {a b : T} (h : a ≠ b), type_of% (residue_can_grow_of_ne h)
  /-- **Claim 4 (No recovery).** -/
  regress_convergence : ∀ [Fintype T] (ch : Chain T), type_of% (Regress.convergence ch)
  /-- **Claim 17 (Every level, every join).** -/
  regress_uptake : ∀ [Fintype T] (j : Join A.process), type_of% (Regress.uptake j)
  /-- **Claim 3 (Silence).** -/
  response_silence : ∀ i {s t : T} (h : ∀ k, (A.process i).grainings k s = (A.process i).grainings k t), type_of% (Response.silence (A.process i) h)
  /-- **Claim 5 (The non-event).** -/
  response_nonevent : type_of% (Response.nonevent (S := T))
  /-- **Claim 6 (Borrowing).** -/
  response_borrowing : (∀ i (X : Accessible T) {Q : Type} (q : T → Q) (hq : ¬ (A.process i).Carries q) (hf : Follows X (A.process i).response q),
      type_of% (Response.borrowing (A.process i) X q hq hf)) ∧
    ∀ i (X : Accessible T) {Q : Type} (q : T → Q) (hq : ¬ (A.process i).Carries q) (hf : Follows X (A.process i).response q) {V : Type} (c : T → V)
      (hc : (A.process i).Carries c) (hr : Carries c (A.process i).response), type_of% (Response.borrowing_every (A.process i) X q hq hf c hc hr)
  /-- **Claim 8 (Not supplied from outside).** -/
  response_unsupplied : ∀ i (q : Process T) (k : q.Index) {V : Type} (h : (q.grainings k).Value → V), type_of% (Response.unsupplied (A.process i) q k h)
  /-- **Claim 1 (Inherited, not emergent).** -/
  composition_nesting : ∀ {κ : Type} {C : κ → Type} {D : Type} (cs : ∀ k, T → C k) (h : (∀ k, C k) → D), type_of% (Composition.nesting cs h)
  /-- **Claim 9 (The between).** -/
  composition_between : type_of% (Composition.between A)
  /-- **Claim 11 (Change by refinement).** -/
  composition_balance : ∀ [Fintype T] [Fintype ι] (ch : Change T ι), type_of% (Composition.balance ch)
  /-- **Claim 11 (Change by refinement).** -/
  composition_payer : ∀ ch : Change T ι, type_of% (Composition.payer ch)
  /-- **Claim 12 (Change by attachment).** -/
  composition_attachment : ∀ i (X : Accessible T) {Q : Type} (q : T → Q) (hq : ∃ z ∈ A.between, Separates q z),
    type_of% (Composition.attachment A i X q hq)
  /-- **Claim 25 (Joint prohibition).** An existence, over the states `T`. -/
  composition_prohibition : ∀ {a b : T} (h : a ≠ b), type_of% (exists_prohibition_of_ne h)
  /-- **Relocation.** An existence, over the states `T`, and the conditions, of any nested arrangement over `T`. -/
  composition_relocation : (∀ {a b : T} (h : a ≠ b), type_of% (exists_relocation_of_ne h)) ∧
    (∀ {a b : T} (h : a ≠ b), type_of% (exists_relocation_by_response_of_ne h)) ∧
    (∀ {a b c : T} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c), type_of% (exists_relocation_nonempty_inner hab hac hbc)) ∧
    (∀ {a b c : T} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c), type_of% (exists_relocation_by_response_nonempty_inner hab hac hbc)) ∧
    type_of% (@relocation_of_conditions T) ∧ type_of% (@relocation_by_response_of_conditions T) ∧ type_of% (@relocation_needs_other_self T)
  /-- **Definition 4 (Invariance under redescription).** -/
  invariance_split : ∀ {V : Type} (f : Feature T ι V), type_of% (Invariance.split f)

/-- **Claim 17 (Every level, every join), each applied.** The list holds at an arrangement over any states. The proof is each theorem, applied. -/
theorem lawsAndResults {T ι : Type} (A : Arrangement T ι) : LawsAndResults A where
  law_obtains := fun c w => Law.obtains c w
  law_constitution := fun i k => Law.constitution (A.process i) k
  law_factorization := fun i => Law.factorization (A.process i)
  regress_closure := fun c g w => Regress.closure c g w
  regress_monotonicity := ⟨fun c g => Regress.monotonicity c g, fun h => residue_can_grow_of_ne h⟩
  regress_convergence := fun ch => Regress.convergence ch
  regress_uptake := fun j => Regress.uptake j
  response_silence := fun i _ _ h => Response.silence (A.process i) h
  response_nonevent := Response.nonevent
  response_borrowing := ⟨fun i X _ q hq hf => Response.borrowing (A.process i) X q hq hf, fun i X _ q hq hf _ c hc hr => Response.borrowing_every (A.process i) X q hq hf c hc hr⟩
  response_unsupplied := fun i q k _ h => Response.unsupplied (A.process i) q k h
  composition_nesting := fun cs h => Composition.nesting cs h
  composition_between := Composition.between A
  composition_balance := fun ch => Composition.balance ch
  composition_payer := fun ch => Composition.payer ch
  composition_attachment := fun i X _ q hq => Composition.attachment A i X q hq
  composition_prohibition := fun h => exists_prohibition_of_ne h
  composition_relocation := ⟨fun h => exists_relocation_of_ne h, fun h => exists_relocation_by_response_of_ne h, fun hab hac hbc => exists_relocation_nonempty_inner hab hac hbc, fun hab hac hbc => exists_relocation_by_response_nonempty_inner hab hac hbc, relocation_of_conditions, relocation_by_response_of_conditions, relocation_needs_other_self⟩
  invariance_split := fun f => Invariance.split f

/-- **Claim 17 (Every level, every join).** Every law and derived result holds of what a cut of a nested arrangement reads, at any level at which an arrangement stands, and at any scale and span: the list holds at the total reading of what the cut reads. A result that says something can happen does so where the cut's states leave room for it, as the fields' premises say (`one_coarse_state`). `Invariance.cuts_exactly` is the same at the exact reading, where the cut has it. -/
theorem Invariance.cuts (cut : Cut S τ) {n : Nested S} (h : cut.Stands n) : LawsAndResults (cut.read h) :=
  lawsAndResults _

/-- **Claim 17 (Every level, every join), at the exact reading.** The list holds at the exact reading of what a cut reads, at a cut whose scale identifies no pair a response at its level separates. -/
theorem Invariance.cuts_exactly (cut : Cut S τ) {n : Nested S} (h : cut.ReadsExactly n) : LawsAndResults (cut.readExactly h) :=
  lawsAndResults _

/-! ## Invariance under changes of cut -/

/-- **Claim 17 (Every level, every join).** A reading of a nested arrangement: a cut, at some level and scale, over some finite span of at least one history, whose level stands there. What it reads is the total reading. -/
structure Reading (n : Nested S) where
  /-- Which histories it reads together. -/
  Span : Type
  /-- Finitely many. This records what a span is, and no proof here uses it. -/
  finite : Finite Span
  /-- At least one. This records what a span is, and no proof here uses it. -/
  nonempty : Nonempty Span
  /-- The cut. -/
  cut : Cut S Span
  /-- An arrangement stands at its level. -/
  stands : cut.Stands n

/-- **Definition 4 (Invariance under redescription), a change of cut.** A kind of change: from any reading of a nested arrangement to any other, at another level, scale or span. -/
def changeOfCut (n : Nested S) : Reading n → Reading n → Prop :=
  fun _ _ => True

/-- **Claim 17 (Every level, every join).** Each law and derived result is invariant under changes of cut. In plain words: the statement "the list holds at what this cut reads" is true at each reading, so no change of cut moves it. That it holds at each is the instantiation above and no more. -/
theorem Invariance.under_cuts (n : Nested S) : InvariantUnder (changeOfCut n) fun r : Reading n => LawsAndResults (r.cut.read r.stands) :=
  fun _ _ _ => propext ⟨fun _ => Invariance.cuts _ _, fun _ => Invariance.cuts _ _⟩

/-- **Claim 17 (Every level, every join).** Residue is not invariant under changes of cut: a change of cut moves it. -/
theorem residue_not_invariant_under_cuts :
    ∃ (S : Type) (_ : Fintype S) (n : Nested S), ¬ InvariantUnder (changeOfCut n) fun r : Reading n => r.cut.residue r.stands := by
  obtain ⟨S, hS, n, a, b, ha, hb, -, -, -, hlt⟩ := residue_can_grow_by_scale
  refine ⟨S, hS, n, fun hinv => ?_⟩
  have heq := hinv ⟨Unit, inferInstance, inferInstance, b, hb⟩ ⟨Unit, inferInstance, inferInstance, a, ha⟩ trivial
  exact absurd heq (Nat.ne_of_lt hlt)

/-! ## Relocation at a cut -/

/-- An unchanged between leaves the joint coarse-graining's constitution as it was: a pair of one state lies in each, and a pair of distinct states lies in each exactly when it lies in the between. -/
theorem constitution_asProcess_eq_of_between_eq {ι ι' : Type} {A : Arrangement S ι} {A' : Arrangement S ι'} (h : A'.between = A.between) :
    A'.asProcess.constitution = A.asProcess.constitution := by
  ext z
  by_cases hd : z.IsDiag
  · exact ⟨fun _ => mem_constitution_of_isDiag _ hd, fun _ => mem_constitution_of_isDiag _ hd⟩
  · constructor
    · intro hin
      have hmem : z ∈ A'.between := ⟨hd, (mem_constitution_asProcess A' z).mp hin⟩
      exact (mem_constitution_asProcess A z).mpr (h ▸ hmem : z ∈ A.between).2
    · intro hin
      have hmem : z ∈ A.between := ⟨hd, (mem_constitution_asProcess A z).mp hin⟩
      exact (mem_constitution_asProcess A' z).mpr (h.symm ▸ hmem : z ∈ A'.between).2

/-- **Relocation, at a cut, constitutions.** A cut reads an arrangement at its level through its members' joint coarse-graining, at whatever scale and span. So a change that leaves an arrangement's between leaves its constitution as the cut reads it, and the level above, reading that process, has nothing to lose: the case of `relocation_needs_other_self`, where the arrangement as a process above is what the cut reads. Stated of the total reading, which asks nothing of the scale; the exact reading has the same constitution (`Cut.constitution_read_eq_readExactly`). -/
theorem relocation_at_cut (cut : Cut S τ) {m m' : Nested S} (hbetween : m'.between = m.between) : (cut.readProcess m').constitution = (cut.readProcess m).constitution := by
  have hlevel : m'.level.between = m.level.between := by
    cases m
    cases m'
    exact hbetween
  have hsame : m'.asProcess.constitution = m.asProcess.constitution := constitution_asProcess_eq_of_between_eq hlevel
  have hsetoid : m'.asProcess.atScaleSetoid cut.scale = m.asProcess.atScaleSetoid cut.scale := by
    have hker : Setoid.ker m'.asProcess.constitutive.map = Setoid.ker m.asProcess.constitutive.map := by
      ext s t
      exact (mem_kernel _ s t).symm.trans ((Set.ext_iff.mp hsame _).trans (mem_kernel _ s t))
    exact congrArg (· ⊔ Setoid.ker cut.scale) hker
  ext z
  induction z with
  | _ f g =>
    unfold Cut.readProcess
    rw [mem_constitution_overSpan, mem_constitution_overSpan]
    refine forall_congr' fun t => ?_
    induction f t using Quotient.inductionOn with
    | _ s =>
      induction g t using Quotient.inductionOn with
      | _ u =>
        rw [show Quotient.mk (Setoid.ker cut.scale) s = coarsen cut.scale s from rfl, show Quotient.mk (Setoid.ker cut.scale) u = coarsen cut.scale u from rfl,
          Process.mem_constitution_imageAtScale, Process.mem_constitution_imageAtScale, hsetoid]

/-- **Relocation, at a cut, the level above.** Where the arrangement as a process above is the one a cut reads, so its own joint coarse-graining, an unchanged between at its level leaves that process's constitution as it was and, with nothing else changing above, the between above as it was. -/
theorem relocation_at_cut_above {ι κ : Type} {A A' : Arrangement S ι} {O O' : Arrangement S κ} {top top' : Process S} {ins ins' : ι → Option (Nested S)}
    {tops tops' : κ → Option (Nested S)} {m : κ} (hT : (Nested.mk top O tops).Coherent) (hT' : (Nested.mk top' O' tops').Coherent)
    (hm : tops m = some (.mk A.asProcess A ins)) (hm' : tops' m = some (.mk A'.asProcess A' ins')) (hbetween : A'.between = A.between)
    (hother : ∀ n, n ≠ m → O'.process n = O.process n) :
    A'.asProcess.constitution = A.asProcess.constitution ∧ (Nested.mk top' O' tops').between = (Nested.mk top O tops).between :=
  relocation_needs_other_self hT hT' hm hm' (fun z => mem_constitution_asProcess A z) (fun z => mem_constitution_asProcess A' z) hbetween hother

/-- **Relocation, with the process above never coarser than its members together.** Composed from all its members together before and after, an arrangement as a process leaves the between above as it was (`relocation_needs_other_self`), so a growth needs it composed otherwise, and this shows that otherwise need not be more coarsely. On two bits no member moves. The inner between stays because nothing at its level changes, and the between above grows by the free change of `self` alone, from finer than its members together to exactly them. This is not the kind of relocation the conditions treat, where `self` reads one member before and after: here before the change it reads no member. Where `self` reads one member, it is coarser than their joint coarse-graining wherever a sibling tells more (`Nested.ComposedFrom.constitution_asProcess_ssubset`). Where it does not, as here, it need not be. -/
theorem relocation_without_coarser_self :
    ∃ (p q : Process (Bool × Bool)) (c : Bool × Bool → Bool × Bool) (c' : Bool × Bool → Bool),
      (tower p q c).Coherent ∧ (tower p q c').Coherent ∧
      (towerInner p q c').between = (towerInner p q c).between ∧
      (tower p q c).between ⊂ (tower p q c').between ∧
      (towerInner p q c').ComposedFromAll ∧
      kernel c ⊆ (towerInner p q c).asProcess.constitution ∧ kernel c' ⊆ (towerInner p q c').asProcess.constitution := by
  let p : Process (Bool × Bool) := Process.reading Prod.fst
  have hzz : (s(((false, false) : Bool × Bool), ((false, true) : Bool × Bool))).IsDiag → False := by
    simp [Sym2.mk_isDiag_iff]
  refine ⟨p, p, id, Prod.fst, tower_coherent _ _ _, tower_coherent _ _ _, rfl, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hd, hk⟩ := (mem_between_tower _ _ _ z).mp hz
    exact (mem_between_tower _ _ _ z).mpr ⟨hd, kernel_id_subset _ hk⟩
  · intro hsub
    have hmem : s(((false, false) : Bool × Bool), ((false, true) : Bool × Bool)) ∈ (tower p p (Prod.fst : Bool × Bool → Bool)).between :=
      (mem_between_tower _ _ _ _).mpr ⟨hzz, (mem_kernel Prod.fst _ _).mpr rfl⟩
    have h := ((mem_between_tower _ _ _ _).mp (hsub hmem)).2
    have heq : ((false, false) : Bool × Bool) = (false, true) := (mem_kernel id _ _).mp h
    exact absurd heq (by decide)
  · intro z
    constructor
    · intro hz b
      cases b <;> exact hz
    · intro hz
      exact hz false
  · intro z hz
    refine (Nested.mem_constitution_asProcess _ z).mpr fun r hr => ?_
    obtain ⟨b, rfl⟩ := hr
    cases b <;> exact kernel_id_subset _ hz
  · intro z hz
    refine (Nested.mem_constitution_asProcess _ z).mpr fun r hr => ?_
    obtain ⟨b, rfl⟩ := hr
    cases b <;> exact hz

/-- **Relocation, where `self` reads one member.** Where an arrangement as a process is composed from one member, and a sibling tells apart a pair that member does not, the arrangement as `self` is strictly coarser than its members' joint coarse-graining. -/
theorem Nested.ComposedFrom.constitution_asProcess_ssubset {m : Nested S} {p q : Process S} (hc : m.ComposedFrom p) (hq : m.HoldsProcess q) {z : Sym2 S}
    (hp : z ∈ p.constitution) (hz : z ∉ q.constitution) : m.asProcess.constitution ⊂ m.self.constitution := by
  refine ⟨fun y hy => ?_, fun hsub => hz ?_⟩
  · rw [hc.2]
    exact (Nested.mem_constitution_asProcess m y).mp hy p hc.1
  · exact (Nested.mem_constitution_asProcess m z).mp (hsub (hc.2 ▸ hp)) q hq

/-- **Relocation, at a cut, responses.** A change of response can still reach what is read above. On two states and one history, a member's rule comes to give a constant. Its arrangement's between stays, and the process the cut reads keeps its constitution, while that process's response comes to identify a pair it separated. So a level above that reads the response loses the pair (`relocation_from_all_responses`). The scale identifies nothing, so the cut reads both exactly, and the value of the total reading is that one response. -/
theorem relocation_by_response_at_cut :
    ∃ (m m' : Nested Bool) (cut : Cut Bool Unit),
      kernel cut.scale ⊆ kernel m.asProcess.response ∧ kernel cut.scale ⊆ kernel m'.asProcess.response ∧
      m'.between = m.between ∧ (cut.readProcess m').constitution = (cut.readProcess m).constitution ∧
        kernel (cut.readProcess m).response ⊂ kernel (cut.readProcess m').response := by
  let p : Process Bool := Process.reading id
  let q : Process Bool := p.withRule fun _ => ()
  let m : Nested Bool := towerInner p q fun _ => ()
  let m' : Nested Bool := towerInner q q fun _ => ()
  let cut : Cut Bool Unit := ⟨0, Bool, id⟩
  have hdiag : ∀ {C : Type} (d : Bool → C), kernel cut.scale ⊆ kernel d := fun d => kernel_id_subset d
  have hb : m'.between = m.between := by
    ext z
    rw [mem_between_towerInner, mem_between_towerInner]
    exact Iff.rfl
  refine ⟨m, m', cut, hdiag _, hdiag _, hb, relocation_at_cut cut hb, ?_⟩
  have hvalue : ∀ (n : Nested Bool) (s : Bool), n.asProcess.valueAtScale cut.scale (coarsen cut.scale s) = {n.asProcess.response s} :=
    fun n => (Process.imageAtScale_singleton_iff _ _).mpr (hdiag _)
  have hresponse : ∀ (n : Nested Bool) (f g : Unit → Bool),
      s(cut.pull f, cut.pull g) ∈ kernel (cut.readProcess n).response ↔ s(f (), g ()) ∈ kernel n.asProcess.response := by
    intro n f g
    refine (mem_kernel _ _ _).trans ⟨fun heq => (mem_kernel n.asProcess.response _ _).mpr ?_, fun hin => funext fun _ => ?_⟩
    · have hat : n.asProcess.valueAtScale cut.scale (cut.pull f ()) = n.asProcess.valueAtScale cut.scale (cut.pull g ()) := congrFun heq ()
      change n.asProcess.valueAtScale cut.scale (coarsen cut.scale (f ())) = n.asProcess.valueAtScale cut.scale (coarsen cut.scale (g ())) at hat
      rw [hvalue, hvalue] at hat
      exact Set.singleton_injective hat
    · change n.asProcess.valueAtScale cut.scale (coarsen cut.scale (f ())) = n.asProcess.valueAtScale cut.scale (coarsen cut.scale (g ()))
      rw [hvalue, hvalue, (mem_kernel n.asProcess.response _ _).mp hin]
  have hout : s(cut.pull (fun _ => false), cut.pull (fun _ => true)) ∉ kernel (cut.readProcess m).response := by
    intro hin
    have hk := (hresponse m _ _).mp hin
    have hp := (Nested.mem_kernel_response_asProcess m _).mp hk p ⟨true, rfl⟩
    exact Bool.false_ne_true ((mem_kernel _ false true).mp hp)
  have hpull : ∀ x : cut.States, ∃ s, cut.pull (fun _ => s) = x := fun x => by
    obtain ⟨s, hs⟩ := Quotient.exists_rep (x ())
    exact ⟨s, funext fun _ => hs⟩
  have hconst : ∀ z, z ∈ kernel (cut.readProcess m').response := by
    intro z
    induction z with
    | _ x y =>
      obtain ⟨a, rfl⟩ := hpull x
      obtain ⟨b, rfl⟩ := hpull y
      refine (hresponse m' _ _).mpr ((mem_kernel _ _ _).mpr (funext fun i => ?_))
      cases i <;> rfl
  exact ⟨fun z _ => hconst z, fun hsub => hout (hsub (hconst _))⟩

/-- **Claim 25 (Joint prohibition), with no process.** Over one state, an arrangement with no process and the empty outcome meet the statement: no process excludes it, there being none, and nothing reaches it, there being no state in it. So `not_prohibition_of_subsingleton` needs a position. -/
theorem prohibition_of_no_process :
    ∃ (F : ForbidAllow Unit Empty) (O : Outcome Unit), (∀ i, ¬ Excludes (F.responseAt i) O) ∧ ¬ F.Reaches O :=
  ⟨{ finite := inferInstance, process := fun e => e.elim, joins := ∅, verdict := fun e => e.elim }, ∅,
    fun e => e.elim, fun ⟨_, hs, _⟩ => hs⟩

end Companion
