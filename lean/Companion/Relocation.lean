import Companion.Levels
import Mathlib.Data.Fin.VecNotation

/-!
# Relocation

Relocation: changing one process's constitution or response at one level can leave the between unchanged and
enlarge the between at another level of a nested arrangement. A level is a depth of nesting, as An arrangement says.

The route: the between at a level reads the constitutions of the processes at that level. An inner arrangement is one such
process at the level above, and the definition leaves open what its constitution is. Where it is composed from one member, a
change of that member reaches the level above and the two changes are one: `Nested.Coherent` makes the process above the inner
arrangement, and `Nested.ComposedFrom` makes what it tells apart the member's, before and after. A member can then stop telling a
pair apart that a sibling still tells apart: the inner between does not move, and the level above, which reads that member, loses the
pair. `relocation_of_conditions` states the conditions for a change of constitution and `relocation_by_response_of_conditions` for a
change of response, where no constitution moves and so no sibling is needed. `Composition.relocation` and `relocation_by_response` are
witnesses on four states with a distinct sibling and an inner between that is not empty.

Composed from all its members together, the two kinds part. For constitutions an unchanged between leaves the arrangement as a
process unchanged, so the level above has nothing to lose (`relocation_needs_other_self`). For responses it does not:
`relocation_from_all_responses` is a witness.
-/

namespace Companion

variable {S : Type}

/-! ## The two levels of a relocation -/

/-- The inner half of the conditions: a coarsening at one position, where a sibling still tells apart what it stops telling
apart, leaves the between of that level as it was. -/
theorem between_eq_of_sibling_tells {ι : Type} {A A' : Arrangement S ι} {k : ι}
    (hsib : ∀ i, i ≠ k → A'.process i = A.process i)
    (hcoarse : (A.process k).constitution ⊆ (A'.process k).constitution)
    (hkept : ∀ z, ¬ z.IsDiag → z ∈ (A'.process k).constitution → z ∉ (A.process k).constitution →
      ∃ i, i ≠ k ∧ z ∉ (A.process i).constitution) :
    A'.between = A.between := by
  ext z
  constructor
  · rintro ⟨hd, hall⟩
    have hothers : ∀ i, i ≠ k → z ∈ (A.process i).constitution := fun i hi => hsib i hi ▸ hall i
    refine ⟨hd, fun i => ?_⟩
    by_cases hi : i = k
    · subst hi
      by_contra hout
      obtain ⟨j, hj, hjout⟩ := hkept z hd (hall i) hout
      exact hjout (hothers j hj)
    · exact hothers i hi
  · rintro ⟨hd, hall⟩
    refine ⟨hd, fun i => ?_⟩
    by_cases hi : i = k
    · subst hi
      exact hcoarse (hall i)
    · rw [hsib i hi]
      exact hall i

/-- The inner half for a change of response: where every constitution stays, the between stays. -/
theorem between_eq_of_constitutions_stay {ι : Type} {A A' : Arrangement S ι}
    (hsame : ∀ i, (A'.process i).constitution = (A.process i).constitution) : A'.between = A.between := by
  ext z
  exact and_congr_right fun _ => forall_congr' fun i => by rw [hsame i]

/-- The outer half of the conditions: where the process at one position comes to identify a pair of distinct states that the
others at its level already identify, and loses nothing, the between of that level grows by that pair at least. -/
theorem between_ssubset_of_identifies {κ : Type} {O O' : Arrangement S κ} {m : κ}
    (hother : ∀ n, n ≠ m → O'.process n = O.process n)
    (hself : (O.process m).constitution ⊆ (O'.process m).constitution)
    {x : Sym2 S} (hd : ¬ x.IsDiag) (hin : x ∈ (O'.process m).constitution) (hout : x ∉ (O.process m).constitution)
    (hrest : ∀ n, n ≠ m → x ∈ (O.process n).constitution) :
    O.between ⊂ O'.between := by
  refine ⟨fun z hz => ⟨hz.1, fun n => ?_⟩, fun hsub => ?_⟩
  · by_cases hn : n = m
    · subst hn
      exact hself (hz.2 n)
    · rw [hother n hn]
      exact hz.2 n
  · have hmem : x ∈ O'.between := ⟨hd, fun n => by
      by_cases hn : n = m
      · subst hn
        exact hin
      · rw [hother n hn]
        exact hrest n hn⟩
    exact hout ((hsub hmem).2 m)

/-- Where a nested arrangement hangs together, the process at a position is the one the arrangement at that position is. -/
theorem Nested.Coherent.self_eq {self : Process S} {ι : Type} {level : Arrangement S ι} {inner : ι → Option (Nested S)}
    (h : (Nested.mk self level inner).Coherent) {i : ι} {n : Nested S} (hi : inner i = some n) : n.self = level.process i := by
  cases h with
  | mk hself _ => exact hself i n hi

/-- The step above both kinds of relocation. In a nested arrangement that hangs together before and after, with one position's
inner arrangement changing and nothing else changing above: where the inner between stays, the between at that depth stays, and
where the inner arrangement as a process comes to identify a pair no other process above tells apart, and loses nothing, the between
at the depth above grows. -/
theorem betweenAt_of_inner_change {ι κ : Type} {A A' : Arrangement S ι} {O O' : Arrangement S κ}
    {self self' top top' : Process S} {ins ins' : ι → Option (Nested S)} {tops tops' : κ → Option (Nested S)} {m : κ}
    (hT : (Nested.mk top O tops).Coherent) (hT' : (Nested.mk top' O' tops').Coherent)
    (hm : tops m = some (.mk self A ins)) (hm' : tops' m = some (.mk self' A' ins'))
    (hinner : A'.between = A.between)
    (hcoarse : self.constitution ⊆ self'.constitution)
    (htops : ∀ n, n ≠ m → tops' n = tops n) (hother : ∀ n, n ≠ m → O'.process n = O.process n)
    {x : Sym2 S} (hd : ¬ x.IsDiag) (hin : x ∈ self'.constitution) (hout : x ∉ self.constitution)
    (hrest : ∀ n, n ≠ m → x ∈ (O.process n).constitution) :
    (Nested.mk top' O' tops').betweenAt 1 = (Nested.mk top O tops).betweenAt 1 ∧
      (Nested.mk top O tops).betweenAt 0 ⊂ (Nested.mk top' O' tops').betweenAt 0 := by
  have hself : self = O.process m := hT.self_eq hm
  have hself' : self' = O'.process m := hT'.self_eq hm'
  subst hself hself'
  refine ⟨?_, ?_⟩
  · ext z
    rw [Nested.mem_betweenAt_one_iff, Nested.mem_betweenAt_one_iff]
    refine and_congr_right fun _ => ⟨fun h n k hk => ?_, fun h n k hk => ?_⟩
    · by_cases hn : n = m
      · subst hn
        obtain rfl : Nested.mk (O.process n) A ins = k := Option.some.inj (hm.symm.trans hk)
        change z ∈ A.between
        rw [← hinner]
        exact h n _ hm'
      · exact h n k ((htops n hn).trans hk)
    · by_cases hn : n = m
      · subst hn
        obtain rfl : Nested.mk (O'.process n) A' ins' = k := Option.some.inj (hm'.symm.trans hk)
        change z ∈ A'.between
        rw [hinner]
        exact h n _ hm
      · exact h n k ((htops n hn).symm.trans hk)
  · rw [Nested.betweenAt_zero, Nested.betweenAt_zero]
    exact between_ssubset_of_identifies hother hcoarse hd hin hout hrest

/-- **Claim 17 (Every level, every join).** In a nested arrangement that hangs together before and
after, whose inner arrangement as a process tells apart exactly what its member at position `k` tells apart, before and after. The
inner level: nothing else changes, the member only coarsens, and a sibling still tells apart what it stops telling apart. The level
above: nothing else changes, and no other process tells apart the pair the member stops telling apart. Then the inner between is as it
was, the between at that depth is as it was, and the between at the depth above grows. -/
theorem relocation_of_conditions {ι κ : Type} {A A' : Arrangement S ι} {O O' : Arrangement S κ}
    {self self' top top' : Process S} {ins ins' : ι → Option (Nested S)} {tops tops' : κ → Option (Nested S)} {k : ι} {m : κ}
    (hT : (Nested.mk top O tops).Coherent) (hT' : (Nested.mk top' O' tops').Coherent)
    (hm : tops m = some (.mk self A ins)) (hm' : tops' m = some (.mk self' A' ins'))
    (hc : (Nested.mk self A ins).ComposedFrom (A.process k)) (hc' : (Nested.mk self' A' ins').ComposedFrom (A'.process k))
    (hsib : ∀ i, i ≠ k → A'.process i = A.process i)
    (hcoarse : (A.process k).constitution ⊆ (A'.process k).constitution)
    (hkept : ∀ z, ¬ z.IsDiag → z ∈ (A'.process k).constitution → z ∉ (A.process k).constitution →
      ∃ i, i ≠ k ∧ z ∉ (A.process i).constitution)
    (htops : ∀ n, n ≠ m → tops' n = tops n) (hother : ∀ n, n ≠ m → O'.process n = O.process n)
    {x : Sym2 S} (hd : ¬ x.IsDiag) (hin : x ∈ (A'.process k).constitution) (hout : x ∉ (A.process k).constitution)
    (hrest : ∀ n, n ≠ m → x ∈ (O.process n).constitution) :
    (Nested.mk self' A' ins').between = (Nested.mk self A ins).between ∧
      (Nested.mk top' O' tops').betweenAt 1 = (Nested.mk top O tops).betweenAt 1 ∧
      (Nested.mk top O tops).betweenAt 0 ⊂ (Nested.mk top' O' tops').betweenAt 0 := by
  have he : self.constitution = (A.process k).constitution := hc.2
  have he' : self'.constitution = (A'.process k).constitution := hc'.2
  have hinner : A'.between = A.between := between_eq_of_sibling_tells hsib hcoarse hkept
  exact ⟨hinner, betweenAt_of_inner_change hT hT' hm hm' hinner (he ▸ he' ▸ hcoarse) htops hother hd (he' ▸ hin) (he ▸ hout) hrest⟩

/-- **Relocation, its conditions for a change of response.** In a nested arrangement that hangs together before and
after, whose inner arrangement as a process tells apart exactly what its member's response at position `k` tells apart, before and
after. The inner level: every constitution stays, and the member's response only coarsens. The level above: nothing else changes,
and no other process tells apart the pair the response stops telling apart. Then the inner between is as it was, the between at that
depth is as it was, and the between at the depth above grows. -/
theorem relocation_by_response_of_conditions {ι κ : Type} {A A' : Arrangement S ι} {O O' : Arrangement S κ}
    {self self' top top' : Process S} {ins ins' : ι → Option (Nested S)} {tops tops' : κ → Option (Nested S)} {k : ι} {m : κ}
    (hT : (Nested.mk top O tops).Coherent) (hT' : (Nested.mk top' O' tops').Coherent)
    (hm : tops m = some (.mk self A ins)) (hm' : tops' m = some (.mk self' A' ins'))
    (hc : (Nested.mk self A ins).ComposedFromResponse (A.process k))
    (hc' : (Nested.mk self' A' ins').ComposedFromResponse (A'.process k))
    (hsame : ∀ i, (A'.process i).constitution = (A.process i).constitution)
    (hcoarse : kernel (A.process k).response ⊆ kernel (A'.process k).response)
    (htops : ∀ n, n ≠ m → tops' n = tops n) (hother : ∀ n, n ≠ m → O'.process n = O.process n)
    {x : Sym2 S} (hd : ¬ x.IsDiag) (hin : x ∈ kernel (A'.process k).response) (hout : x ∉ kernel (A.process k).response)
    (hrest : ∀ n, n ≠ m → x ∈ (O.process n).constitution) :
    (Nested.mk self' A' ins').between = (Nested.mk self A ins).between ∧
      (Nested.mk top' O' tops').betweenAt 1 = (Nested.mk top O tops).betweenAt 1 ∧
      (Nested.mk top O tops).betweenAt 0 ⊂ (Nested.mk top' O' tops').betweenAt 0 := by
  have he : self.constitution = kernel (A.process k).response := hc.2
  have he' : self'.constitution = kernel (A'.process k).response := hc'.2
  have hinner : A'.between = A.between := between_eq_of_constitutions_stay hsame
  exact ⟨hinner, betweenAt_of_inner_change hT hT' hm hm' hinner (he ▸ he' ▸ hcoarse) htops hother hd (he' ▸ hin) (he ▸ hout) hrest⟩

/-! ## The witnesses -/

/-- The conditions for a change of constitution, in a tower whose inner arrangement as a process reads the member `p`. -/
theorem tower_relocates {p p' q : Process S} (hcoarse : p.constitution ⊆ p'.constitution)
    (hkept : ∀ z, ¬ z.IsDiag → z ∈ p'.constitution → z ∉ p.constitution → z ∉ q.constitution)
    {x : Sym2 S} (hd : ¬ x.IsDiag) (hin : x ∈ p'.constitution) (hout : x ∉ p.constitution) :
    (towerInner p' q p'.constitutive).between = (towerInner p q p.constitutive).between ∧
      (tower p' q p'.constitutive).betweenAt 1 = (tower p q p.constitutive).betweenAt 1 ∧
      (tower p q p.constitutive).betweenAt 0 ⊂ (tower p' q p'.constitutive).betweenAt 0 :=
  relocation_of_conditions (A := innerLevel p q) (A' := innerLevel p' q) (k := true) (m := ())
    (tower_coherent p q p.constitutive) (tower_coherent p' q p'.constitutive) rfl rfl
    ⟨⟨true, rfl⟩, rfl⟩ ⟨⟨true, rfl⟩, rfl⟩
    (fun i hi => by
      cases i with
      | false => rfl
      | true => exact absurd rfl hi)
    hcoarse (fun z hz hzin hzout => ⟨false, Bool.false_ne_true, hkept z hz hzin hzout⟩)
    (fun n hn => absurd (Subsingleton.elim n ()) hn) (fun n hn => absurd (Subsingleton.elim n ()) hn)
    hd hin hout (fun n hn => absurd (Subsingleton.elim n ()) hn)

/-- The conditions for a change of response, in a tower whose inner arrangement as a process reads the member's response. -/
theorem tower_relocates_by_response {p p' q : Process S} (hsame : p'.constitution = p.constitution)
    (hcoarse : kernel p.response ⊆ kernel p'.response)
    {x : Sym2 S} (hd : ¬ x.IsDiag) (hin : x ∈ kernel p'.response) (hout : x ∉ kernel p.response) :
    (towerInner p' q p'.response).between = (towerInner p q p.response).between ∧
      (tower p' q p'.response).betweenAt 1 = (tower p q p.response).betweenAt 1 ∧
      (tower p q p.response).betweenAt 0 ⊂ (tower p' q p'.response).betweenAt 0 :=
  relocation_by_response_of_conditions (A := innerLevel p q) (A' := innerLevel p' q) (k := true) (m := ())
    (tower_coherent p q p.response) (tower_coherent p' q p'.response) rfl rfl
    ⟨⟨true, rfl⟩, rfl⟩ ⟨⟨true, rfl⟩, rfl⟩
    (fun i => by
      cases i with
      | false => rfl
      | true => exact hsame)
    hcoarse (fun n hn => absurd (Subsingleton.elim n ()) hn) (fun n hn => absurd (Subsingleton.elim n ()) hn)
    hd hin hout (fun n hn => absurd (Subsingleton.elim n ()) hn)

/-- The member of the witnesses before the change, on four states: it identifies states 0 and 1, and tells the rest apart. -/
def memberBefore : Fin 4 → Fin 3 :=
  ![0, 0, 1, 2]

/-- What the change makes of the member's values: the last two come to one. -/
def merged : Fin 3 → Fin 2 :=
  ![0, 1, 1]

/-- The sibling of the witnesses: it identifies states 0, 1 and 3, and tells state 2 from them. -/
def siblingMap : Fin 4 → Bool :=
  ![false, false, true, false]

/-- What the member identifies before the change, it identifies after. -/
theorem merged_coarsens : ∀ s t : Fin 4, memberBefore s = memberBefore t → merged (memberBefore s) = merged (memberBefore t) := by
  decide

/-- What the member comes to identify, the sibling still tells apart. -/
theorem sibling_tells : ∀ s t : Fin 4, merged (memberBefore s) = merged (memberBefore t) → memberBefore s ≠ memberBefore t →
    siblingMap s ≠ siblingMap t := by
  decide

/-- The pair the witnesses move: states 2 and 3 are distinct. -/
theorem not_isDiag_two_three : ¬ (s((2 : Fin 4), (3 : Fin 4)) : Sym2 (Fin 4)).IsDiag := by
  rw [Sym2.mk_isDiag_iff]
  decide

/-- The member tells states 2 and 3 apart before the change. -/
theorem two_three_not_mem_kernel : s((2 : Fin 4), (3 : Fin 4)) ∉ kernel memberBefore := fun h =>
  absurd ((mem_kernel memberBefore 2 3).mp h) (by decide)

/-- The member and its sibling are not constituted alike: the sibling identifies states 0 and 3, and the member does not. -/
theorem member_ne_sibling {p q : Process (Fin 4)} (hp : p.constitution = kernel memberBefore)
    (hq : q.constitution = kernel siblingMap) : p ≠ q := by
  rintro rfl
  have hin : s((0 : Fin 4), (3 : Fin 4)) ∈ kernel siblingMap := (mem_kernel siblingMap 0 3).mpr (by decide)
  have hmem : s((0 : Fin 4), (3 : Fin 4)) ∈ kernel memberBefore := hp ▸ hq.symm ▸ hin
  exact absurd ((mem_kernel memberBefore 0 3).mp hmem) (by decide)

/-- The inner between of the witnesses is not empty: the member and its sibling both identify states 0 and 1, before and after. -/
theorem zero_one_mem_between {V : Type} {p q : Process (Fin 4)} (c : Fin 4 → V) (hp : s((0 : Fin 4), (1 : Fin 4)) ∈ p.constitution)
    (hq : s((0 : Fin 4), (1 : Fin 4)) ∈ q.constitution) : (towerInner p q c).between.Nonempty :=
  ⟨s(0, 1), (mem_between_towerInner p q c _).mpr ⟨by rw [Sym2.mk_isDiag_iff]; decide, hp, hq⟩⟩

/-- **Claim 17 (Every level, every join).** Changing one process's constitution at one level can leave the between unchanged and enlarge
the between at another level of a nested arrangement. On four states, a tower's inner arrangement holds a member `p` and a distinct
sibling `q`, and as a process it tells apart what `p` tells apart. The two identify one pair, so the between at depth one is not
empty. `p` comes to identify a pair that `q` still tells apart: the between at depth one is as it was, and the between at depth zero
grows. -/
theorem Composition.relocation :
    ∃ (S : Type) (_ : Fintype S) (p p' q : Process S),
      3 ≤ Fintype.card S ∧ p ≠ q ∧ p' ≠ q ∧ p.constitution ≠ p'.constitution ∧
        (tower p q p.constitutive).Coherent ∧ (tower p' q p'.constitutive).Coherent ∧
        (tower p q p.constitutive).AtDepth 1 (towerInner p q p.constitutive) ∧
        (tower p' q p'.constitutive).AtDepth 1 (towerInner p' q p'.constitutive) ∧
        (towerInner p q p.constitutive).ComposedFrom p ∧ (towerInner p' q p'.constitutive).ComposedFrom p' ∧
        (towerInner p q p.constitutive).HoldsProcess q ∧ (towerInner p' q p'.constitutive).HoldsProcess q ∧
        ((tower p q p.constitutive).betweenAt 1).Nonempty ∧
        (tower p' q p'.constitutive).betweenAt 1 = (tower p q p.constitutive).betweenAt 1 ∧
        (tower p q p.constitutive).betweenAt 0 ⊂ (tower p' q p'.constitutive).betweenAt 0 := by
  let p : Process (Fin 4) := Process.reading memberBefore
  let p' : Process (Fin 4) := Process.reading (merged ∘ memberBefore)
  let q : Process (Fin 4) := Process.reading siblingMap
  have hcoarse : p.constitution ⊆ p'.constitution := by
    intro z
    induction z with
    | _ s t => exact fun h => (mem_kernel _ s t).mpr (merged_coarsens s t ((mem_kernel memberBefore s t).mp h))
  have hkept : ∀ z, ¬ z.IsDiag → z ∈ p'.constitution → z ∉ p.constitution → z ∉ q.constitution := by
    intro z
    induction z with
    | _ s t =>
      intro _ hin hout hq
      refine sibling_tells s t ((mem_kernel (merged ∘ memberBefore) s t).mp hin)
        (fun h => hout ((mem_kernel memberBefore s t).mpr h)) ((mem_kernel siblingMap s t).mp hq)
  have hin : s((2 : Fin 4), (3 : Fin 4)) ∈ p'.constitution := (mem_kernel (merged ∘ memberBefore) 2 3).mpr (by decide)
  have hout : s((2 : Fin 4), (3 : Fin 4)) ∉ p.constitution := two_three_not_mem_kernel
  have hall := tower_relocates (q := q) hcoarse hkept not_isDiag_two_three hin hout
  have h01p : s((0 : Fin 4), (1 : Fin 4)) ∈ p.constitution := (mem_kernel memberBefore 0 1).mpr (by decide)
  have h01q : s((0 : Fin 4), (1 : Fin 4)) ∈ q.constitution := (mem_kernel siblingMap 0 1).mpr (by decide)
  have hne : p ≠ q := member_ne_sibling rfl rfl
  have hne' : p' ≠ q := by
    intro heq
    have hmem : s((0 : Fin 4), (3 : Fin 4)) ∈ p'.constitution := heq ▸ (mem_kernel siblingMap 0 3).mpr (by decide)
    exact absurd ((mem_kernel (merged ∘ memberBefore) 0 3).mp hmem) (by decide)
  refine ⟨Fin 4, inferInstance, p, p', q, by simp, hne, hne', fun heq => hout (heq ▸ hin), tower_coherent _ _ _, tower_coherent _ _ _,
    tower_atDepth _ _ _, tower_atDepth _ _ _, ⟨⟨true, rfl⟩, rfl⟩, ⟨⟨true, rfl⟩, rfl⟩, ⟨false, rfl⟩, ⟨false, rfl⟩, ?_, hall.2.1, hall.2.2⟩
  rw [tower_betweenAt_one]
  exact zero_one_mem_between _ h01p h01q

/-- **Relocation.** Changing one process's response at one level can leave the between unchanged and enlarge the
between at another level of a nested arrangement. On four states, a tower's inner arrangement holds a member `p` and a distinct
sibling `q`, and as a process it tells apart what `p`'s response tells apart. The rule of `p` comes to merge two values. Its
constitution and its coarse-grainings stay, so the between at depth one is as it was, and it is not empty, and the between at depth zero
grows. This reads a response, a quantity of the states, as a coarse-graining the level above can make its own of. -/
theorem relocation_by_response :
    ∃ (S : Type) (_ : Fintype S) (p q : Process S) (B B' : Type) (g : (∀ k, p.Value k) → B) (g' : (∀ k, p.Value k) → B'),
      3 ≤ Fintype.card S ∧ p.withRule g ≠ q ∧ p.withRule g' ≠ q ∧
        (p.withRule g').constitution = (p.withRule g).constitution ∧
        kernel (p.withRule g).response ≠ kernel (p.withRule g').response ∧
        (tower (p.withRule g) q (p.withRule g).response).Coherent ∧
        (tower (p.withRule g') q (p.withRule g').response).Coherent ∧
        (tower (p.withRule g) q (p.withRule g).response).AtDepth 1 (towerInner (p.withRule g) q (p.withRule g).response) ∧
        (tower (p.withRule g') q (p.withRule g').response).AtDepth 1 (towerInner (p.withRule g') q (p.withRule g').response) ∧
        (towerInner (p.withRule g) q (p.withRule g).response).ComposedFromResponse (p.withRule g) ∧
        (towerInner (p.withRule g') q (p.withRule g').response).ComposedFromResponse (p.withRule g') ∧
        (towerInner (p.withRule g) q (p.withRule g).response).HoldsProcess q ∧
        (towerInner (p.withRule g') q (p.withRule g').response).HoldsProcess q ∧
        ((tower (p.withRule g) q (p.withRule g).response).betweenAt 1).Nonempty ∧
        (tower (p.withRule g') q (p.withRule g').response).betweenAt 1 = (tower (p.withRule g) q (p.withRule g).response).betweenAt 1 ∧
        (tower (p.withRule g) q (p.withRule g).response).betweenAt 0 ⊂ (tower (p.withRule g') q (p.withRule g').response).betweenAt 0 := by
  let p : Process (Fin 4) := Process.reading memberBefore
  let q : Process (Fin 4) := Process.reading siblingMap
  let g : (∀ k, p.Value k) → Fin 3 := fun v => v ()
  let g' : (∀ k, p.Value k) → Fin 2 := fun v => merged (v ())
  have hcoarse : kernel (p.withRule g).response ⊆ kernel (p.withRule g').response := by
    intro z
    induction z with
    | _ s t => exact fun h => (mem_kernel _ s t).mpr (merged_coarsens s t ((mem_kernel (p.withRule g).response s t).mp h))
  have hin : s((2 : Fin 4), (3 : Fin 4)) ∈ kernel (p.withRule g').response :=
    (mem_kernel (merged ∘ memberBefore) 2 3).mpr (by decide)
  have hout : s((2 : Fin 4), (3 : Fin 4)) ∉ kernel (p.withRule g).response := two_three_not_mem_kernel
  have hall := tower_relocates_by_response (p := p.withRule g) (p' := p.withRule g') (q := q) rfl hcoarse not_isDiag_two_three hin hout
  have h01p : s((0 : Fin 4), (1 : Fin 4)) ∈ (p.withRule g).constitution := (mem_kernel memberBefore 0 1).mpr (by decide)
  have h01q : s((0 : Fin 4), (1 : Fin 4)) ∈ q.constitution := (mem_kernel siblingMap 0 1).mpr (by decide)
  refine ⟨Fin 4, inferInstance, p, q, Fin 3, Fin 2, g, g', by simp, member_ne_sibling rfl rfl, member_ne_sibling rfl rfl, rfl,
    fun heq => hout (heq ▸ hin), tower_coherent _ _ _, tower_coherent _ _ _, tower_atDepth _ _ _, tower_atDepth _ _ _,
    ⟨⟨true, rfl⟩, rfl⟩, ⟨⟨true, rfl⟩, rfl⟩, ⟨false, rfl⟩, ⟨false, rfl⟩, ?_, hall.2.1, hall.2.2⟩
  rw [tower_betweenAt_one]
  exact zero_one_mem_between _ h01p h01q

/-! ## Composed from all the members together -/

/-- The pair of the two states of `Bool`. -/
theorem not_isDiag_false_true : ¬ (s(false, true) : Sym2 Bool).IsDiag := by
  simp [Sym2.mk_isDiag_iff]

/-- An inner arrangement that as a process reads both its members' responses is composed from all their responses together. -/
theorem towerInner_composedFromAllResponses (p q : Process S) :
    (towerInner p q fun s => (p.response s, q.response s)).ComposedFromAllResponses := by
  intro z
  induction z with
  | _ s t =>
    change s(s, t) ∈ kernel (fun s => (p.response s, q.response s)) ↔ ∀ i : Bool, s(s, t) ∈ kernel (cond i p q).response
    simp only [mem_kernel, Bool.forall_bool, Bool.cond_false, Bool.cond_true, Prod.mk.injEq]
    exact and_comm

/-- **Relocation.** Relocation by response happens even where the arrangement as a process is composed from all
its members' responses together. On two states, `p` and `q` are both constituted to tell the states apart, `q` responds with a
constant and `p` with what it reads, and the arrangement as a process reads both responses. The rule of `p` comes to give a constant: every
constitution stays, so the between at depth one is as it was, here empty, and the between at depth zero grows. So "not from all of them
together" holds of constitutions (`relocation_needs_other_self`) and not of responses. -/
theorem relocation_from_all_responses :
    ∃ (S : Type) (_ : Fintype S) (p p' q : Process S) (V V' : Type) (c : S → V) (c' : S → V'),
      p'.constitution = p.constitution ∧
        (towerInner p q c).ComposedFromAllResponses ∧ (towerInner p' q c').ComposedFromAllResponses ∧
        (tower p q c).Coherent ∧ (tower p' q c').Coherent ∧
        (towerInner p' q c').between = (towerInner p q c).between ∧
        (tower p q c).between ⊂ (tower p' q c').between := by
  let p : Process Bool := Process.reading id
  let p' : Process Bool := p.withRule fun _ => ()
  let q : Process Bool := p.withRule fun _ => ()
  let c : Bool → Bool × Unit := fun s => (p.response s, q.response s)
  let c' : Bool → Unit × Unit := fun s => (p'.response s, q.response s)
  have hout : s(false, true) ∉ kernel c := fun hin =>
    Bool.false_ne_true (congrArg Prod.fst ((mem_kernel c false true).mp hin))
  have hin : s(false, true) ∈ kernel c' := (mem_kernel c' false true).mpr rfl
  refine ⟨Bool, inferInstance, p, p', q, Bool × Unit, Unit × Unit, c, c', rfl, towerInner_composedFromAllResponses p q,
    towerInner_composedFromAllResponses p' q, tower_coherent _ _ _, tower_coherent _ _ _, ?_, ?_⟩
  · ext z
    rw [mem_between_towerInner, mem_between_towerInner]
    exact Iff.rfl
  · refine ⟨fun z hz => ?_, fun hsub => ?_⟩
    · exact (mem_between_tower _ _ _ z).mpr ⟨((mem_between_tower _ _ _ z).mp hz).1, mem_kernel_const ((), ()) z⟩
    · have hmem : s(false, true) ∈ (tower p' q c').between :=
        (mem_between_tower _ _ _ _).mpr ⟨not_isDiag_false_true, hin⟩
      exact hout ((mem_between_tower _ _ _ _).mp (hsub hmem)).2

/-- A constitution holds every pair of one state, as the kernel of any map does. -/
theorem mem_constitution_of_isDiag (p : Process S) {z : Sym2 S} (hz : z.IsDiag) : z ∈ p.constitution :=
  hz.map

/-- **Claim 17 (Every level, every join).** Where an inner arrangement as a process is composed from all
its members' constitutions together, before and after, an unchanged between at its level leaves its constitution unchanged. In a
nested arrangement that hangs together, with nothing else changing above, the between at the level above then stays too. So a
relocation of this upward kind needs the arrangement as a process to be composed otherwise than from all its members' constitutions together, before or after. It need not be composed more coarsely (`relocation_without_coarser_self`). -/
theorem relocation_needs_other_self {ι κ : Type} {A A' : Arrangement S ι} {O O' : Arrangement S κ}
    {self self' top top' : Process S} {ins ins' : ι → Option (Nested S)} {tops tops' : κ → Option (Nested S)} {m : κ}
    (hT : (Nested.mk top O tops).Coherent) (hT' : (Nested.mk top' O' tops').Coherent)
    (hm : tops m = some (.mk self A ins)) (hm' : tops' m = some (.mk self' A' ins'))
    (hc : (Nested.mk self A ins).ComposedFromAll) (hc' : (Nested.mk self' A' ins').ComposedFromAll)
    (hbetween : A'.between = A.between) (hother : ∀ n, n ≠ m → O'.process n = O.process n) :
    self'.constitution = self.constitution ∧ (Nested.mk top' O' tops').between = (Nested.mk top O tops).between := by
  have hsame : self'.constitution = self.constitution := by
    ext z
    by_cases hd : z.IsDiag
    · exact ⟨fun _ => mem_constitution_of_isDiag self hd, fun _ => mem_constitution_of_isDiag self' hd⟩
    · have hiff : (∀ i, z ∈ (A'.process i).constitution) ↔ ∀ i, z ∈ (A.process i).constitution := by
        constructor
        · intro h
          exact ((hbetween ▸ (⟨hd, h⟩ : z ∈ A'.between) : z ∈ A.between)).2
        · intro h
          have hin : z ∈ A'.between := hbetween.symm ▸ (⟨hd, h⟩ : z ∈ A.between)
          exact hin.2
      rw [hc' z, hc z, hiff]
  refine ⟨hsame, ?_⟩
  have hself : self = O.process m := hT.self_eq hm
  have hself' : self' = O'.process m := hT'.self_eq hm'
  subst hself hself'
  apply between_eq_of_constitutions_stay
  intro n
  by_cases hn : n = m
  · subst hn
    exact hsame
  · rw [hother n hn]

end Companion
