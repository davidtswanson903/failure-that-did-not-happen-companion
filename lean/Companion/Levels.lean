import Companion.Compositions

/-!
# Levels

A nested arrangement of two levels, and what its levels do to Claim 9 (The between). The arrangement at the outer level holds
one process, the inner arrangement as a process, whose coarse-graining is composed from what is further in: it makes a
coarse-graining of the values of a member's. So the inner between and the outer between are two sets, and a process further in
can tell apart what the level above does not.

This fixes what a response of an arrangement is in Claim 9 (The between): the response of a process at the arrangement's own
level. A response further in can separate a pair in the between further out (`nested_response_separates`).
-/

namespace Companion

variable {S : Type}

/-- The inner level of a tower: an arrangement of two processes, with no joins among them. -/
def innerLevel (p q : Process S) : Arrangement S Bool :=
  ⟨inferInstance, fun b => cond b p q, ∅⟩

/-- The inner arrangement of a tower: `p` and `q` at its level, and as a process the level above reads `c`. -/
def towerInner {V : Type} (p q : Process S) (c : S → V) : Nested S :=
  .mk (Process.reading c) (innerLevel p q) (fun _ => none)

/-- A tower of two levels: the outer level holds one process, the inner arrangement, which as a process reads `c`. -/
def tower {V : Type} (p q : Process S) (c : S → V) : Nested S :=
  .mk (Process.reading c) ⟨inferInstance, fun _ : Unit => Process.reading c, ∅⟩
    (fun _ => some (towerInner p q c))

/-- A tower hangs together: the process at the outer position is the one its inner arrangement is, and the inner arrangement
has no arrangement among its processes. -/
theorem tower_coherent {V : Type} (p q : Process S) (c : S → V) : (tower p q c).Coherent := by
  refine .mk (fun _ n hn => ?_) (fun _ n hn => ?_)
  · obtain rfl : towerInner p q c = n := Option.some.inj hn
    rfl
  · obtain rfl : towerInner p q c = n := Option.some.inj hn
    exact .mk (fun _ _ h => absurd h (by simp)) (fun _ _ h => absurd h (by simp))

/-- At depth zero of a nested arrangement stands only itself. -/
theorem Nested.eq_of_atDepth_zero {n m : Nested S} (h : n.AtDepth 0 m) : m = n := by
  cases h
  rfl

/-- At depth one of a nested arrangement stands exactly what its positions are. -/
theorem Nested.atDepth_one_iff {self : Process S} {ι : Type} {level : Arrangement S ι} {inner : ι → Option (Nested S)} {m : Nested S} :
    (Nested.mk self level inner).AtDepth 1 m ↔ ∃ i, inner i = some m := by
  constructor
  · intro h
    cases h with
    | inside hi hm =>
      obtain rfl := Nested.eq_of_atDepth_zero hm
      exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    exact .inside hi (.here _)

/-- A pair lies in the between of a nested arrangement's own level exactly when it is a pair of distinct states every process
that stands there is constituted to identify. -/
theorem Nested.mem_between_iff {n : Nested S} {z : Sym2 S} :
    z ∈ n.between ↔ ¬ z.IsDiag ∧ ∀ p, n.HoldsProcess p → z ∈ p.constitution := by
  cases n with
  | mk self level inner =>
    constructor
    · rintro ⟨hd, hall⟩
      refine ⟨hd, fun p hp => ?_⟩
      obtain ⟨i, rfl⟩ := hp
      exact hall i
    · rintro ⟨hd, hall⟩
      exact ⟨hd, fun i => hall _ ⟨i, rfl⟩⟩

/-- At depth zero, the between at the level is the arrangement's own between. -/
theorem Nested.betweenAt_zero (n : Nested S) : n.betweenAt 0 = n.between := by
  ext z
  rw [Nested.mem_between_iff]
  constructor
  · rintro ⟨hd, hall⟩
    exact ⟨hd, fun p hp => hall n (.here n) p hp⟩
  · rintro ⟨hd, hall⟩
    refine ⟨hd, fun m hm p hp => ?_⟩
    obtain rfl := Nested.eq_of_atDepth_zero hm
    exact hall p hp

/-- At depth one, a pair lies in the between at the level exactly when it lies in the between of each arrangement its positions are,
so with one arrangement at that depth the between at the level is that arrangement's. -/
theorem Nested.mem_betweenAt_one_iff {self : Process S} {ι : Type} {level : Arrangement S ι} {inner : ι → Option (Nested S)} {z : Sym2 S} :
    z ∈ (Nested.mk self level inner).betweenAt 1 ↔ ¬ z.IsDiag ∧ ∀ i m, inner i = some m → z ∈ m.between := by
  constructor
  · rintro ⟨hd, hall⟩
    exact ⟨hd, fun i m hi => Nested.mem_between_iff.mpr ⟨hd, hall m (.inside hi (.here m))⟩⟩
  · rintro ⟨hd, hall⟩
    refine ⟨hd, fun m hm p hp => ?_⟩
    obtain ⟨i, hi⟩ := Nested.atDepth_one_iff.mp hm
    exact (Nested.mem_between_iff.mp (hall i m hi)).2 p hp

/-- A tower's inner arrangement is at depth one of it. -/
theorem tower_atDepth {V : Type} (p q : Process S) (c : S → V) : (tower p q c).AtDepth 1 (towerInner p q c) :=
  .inside (i := ()) rfl (.here _)

/-- The between at the outer level of a tower is the pairs of distinct states the inner arrangement, as a process, identifies. -/
theorem mem_between_tower {V : Type} (p q : Process S) (c : S → V) (z : Sym2 S) :
    z ∈ (tower p q c).between ↔ ¬ z.IsDiag ∧ z ∈ kernel c :=
  ⟨fun h => ⟨h.1, h.2 ()⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩

/-- With one arrangement at depth one, the between at that level of a tower is the between of its inner arrangement. -/
theorem tower_betweenAt_one {V : Type} (p q : Process S) (c : S → V) :
    (tower p q c).betweenAt 1 = (towerInner p q c).between := by
  ext z
  rw [tower, Nested.mem_betweenAt_one_iff]
  constructor
  · rintro ⟨_, hall⟩
    exact hall () _ rfl
  · intro hz
    refine ⟨hz.1, fun _ m hi => ?_⟩
    obtain rfl : towerInner p q c = m := Option.some.inj hi
    exact hz

/-- The between at the inner level of a tower is the pairs of distinct states its two processes both identify. -/
theorem mem_between_towerInner {V : Type} (p q : Process S) (c : S → V) (z : Sym2 S) :
    z ∈ (towerInner p q c).between ↔ ¬ z.IsDiag ∧ z ∈ p.constitution ∧ z ∈ q.constitution :=
  ⟨fun h => ⟨h.1, h.2 true, h.2 false⟩, fun h => ⟨h.1, fun b => by cases b; exacts [h.2.2, h.2.1]⟩⟩

/-- **Claim 9 (The between).** What a response of an arrangement must mean: a response further in can separate a pair in the
between further out. In a tower on two states, the inner process `q` tells them apart and responds to the difference,
and the level above, reading nothing of it, has that pair in its between. So the first clause holds of the responses of the
processes at an arrangement's own level. -/
theorem nested_response_separates :
    ∃ (S : Type) (_ : Fintype S) (T inner : Nested S) (q : Process S) (z : Sym2 S),
      T.Coherent ∧ T.AtDepth 1 inner ∧ inner.HoldsProcess q ∧ z ∈ T.between ∧ Separates q.response z := by
  let c : Bool → Unit := fun _ => ()
  let q : Process Bool := Process.reading id
  refine ⟨Bool, inferInstance, tower q q c, towerInner q q c, q, s(false, true), tower_coherent _ _ _, tower_atDepth _ _ _,
    ⟨true, rfl⟩, ?_, ?_⟩
  · exact (mem_between_tower _ _ _ _).mpr ⟨by simp [Sym2.mk_isDiag_iff], (mem_kernel c _ _).mpr rfl⟩
  · intro hin
    exact Bool.false_ne_true ((mem_kernel q.response false true).mp hin)

end Companion
