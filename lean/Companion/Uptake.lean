import Companion.Regress
import Companion.Compositions

/-!
# Uptake

Claim 17 (Every level, every join): what a process makes of a coarse-graining it takes up composes with that process's constitution, so nesting and monotonicity
cover it with no further principle. It sits after the compositions because its proof applies `Composition.nesting` and
`Regress.monotonicity` themselves.

The route: what the taker of a join makes is at once a map of the source's values, by the join, and a map of its own constitutive
values, by `Law.constitution`. So `Composition.nesting` applies to it from either side, and `Regress.monotonicity` gives the
kernels and the residues from either side. And since it is a map of the taker's constitutive values, it carries nothing beyond what the
taker already tells apart: where the source separates a pair the taker's constitution identifies, the join's map gives the two values
one value. A join exists whenever a process takes up a coarse-graining another makes (`Process.joinOfTakeUp`), and
`join_occurs` is one whose map is not constant, between processes constituted differently.
-/

namespace Companion

variable {S : Type}

/-- What a join makes is a further coarse-graining of its source, so it identifies every pair the source identifies. -/
theorem join_source_subset {ι : Type} {process : ι → Process S} (j : Join process) :
    kernel ((process j.giver).grainings j.source) ⊆ kernel ((process j.taker).grainings j.made) :=
  kernel_subset_of_carries ⟨j.further, funext j.made_eq⟩

/-- What a join makes, written as the further coarse-graining of its source that it is. -/
theorem join_made_eq_comp {ι : Type} {process : ι → Process S} (j : Join process) :
    ((process j.taker).grainings j.made).map = j.further ∘ ((process j.giver).grainings j.source).map :=
  funext j.made_eq

/-- **Claim 17 (Every level, every join).** What a process makes of a coarse-graining it takes up composes with that process's constitution, so nesting and
monotonicity cover it with no further principle. What the taker of a join makes factors through what it is constituted to make, and through the
source. By `Composition.nesting`, it separates no pair the source identifies or its constitution identifies, and nothing the taker composes from
what it makes, the taken-up one among them, separates a pair in its constitution. By `Regress.monotonicity`, its residue is at least the
source's and at least the constitution's, and grows from the source's exactly when the join's map joins two values the source gave. And the join
carries nothing beyond what the taker already tells apart: at a pair in its constitution, the map gives the source's two values one value. -/
theorem Regress.uptake [Fintype S] {ι : Type} {process : ι → Process S} (j : Join process) :
    Carries (process j.taker).constitutive ((process j.taker).grainings j.made) ∧
      Carries ((process j.giver).grainings j.source) ((process j.taker).grainings j.made) ∧
      kernel ((process j.giver).grainings j.source) ⊆ kernel ((process j.taker).grainings j.made) ∧
      (process j.taker).constitution ⊆ kernel ((process j.taker).grainings j.made) ∧
      (∀ {D : Type} (h : (∀ k, (process j.taker).Value k) → D),
        (process j.taker).constitution ⊆ kernel (fun s => h (fun k => (process j.taker).grainings k s))) ∧
      residue ((process j.giver).grainings j.source) ≤ residue ((process j.taker).grainings j.made) ∧
      residue (process j.taker).constitutive ≤ residue ((process j.taker).grainings j.made) ∧
      (residue ((process j.giver).grainings j.source) < residue ((process j.taker).grainings j.made) ↔
        ∃ s t, (process j.giver).grainings j.source s ≠ (process j.giver).grainings j.source t ∧
          j.further ((process j.giver).grainings j.source s) = j.further ((process j.giver).grainings j.source t)) ∧
      ∀ s t, s(s, t) ∈ (process j.taker).constitution →
        j.further ((process j.giver).grainings j.source s) = j.further ((process j.giver).grainings j.source t) := by
  have hmono := Regress.monotonicity ((process j.giver).grainings j.source).map j.further
  have hmono' := Regress.monotonicity (process j.taker).constitutive.map ((process j.taker).further j.made)
  rw [← join_made_eq_comp j] at hmono
  refine ⟨⟨(process j.taker).further j.made, rfl⟩, ⟨j.further, join_made_eq_comp j⟩, ?_, ?_, ?_, hmono.2.1, hmono'.2.1, hmono.2.2, ?_⟩
  · intro z hz
    have hnest := Composition.nesting (κ := Unit) (fun _ => ((process j.giver).grainings j.source).map) (fun v => j.further (v ()))
      (Set.mem_iInter.mpr fun _ => hz)
    rwa [show (fun s => j.further (((process j.giver).grainings j.source).map s)) = ((process j.taker).grainings j.made).map from
      (join_made_eq_comp j).symm] at hnest
  · intro z hz
    exact Composition.nesting (κ := Unit) (fun _ => (process j.taker).constitutive.map)
      (fun v => (process j.taker).further j.made (v ())) (Set.mem_iInter.mpr fun _ => hz)
  · intro D h z hz
    exact Composition.nesting (fun k => ((process j.taker).grainings k).map) h
      (Set.mem_iInter.mpr fun k => mem_grainings_of_mem_constitution hz k)
  · intro s t hst
    exact (join_supplies_nothing j).2 s t hst

/-- A taking up is a join: where `p` makes a map `f` of its constitutive values equal to a map `h` of the values of a coarse-graining
`q` makes, the two stand as giver and taker in an arrangement's family. -/
def Process.joinOfTakeUp (p q : Process S) (i : q.Index) {V : Type} (h : (q.grainings i).Value → V)
    (f : p.constitutive.Value → V) (hf : ∀ s, f (p.constitutive s) = h (q.grainings i s)) :
    Join (fun b : Bool => cond b (p.takeUp f) q) where
  taker := true
  giver := false
  another := Bool.false_ne_true
  source := i
  made := none
  further := h
  made_eq := hf

/-- **Claim 17 (Every level, every join).** A join occurs, between processes constituted differently and with a map that is not constant. On two bits, the
giver reads both and makes that reading; the taker is constituted to read the first bit alone, and takes up the giver's coarse-graining by making the
negation of the first bit. The source separates a pair the taker's constitution identifies, and what the taker makes identifies it. -/
theorem join_occurs :
    ∃ (S ι : Type) (_ : Fintype S) (A : Arrangement S ι) (j : Join A.process),
      j ∈ A.joins ∧ (A.process j.giver).constitution ≠ (A.process j.taker).constitution ∧
        (∃ x y, j.further x ≠ j.further y) ∧
        ∃ s t, s(s, t) ∈ (A.process j.taker).constitution ∧
          (A.process j.giver).grainings j.source s ≠ (A.process j.giver).grainings j.source t ∧
          (A.process j.taker).grainings j.made s = (A.process j.taker).grainings j.made t := by
  let p : Process (Bool × Bool) := Process.reading Prod.fst
  let q : Process (Bool × Bool) := Process.reading id
  let h : Bool × Bool → Bool := fun s => !s.1
  let f : Bool → Bool := fun a => !a
  let j := Process.joinOfTakeUp p q () h f (fun _ => rfl)
  let A : Arrangement (Bool × Bool) Bool := ⟨inferInstance, fun b => cond b (p.takeUp f) q, {j}⟩
  have hpair : s(((false, false) : Bool × Bool), ((false, true) : Bool × Bool)) ∈ p.constitution :=
    (mem_kernel Prod.fst _ _).mpr rfl
  refine ⟨Bool × Bool, Bool, inferInstance, A, j, rfl, fun heq => ?_, ⟨(false, false), (true, false), ?_⟩,
    (false, false), (false, true), hpair, ?_, rfl⟩
  · have hkernels : kernel (id : Bool × Bool → Bool × Bool) = kernel (Prod.fst : Bool × Bool → Bool) := heq
    have hmem : s(((false, false) : Bool × Bool), ((false, true) : Bool × Bool)) ∈ kernel (id : Bool × Bool → Bool × Bool) := by
      rw [hkernels]
      exact hpair
    exact absurd ((mem_kernel id _ _).mp hmem) (by decide)
  · exact Bool.false_ne_true.symm
  · intro heq
    have hsame : ((false, false) : Bool × Bool) = (false, true) := heq
    exact absurd hsame (by decide)

/-- **Claim 17 (Every level, every join), why a join is shown with a map that is not constant.** A taker that makes a constant coarse-graining has a
join with any other process and any coarse-graining it makes, its map constant. Such a join ties the two processes to nothing, so that
a join exists says nothing unless its map is not constant. -/
theorem exists_join_of_constant {ι : Type} {process : ι → Process S} {g t : ι} (hne : g ≠ t) (source : (process g).Index)
    (made : (process t).Index) (v : ((process t).grainings made).Value) (hv : ∀ s, (process t).grainings made s = v) :
    ∃ j : Join process, j.giver = g ∧ j.taker = t ∧ ∀ x y, j.further x = j.further y :=
  ⟨⟨t, g, hne, source, made, fun _ => v, hv⟩, rfl, rfl, fun _ _ => rfl⟩

end Companion
