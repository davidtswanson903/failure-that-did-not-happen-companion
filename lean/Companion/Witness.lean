import Companion.Laws
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset

/-!
# The witness

Claim 25 (Joint prohibition), by the eight processes over the 256 states `Fin 8 → Bool`. A state raises some of eight concerns,
each process forbids exactly the states raising its concern, and the outcome is the states raising at least five: a state
raising `k` concerns has size `10 + 20 k`, the case of a project of `10 + 20 k` homes, and the outcome is size at least 100,
93 states. No process alone excludes the outcome and the arrangement never reaches it.

The route is an argument and uses no enumeration, but for the count of 93. A state raising all concerns but one is in the
outcome and its own process allows it, so no process excludes the outcome; a state in the outcome raises at least one
concern, whose process forbids it, so the arrangement never reaches the outcome.
-/

namespace Companion

/-- The 256 states: which of eight concerns a state raises. -/
abbrev WitnessState : Type :=
  Fin 8 → Bool

/-- How many concerns a state raises. -/
def raised (s : WitnessState) : ℕ :=
  (Finset.univ.filter fun i => s i = true).card

/-- The size of a state: 10 and 20 for each concern it raises. -/
def size (s : WitnessState) : ℕ :=
  10 + 20 * raised s

/-- The process for one concern: it is constituted to read that concern alone, makes that coarse-graining and responds
through it, forbidding exactly the states that raise the concern. -/
def review (i : Fin 8) : Process WitnessState where
  constitutive := ⟨Bool, fun s => s i⟩
  Index := Unit
  Value := fun _ => Bool
  further := fun _ => id
  Action := Verdict
  rule := fun v => if v () = true then Verdict.forbid else Verdict.allow

/-- The eight processes, as an arrangement whose responses only forbid or allow. -/
def witness : ForbidAllow WitnessState (Fin 8) where
  finite := inferInstance
  process := review
  joins := ∅
  verdict := fun _ a => a

/-- The outcome: the states of size at least 100. -/
def witnessOutcome : Outcome WitnessState :=
  {s | 100 ≤ size s}

/-- What each process does at a state, by the definitions. -/
theorem responseAt_witness (i : Fin 8) (s : WitnessState) :
    witness.responseAt i s = if s i = true then Verdict.forbid else Verdict.allow :=
  rfl

/-- Each process forbids exactly the states raising its concern. -/
theorem responseAt_eq_forbid_iff (i : Fin 8) (s : WitnessState) : witness.responseAt i s = Verdict.forbid ↔ s i = true := by
  rw [responseAt_witness]
  by_cases h : s i = true <;> simp [h]

/-- The state raising every concern but one. -/
def allBut (i : Fin 8) : WitnessState :=
  fun k => decide (k ≠ i)

/-- It raises seven concerns, for each of the eight. -/
theorem raised_allBut : ∀ i : Fin 8, raised (allBut i) = 7 := by
  decide

/-- The first step: no process alone excludes the outcome, since the state raising all but its concern is in the outcome
and it does not forbid there. -/
theorem not_excludes_witnessOutcome (i : Fin 8) : ¬ Excludes (witness.responseAt i) witnessOutcome := by
  intro hex
  have hin : allBut i ∈ witnessOutcome := by
    change 100 ≤ 10 + 20 * raised (allBut i)
    rw [raised_allBut i]
    omega
  have hraised : allBut i i = true := (responseAt_eq_forbid_iff i _).mp (hex _ hin)
  simp [allBut] at hraised

/-- The second step: the arrangement never reaches the outcome, since a state in it raises a concern, whose process forbids
there. -/
theorem not_reaches_witnessOutcome : ¬ witness.Reaches witnessOutcome := by
  rintro ⟨s, hs, hnone⟩
  have hsize : 100 ≤ 10 + 20 * raised s := hs
  have hpos : 0 < raised s := by omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact hnone i ((responseAt_eq_forbid_iff i s).mpr (Finset.mem_filter.mp hi).2)

/-- **Claim 25 (Joint prohibition).** Some arrangements never reach an outcome that no response in them alone excludes,
among arrangements whose responses only forbid or allow: there is one of eight processes over 256 states. -/
theorem Composition.prohibition :
    ∃ (S ι : Type) (_ : Fintype S) (_ : Fintype ι) (F : ForbidAllow S ι) (O : Outcome S),
      Fintype.card S = 256 ∧ Fintype.card ι = 8 ∧
        (∀ i, ¬ Excludes (F.responseAt i) O) ∧ ¬ F.Reaches O :=
  ⟨WitnessState, Fin 8, inferInstance, inferInstance, witness, witnessOutcome, by simp, by simp,
    not_excludes_witnessOutcome, not_reaches_witnessOutcome⟩

/-- **Claim 25 (Joint prohibition).** The size of the case: the outcome holds 93 of the 256 states. -/
theorem witnessOutcome_ncard : witnessOutcome.ncard = 93 := by
  have h : witnessOutcome = ↑(Finset.univ.filter fun s : WitnessState => 100 ≤ size s) := by
    ext s
    simp [witnessOutcome]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

end Companion
