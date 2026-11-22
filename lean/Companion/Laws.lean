import Companion.Basic

/-!
# The laws

The three laws, each a theorem about the objects of `Companion.Basic`. Each proves a mathematical statement, and each proof unfolds a definition: the objects
are built so that the statement holds of them. None says anything about identification, that these mathematics are what holds of real arrangements. No proof touches
that. No law is an `axiom`.
-/

namespace Companion

variable {S : Type}

/-- **Claim 2 (The condition of response).** A coarse-graining is evaluated only on the state that obtains: its evaluation in a situation is its value at that state, and it is
the same in every situation where that state obtains, whatever would have obtained. This proves the mathematical statement, by unfolding `evaluate`, and says
nothing about identification. -/
theorem Law.obtains {C : Type} (c : S → C) (w : Situation S) :
    evaluate c w = c w.obtains ∧ ∀ w' : Situation S, w'.obtains = w.obtains → evaluate c w' = evaluate c w :=
  ⟨rfl, fun _ h => congrArg c h⟩

/-- A quantity a coarse-graining carries identifies every pair the coarse-graining identifies. -/
theorem kernel_subset_of_carries {C Q : Type} {c : S → C} {q : S → Q} (h : Carries c q) : kernel c ⊆ kernel q := by
  obtain ⟨g, rfl⟩ := h
  intro z
  induction z with
  | _ s t =>
    intro hz
    rw [mem_kernel] at hz ⊢
    exact congrArg g hz

/-- **Claim 2 (The condition of response).** A coarse-graining factors through the constitution of the process that makes it, so it identifies every pair that constitution
identifies. This proves the mathematical statement, the factoring by unfolding `Process.grainings`, and says nothing about identification. -/
theorem Law.constitution (p : Process S) (i : p.Index) :
    Carries p.constitutive (p.grainings i) ∧ p.constitution ⊆ kernel (p.grainings i) :=
  ⟨⟨p.further i, rfl⟩, kernel_subset_of_carries ⟨p.further i, rfl⟩⟩

/-- **Claim 2 (The condition of response).** A process's response depends on the states only through its coarse-grainings: it is a function of their values, read together.
This proves the mathematical statement, by unfolding `Process.response`, and says nothing about identification. -/
theorem Law.factorization (p : Process S) : p.Carries p.response :=
  ⟨p.rule, rfl⟩

end Companion
