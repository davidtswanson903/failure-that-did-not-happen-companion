import Companion.Laws
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.OrderIsoNat

/-!
# The regress

Claim 4 (No recovery): a coarse-graining of a coarse-graining is one, evaluated
on a value that obtains; its kernel only grows; and on finite states a chain of them stabilizes. Claim 17 (Every level, every join) applies
monotonicity and nesting together, so it is in `Companion.Uptake`.

The route: `Law.obtains` gives closure in one rewriting. The kernel of `c` lies in the kernel of `g ∘ c` by congruence, and
residue is its size, which gives monotonicity. The kernels along a chain are then an increasing sequence in the finite
powerset of the pairs, which stabilizes.
-/

namespace Companion

variable {S : Type}

/-- **Claim 4 (No recovery).** A coarse-graining of a coarse-graining is itself a coarse-graining, `g ∘ c : S → D`, evaluated on
a value that obtains: in every situation its value is `g` of the value `c` gives there, and that value is `c` at the state
that obtains. -/
theorem Regress.closure {C D : Type} (c : S → C) (g : C → D) (w : Situation S) :
    evaluate (g ∘ c) w = g (evaluate c w) ∧ evaluate c w = c w.obtains := by
  rw [(Law.obtains (g ∘ c) w).1, (Law.obtains c w).1]
  exact ⟨rfl, rfl⟩

/-- The first step: the kernel of a coarse-graining lies in the kernel of any further one. -/
theorem kernel_subset_comp {C D : Type} (c : S → C) (g : C → D) : kernel c ⊆ kernel (g ∘ c) :=
  kernel_subset_of_carries ⟨g, rfl⟩

/-- On finite states any set of pairs is finite. -/
theorem finite_pairs [Fintype S] (X : Set (Sym2 S)) : X.Finite :=
  Set.toFinite X

/-- The second step: a larger kernel holds at least as many pairs of distinct states. -/
theorem residue_le_comp [Fintype S] {C D : Type} (c : S → C) (g : C → D) : residue c ≤ residue (g ∘ c) :=
  Set.ncard_le_ncard (fun _ hz => ⟨kernel_subset_comp c g hz.1, hz.2⟩) (finite_pairs _)

/-- The third step: residue grows exactly when the further map joins two values the earlier one gave, since exactly then
the larger kernel holds a pair of distinct states the smaller does not. -/
theorem residue_lt_comp_iff [Fintype S] {C D : Type} (c : S → C) (g : C → D) :
    residue c < residue (g ∘ c) ↔ ∃ s t, c s ≠ c t ∧ g (c s) = g (c t) := by
  constructor
  · intro hlt
    by_contra hnone
    push Not at hnone
    refine absurd (Set.ncard_le_ncard ?_ (finite_pairs _)) (not_le.mpr hlt)
    intro z hz
    refine ⟨?_, hz.2⟩
    induction z with
    | _ s t =>
      have hk : g (c s) = g (c t) := (mem_kernel (g ∘ c) s t).mp hz.1
      by_contra hne
      exact hnone s t ((mem_kernel c s t).not.mp hne) hk
  · rintro ⟨s, t, hne, hg⟩
    refine Set.ncard_lt_ncard ?_ (finite_pairs _)
    refine ⟨fun _ hz => ⟨kernel_subset_comp c g hz.1, hz.2⟩, fun hsub => ?_⟩
    have hin : s(s, t) ∈ distinctPairs (kernel (g ∘ c)) := by
      refine ⟨(mem_kernel (g ∘ c) s t).mpr hg, ?_⟩
      rw [Sym2.mk_isDiag_iff]
      rintro rfl
      exact hne rfl
    exact hne ((mem_kernel c s t).mp (hsub hin).1)

/-- **Claim 4 (No recovery).** Further coarse-graining never separates a pair an earlier one identified, so residue cannot
shrink, and it grows exactly when the further map joins two values the earlier one gave. The sizes use that `S` is finite. -/
theorem Regress.monotonicity [Fintype S] {C D : Type} (c : S → C) (g : C → D) :
    kernel c ⊆ kernel (g ∘ c) ∧ residue c ≤ residue (g ∘ c) ∧
      (residue c < residue (g ∘ c) ↔ ∃ s t, c s ≠ c t ∧ g (c s) = g (c t)) :=
  ⟨kernel_subset_comp c g, residue_le_comp c g, residue_lt_comp_iff c g⟩

/-- **Claim 4 (No recovery).** Residue can grow: on two states, the map that identifies everything has residue one and
the identity residue zero. -/
theorem residue_can_grow :
    ∃ (S C D : Type) (_ : Fintype S) (c : S → C) (g : C → D), residue c < residue (g ∘ c) :=
  ⟨Bool, Bool, Unit, inferInstance, id, fun _ => (),
    (residue_lt_comp_iff _ _).mpr ⟨false, true, Bool.false_ne_true, rfl⟩⟩

/-- **Claim 4 (No recovery), over any states.** Over any finite states that hold two distinct states, residue can grow: the map that identifies everything is a further map of the one that identifies nothing, and it joins two of its values. -/
theorem residue_can_grow_of_ne [Fintype S] {a b : S} (h : a ≠ b) :
    ∃ (C D : Type) (c : S → C) (g : C → D), residue c < residue (g ∘ c) :=
  ⟨S, Unit, id, fun _ => (), (residue_lt_comp_iff _ _).mpr ⟨a, b, h, rfl⟩⟩

/-- A chain of further coarse-graining: a first map from the states, then at each step a map of the last values. -/
structure Chain (S : Type) where
  /-- The values at each step. -/
  Value : ℕ → Type
  /-- The first coarse-graining. -/
  first : S → Value 0
  /-- The further map at each step. -/
  step : ∀ n, Value n → Value (n + 1)

/-- The coarse-graining a chain has reached at step `n`. -/
def Chain.map (ch : Chain S) : ∀ n, S → ch.Value n
  | 0 => ch.first
  | n + 1 => ch.step n ∘ ch.map n

/-- The kernels grow along a chain: each step is a further coarse-graining of the last. -/
theorem chain_kernel_monotone (ch : Chain S) : Monotone (fun n => kernel (ch.map n)) :=
  monotone_nat_of_le_succ fun n => kernel_subset_comp (ch.map n) (ch.step n)

/-- The kernels then stabilize: an increasing sequence of subsets of the finite set of pairs stops growing. -/
theorem chain_kernel_stabilizes [Fintype S] (ch : Chain S) :
    ∃ N, ∀ n, N ≤ n → kernel (ch.map n) = kernel (ch.map N) := by
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition
    (⟨fun n => kernel (ch.map n), chain_kernel_monotone ch⟩ : ℕ →o Set (Sym2 S))
  exact ⟨N, fun n hn => (hN n hn).symm⟩

/-- **Claim 4 (No recovery).** Along any chain of further coarse-graining, on finite states, the kernels grow and then
stabilize, and no further coarse-graining recovers what an earlier one identified. -/
theorem Regress.convergence [Fintype S] (ch : Chain S) :
    Monotone (fun n => kernel (ch.map n)) ∧
      (∃ N, ∀ n, N ≤ n → kernel (ch.map n) = kernel (ch.map N)) ∧
      ∀ m {D : Type} (g : ch.Value m → D), kernel (ch.map m) ⊆ kernel (g ∘ ch.map m) :=
  ⟨chain_kernel_monotone ch, chain_kernel_stabilizes ch, fun m _ g => kernel_subset_comp (ch.map m) g⟩

end Companion
