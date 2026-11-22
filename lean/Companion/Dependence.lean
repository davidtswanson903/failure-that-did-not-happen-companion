import Companion.Basic
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.Independence.Basic

/-!
# Moving with, and how far

Claim 6 (Borrowing), its last clause. A weighting of the accessible states, positive at each and nothing outside them, reads "moves with" as
dependence under that weighting: two quantities move together when they are not independent. The count of cases is one such weighting. How far
a response can follow what it does not register is bounded by how far what it passes through moves with it, read as the information each carries
about the other, the divergence of their joint law from the product of their laws. The bound is data processing, Mathlib's `klDiv_map_le`.
-/

open MeasureTheory ProbabilityTheory InformationTheory

namespace Companion

variable {S : Type} [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- **Claim 6 (Borrowing), a weighting.** Weights on the states, positive at each accessible state and nothing outside them. The count of cases is
one such weighting. -/
def Weighs (μ : Measure S) (X : Accessible S) : Prop :=
  (∀ s ∈ X, μ {s} ≠ 0) ∧ μ Xᶜ = 0

/-- **Claim 6 (Borrowing), moving with.** Under a weighting, `b` moves with `q` when the two are not independent. -/
def MovesWith {Q B : Type} [MeasurableSpace Q] [MeasurableSpace B] (μ : Measure S) (q : S → Q) (b : S → B) : Prop :=
  ¬ IndepFun q b μ

/-- **Claim 6 (Borrowing), how far.** The information two quantities carry about each other under a weighting: the divergence of their joint law from
the product of their laws. -/
noncomputable def information {Q B : Type} [MeasurableSpace Q] [MeasurableSpace B] (μ : Measure S) (q : S → Q) (b : S → B) : ENNReal :=
  klDiv (μ.map fun s => (q s, b s)) ((μ.map q).prod (μ.map b))

/-- **Claim 6 (Borrowing), as far as it moves with it.** For a process, a weighting of the accessible states, any quantity `q` and any quantity `b`
the response passes through, those the process registers among them: the response carries no more information about `q` than `b` does; where `b`
does not move with `q`, neither does the response; and where `q` fixes `b` across the accessible states and `b` varies with `q` there, `b` moves
with `q`. -/
theorem Response.as_far_as (p : Process S) [MeasurableSpace p.Action] (μ : Measure S) [IsFiniteMeasure μ] (X : Accessible S) (hμ : Weighs μ X)
    {Q B : Type} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [MeasurableSpace B] [DiscreteMeasurableSpace B] (q : S → Q) (b : S → B)
    (hb : Carries b p.response) :
    information μ q p.response ≤ information μ q b ∧ (¬ MovesWith μ q b → ¬ MovesWith μ q p.response) ∧
      (Fixes X q b → VariesWith X b q → MovesWith μ q b) := by
  obtain ⟨h, hh⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · rw [hh]
    have hg : Measurable (Prod.map (id : Q → Q) h) := measurable_id.prodMap .of_discrete
    have hjoint : μ.map (fun s => (q s, (h ∘ b) s)) = (μ.map fun s => (q s, b s)).map (Prod.map id h) := by
      rw [Measure.map_map hg .of_discrete]
      rfl
    have hprod : (μ.map q).prod (μ.map (h ∘ b)) = ((μ.map q).prod (μ.map b)).map (Prod.map id h) := by
      rw [← Measure.map_prod_map _ _ measurable_id .of_discrete, Measure.map_id, Measure.map_map .of_discrete .of_discrete]
    unfold information
    rw [hjoint, hprod]
    exact klDiv_map_le _ _ hg
  · simp only [MovesWith, not_not]
    intro hind
    rw [hh]
    exact hind.comp measurable_id .of_discrete
  · rintro hfix ⟨s, hs, t, ht, -, hbst⟩ hind
    have hmul := hind.measure_inter_preimage_eq_mul {q s} {b t} .of_discrete .of_discrete
    have hq0 : μ (q ⁻¹' {q s}) ≠ 0 := fun h0 =>
      hμ.1 s hs (measure_mono_null (Set.singleton_subset_iff.mpr (show s ∈ q ⁻¹' {q s} from rfl)) h0)
    have hb0 : μ (b ⁻¹' {b t}) ≠ 0 := fun h0 =>
      hμ.1 t ht (measure_mono_null (Set.singleton_subset_iff.mpr (show t ∈ b ⁻¹' {b t} from rfl)) h0)
    have hne : μ (q ⁻¹' {q s} ∩ b ⁻¹' {b t}) ≠ 0 := by
      rw [hmul]
      exact mul_ne_zero hq0 hb0
    obtain ⟨u, hu, huX⟩ : ∃ u ∈ q ⁻¹' {q s} ∩ b ⁻¹' {b t}, u ∈ X := by
      by_contra hno
      push Not at hno
      exact hne (measure_mono_null (fun u hu => hno u hu) hμ.2)
    exact hbst ((hfix u huX s hs hu.1).symm.trans hu.2)

end Companion
