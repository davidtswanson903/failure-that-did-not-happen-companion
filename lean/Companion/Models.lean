import Companion.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Sym

/-!
# Two models in closed form

The companion's Model S and Model A. Model S reads the sieve as a chain on three states, held, unheld and cut, and its survival, years kept,
hazard and survivors' worth follow in closed form. Model A reads what an arrangement is for as a quantity and measures how much of the
accessible states a register settles it on. Neither is a claim of the book; each is proved as stated, and the rates and sizes it is run at are
the scripts'.
-/

open Finset Filter Topology

namespace Companion

/-! ## Model A: adequacy for a purpose -/

section Adequacy

variable {S C Q : Type} [DecidableEq C] [DecidableEq Q]

/-- **Model A (Adequacy for a purpose), the region.** The accessible states whose class under the register the purpose takes one value across. -/
def adequacyRegion (c : S → C) (q : S → Q) (X : Finset S) : Finset S :=
  X.filter fun x => ∀ y ∈ X, c y = c x → q y = q x

/-- **Model A (Adequacy for a purpose), adequacy.** The share of the accessible states in the region, and `1` where there are none. -/
def adequacy (c : S → C) (q : S → Q) (X : Finset S) : ℚ :=
  if X.card = 0 then 1 else (adequacyRegion c q X).card / X.card

/-- The region lies in the accessible states. -/
theorem adequacyRegion_subset (c : S → C) (q : S → Q) (X : Finset S) : adequacyRegion c q X ⊆ X :=
  filter_subset _ _

/-- The region is all the accessible states exactly when the register fixes the purpose across them. -/
theorem adequacyRegion_eq_iff (c : S → C) (q : S → Q) (X : Finset S) : adequacyRegion c q X = X ↔ Fixes (↑X : Set S) c q := by
  rw [adequacyRegion, filter_eq_self]
  exact ⟨fun h s hs t ht hc => h t ht s hs hc, fun h x hx y hy hc => h y hy x hx hc⟩

/-- **Model A (Adequacy for a purpose), A.1, adequate means carried.** Adequacy is `1` exactly when the register carries the purpose across the accessible
states, which is the register fixing it there. -/
theorem Adequacy.carried (c : S → C) (q : S → Q) (X : Finset S) : adequacy c q X = 1 ↔ Fixes (↑X : Set S) c q := by
  rw [← adequacyRegion_eq_iff, adequacy]
  split_ifs with h
  · rw [card_eq_zero.mp h]
    exact ⟨fun _ => subset_empty.mp (adequacyRegion_subset c q ∅), fun _ => rfl⟩
  · have hX : (X.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h
    rw [div_eq_one_iff_eq hX, Nat.cast_inj]
    exact ⟨fun hc => eq_of_subset_of_card_le (adequacyRegion_subset c q X) hc.ge, fun he => by rw [he]⟩

/-- **Model A (Adequacy for a purpose), A.2, relative to the purpose.** A function of the purpose is settled wherever the purpose is. -/
theorem Adequacy.coarser_purpose {Q' : Type} [DecidableEq Q'] (c : S → C) (q : S → Q) (f : Q → Q') (X : Finset S) :
    adequacyRegion c q X ⊆ adequacyRegion c (f ∘ q) X := by
  intro x hx
  rw [adequacyRegion, mem_filter] at hx ⊢
  exact ⟨hx.1, fun y hy hc => congrArg f (hx.2 y hy hc)⟩

/-- **Model A (Adequacy for a purpose), A.3, borrowing.** A state settled across the accessible states stays settled across any smaller set holding it. -/
theorem Adequacy.borrowing [DecidableEq S] (c : S → C) (q : S → Q) {X Y : Finset S} (hY : Y ⊆ X) : adequacyRegion c q X ∩ Y ⊆ adequacyRegion c q Y := by
  intro x hx
  rw [mem_inter, adequacyRegion, mem_filter] at hx
  rw [adequacyRegion, mem_filter]
  exact ⟨hx.2, fun y hy hc => hx.1.2 y (hY hy) hc⟩

/-- **Model A (Adequacy for a purpose), A.4, no recovery.** A description built from a register settles the purpose on no state the register does not, so
adequacy can only fall along a chain of descriptions each built from the last. -/
theorem Adequacy.no_recovery {D : Type} [DecidableEq D] (c : S → C) (g : C → D) (q : S → Q) (X : Finset S) :
    adequacyRegion (g ∘ c) q X ⊆ adequacyRegion c q X ∧ adequacy (g ∘ c) q X ≤ adequacy c q X := by
  have hsub : adequacyRegion (g ∘ c) q X ⊆ adequacyRegion c q X := by
    intro x hx
    rw [adequacyRegion, mem_filter] at hx ⊢
    exact ⟨hx.1, fun y hy hc => hx.2 y hy (congrArg g hc)⟩
  refine ⟨hsub, ?_⟩
  unfold adequacy
  split_ifs
  · exact le_rfl
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) (Nat.cast_nonneg _)

/-- **Model A (Adequacy for a purpose), A.5, pooling, capped by the between.** The registers of the parties read together settle the purpose wherever any
one of them does, and an accessible state falls outside what they settle together exactly when some accessible state no party tells it apart
from takes another value of the purpose. -/
theorem Adequacy.pooling {ι : Type} [Fintype ι] (c : ι → S → C) (q : S → Q) (X : Finset S) :
    (∀ i, adequacyRegion (c i) q X ⊆ adequacyRegion (fun x i => c i x) q X) ∧
      ∀ x ∈ X, x ∉ adequacyRegion (fun x i => c i x) q X ↔ ∃ y ∈ X, (∀ i, c i y = c i x) ∧ q y ≠ q x := by
  refine ⟨fun i x hx => ?_, fun x hx => ?_⟩
  · rw [adequacyRegion, mem_filter] at hx ⊢
    exact ⟨hx.1, fun y hy hc => hx.2 y hy (congrFun hc i)⟩
  · rw [adequacyRegion, mem_filter]
    constructor
    · intro h
      have h' : ¬ ∀ y ∈ X, (fun i => c i y) = (fun i => c i x) → q y = q x := fun h' => h ⟨hx, h'⟩
      push Not at h'
      obtain ⟨y, hy, hc, hq⟩ := h'
      exact ⟨y, hy, fun i => congrFun hc i, hq⟩
    · rintro ⟨y, hy, hc, hq⟩ ⟨-, h⟩
      exact hq (h y hy (funext hc))

/-- **Model A (Adequacy for a purpose), A.6, the world moves.** With the register fixed, more accessible states can only take states out of the region. -/
theorem Adequacy.world_moves [DecidableEq S] (c : S → C) (q : S → Q) {X X' : Finset S} (hX : X ⊆ X') : adequacyRegion c q X' ∩ X ⊆ adequacyRegion c q X :=
  Adequacy.borrowing c q hX

open Classical in
/-- **Model A (Adequacy for a purpose), confusions.** The pairs of distinct accessible states the register identifies and the purpose separates. -/
noncomputable def confusions (c : S → C) (q : S → Q) (X : Finset S) : Finset (Sym2 S) :=
  X.sym2.filter fun z => ¬ z.IsDiag ∧ z ∈ kernel c ∧ z ∉ kernel q

open Classical in
/-- **Model A (Adequacy for a purpose), what a refinement pays within the accessible states.** The pairs of distinct accessible states one register tells
apart and another did not. -/
noncomputable def paidWithin {C' : Type} (c : S → C) (c' : S → C') (X : Finset S) : Finset (Sym2 S) :=
  X.sym2.filter fun z => ¬ z.IsDiag ∧ z ∈ kernel c ∧ z ∉ kernel c'

omit [DecidableEq C] in
open Classical in
/-- **Model A (Adequacy for a purpose), A.7, the price of adequacy.** A register adequate for the purpose across the accessible states tells apart every
confusion of a register it replaces, so pays at least their number; the register that reads the purpose itself beside the old one pays exactly
that. -/
theorem Adequacy.price {C' : Type} [DecidableEq C'] (c : S → C) (c' : S → C') (q : S → Q) (X : Finset S) (hc' : Fixes (↑X : Set S) c' q) :
    confusions c q X ⊆ paidWithin c c' X ∧ (confusions c q X).card ≤ (paidWithin c c' X).card ∧
      paidWithin c (fun x => (c x, q x)) X = confusions c q X := by
  have hsub : confusions c q X ⊆ paidWithin c c' X := by
    intro z hz
    rw [confusions, mem_filter] at hz
    rw [paidWithin, mem_filter]
    refine ⟨hz.1, hz.2.1, hz.2.2.1, fun hk => hz.2.2.2 ?_⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep z
    have hX := mem_sym2_iff.mp hz.1
    have ha : a ∈ X := hX a (Sym2.mem_mk_left a b)
    have hb : b ∈ X := hX b (Sym2.mem_mk_right a b)
    exact (mem_kernel q a b).mpr (hc' a ha b hb ((mem_kernel c' a b).mp hk))
  refine ⟨hsub, card_le_card hsub, ?_⟩
  unfold paidWithin confusions
  refine filter_congr fun z _ => ?_
  induction z using Sym2.ind with
  | h a b =>
    rw [mem_kernel, mem_kernel, mem_kernel, Prod.mk.injEq]
    tauto

end Adequacy

/-! ## Model S: the sieve as a chain -/

section Sieve

/-- **Model S (The sieve as a survival model), one year.** The held and unheld shares a year on: held stays held at `a`, passes to unheld at `e`, and unheld stays at
`b`; the rest is cut, which stays cut. -/
def sieveStep (a b e : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (a * p.1, e * p.1 + b * p.2)

/-- **Model S (The sieve as a survival model), the shares after `t` years**, from a start. -/
def sieveAfter (a b e : ℝ) (start : ℝ × ℝ) (t : ℕ) : ℝ × ℝ :=
  (sieveStep a b e)^[t] start

/-- **Model S (The sieve as a survival model), survival from held.** The share still kept, held or unheld, after `t` years from one capacity held at the start. -/
def survivalHeld (a b e : ℝ) (t : ℕ) : ℝ :=
  (sieveAfter a b e (1, 0) t).1 + (sieveAfter a b e (1, 0) t).2

/-- **Model S (The sieve as a survival model), survival from unheld.** The share still kept after `t` years from one capacity unheld at the start. -/
def survivalUnheld (a b e : ℝ) (t : ℕ) : ℝ :=
  (sieveAfter a b e (0, 1) t).1 + (sieveAfter a b e (0, 1) t).2

/-- The shares after one more year are one year on from the shares now. -/
theorem sieveAfter_succ (a b e : ℝ) (start : ℝ × ℝ) (t : ℕ) : sieveAfter a b e start (t + 1) = sieveStep a b e (sieveAfter a b e start t) :=
  Function.iterate_succ_apply' _ _ _

/-- **Model S (The sieve as a survival model), S.1, survival.** From unheld the share kept is `b ^ t`; from held, where `a ≠ b`, it is `a ^ t + e / (a - b) * (a ^ t - b ^ t)`. -/
theorem Sieve.survival (a b e : ℝ) (hab : a ≠ b) (t : ℕ) :
    survivalUnheld a b e t = b ^ t ∧ survivalHeld a b e t = a ^ t + e / (a - b) * (a ^ t - b ^ t) := by
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hu : ∀ t, sieveAfter a b e (0, 1) t = (0, b ^ t) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [sieveAfter_succ, ih, sieveStep]; simp [pow_succ, mul_comm]
  have hh : ∀ t, sieveAfter a b e (1, 0) t = (a ^ t, e / (a - b) * (a ^ t - b ^ t)) := by
    intro t
    induction t with
    | zero => simp [sieveAfter]
    | succ t ih =>
      rw [sieveAfter_succ, ih, sieveStep, Prod.mk.injEq]
      constructor
      · ring
      · field_simp
        ring
  refine ⟨?_, ?_⟩
  · rw [survivalUnheld, hu]
    ring
  · rw [survivalHeld, hh]

/-- **Model S (The sieve as a survival model), S.2, years kept.** For `0 ≤ a, b < 1` and `a ≠ b`, the expected numbers of years kept, the sums of survival over the
years after the start, are `b / (1 - b)` from unheld and `a / (1 - a) + e / ((1 - a) * (1 - b))` from held. -/
theorem Sieve.years_kept (a b e : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b < 1) (hab : a ≠ b) :
    HasSum (fun t => survivalUnheld a b e (t + 1)) (b / (1 - b)) ∧
      HasSum (fun t => survivalHeld a b e (t + 1)) (a / (1 - a) + e / ((1 - a) * (1 - b))) := by
  have hA : HasSum (fun t : ℕ => a ^ (t + 1)) (a / (1 - a)) := by
    simpa [pow_succ, mul_comm, div_eq_mul_inv] using (hasSum_geometric_of_lt_one ha0 ha1).mul_left a
  have hB : HasSum (fun t : ℕ => b ^ (t + 1)) (b / (1 - b)) := by
    simpa [pow_succ, mul_comm, div_eq_mul_inv] using (hasSum_geometric_of_lt_one hb0 hb1).mul_left b
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h1a : 1 - a ≠ 0 := by linarith
  have h1b : 1 - b ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · simpa [(Sieve.survival a b e hab _).1] using hB
  · have h := hA.add ((hA.sub hB).mul_left (e / (a - b)))
    have hfun : (fun t => survivalHeld a b e (t + 1)) = fun t => a ^ (t + 1) + e / (a - b) * (a ^ (t + 1) - b ^ (t + 1)) :=
      funext fun t => (Sieve.survival a b e hab (t + 1)).2
    rw [hfun]
    convert h using 1
    field_simp
    ring

/-- **Model S (The sieve as a survival model), S.3, long-run hazard.** With the yearly chances `a = (1 - h₁)(1 - q)`, `e = (1 - h₁) q` and `b = 1 - h₀`, the
hazard of the capacities held at the start is `h₁` in the first year, and with `a, b > 0`, `a ≠ b` and `e > 0` it tends to `1 - max a b`. -/
theorem Sieve.hazard (h₀ h₁ q : ℝ) (ha : 0 < (1 - h₁) * (1 - q)) (hb : 0 < 1 - h₀) (hab : (1 - h₁) * (1 - q) ≠ 1 - h₀) (he : 0 < (1 - h₁) * q) :
    1 - survivalHeld ((1 - h₁) * (1 - q)) (1 - h₀) ((1 - h₁) * q) 1 / survivalHeld ((1 - h₁) * (1 - q)) (1 - h₀) ((1 - h₁) * q) 0 = h₁ ∧
      Tendsto (fun t => 1 - survivalHeld ((1 - h₁) * (1 - q)) (1 - h₀) ((1 - h₁) * q) (t + 1) /
        survivalHeld ((1 - h₁) * (1 - q)) (1 - h₀) ((1 - h₁) * q) t) atTop (𝓝 (1 - max ((1 - h₁) * (1 - q)) (1 - h₀))) := by
  set a := (1 - h₁) * (1 - q)
  set b := 1 - h₀
  set e := (1 - h₁) * q
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hab
  set k := e / (a - b) with hk
  have hS : ∀ t, survivalHeld a b e t = (1 + k) * a ^ t - k * b ^ t := fun t => by
    rw [(Sieve.survival a b e hab t).2]
    ring
  refine ⟨?_, ?_⟩
  · have h1 : survivalHeld a b e 1 = a + e := by
      rw [(Sieve.survival a b e hab 1).2, pow_one, pow_one, div_mul_cancel₀ e hsub]
    have h0 : survivalHeld a b e 0 = 1 := by
      rw [(Sieve.survival a b e hab 0).2]
      simp
    rw [h1, h0, div_one]
    simp only [a, e]
    ring
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- held stays held less than unheld stays: the unheld root rules
    rw [max_eq_right hlt.le]
    have hk0 : k ≠ 0 := by
      rw [hk]
      exact div_ne_zero he.ne' hsub
    set r := a / b with hr
    have hr0 : 0 ≤ r := div_nonneg ha.le hb.le
    have hr1 : r < 1 := (div_lt_one hb).mpr hlt
    have har : a = r * b := by rw [hr]; field_simp
    have hpow : Tendsto (fun t : ℕ => r ^ t) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hlim : Tendsto (fun t : ℕ => b * ((1 + k) * r * r ^ t - k) / ((1 + k) * r ^ t - k)) atTop
        (𝓝 (b * ((1 + k) * r * 0 - k) / ((1 + k) * 0 - k))) :=
      (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hpow).sub tendsto_const_nhds)).div
        ((tendsto_const_nhds.mul hpow).sub tendsto_const_nhds) (by simpa using hk0)
    have hval : b * ((1 + k) * r * 0 - k) / ((1 + k) * 0 - k) = b := by
      rw [mul_zero, mul_zero, zero_sub, mul_div_assoc, div_self (neg_ne_zero.mpr hk0), mul_one]
    rw [hval] at hlim
    refine (tendsto_const_nhds.sub hlim).congr fun t => ?_
    have hbt : b ^ t ≠ 0 := pow_ne_zero t hb.ne'
    rw [hS, hS, har]
    rw [show (1 + k) * (r * b) ^ (t + 1) - k * b ^ (t + 1) = b ^ t * (b * ((1 + k) * r * r ^ t - k)) by ring_nf,
      show (1 + k) * (r * b) ^ t - k * b ^ t = b ^ t * ((1 + k) * r ^ t - k) by ring_nf, mul_div_mul_left _ _ hbt]
  · -- held stays held more than unheld stays: the held root rules
    rw [max_eq_left hgt.le]
    have hk0 : 0 < k := by
      rw [hk]
      exact div_pos he (sub_pos.mpr hgt)
    set r := b / a with hr
    have hr0 : 0 ≤ r := div_nonneg hb.le ha.le
    have hr1 : r < 1 := (div_lt_one ha).mpr hgt
    have hbr : b = r * a := by rw [hr]; field_simp
    have hpow : Tendsto (fun t : ℕ => r ^ t) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hne : (1 + k) - k * 0 ≠ 0 := by simp; linarith
    have hlim : Tendsto (fun t : ℕ => a * ((1 + k) - k * r * r ^ t) / ((1 + k) - k * r ^ t)) atTop
        (𝓝 (a * ((1 + k) - k * r * 0) / ((1 + k) - k * 0))) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub (tendsto_const_nhds.mul hpow))).div
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul hpow)) hne
    have hval : a * ((1 + k) - k * r * 0) / ((1 + k) - k * 0) = a := by
      have : (1 + k) ≠ 0 := by linarith
      rw [mul_zero, mul_zero, sub_zero, mul_div_assoc, div_self this, mul_one]
    rw [hval] at hlim
    refine (tendsto_const_nhds.sub hlim).congr fun t => ?_
    have hat : a ^ t ≠ 0 := pow_ne_zero t ha.ne'
    rw [hS, hS, hbr]
    rw [show (1 + k) * a ^ (t + 1) - k * (r * a) ^ (t + 1) = a ^ t * (a * ((1 + k) - k * r * r ^ t)) by ring_nf,
      show (1 + k) * a ^ t - k * (r * a) ^ t = a ^ t * ((1 + k) - k * r ^ t) by ring_nf, mul_div_mul_left _ _ hat]

/-- **Model S (The sieve as a survival model), S.4, survivors' worth.** Over a finite weighting of capacities, where the chance that one is kept is a function `S` of its
registered signal, the mean worth of those kept less the mean worth of all is the covariance of worth with that chance over the chance's mean;
where the weighting is a product of one on worth and one on the signal, the two means are equal. -/
theorem Sieve.survivors_worth {Ω : Type} [Fintype Ω] (μ w kept : Ω → ℝ) (hk : ∑ ω, μ ω * kept ω ≠ 0) :
    (∑ ω, μ ω * w ω * kept ω) / (∑ ω, μ ω * kept ω) - ∑ ω, μ ω * w ω =
      ((∑ ω, μ ω * w ω * kept ω) - (∑ ω, μ ω * w ω) * (∑ ω, μ ω * kept ω)) / (∑ ω, μ ω * kept ω) := by
  field_simp

/-- **Model S (The sieve as a survival model), S.4, a signal that does not move with worth.** Where worth and the signal are drawn apart, a product weighting, the
mean worth of the capacities kept is the mean worth of all. -/
theorem Sieve.worth_independent {W G : Type} [Fintype W] [Fintype G] (μw : W → ℝ) (μs : G → ℝ) (w : W → ℝ) (S : G → ℝ)
    (hw : ∑ x, μw x = 1) (hS : ∑ s, μs s * S s ≠ 0) :
    (∑ p : W × G, μw p.1 * μs p.2 * w p.1 * S p.2) / (∑ p : W × G, μw p.1 * μs p.2 * S p.2) = ∑ x, μw x * w x := by
  have hnum : (∑ p : W × G, μw p.1 * μs p.2 * w p.1 * S p.2) = (∑ x, μw x * w x) * ∑ s, μs s * S s := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hden : (∑ p : W × G, μw p.1 * μs p.2 * S p.2) = ∑ s, μs s * S s := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hw, one_mul]
  rw [hnum, hden]
  field_simp

end Sieve

/-! ## Model A over time -/

section OverTime

/-- **Model A (Adequacy for a purpose), expected adequacy over time.** With survival `S` of the correction and the world multiplying adequacy by `d` in each
year after the correction is cut: survival, plus the decay after each year the correction could have been cut. -/
def expectedAdequacy (S : ℕ → ℝ) (d : ℝ) (t : ℕ) : ℝ :=
  S t + ∑ j ∈ range t, (S j - S (j + 1)) * d ^ (t - j)

/-- A geometric tail: the sum of `K r ^ j d ^ (t - j)` over the years before `t`. -/
theorem geom_tail (K r d : ℝ) (hrd : d ≠ r) (t : ℕ) :
    ∑ j ∈ range t, K * r ^ j * d ^ (t - j) = K * d / (d - r) * (d ^ t - r ^ t) := by
  have hsub : d - r ≠ 0 := sub_ne_zero.mpr hrd
  have hsplit : ∑ j ∈ range t, K * r ^ j * d ^ (t - j) = K * d * ∑ j ∈ range t, r ^ j * d ^ (t - 1 - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [show t - j = (t - 1 - j) + 1 by omega, pow_succ]
    ring
  have hgeom := geom_sum₂_mul r d t
  rw [hsplit, div_mul_eq_mul_div, eq_div_iff hsub]
  calc K * d * (∑ j ∈ range t, r ^ j * d ^ (t - 1 - j)) * (d - r)
      = -(K * d) * ((∑ j ∈ range t, r ^ j * d ^ (t - 1 - j)) * (r - d)) := by ring
    _ = K * d * (d ^ t - r ^ t) := by rw [hgeom]; ring

/-- **Model A (Adequacy for a purpose), A.8, an unheld correction.** With survival `b ^ t`, expected adequacy is `b ^ t + (1 - b) d / (d - b) (d ^ t - b ^ t)`. -/
theorem Adequacy.over_time_unheld (b d : ℝ) (hbd : d ≠ b) (t : ℕ) :
    expectedAdequacy (fun s => b ^ s) d t = b ^ t + (1 - b) * d / (d - b) * (d ^ t - b ^ t) := by
  rw [expectedAdequacy, ← geom_tail (1 - b) b d hbd t]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Model A (Adequacy for a purpose), A.8, a held correction.** With survival `(1 + k) a ^ t - k b ^ t`, expected adequacy is that survival plus
`(1 + k)(1 - a) d / (d - a) (d ^ t - a ^ t) - k (1 - b) d / (d - b) (d ^ t - b ^ t)`. -/
theorem Adequacy.over_time_held (a b k d : ℝ) (had : d ≠ a) (hbd : d ≠ b) (t : ℕ) :
    expectedAdequacy (fun s => (1 + k) * a ^ s - k * b ^ s) d t =
      ((1 + k) * a ^ t - k * b ^ t) + (1 + k) * (1 - a) * d / (d - a) * (d ^ t - a ^ t) - k * (1 - b) * d / (d - b) * (d ^ t - b ^ t) := by
  rw [expectedAdequacy, ← geom_tail ((1 + k) * (1 - a)) a d had t, ← geom_tail (k * (1 - b)) b d hbd t, add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

end OverTime

end Companion
