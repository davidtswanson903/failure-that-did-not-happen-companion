import Companion.Claims
import Companion.Time
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# How much is held

Holding has no size and no sign. Two claims of the book speak of how much is held, and each needs a rule to say so, stated here as a definition and carrying what strength its theorems have. A fixed budget of effort divides a whole among uses by a weight on the loss held on each. A priced act is one taken where what it returns exceeds the loss held on its being wrong. Correction runs on acts: it is made only where something registered says an act was wrong, and that comes only from an act.
-/

namespace Companion

variable {S : Type}

/-! ## A fixed budget of effort -/

section Budget

variable {U : Type} [Fintype U]

/-- **Claim 21 (Effort follows what is held).** What a weight gives across all the uses, at a profile of held losses. -/
noncomputable def Effort.total (w : ℝ → ℝ) (l : U → ℝ) : ℝ :=
  ∑ v, w (l v)

/-- **Claim 21 (Effort follows what is held), a fixed budget of effort.** Each use's share of a fixed whole is its weight over the weights of all the uses, at the profile of losses held on each. -/
noncomputable def Effort.share (w : ℝ → ℝ) (l : U → ℝ) (u : U) : ℝ :=
  w (l u) / Effort.total w l

/-- **Claim 21 (Effort follows what is held), a weight that follows held losses.** A weight never below nothing, and rising with the loss. -/
structure Effort.Follows (w : ℝ → ℝ) : Prop where
  /-- It is never below nothing. -/
  nonneg : ∀ x, 0 ≤ x → 0 ≤ w x
  /-- It rises with the loss. -/
  rises : ∀ x y, 0 ≤ x → x < y → w x < w y

/-- **Claim 21 (Effort follows what is held).** Effort in proportion to the square of the loss held is such a weight. It is the rule the book's computation of reporting runs. -/
theorem Effort.follows_square : Effort.Follows fun x => x ^ 2 :=
  ⟨fun _ _ => sq_nonneg _, fun _ _ hx hxy => by nlinarith⟩

/-- The shares add up to the whole, wherever anything is held. -/
theorem Effort.share_sum (w : ℝ → ℝ) (l : U → ℝ) (h : Effort.total w l ≠ 0) : ∑ u, Effort.share w l u = 1 := by
  simp only [Effort.share, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ h

/-- **Claim 21 (Effort follows what is held).** Under a fixed budget that follows held losses, let the loss held on one use rise and every other stand as it was, where another use has some share. That use's share falls, the first one's rises, and the whole stays. Where a report is held and the work it describes is not held more than it was, effort moves from the work to the report. The rule carries this. -/
theorem Effort.moves [DecidableEq U] {w : ℝ → ℝ} (hw : Effort.Follows w) (l l' : U → ℝ) (report work : U) (hne : work ≠ report) (hl : ∀ u, 0 ≤ l u)
    (hup : l report < l' report) (hsame : ∀ u, u ≠ report → l' u = l u) (hwork : 0 < w (l work)) :
    Effort.share w l' work < Effort.share w l work ∧ Effort.share w l report < Effort.share w l' report ∧ ∑ u, Effort.share w l' u = 1 := by
  set R : ℝ := ∑ u ∈ Finset.univ.erase report, w (l u) with hR
  have hR' : ∑ u ∈ Finset.univ.erase report, w (l' u) = R :=
    Finset.sum_congr rfl fun u hu => by rw [hsame u (Finset.ne_of_mem_erase hu)]
  have htot : Effort.total w l = w (l report) + R := (Finset.add_sum_erase _ _ (Finset.mem_univ report)).symm
  have htot' : Effort.total w l' = w (l' report) + R := by
    rw [← hR']
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ report)).symm
  have hRpos : 0 < R :=
    lt_of_lt_of_le hwork (Finset.single_le_sum (f := fun u => w (l u)) (fun u _ => hw.nonneg _ (hl u)) (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ work⟩))
  have ha := hw.nonneg _ (hl report)
  have hrise := hw.rises _ _ (hl report) hup
  have hD : 0 < w (l report) + R := by linarith
  have hD' : 0 < w (l' report) + R := by linarith
  refine ⟨?_, ?_, Effort.share_sum w l' (by rw [htot']; exact hD'.ne')⟩
  · rw [Effort.share, Effort.share, htot, htot', hsame work hne]
    exact div_lt_div_of_pos_left hwork hD (by linarith)
  · rw [Effort.share, Effort.share, htot, htot', div_lt_div_iff₀ hD hD']
    nlinarith

omit [Fintype U] in
/-- **Claim 21 (Effort follows what is held), the whole must be fixed.** Give each use its weight with no fixed whole, and a rise in the loss on one use gives that use more and takes nothing from another. So what moves effort from the work is that the whole is fixed. -/
theorem Effort.needs_fixed_whole {w : ℝ → ℝ} (hw : Effort.Follows w) (l l' : U → ℝ) (report work : U) (hne : work ≠ report) (hl : 0 ≤ l report) (hup : l report < l' report) (hsame : ∀ u, u ≠ report → l' u = l u) :
    w (l report) < w (l' report) ∧ w (l' work) = w (l work) :=
  ⟨hw.rises _ _ hl hup, by rw [hsame work hne]⟩

end Budget

/-! ## What sorts reporting -/

/-- Four uses of an office's effort: the work, filing the report, raising the figure by other means, and other duties. -/
inductive Use : Type
  /-- The work the report describes. -/
  | work
  /-- Filing the report. -/
  | report
  /-- Raising the figure by other means. -/
  | means
  /-- Other duties. -/
  | other
  deriving DecidableEq

instance : Fintype Use :=
  ⟨{Use.work, Use.report, Use.means, Use.other}, fun u => by cases u <;> simp⟩

/-- A sum over the four uses. -/
theorem Use.sum (f : Use → ℝ) : ∑ u, f u = f Use.work + f Use.report + f Use.means + f Use.other := by
  change ∑ u ∈ {Use.work, Use.report, Use.means, Use.other}, f u = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- **Claim 24 (What sorts reporting).** The losses held: `a` on the work and `b` on other duties, as with no requirement at all, with `h` more on the work where someone holds a loss on the thing reported, and `g` on the other means where a loss on the figure reaches them. -/
def Use.held (a b h g : ℝ) : Use → ℝ
  | Use.work => a + h
  | Use.report => 0
  | Use.means => g
  | Use.other => b

/-- **Claim 24 (What sorts reporting).** Under a fixed budget that follows held losses and gives nothing where nothing is held, the three kinds of what is held sort what a requirement does to the work, against no requirement. Hold nothing on it, and every share stays. Hold a loss on the thing reported, and the share of the work rises. Hold a loss on the figure, and the other means come to have a share where they had none, and the work's falls exactly as the last line says. The rule carries this. -/
theorem Effort.sorts {w : ℝ → ℝ} (hw : Effort.Follows w) (h0 : w 0 = 0) {a b h g : ℝ} (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hg : 0 < g) :
    Effort.share w (Use.held a b 0 0) Use.report = 0 ∧ Effort.share w (Use.held a b 0 0) Use.means = 0 ∧
      Effort.share w (Use.held a b 0 0) Use.work < Effort.share w (Use.held a b h 0) Use.work ∧ Effort.share w (Use.held a b h 0) Use.means = 0 ∧
      0 < Effort.share w (Use.held a b h g) Use.means ∧
      (Effort.share w (Use.held a b h g) Use.work < Effort.share w (Use.held a b 0 0) Use.work ↔ w (a + h) * w b < w a * (w b + w g)) := by
  have hwa : 0 < w a := by simpa [h0] using hw.rises 0 a le_rfl ha
  have hwb : 0 < w b := by simpa [h0] using hw.rises 0 b le_rfl hb
  have hwg : 0 < w g := by simpa [h0] using hw.rises 0 g le_rfl hg
  have hwah : w a < w (a + h) := hw.rises a (a + h) ha.le (by linarith)
  have hadd : a + 0 = a := add_zero a
  have tot0 : Effort.total w (Use.held a b 0 0) = w a + w b := by
    rw [Effort.total, Use.sum]
    simp only [Use.held, hadd, h0]
    ring
  have toth : Effort.total w (Use.held a b h 0) = w (a + h) + w b := by
    rw [Effort.total, Use.sum]
    simp only [Use.held, h0]
    ring
  have totg : Effort.total w (Use.held a b h g) = w (a + h) + w g + w b := by
    rw [Effort.total, Use.sum]
    simp only [Use.held, h0]
    ring
  have hD0 : 0 < w a + w b := by linarith
  have hDh : 0 < w (a + h) + w b := by linarith
  have hDg : 0 < w (a + h) + w g + w b := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Effort.share, Use.held, h0]
  · simp [Effort.share, Use.held, h0]
  · rw [Effort.share, Effort.share, tot0, toth]
    simp only [Use.held, hadd]
    rw [div_lt_div_iff₀ hD0 hDh]
    nlinarith
  · simp [Effort.share, Use.held, h0]
  · rw [Effort.share, totg]
    exact div_pos hwg hDg
  · rw [Effort.share, Effort.share, tot0, totg]
    simp only [Use.held, hadd]
    rw [div_lt_div_iff₀ hDg hD0]
    constructor <;> intro hcmp <;> nlinarith

/-- **Claim 24 (What sorts reporting), a loss on the figure can go either way.** Under effort in proportion to the square of the loss held, a loss on the figure that reaches the other means heavily takes effort from the work, and one that reaches them lightly does not. So where a requirement sits depends on what is held, and on how much reaches each use. -/
theorem Effort.gamed_either_way :
    (Effort.share (fun x => x ^ 2) (Use.held 1 1 1 2) Use.work < Effort.share (fun x => x ^ 2) (Use.held 1 1 0 0) Use.work) ∧
      ¬ (Effort.share (fun x => x ^ 2) (Use.held 1 1 1 1) Use.work < Effort.share (fun x => x ^ 2) (Use.held 1 1 0 0) Use.work) := by
  constructor
  · rw [(Effort.sorts Effort.follows_square (by norm_num) one_pos one_pos one_pos (by norm_num)).2.2.2.2.2]
    norm_num
  · rw [(Effort.sorts Effort.follows_square (by norm_num) one_pos one_pos one_pos one_pos).2.2.2.2.2]
    norm_num

/-! ## Correction -/

open Classical in
/-- How many of the first `n` steps of a course meet a condition. -/
noncomputable def Course.count (x : Course S) (P : S → Prop) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun t => P (x t)).card

/-- **Claim 38 (Correction runs on error), correction.** A process corrects along a course when what it corrects on is something it registers, read from the state that obtains: it corrects at a step only where that says it was wrong, and that says so only after an act at the step before. The clause from an act is what the claim says. An act is any quantity of the state, tied to the process by nothing here (`Correction.any_act`). -/
structure Correcting (p : Process S) (x : Course S) (act wrong correct : S → Prop) : Prop where
  /-- It registers whether it was wrong. -/
  registers : p.Carries wrong
  /-- It corrects only where that says it was wrong. -/
  on_error : ∀ t, correct (x (t + 1)) → wrong (x (t + 1))
  /-- That says so only after an act. -/
  from_acts : ∀ t, wrong (x (t + 1)) → act (x t)

open Classical in
/-- **Claim 38 (Correction runs on error), no faster than acts.** Along any span, the steps on which a process corrects are no more than the acts before them that came back wrong, and those no more than its acts. -/
theorem Correction.no_faster {p : Process S} {x : Course S} {act wrong correct : S → Prop} (h : Correcting p x act wrong correct) (n : ℕ) :
    Course.count (fun t => x (t + 1)) correct n ≤ ((Finset.range n).filter fun t => act (x t) ∧ wrong (x (t + 1))).card ∧
      ((Finset.range n).filter fun t => act (x t) ∧ wrong (x (t + 1))).card ≤ Course.count x act n := by
  constructor
  · refine Finset.card_le_card fun t ht => ?_
    rw [Finset.mem_filter] at ht ⊢
    have hw := h.on_error t ht.2
    exact ⟨ht.1, h.from_acts t hw, hw⟩
  · refine Finset.card_le_card fun t ht => ?_
    rw [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩

/-- **Claim 38 (Correction runs on error), an act is free.** Any quantity serves as the act, the constant one among them, so the definition does not itself tie an act to the process. -/
theorem Correction.any_act (p : Process S) (x : Course S) (wrong correct : S → Prop) (hc : p.Carries wrong) (he : ∀ t, correct (x (t + 1)) → wrong (x (t + 1))) :
    Correcting p x (fun _ => True) wrong correct :=
  ⟨hc, he, fun _ _ => trivial⟩

/-- **Claim 38 (Correction runs on error), what an act not taken leaves.** Where at one state that obtains two acts not taken would have had two outcomes, one wrong and one not, whether the act not taken would have been wrong is carried by no coarse-graining. So nothing comes back from an act not taken: this is Claim 5 (The non-event) at work. -/
theorem Correction.unacted_not_carried {Q : Type} (o : S → Q) (e : Q) {s t t' : S} (ht : t ≠ s) (ht' : t' ≠ s) (hw : o t ≠ e) (hw' : o t' = e) {C : Type} (c : S → C) :
    ¬ CarriesOfSituation c fun w : Situation S => o w.wouldHave ≠ e := by
  refine Response.nonevent.1 c _ ⟨⟨s, t⟩, ⟨s, t'⟩, ht, ht', rfl, fun h => ?_⟩
  have : o t ≠ e ↔ o t' ≠ e := by simpa using h
  exact (this.mp hw) hw'

/-- Whether what came back says it was wrong, in the witnesses on two states. -/
def acted (s : Bool) : Prop :=
  s = true

/-- **Claim 38 (Correction runs on error), the clause from an act cannot be dropped.** A process can register that it was wrong with no act of its own behind it, where another's act comes back to it: it does not act along this course, and it corrects at every step. So the claim's "its acts" reads as the acts whose return reaches it. -/
theorem Correction.without_own_act :
    (Process.reading id : Process Bool).Carries acted ∧
      Course.count (fun _ => true) (fun _ => False) 3 < Course.count (fun t => (fun _ : ℕ => true) (t + 1)) acted 3 :=
  ⟨⟨fun v => (v () : Bool) = true, rfl⟩, by simp [Course.count, acted]⟩

/-! ## Priced acts -/

/-- **Claim 38 (Correction runs on error), a priced act.** An act is taken where what it returns exceeds the loss held on its being wrong, at weight `c`, less what is held on waiting, at weight `v`. The rule carries what follows of it. -/
def PricedAct (ret err wait : S → ℝ) (c v : ℝ) (s : S) : Prop :=
  c * err s < ret s + v * wait s

/-- **Claim 38 (Correction runs on error), the rule as a response.** A process that reads what an act returns and the errors of acting and of waiting, and responds by that rule. The rule asks that those quantities be registered, which is why an error of waiting read here is a quantity of the state and not what would have obtained (`waiting_not_a_response`). -/
def pricedProcess (ret err wait : S → ℝ) (c v : ℝ) : Process S :=
  (Process.reading fun s => (ret s, err s, wait s)).withRule fun u => c * (u ()).2.1 < (u ()).1 + v * (u ()).2.2

/-- That process responds with the rule. -/
theorem pricedProcess_response (ret err wait : S → ℝ) (c v : ℝ) (s : S) : (pricedProcess ret err wait c v).response s = PricedAct ret err wait c v s :=
  rfl

/-- **Claim 38 (Correction runs on error), it acts less.** Under the rule, a heavier weight on the loss held on being wrong takes no act that a lighter one does not, and along any span it takes no more. -/
theorem Priced.acts_less (ret err wait : S → ℝ) {c c' v : ℝ} (hc : c ≤ c') (herr : ∀ s, 0 ≤ err s) :
    (∀ s, PricedAct ret err wait c' v s → PricedAct ret err wait c v s) ∧
      ∀ (x : Course S) (n : ℕ), Course.count x (PricedAct ret err wait c' v) n ≤ Course.count x (PricedAct ret err wait c v) n := by
  have hsub : ∀ s, PricedAct ret err wait c' v s → PricedAct ret err wait c v s := fun s h =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc (herr s)) h
  classical
  refine ⟨hsub, fun x n => Finset.card_le_card fun t ht => ?_⟩
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, hsub _ ht.2⟩

/-- **Claim 38 (Correction runs on error), it can fall below the pace.** Over any span in which an act could be wrong at every step, some weight on being wrong leaves no act and so no correction. The world's pace is modelled nowhere, and falling below it reads as no corrections. -/
theorem Priced.heavy_stops (ret err wait : S → ℝ) (x : Course S) (n : ℕ) (herr : ∀ t < n, 0 < err (x t)) :
    ∃ c : ℝ, ∀ t < n, ¬ PricedAct ret err wait c 0 (x t) := by
  refine ⟨∑ t ∈ Finset.range n, |ret (x t)| / err (x t), fun t ht hact => ?_⟩
  have hpos := herr t ht
  have hle : |ret (x t)| / err (x t) ≤ ∑ t ∈ Finset.range n, |ret (x t)| / err (x t) :=
    Finset.single_le_sum (f := fun t => |ret (x t)| / err (x t))
      (fun u hu => div_nonneg (abs_nonneg _) (herr u (Finset.mem_range.mp hu)).le) (Finset.mem_range.mpr ht)
  have hmul : |ret (x t)| ≤ (∑ t ∈ Finset.range n, |ret (x t)| / err (x t)) * err (x t) := by
    rwa [div_le_iff₀ hpos] at hle
  have hact' : (∑ t ∈ Finset.range n, |ret (x t)| / err (x t)) * err (x t) < ret (x t) + 0 * wait (x t) := hact
  have := le_abs_self (ret (x t))
  rw [zero_mul, add_zero] at hact'
  linarith

open Classical in
/-- **Claim 40 (The anxious arrangement), what a party supposes.** How often a party supposes at step `t` that its acts go wrong, from its own acts of the
last `L` steps: the errors among them, plus one, over the acts, plus two. With no act to go on, it supposes half. -/
noncomputable def windowErr (acts wrong : ℕ → Prop) (L t : ℕ) : ℝ :=
  ((((Finset.Ico (t - L) t).filter wrong).card : ℝ) + 1) / ((((Finset.Ico (t - L) t).filter acts).card : ℝ) + 2)

open Classical in
/-- **Claim 40 (The anxious arrangement), with no act to go on.** Where no act was taken in the last `L` steps, and an error is only of an act, a party
supposes half its acts go wrong. -/
theorem windowErr_quiet (acts wrong : ℕ → Prop) (hwrong : ∀ t, wrong t → acts t) (L t : ℕ) (hnone : ∀ u ∈ Finset.Ico (t - L) t, ¬ acts u) :
    windowErr acts wrong L t = 1 / 2 := by
  have hw : (Finset.Ico (t - L) t).filter wrong = ∅ := Finset.filter_eq_empty_iff.mpr fun u hu hwu => hnone u hu (hwrong u hwu)
  have ha : (Finset.Ico (t - L) t).filter acts = ∅ := Finset.filter_eq_empty_iff.mpr fun u hu => hnone u hu
  rw [windowErr, hw, ha]
  norm_num

/-- **Claim 40 (The anxious arrangement), the loop runs down.** A party acting by the priced rule, with nothing held on waiting, what it supposes read from
its own acts of the last `L` steps, and an error only of an act: where what an act returns is at most half the weight on being wrong, `L` steps with
no act are followed by no act at any later step. -/
theorem Priced.window_stops (acts wrong : ℕ → Prop) (hwrong : ∀ t, wrong t → acts t) (L : ℕ) (ret wait : ℕ → ℝ) (c : ℝ)
    (hrule : ∀ t, acts t ↔ PricedAct ret (windowErr acts wrong L) wait c 0 t) (hret : ∀ t, ret t ≤ c / 2)
    (t₀ : ℕ) (hquiet : ∀ t, t₀ ≤ t → t < t₀ + L → ¬ acts t) : ∀ t, t₀ ≤ t → ¬ acts t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    by_cases hL : t < t₀ + L
    · exact hquiet t ht hL
    · have herr := windowErr_quiet acts wrong hwrong L t fun u hu => by
        rw [Finset.mem_Ico] at hu
        exact ih u hu.2 (by omega)
      intro hact
      have h := (hrule t).mp hact
      rw [PricedAct, herr, zero_mul, add_zero] at h
      linarith [hret t]

/-- **Claim 40 (The anxious arrangement), held waiting ends the stop.** The same party with a positive weight on waiting, waiting counting the steps since
its last act, and what an act returns never below nothing: from any step, it acts again at some later step. -/
theorem Priced.window_resumes (acts wrong : ℕ → Prop) (hwrong : ∀ t, wrong t → acts t) (L : ℕ) (ret wait : ℕ → ℝ) (c v : ℝ) (hv : 0 < v)
    (hrule : ∀ t, acts t ↔ PricedAct ret (windowErr acts wrong L) wait c v t) (hret : ∀ t, 0 ≤ ret t)
    (t₀ : ℕ) (hwait0 : 0 ≤ wait t₀) (hwait : ∀ t, ¬ acts t → wait (t + 1) = wait t + 1) : ∃ t, t₀ ≤ t ∧ acts t := by
  by_contra hno
  push Not at hno
  have hgrow : ∀ k : ℕ, (k : ℝ) ≤ wait (t₀ + k) := by
    intro k
    induction k with
    | zero => simpa using hwait0
    | succ k ih =>
      rw [← Nat.add_assoc, hwait _ (hno _ (Nat.le_add_right _ _))]
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (c / (2 * v))
  have hck : c < k * (2 * v) := (div_lt_iff₀ (by positivity)).mp hk
  have herr := windowErr_quiet acts wrong hwrong L (t₀ + (L + k)) fun u hu => hno u (by rw [Finset.mem_Ico] at hu; omega)
  have hw : ((L + k : ℕ) : ℝ) ≤ wait (t₀ + (L + k)) := hgrow (L + k)
  push_cast at hw
  apply hno (t₀ + (L + k)) (by omega)
  rw [hrule, PricedAct, herr]
  nlinarith [mul_le_mul_of_nonneg_left hw hv.le, mul_nonneg hv.le (Nat.cast_nonneg L : (0 : ℝ) ≤ L), hret (t₀ + (L + k))]

/-- **Claim 38 (Correction runs on error), it occurs.** One party on one run of occasions, the same return and the same error at each. Priced lightly it acts at every step, what comes back says it was wrong, and it corrects at every step of a span. Priced heavily it acts at none, and it corrects at none. -/
theorem Correction.pace_occurs (n : ℕ) (hn : 0 < n) :
    Correcting (Process.reading id) (fun _ => true) (PricedAct (fun _ => 1) (fun _ => 1) (fun _ => 0) 0 0) acted acted ∧
      Course.count (fun t => (fun _ : ℕ => true) (t + 1)) acted n = n ∧
      Correcting (Process.reading id) (fun _ => false) (PricedAct (fun _ => 1) (fun _ => 1) (fun _ => 0) 2 0) acted acted ∧
      Course.count (fun t => (fun _ : ℕ => false) (t + 1)) acted n = 0 ∧ Course.count (fun t => (fun _ : ℕ => false) (t + 1)) acted n < n := by
  have hcarry : (Process.reading id : Process Bool).Carries acted := ⟨fun v => (v () : Bool) = true, rfl⟩
  refine ⟨⟨hcarry, fun _ h => h, fun _ _ => ?_⟩, ?_, ⟨hcarry, fun _ h => h, fun _ h => absurd h (by simp [acted])⟩, ?_, ?_⟩
  · change (0 : ℝ) * 1 < 1 + 0 * 0
    norm_num
  · classical
    simp [Course.count, acted]
  · classical
    simp [Course.count, acted]
  · classical
    simpa [Course.count, acted] using hn

/-- **Claim 38 (Correction runs on error), holding has no sign.** A process can hold the error and act where it is largest, as one that checks does. So the claim's "it acts less" is the rule's, and holding a quantity does not give it. -/
theorem holding_error_has_no_sign :
    (Process.reading id : Process Bool).Holds Set.univ (id : Bool → Bool) ∧ ∀ s, (Process.reading id : Process Bool).response s = true ↔ s = true :=
  ⟨⟨⟨fun v => v (), rfl⟩, fun _ _ _ _ e => e, false, trivial, true, trivial, Bool.false_ne_true, Bool.false_ne_true⟩, fun _ => Iff.rfl⟩

/-! ## The anxious arrangement -/

/-- **Claim 40 (The anxious arrangement), toward not acting.** With a loss held on acting and none on waiting, a party takes no act that a rule holding waiting too does not take, and along any span it takes no more. -/
theorem Priced.toward_not_acting (ret err wait : S → ℝ) (c : ℝ) {v : ℝ} (hv : 0 ≤ v) (hwait : ∀ s, 0 ≤ wait s) :
    (∀ s, PricedAct ret err wait c 0 s → PricedAct ret err wait c v s) ∧
      ∀ (x : Course S) (n : ℕ), Course.count x (PricedAct ret err wait c 0) n ≤ Course.count x (PricedAct ret err wait c v) n := by
  have hsub : ∀ s, PricedAct ret err wait c 0 s → PricedAct ret err wait c v s := fun s h => by
    have h0 : c * err s < ret s + 0 * wait s := h
    have : 0 ≤ v * wait s := mul_nonneg hv (hwait s)
    change c * err s < ret s + v * wait s
    linarith
  classical
  refine ⟨hsub, fun x n => Finset.card_le_card fun t ht => ?_⟩
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, hsub _ ht.2⟩

/-- **Claim 40 (The anxious arrangement), a bound.** Correction under a loss held on acting alone is no faster than the acts that rule takes, and those are no more than a rule holding waiting too would take. It is a bound and not a pace: `Priced.can_correct_every_step`. -/
theorem Priced.corrections_bounded {p : Process S} {x : Course S} {wrong correct : S → Prop} (ret err wait : S → ℝ) (c : ℝ) {v : ℝ} (hv : 0 ≤ v) (hwait : ∀ s, 0 ≤ wait s)
    (h : Correcting p x (PricedAct ret err wait c 0) wrong correct) (n : ℕ) :
    Course.count (fun t => x (t + 1)) correct n ≤ Course.count x (PricedAct ret err wait c v) n :=
  ((Correction.no_faster h n).1.trans (Correction.no_faster h n).2).trans ((Priced.toward_not_acting ret err wait c hv hwait).2 x n)

/-- **Claim 40 (The anxious arrangement), slowly is no consequence.** With the error of acting held at a positive weight and the error of waiting not, a party can act and correct at every step of a course. -/
theorem Priced.can_correct_every_step (n : ℕ) :
    Correcting (Process.reading id) (fun _ => true) (PricedAct (fun _ : Bool => (1 : ℝ)) (fun _ => 1) (fun _ => 0) (1 / 2) 0) acted acted ∧
      Course.count (fun t => (fun _ : ℕ => true) (t + 1)) acted n = n := by
  have hcarry : (Process.reading id : Process Bool).Carries acted := ⟨fun v => (v () : Bool) = true, rfl⟩
  refine ⟨⟨hcarry, fun _ h => h, fun _ _ => ?_⟩, ?_⟩
  · change ((1 : ℝ) / 2) * 1 < 1 + 0 * 0
    norm_num
  · classical
    simp [Course.count, acted]

/-- **Claim 40 (The anxious arrangement), the difference is real.** An act a party that holds waiting too takes, and one that holds only acting does not. -/
theorem Priced.toward_not_acting_occurs :
    PricedAct (fun _ : Unit => (1 : ℝ)) (fun _ => 1) (fun _ => 1) 2 2 () ∧ ¬ PricedAct (fun _ : Unit => (1 : ℝ)) (fun _ => 1) (fun _ => 1) 2 0 () := by
  constructor
  · change (2 : ℝ) * 1 < 1 + 2 * 1
    norm_num
  · change ¬ (2 : ℝ) * 1 < 1 + 0 * 1
    norm_num

/-- **Claim 39 (Which error is held), held at all.** However small the weight on the error of acting, there is a state at which a party holding it at no weight acts and a party holding it at that weight does not. -/
theorem Priced.any_weight_forgoes {c : ℝ} (hc : 0 < c) :
    PricedAct (fun _ : Unit => c) (fun _ => 1) (fun _ => 0) 0 0 () ∧ ¬ PricedAct (fun _ : Unit => c) (fun _ => 1) (fun _ => 0) c 0 () := by
  constructor
  · change (0 : ℝ) * 1 < c + 0 * 0
    linarith
  · change ¬ c * 1 < c + 0 * 0
    linarith

/-- **Claim 40 (The anxious arrangement), waiting cannot be priced at the state.** Let the error of waiting be a quantity of situations, and let a rule act differently at two situations with one state that obtains because of it. No process's response is that rule: the rule asks for what Claim 5 (The non-event) says reaches no one. -/
theorem waiting_not_a_response {Q : Type} (F : Situation S → Q) (rule : Q → Prop) {w w' : Situation S} (ho : w.obtains = w'.obtains) (hne : rule (F w) ≠ rule (F w')) (p : Process S) :
    ¬ ∃ e : p.Action → Prop, ∀ v : Situation S, e (evaluate p.response v) = rule (F v) := by
  rintro ⟨e, he⟩
  refine hne ?_
  rw [← he w, ← he w']
  simp [evaluate, ho]

end Companion
