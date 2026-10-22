/-
# Glue (Z7): the Lemma 5 data (a), (b) of `sharp_of_pointwise` from the A-certificate files

* (a) is `Esharp_sub_le_eStar` (`Z7/Glue/CertPoint.lean`).
* (b) the step data: `xE i` = the `i`-th event point of `events 400`, `uE i = e*(midpoint)`,
  `LE = #events - 1`, with `xE 0 = 1`, `xE LE = 400`, strictly increasing, `e* ≤ uE i` on each open
  cell (`CertA.eStar_eq_mid`), and `ABody 400 = Σ_i uE i (1/xE i − 1/xE (i+1))`.
* the tail `e*(y) ≤ 33 + G{y}` for `y ≥ 400` is `CertA.eStar_le_tail` (`Z7/CertA/Tail.lean`;
  `33 = S + 15`, PROOF_ZETA (5.2)).

All list facts are proved for an abstract list `l` (strictly increasing, inside `[1, 400]`,
containing `1` and `400`), so that `events 400` (30,972 entries) is never unfolded.

Status: complete (no `sorry`). Nothing here uses `native_decide`.
-/
import ZetaIrrational.Z7.CertA.Attain
import ZetaIrrational.Z7.Glue.CertPoint
import ZetaIrrational.Z7.CertA.Tail
import ZetaIrrational.Z7.Glue.Sharp

namespace ZetaIrr.Z7

open Filter Topology Finset

/-! ### Generic list facts -/

lemma consec_getElem : ∀ (l : List ℚ) (i : ℕ) (h : i + 1 < l.length),
    CertA.Consec l (l[i]'(by omega)) (l[i + 1])
  | a :: b :: t, 0, _ => ⟨[], t, by simp⟩
  | a :: b :: t, i + 1, h => by
    obtain ⟨l₁, l₂, hl⟩ := consec_getElem (b :: t) i (by simp at h ⊢; omega)
    refine ⟨a :: l₁, l₂, ?_⟩
    simp only [List.getElem_cons_succ] at hl ⊢
    exact congrArg (List.cons a) hl
  | [a], i, h => by simp at h
  | [], i, h => by simp at h

lemma pairSum_eq_sum {β : Type} [AddCommMonoid β] (g : ℚ → ℚ → β) :
    ∀ l : List ℚ, CertA.pairSum g l =
      ∑ i ∈ range (l.length - 1), g (l.getD i 0) (l.getD (i + 1) 0)
  | a :: b :: t => by
    rw [CertA.pairSum, pairSum_eq_sum g (b :: t)]
    have hlen : (a :: b :: t).length - 1 = ((b :: t).length - 1) + 1 := by simp
    rw [hlen, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]
  | [a] => by simp [CertA.pairSum]
  | [] => by simp [CertA.pairSum]

/-! ### Step data from an abstract sorted list -/

section StepList

variable (l : List ℚ)

/-- Number of cells. -/
def LL : ℕ := l.length - 1

/-- Breakpoints `x i` (the list entries). -/
noncomputable def xL (i : ℕ) : ℝ := ((l.getD i 0 : ℚ) : ℝ)

/-- Step values `u i = e*(midpoint of cell i)`. -/
noncomputable def uL (i : ℕ) : ℝ :=
  ((CertA.eStar ((l.getD i 0 + l.getD (i + 1) 0) / 2) : ℚ) : ℝ)

variable {l}

lemma list_lt (hpw : l.Pairwise (· < ·)) {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    l[i]'(hij.trans hj) < l[j] :=
  List.pairwise_iff_getElem.mp hpw i j (hij.trans hj) hj hij

lemma list_le (hpw : l.Pairwise (· < ·)) {i j : ℕ} (hij : i ≤ j) (hj : j < l.length) :
    l[i]'(lt_of_le_of_lt hij hj) ≤ l[j] := by
  rcases hij.lt_or_eq with h | rfl
  · exact (list_lt hpw h hj).le
  · exact le_rfl

lemma list_length (h1 : (1 : ℚ) ∈ l) (h4 : (400 : ℚ) ∈ l) : 2 ≤ l.length := by
  obtain ⟨i, hi, e1⟩ := List.getElem_of_mem h1
  obtain ⟨j, hj, e4⟩ := List.getElem_of_mem h4
  by_contra hc
  have hi0 : i = 0 := by omega
  have hj0 : j = 0 := by omega
  subst hi0 hj0
  rw [e1] at e4; norm_num at e4

lemma list_head (hpw : l.Pairwise (· < ·)) (hb : ∀ z ∈ l, 1 ≤ z ∧ z ≤ 400)
    (h1 : (1 : ℚ) ∈ l) (h4 : (400 : ℚ) ∈ l) : l.getD 0 0 = 1 := by
  have hlen := list_length h1 h4
  rw [List.getD_eq_getElem _ _ (by omega)]
  apply le_antisymm
  · obtain ⟨i, hi, e1⟩ := List.getElem_of_mem h1
    rw [← e1]; exact list_le hpw (Nat.zero_le i) hi
  · exact (hb _ (List.getElem_mem _)).1

lemma list_last (hpw : l.Pairwise (· < ·)) (hb : ∀ z ∈ l, 1 ≤ z ∧ z ≤ 400)
    (h1 : (1 : ℚ) ∈ l) (h4 : (400 : ℚ) ∈ l) : l.getD (LL l) 0 = 400 := by
  have hlen := list_length h1 h4
  unfold LL
  rw [List.getD_eq_getElem _ _ (by omega)]
  apply le_antisymm
  · exact (hb _ (List.getElem_mem _)).2
  · obtain ⟨i, hi, e4⟩ := List.getElem_of_mem h4
    rw [← e4]; exact list_le hpw (by omega) (by omega)

lemma xL_zero (hpw : l.Pairwise (· < ·)) (hb : ∀ z ∈ l, 1 ≤ z ∧ z ≤ 400)
    (h1 : (1 : ℚ) ∈ l) (h4 : (400 : ℚ) ∈ l) : xL l 0 = 1 := by
  unfold xL; rw [list_head hpw hb h1 h4]; simp

lemma xL_LL (hpw : l.Pairwise (· < ·)) (hb : ∀ z ∈ l, 1 ≤ z ∧ z ≤ 400)
    (h1 : (1 : ℚ) ∈ l) (h4 : (400 : ℚ) ∈ l) : xL l (LL l) = ((400 : ℕ) : ℝ) := by
  unfold xL; rw [list_last hpw hb h1 h4]; simp

lemma xL_lt (hpw : l.Pairwise (· < ·)) (i : ℕ) (hi : i < LL l) : xL l i < xL l (i + 1) := by
  unfold xL
  unfold LL at hi
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact_mod_cast list_lt hpw (Nat.lt_succ_self i) (by omega)

lemma consec_list (i : ℕ) (hi : i < LL l) :
    CertA.Consec l (l.getD i 0) (l.getD (i + 1) 0) := by
  unfold LL at hi
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact consec_getElem l i (by omega)

variable (l) in
lemma pairSum_cast_eq :
    ((CertA.pairSum (fun a b => CertA.eStar ((a + b) / 2) * (1 / a - 1 / b)) l : ℚ) : ℝ) =
      ∑ i ∈ range (LL l), uL l i * (1 / xL l i - 1 / xL l (i + 1)) := by
  rw [pairSum_eq_sum, Rat.cast_sum]
  refine sum_congr rfl (fun i _ => ?_)
  unfold uL xL
  push_cast
  ring

end StepList

/-! ### Instantiation with `events 400` -/

lemma evs_pairwise : (CertA.events 400).Pairwise (· < ·) := CertA.events_pairwise 400

lemma evs_bounds : ∀ z ∈ CertA.events 400, 1 ≤ z ∧ z ≤ 400 := CertA.events_bounds

lemma one_mem_evs : (1 : ℚ) ∈ CertA.events 400 := by
  have := CertA.int_mem_events 1 le_rfl (by norm_num)
  rwa [Int.cast_one] at this

lemma four_hundred_mem_evs : (400 : ℚ) ∈ CertA.events 400 := by
  have := CertA.int_mem_events 400 (by norm_num) le_rfl
  rwa [show ((400 : ℤ) : ℚ) = 400 by norm_num] at this

lemma cell_le_evs (i : ℕ) (hi : i < LL (CertA.events 400)) (q : ℚ)
    (h1 : xL (CertA.events 400) i < q) (h2 : (q : ℝ) < xL (CertA.events 400) (i + 1)) :
    ((CertA.eStar q : ℚ) : ℝ) ≤ uL (CertA.events 400) i := by
  unfold xL at h1 h2
  have h1' : (CertA.events 400).getD i 0 < q := by exact_mod_cast h1
  have h2' : q < (CertA.events 400).getD (i + 1) 0 := by exact_mod_cast h2
  unfold uL
  rw [CertA.eStar_eq_mid _ _ (consec_list i hi) q h1' h2']

lemma tail_le (q : ℚ) (hq : ((400 : ℕ) : ℚ) ≤ q) :
    ((CertA.eStar q : ℚ) : ℝ) ≤ 33 + (G : ℝ) * ((Int.fract q : ℚ) : ℝ) := by
  have hq' : (1 : ℚ) ≤ q := le_trans (by norm_num) hq
  have h := CertA.eStar_le_tail q hq'
  exact_mod_cast h

end ZetaIrr.Z7
