/-
# The A-certificate for Z7: a kernel-reducible sort for the event list

`events X` (`Z7/CertA/Defs.lean`) uses `List.mergeSort`, which is defined by well-founded recursion
and does not reduce well in the kernel. Here:

* `msort` is a merge sort by structural recursion (with fuel); for *every* fuel and comparator it
  only permutes its input (`mem_msort`), so no correctness proof of the comparator is needed;
* `eq_of_pairwise_lt` — two strictly increasing lists with the same members are equal;
* `events_eq_of_check` — if `dedupAdj (msort … (cuts X ++ crossings 1 X)) = L` and `L` is strictly
  increasing (checked by `sortedLT`), then `events X = L`.

The comparator `qleN` compares `a.num.toNat * b.den` with `b.num.toNat * a.den` (correct for
`a, b ≥ 0`, which is all that is needed here; correctness is not used in any proof).

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.CertA.Defs

namespace ZetaIrr.Z7.CertA

/-! ## Merge sort with fuel -/

variable {α : Type}

/-- Insert the run `x :: xs` into `ys` (structural in `ys`); `rec` is the merge of `xs`. -/
def mergeI (le : α → α → Bool) (x : α) (xs : List α) (rec : List α → List α) :
    List α → List α
  | [] => x :: xs
  | y :: ys => if le x y then x :: rec (y :: ys) else y :: mergeI le x xs rec ys

/-- Merge (structural in the first list). -/
def mergeL (le : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => mergeI le x xs (mergeL le xs) ys

/-- Split into the elements at even and at odd positions. -/
def splitL : List α → List α × List α
  | [] => ([], [])
  | a :: l => ((a :: (splitL l).2), (splitL l).1)

/-- Merge sort with fuel `n` (returns the input unchanged when the fuel runs out). -/
def msort (le : α → α → Bool) : ℕ → List α → List α
  | 0, l => l
  | n + 1, l =>
    match l with
    | [] => []
    | [a] => [a]
    | a :: b :: t => mergeL le (msort le n (splitL (a :: b :: t)).1)
        (msort le n (splitL (a :: b :: t)).2)

lemma mem_mergeI (le : α → α → Bool) (x : α) (xs : List α) (rec : List α → List α)
    (hrec : ∀ ys z, z ∈ rec ys ↔ z ∈ xs ∨ z ∈ ys) :
    ∀ (ys : List α) (z : α), z ∈ mergeI le x xs rec ys ↔ z ∈ x :: xs ∨ z ∈ ys
  | [], z => by simp [mergeI]
  | y :: ys, z => by
    rw [mergeI]
    split_ifs
    · simp only [List.mem_cons, hrec]; tauto
    · simp only [List.mem_cons, mem_mergeI le x xs rec hrec ys z]; tauto

lemma mem_mergeL (le : α → α → Bool) :
    ∀ (xs ys : List α) (z : α), z ∈ mergeL le xs ys ↔ z ∈ xs ∨ z ∈ ys
  | [], ys, z => by simp [mergeL]
  | x :: xs, ys, z => by
    rw [mergeL]
    exact mem_mergeI le x xs _ (fun ys z => mem_mergeL le xs ys z) ys z

lemma mem_splitL : ∀ (l : List α) (z : α), z ∈ l ↔ z ∈ (splitL l).1 ∨ z ∈ (splitL l).2
  | [], z => by simp [splitL]
  | a :: l, z => by
    simp only [splitL, List.mem_cons]
    rw [mem_splitL l z]; tauto

lemma mem_msort (le : α → α → Bool) : ∀ (n : ℕ) (l : List α) (z : α), z ∈ msort le n l ↔ z ∈ l
  | 0, l, z => by simp [msort]
  | n + 1, [], z => by simp [msort]
  | n + 1, [a], z => by simp [msort]
  | n + 1, a :: b :: t, z => by
    rw [msort, mem_mergeL, mem_msort le n, mem_msort le n, ← mem_splitL]

/-! ## Strictly increasing lists -/

/-- Comparator for `msort` (exact for nonnegative rationals). -/
def qleN (a b : ℚ) : Bool := Nat.ble (Nat.mul a.num.toNat b.den) (Nat.mul b.num.toNat a.den)

/-- Boolean check that a list of rationals is strictly increasing (adjacent pairs). -/
def sortedLT : List ℚ → Bool
  | a :: b :: l => decide (a < b) && sortedLT (b :: l)
  | _ => true

lemma pairwise_of_sortedLT : ∀ l : List ℚ, sortedLT l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [sortedLT, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pairwise_of_sortedLT (b :: l) h.2
    refine List.Pairwise.cons (fun z hz => ?_) ih
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h.1
    · exact h.1.trans ((List.pairwise_cons.1 ih).1 z hz)

/-- Two strictly increasing lists with the same members are equal. -/
lemma eq_of_pairwise_lt : ∀ (l₁ l₂ : List ℚ), l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ z, z ∈ l₁ ↔ z ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by simpa using (h b).2 List.mem_cons_self
  | a :: _, [], _, _, h => by simpa using (h a).1 List.mem_cons_self
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with hb | hb
      · exact hb
      rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with ha | ha
      · exact ha.symm
      exact absurd ((h₁.1 b ha).trans (h₂.1 a hb)) (lt_irrefl a)
    subst hab
    congr 1
    apply eq_of_pairwise_lt l₁ l₂ h₁.2 h₂.2
    intro z
    constructor
    · intro hz
      rcases List.mem_cons.1 ((h z).1 (List.mem_cons_of_mem _ hz)) with rfl | hz'
      · exact absurd (h₁.1 z hz) (lt_irrefl z)
      · exact hz'
    · intro hz
      rcases List.mem_cons.1 ((h z).2 (List.mem_cons_of_mem _ hz)) with rfl | hz'
      · exact absurd (h₂.1 z hz) (lt_irrefl z)
      · exact hz'

/-- `events X` is any strictly increasing list with the same members as the (kernel-sortable)
`dedupAdj (msort …)`. -/
lemma events_eq_of_check (X n : ℕ) (L : List ℚ)
    (hL : dedupAdj (msort qleN n (cuts X ++ crossings 1 X)) = L)
    (hs : sortedLT L = true)
    (hpw : (events X).Pairwise (· < ·))
    (hmem : ∀ z, z ∈ events X ↔ z ∈ cuts X ∨ z ∈ crossings 1 X)
    (hdd : ∀ (l : List ℚ) (z : ℚ), z ∈ dedupAdj l ↔ z ∈ l) :
    events X = L := by
  apply eq_of_pairwise_lt _ _ hpw (pairwise_of_sortedLT L hs)
  intro z
  rw [hmem, ← hL, hdd, mem_msort, List.mem_append]

end ZetaIrr.Z7.CertA
