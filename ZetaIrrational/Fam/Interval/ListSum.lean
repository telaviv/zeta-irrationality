/-
# List-form phase functions as sums (generic bridge lemmas)

For a factor list `l : List Fac` (`Interval/Psi.lean`), the recursively defined `psiL`, `dpsiL`,
`d2psiL`, `d3psiL` equal the sums of `l.map` of their summands, and a `Fin n`-indexed sum over an
enumeration `A` of the list (`List.ofFn A = l`) equals the list sum. This turns the bridge between
the interval certificate (list form) and the `Fin n`-indexed `Analytic/` definitions into
per-index identities of the factor data, avoiding a large `ring_nf` over all factors
(used in `Z7/Interval/BridgeZ7.lean`).
-/
import ZetaIrrational.Interval.Psi

namespace ZetaIrr.Fam.Interval

open Complex ZetaIrr.Interval

lemma psiL_eq_sum (l : List Fac) (z : ℂ) :
    psiL l z = (l.map fun a => (a.c : ℂ) * (a.α z * log (a.α z))).sum := by
  induction l with
  | nil => simp [psiL]
  | cons a l ih => simp [psiL, ih]

lemma dpsiL_eq_sum (l : List Fac) (z : ℂ) :
    dpsiL l z = (l.map fun a => (a.c : ℂ) * ((a.s : ℂ) * (log (a.α z) + 1))).sum := by
  induction l with
  | nil => simp [dpsiL]
  | cons a l ih => simp [dpsiL, ih]

lemma d2psiL_eq_sum (l : List Fac) (z : ℂ) :
    d2psiL l z = (l.map fun a => (a.c : ℂ) * ((a.s : ℂ) * (a.s : ℂ) / a.α z)).sum := by
  induction l with
  | nil => simp [d2psiL]
  | cons a l ih => simp [d2psiL, ih]

lemma d3psiL_eq_sum (l : List Fac) (z : ℂ) :
    d3psiL l z = (l.map fun a =>
      (a.c : ℂ) * (-((a.s : ℂ) * (a.s : ℂ) * (a.s : ℂ)) / a.α z ^ 2)).sum := by
  induction l with
  | nil => simp [d3psiL]
  | cons a l ih => simp [d3psiL, ih]

/-- A `Fin n`-indexed sum over an enumeration of a list is the list sum. -/
lemma sum_fin_eq_list {n : ℕ} (A : Fin n → Fac) (F : Fac → ℂ) :
    ∑ i, F (A i) = ((List.ofFn A).map F).sum := by
  rw [List.map_ofFn, List.sum_ofFn]; rfl

end ZetaIrr.Fam.Interval
