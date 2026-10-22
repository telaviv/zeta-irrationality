/-
# Sums of logarithms over runs of consecutive (half-)integers versus `F(y) = y log y`

Elementary one-sided comparisons, all consequences of the convexity of `F`
(`F_tangent`): for `c > 0`, `log c ≤ F(c+1) - F(c) - 1`, and for `c ≥ 1`,
`F(c) - F(c-1) - 1 ≤ log c`. Telescoping gives:

* `sum_log_int_le`: `Σ_{l=a}^{a+j} log(t - l) ≤ F(t - a + 1) - F(t - a - j) - (j + 1)`;
* `sum_log_half_ge`: `Σ_{k=A}^{A+j} log(t + k + 1/2) ≥ F(t + A + j + 1/2) - F(t + A - 1/2) - (j + 1)`;
* `log_factorial_le`: `log n! ≤ n log n - n + log(n+1) + 1`;
* `F_scale`: `F(n y) = n F(y) + n y log n`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Size.Common

namespace ZetaIrr.Size

open Real Finset

lemma log_le_F_succ {c : ℝ} (hc : 0 < c) : Real.log c ≤ F (c + 1) - F c - 1 := by
  have := F_tangent (y := c + 1) (y₀ := c) (by linarith) hc
  linarith

lemma F_pred_le_log {c : ℝ} (hc : 1 ≤ c) : F c - F (c - 1) - 1 ≤ Real.log c := by
  have := F_tangent (y := c - 1) (y₀ := c) (by linarith) (by linarith)
  linarith

/-- Numerator runs: `Σ_{l ∈ [a, a+j]} log(t - l) ≤ F(t - a + 1) - F(t - (a+j)) - (j+1)`. -/
lemma sum_log_int_le (t : ℝ) (a : ℤ) (j : ℕ) (h : (((a + j : ℤ)) : ℝ) < t) :
    ∑ l ∈ Icc a (a + j), Real.log (t - l) ≤
      F (t - a + 1) - F (t - ((a + j : ℤ) : ℝ)) - (j + 1) := by
  induction j with
  | zero =>
    simp only [Nat.cast_zero, add_zero, Icc_self, sum_singleton] at h ⊢
    have := log_le_F_succ (c := t - a) (by linarith)
    have e : t - (a : ℝ) + 1 = t - a + 1 := rfl
    linarith
  | succ j ih =>
    have hj : (((a + j : ℤ)) : ℝ) < t := by push_cast at h ⊢; linarith
    have hins : insert (a + j + 1) (Icc a (a + j)) = Icc a (a + (j + 1 : ℕ)) := by
      rw [insert_Icc_right_eq_Icc_add_one (by omega)]; push_cast; ring_nf
    have hnot : a + j + 1 ∉ Icc a (a + j) := by simp
    rw [← hins, sum_insert hnot]
    have h1 := ih hj
    have h2 := log_le_F_succ (c := t - ((a + j + 1 : ℤ) : ℝ)) (by push_cast at h ⊢; linarith)
    have e1 : t - ((a + j + 1 : ℤ) : ℝ) + 1 = t - ((a + j : ℤ) : ℝ) := by push_cast; ring
    have e2 : ((a + (j + 1 : ℕ) : ℤ) : ℝ) = ((a + j + 1 : ℤ) : ℝ) := by push_cast; ring
    rw [e1] at h2
    rw [e2]
    push_cast at h1 h2 ⊢
    linarith

/-- Denominator runs: `Σ_{k ∈ [A, A+j]} log(t + k + 1/2) ≥ F(t+A+j+1/2) - F(t+A-1/2) - (j+1)`. -/
lemma sum_log_half_ge (t : ℝ) (A j : ℕ) (ht : 1 / 2 ≤ t + A) :
    F (t + ((A + j : ℕ) : ℝ) + 1 / 2) - F (t + A - 1 / 2) - (j + 1) ≤
      ∑ k ∈ Icc A (A + j), Real.log (t + k + 1 / 2) := by
  induction j with
  | zero =>
    simp only [Nat.cast_zero, add_zero, Icc_self, sum_singleton]
    have := F_pred_le_log (c := t + A + 1 / 2) (by linarith)
    have e : t + (A : ℝ) + 1 / 2 - 1 = t + A - 1 / 2 := by ring
    rw [e] at this
    linarith
  | succ j ih =>
    have hins : insert (A + j + 1) (Icc A (A + j)) = Icc A (A + (j + 1)) := by
      rw [insert_Icc_right_eq_Icc_add_one (by omega), add_assoc]
    have hnot : A + j + 1 ∉ Icc A (A + j) := by simp
    rw [← hins, sum_insert hnot]
    have h2 := F_pred_le_log (c := t + ((A + j + 1 : ℕ) : ℝ) + 1 / 2) (by push_cast; linarith)
    have e1 : t + ((A + j + 1 : ℕ) : ℝ) + 1 / 2 - 1 = t + ((A + j : ℕ) : ℝ) + 1 / 2 := by
      push_cast; ring
    rw [e1] at h2
    have e2 : ((A + (j + 1) : ℕ) : ℝ) = ((A + j + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e2]
    push_cast at ih h2 ⊢
    linarith

/-- `log n! ≤ F(n+1) - n`. -/
lemma log_factorial_le_F (n : ℕ) : Real.log (n.factorial : ℝ) ≤ F (n + 1) - n := by
  induction n with
  | zero => simp [F]
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have := log_le_F_succ (c := ((n + 1 : ℕ) : ℝ)) (by positivity)
    push_cast at this ih ⊢
    have e : (n : ℝ) + 1 + 1 = n + 1 + 1 := rfl
    linarith

/-- `log n! ≤ n log n - n + log(n+1) + 1`. -/
lemma log_factorial_le (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log n - n + Real.log (n + 1) + 1 := by
  have h1 := log_factorial_le_F n
  have h2 := F_tangent (y := (n : ℝ)) (y₀ := n + 1) (by positivity) (by positivity)
  unfold F at h1 h2
  nlinarith

/-- Scaling: `F(n y) = n F(y) + n y log n` for `n > 0`, `y ≥ 0`. -/
lemma F_scale {n y : ℝ} (hn : 0 < n) (hy : 0 ≤ y) : F (n * y) = n * F y + n * y * Real.log n := by
  unfold F
  rcases hy.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_mul hn.ne' h.ne']; ring

end ZetaIrr.Size
