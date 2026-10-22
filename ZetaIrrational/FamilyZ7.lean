/-
# The concrete family Z7: parameters, `R_n`, `L_n`, and the assembly from the inputs

The parameter set "Z7":
* `r = 11/12`, `n ∈ 240ℕ`, zero multiplicity `5`, `S = 18` pole blocks, `G = 547/120`;
* the pole blocks have offsets `δ = k/80`, `k = 1, …, 18`, each of multiplicity 1;
* the factor `2t + n` makes `deg R_n = -1094(m+1) - 17` odd (needed for Lemma 2).

With `n = 240(m+1)`: `rn = 220(m+1)`, `(1+r)n = 460(m+1)`, `δ n = 3k(m+1)`.

Contents:
* the concrete `R_n` and `L_n = Σ_{t ≥ 1} R_n⁗(t)`;
* `S = 18`, `G > 0`, and the block offsets `0 < δ < 1/2`;
* `margin_Z7`: `V + A < 0` for `V ≤ Vcert = -10.1167` and `A ≤ Acert` (margin ≈ 0.198);
* `Hyp`, collecting the conclusions of Lemmas 3–6 for these `R_n`, `L_n`, and
  `oneOfZeta7To21_of_hyp : Hyp → OneOfZeta7To21`.

`Vcert` bounds the real part of the saddle value `Ω` of Lemma 6 (certified `Re Ω ≤ -10.1167485`),
and `Acert` bounds the constant `A` of Lemma 5.
-/
import ZetaIrrational.Defs
import ZetaIrrational.Statement
import ZetaIrrational.Assembly

namespace ZetaIrr

open Filter Topology

/-- The upper bound of the exact A certificate of Lemma 5 (X = 400,
30,137 event intervals). -/
def Acert : ℚ := 11757994664484187722611840743096153 / 1185451381619680151243401356902400

/-- The saddle-point size constant: `Re Ω ≤ Vcert` (certified `Re Ω ≤ -10.1167485`). -/
def Vcert : ℚ := -101167 / 10000

/-- **The final inequality for Z7.** `V + A < 0` for `V ≤ Vcert` and `A ≤ Acert`
(margin about `0.198`). -/
theorem margin_Z7 (V A : ℝ) (hV : V ≤ (Vcert : ℝ)) (hA : A ≤ (Acert : ℝ)) : V + A < 0 := by
  have h : (Vcert : ℝ) + (Acert : ℝ) < 0 := by norm_num [Vcert, Acert]
  linarith

end ZetaIrr

namespace ZetaIrr.Z7

open Filter Topology Finset
open scoped BigOperators

/-- Pole blocks `(k, m)`: offset `δ = k/80`, multiplicity `m`. -/
def blocks : List (ℕ × ℕ) :=
  [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1), (9, 1),
   (10, 1), (11, 1), (12, 1), (13, 1), (14, 1), (15, 1), (16, 1), (17, 1), (18, 1)]

/-- The progression `n = 240 (m+1)` (`q = 240`, avoiding `n = 0`). -/
def nOf (m : ℕ) : ℕ := 240 * (m + 1)

/-- `G = Σ_j m_j (1 - 2δ_j) - 10r`. -/
def G : ℚ := 547 / 120

/-- `S = Σ_j m_j = 18`, so `N = S + 3 = 21` (S even). -/
lemma S_eq : (blocks.map Prod.snd).sum = 18 := by decide

/-- `G > 0`. -/
lemma H1 : 0 < G := by norm_num [G]

/-- Every block offset satisfies `0 < δ < 1/2` (`1 ≤ k < 40`), so each block
`[3k(m+1), n - 3k(m+1)]` is nonempty, contains the centre, and avoids `0`. -/
lemma blocks_bounds : ∀ b ∈ blocks, 1 ≤ b.1 ∧ b.1 < 40 := by decide

/-- The concrete rational function `R_n(t)` for `n = 240 (m+1)`:
`(2t + n) · Π_{l=1}^{rn} (t - l)^5 · Π_{l=n+1}^{(1+r)n} (t + l)^5 /`
`Π_j Π_{k = δ_j n}^{(1-δ_j) n} (t + k)^{m_j}`,
with `r n = 220 (m+1)`, `(1+r) n = 460 (m+1)`, `δ_j n = 3 k_j (m+1)`. -/
noncomputable def R (m : ℕ) (t : ℝ) : ℝ :=
  (2 * t + (nOf m : ℝ)) *
    (∏ l ∈ Icc 1 (220 * (m + 1)), (t - (l : ℝ)) ^ 5) *
    (∏ l ∈ Icc (nOf m + 1) (460 * (m + 1)), (t + (l : ℝ)) ^ 5) /
    (blocks.map (fun b =>
      (∏ k ∈ Icc (3 * b.1 * (m + 1)) (nOf m - 3 * b.1 * (m + 1)), (t + (k : ℝ))) ^ b.2)).prod

/-- The linear form `L_n = Σ_{t ≥ 1} R_n⁗(t)`. -/
noncomputable def L (m : ℕ) : ℝ := ∑' t : ℕ, iteratedDeriv 4 (R m) ((t : ℝ) + 1)

/-- The inputs of the assembly (Lemmas 3–6), stated for the concrete `R_n`, `L_n`
above. -/
structure Hyp where
  /-- Lemma 3: `L_n ∈ ℚ + ℚ ζ(7) + ℚ ζ(9) + … + ℚ ζ(21)`. -/
  ρ : ℕ → ℚ
  τ : ℕ → ℕ → ℚ
  expansion : ∀ m, L m = (ρ m : ℝ) + ∑ j ∈ Icc 3 10, (τ m j : ℝ) * zetaR (2 * j + 1)
  /-- Lemma 4: a common denominator `D_n` (a positive rational). -/
  D : ℕ → ℚ
  D_pos : ∀ m, 0 < D m
  int_ρ : ∀ m, ∃ z : ℤ, (z : ℚ) = D m * ρ m
  int_τ : ∀ m j, ∃ z : ℤ, (z : ℚ) = D m * τ m j
  /-- Lemma 5: the arithmetic integral `A`, with its certified upper bound. -/
  A : ℝ
  hA : A ≤ (Acert : ℝ)
  /-- Lemmas 4–5: `log D_n ≤ G log n! + n A + o(n)`. -/
  εA : ℕ → ℝ
  εA_lim : Tendsto εA atTop (𝓝 0)
  arith : ∀ᶠ m in atTop, Real.log (D m : ℝ)
    ≤ (G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * (A + εA m)
  /-- Lemma 6(i), saddle-point version: `log |L_n| ≤ -G log n! + n V_cert + o(n)`. -/
  εL : ℕ → ℝ
  εL_lim : Tendsto εL atTop (𝓝 0)
  size : ∀ᶠ m in atTop, L m ≠ 0 →
    Real.log |L m| ≤ -(G : ℝ) * Real.log ((nOf m).factorial : ℝ) + (nOf m : ℝ) * (Vcert + εL m)
  /-- Lemma 6(ii): `L_n ≠ 0` for infinitely many `n`. -/
  nonvan : ∃ᶠ m in atTop, L m ≠ 0

/-- **Main theorem (conditional).** The inputs `Hyp` imply that one of `ζ(7), ζ(9), …, ζ(21)` is
irrational. -/
theorem oneOfZeta7To21_of_hyp (H : Hyp) : OneOfZeta7To21 := by
  choose a ha using H.int_ρ
  choose c hc using H.int_τ
  have hform : ∀ m, (a m : ℝ) + ∑ j ∈ Icc 3 10, (c m j : ℝ) * zetaR (2 * j + 1)
      = (H.D m : ℝ) * L m := by
    intro m
    rw [H.expansion m, mul_add, Finset.mul_sum]
    have ha' : (a m : ℝ) = (H.D m : ℝ) * (H.ρ m : ℝ) := by exact_mod_cast ha m
    rw [ha']
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hc' : (c m j : ℝ) = (H.D m : ℝ) * (H.τ m j : ℝ) := by exact_mod_cast hc m j
    rw [hc']
    ring
  have hQ : (Vcert : ℝ) + H.A < 0 := margin_Z7 _ H.A le_rfl H.hA
  apply oneOfZeta7To21_of_forms a c
  · refine Tendsto.congr (fun m => (hform m).symm) ?_
    refine tendsto_mul_zero_of_log_bound (fun m => (H.D m : ℝ)) L nOf
      (fun m => by unfold nOf; omega) (fun m => by exact_mod_cast H.D_pos m)
      ((Vcert : ℝ) + H.A) hQ (fun m => H.εA m + H.εL m)
      (by simpa using H.εA_lim.add H.εL_lim) ?_
    filter_upwards [H.arith, H.size] with m h1 h2 hL
    have h2' := h2 hL
    nlinarith [h1, h2']
  · refine H.nonvan.mono (fun m hm => ?_)
    rw [hform]
    exact mul_ne_zero (by exact_mod_cast (H.D_pos m).ne') hm

end ZetaIrr.Z7
