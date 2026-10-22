import ZetaIrrational.PNT.Port.Consequences

/-!
# The prime number theorem, Chebyshev form (part (a))

`θ` is **Mathlib's** `Chebyshev.theta`: `θ x = ∑_{p ∈ Ioc 0 ⌊x⌋₊, p prime} log p`.

Mathlib v4.35.0 has `Chebyshev.theta` and Chebyshev's bound `Chebyshev.theta_le_log4_mul_x`, but not
the prime number theorem itself. The proof of `θ ~ id` (`Port.chebyshev_asymptotic`) is the
Wiener–Ikehara route of PrimeNumberTheoremAnd (A. Kontorovich, T. Tao, et al., Apache-2.0),
ported via domino14/zeta5; see `ZetaIrrational/PNT/Port/` and its `LICENSE`.

Status: fully proved, no `sorry`.
-/

open Filter Topology
open scoped Chebyshev

namespace ZetaIrr.PNT

/-- **The prime number theorem**, in Chebyshev's form `θ(x)/x → 1`
(`θ` = Mathlib's `Chebyshev.theta`). -/
theorem theta_div_tendsto : Tendsto (fun x : ℝ => θ x / x) atTop (𝓝 1) :=
  (Asymptotics.isEquivalent_iff_tendsto_one (eventually_ne_atTop (0 : ℝ))).mp
    Port.chebyshev_asymptotic

/-- PNT along `x = n / c`, normalised by `n`: `θ(n/c)/n → 1/c` for `c > 0`. -/
theorem theta_nat_div_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => θ ((n : ℝ) / c) / n) atTop (𝓝 (1 / c)) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) / c) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hc
  have h2 := (theta_div_tendsto.comp h1).mul_const (1 / c)
  rw [one_mul] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [Function.comp_apply]
  field_simp

end ZetaIrr.PNT
