/-
# Glue (Z7): the small-prime error term of `log_D_sub_le` is `o(n)`

With `n = 240(m+1)` and `𝒩 = 700(m+1) + 1 ≤ 3n`:
* `tendsto_err2`: the small-prime error `182 ⌊√𝒩⌋ log 𝒩 / n → 0`.

(PROOF_ZETA (4.1). There is no `p = 2` main term here, unlike PROOF_BETA (4.4).)

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.Arith.Lemma4
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace ZetaIrr.Z7

open Filter Topology Finset Asymptotics

lemma nOf_pos (m : ℕ) : (0 : ℝ) < nOf m := by
  unfold nOf; positivity

lemma tendsto_nOf_atTop : Tendsto (fun m => (nOf m : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
  unfold nOf; push_cast; nlinarith

lemma tendsto_NN_atTop : Tendsto (fun m => (Arith.NN m : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun m => ?_) tendsto_natCast_atTop_atTop
  unfold Arith.NN; push_cast; nlinarith

/-- The small-prime error: `182 ⌊√𝒩⌋ log 𝒩 / n → 0` (`𝒩 = 700(m+1)+1 ≤ 3n`). -/
lemma tendsto_err2 :
    Tendsto (fun m => 182 * (Nat.sqrt (Arith.NN m) : ℝ) * Real.log (Arith.NN m) / nOf m)
      atTop (𝓝 0) := by
  have hlo : Tendsto (fun m => Real.log (Arith.NN m) / (Arith.NN m : ℝ) ^ (1 / (2 : ℝ)))
      atTop (𝓝 0) := by
    have := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
      ).comp tendsto_NN_atTop
    simpa [Function.comp_def] using this
  have hup := hlo.const_mul 546
  rw [mul_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun m => ?_) (fun m => ?_)
  · have := nOf_pos m
    have : 0 ≤ Real.log (Arith.NN m) := Real.log_natCast_nonneg _
    positivity
  · have hn := nOf_pos m
    set N : ℝ := (Arith.NN m : ℝ) with hNdef
    have hN : 0 < N := by rw [hNdef]; unfold Arith.NN; positivity
    have hN3 : N ≤ 3 * (nOf m : ℝ) := by rw [hNdef]; unfold Arith.NN nOf; push_cast; nlinarith
    have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg _
    have hs : ((Nat.sqrt (Arith.NN m) : ℕ) : ℝ) ≤ √N := Real.nat_sqrt_le_real_sqrt
    have hspos : 0 < √N := Real.sqrt_pos.mpr hN
    change 182 * ((Nat.sqrt (Arith.NN m) : ℕ) : ℝ) * Real.log N / nOf m
      ≤ 546 * (Real.log N / N ^ (1 / (2 : ℝ)))
    rw [← Real.sqrt_eq_rpow, mul_div_assoc', div_le_div_iff₀ hn hspos]
    have h1 : 182 * ((Nat.sqrt (Arith.NN m) : ℕ) : ℝ) * Real.log N * √N
        ≤ 182 * √N * Real.log N * √N := by gcongr
    have hmul : √N * √N = N := Real.mul_self_sqrt hN.le
    have h2 : 182 * √N * Real.log N * √N = 182 * Real.log N * N := by
      calc 182 * √N * Real.log N * √N = 182 * Real.log N * (√N * √N) := by ring
        _ = 182 * Real.log N * N := by rw [hmul]
    nlinarith [mul_le_mul_of_nonneg_left hN3 (by positivity : (0 : ℝ) ≤ 182 * Real.log N)]

end ZetaIrr.Z7
