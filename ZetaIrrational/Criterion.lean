/-
# The irrationality criterion

The contradiction step of the main theorem. If integer linear forms `a n + ∑ c n i * x i` tend
to `0` and are nonzero for infinitely many `n`, then some `x i` is irrational.
-/
import Mathlib

namespace ZetaIrr

open Filter Topology
open scoped BigOperators

/-- If all `x i` (for `i ∈ s`) are rational, there is a positive integer `Q` such that
`Q * (a + ∑ c i * x i)` is an integer for all integers `a`, `c i`. -/
lemma exists_common_denominator {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hrat : ∀ i ∈ s, ∃ q : ℚ, (q : ℝ) = x i) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ (a : ℤ) (c : ι → ℤ),
      ∃ z : ℤ, (z : ℝ) = (Q : ℝ) * ((a : ℝ) + ∑ i ∈ s, (c i : ℝ) * x i) := by
  classical
  choose! q hq using hrat
  refine ⟨∏ i ∈ s, (q i).den, Finset.prod_pos (fun i _ => (q i).pos), ?_⟩
  intro a c
  -- each `Q * x i` is an integer
  have hint : ∀ i ∈ s, ∃ z : ℤ, (z : ℝ) = ((∏ j ∈ s, (q j).den : ℕ) : ℝ) * x i := by
    intro i hi
    have hdvd : (q i).den ∣ ∏ j ∈ s, (q j).den := Finset.dvd_prod_of_mem _ hi
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨(q i).num * k, ?_⟩
    rw [← hq i hi, hk]
    push_cast
    have hden : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
    rw [Rat.cast_def]
    field_simp
  choose! z hz using hint
  refine ⟨(∏ j ∈ s, (q j).den : ℕ) * a + ∑ i ∈ s, c i * z i, ?_⟩
  push_cast
  rw [mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [hz i hi]
  push_cast
  ring

/-- **Irrationality criterion.** Small, infinitely often nonzero integer linear forms in the `x i`
force one of the `x i` to be irrational. -/
theorem exists_irrational_of_small_forms {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (a : ℕ → ℤ) (c : ℕ → ι → ℤ)
    (hlim : Tendsto (fun n => (a n : ℝ) + ∑ i ∈ s, (c n i : ℝ) * x i) atTop (𝓝 0))
    (hne : ∃ᶠ n in atTop, (a n : ℝ) + ∑ i ∈ s, (c n i : ℝ) * x i ≠ 0) :
    ∃ i ∈ s, Irrational (x i) := by
  by_contra hcon
  push Not at hcon
  have hrat : ∀ i ∈ s, ∃ q : ℚ, (q : ℝ) = x i := by
    intro i hi
    have := hcon i hi
    simpa [Irrational, Set.mem_range] using this
  obtain ⟨Q, hQ, hQint⟩ := exists_common_denominator s x hrat
  set F : ℕ → ℝ := fun n => (a n : ℝ) + ∑ i ∈ s, (c n i : ℝ) * x i with hF
  -- eventually `|F n| < 1 / Q`
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hev : ∀ᶠ n in atTop, |F n| < 1 / (Q : ℝ) := by
    have := (Metric.tendsto_nhds.mp hlim) (1 / (Q : ℝ)) (by positivity)
    filter_upwards [this] with n hn
    simpa [Real.dist_eq] using hn
  obtain ⟨n, hn1, hn2⟩ := (hne.and_eventually hev).exists
  obtain ⟨z, hz⟩ := hQint (a n) (c n)
  have hzF : (z : ℝ) = (Q : ℝ) * F n := by simpa [hF] using hz
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hzF
    exact hn1 (by
      rcases mul_eq_zero.mp hzF.symm with h | h
      · exact absurd h (ne_of_gt hQpos)
      · simpa [hF] using h)
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz0
    exact_mod_cast this
  have : |(z : ℝ)| < 1 := by
    rw [hzF, abs_mul, abs_of_pos hQpos]
    calc (Q : ℝ) * |F n| < (Q : ℝ) * (1 / (Q : ℝ)) := by gcongr
      _ = 1 := by field_simp
  linarith

end ZetaIrr
