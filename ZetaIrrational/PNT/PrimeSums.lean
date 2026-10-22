import ZetaIrrational.PNT.Theta

/-!
# Prime sums with step-function weights

The prime number theorem input for Lemma 5.

`θ` is Mathlib's `Chebyshev.theta`. All prime sums are written with `primeSum w c d`,
`= ∑_{p prime, c < p ≤ d} w p · log p`; `primeSum_eq_sum_filter` converts it to a sum over any
finset containing the relevant primes.

Main results (namespace `ZetaIrr.PNT`):
* `eventually_primeSum_cell_le`: for a weight with `h ≤ u` on `(a, b)`,
  `∑_{n/b < p ≤ n/a} h(n/p) log p ≤ n u (1/a − 1/b) + o(n)`.
* `eventually_primeSum_step_le`: upper bound for a weight `h(n/p)` dominated on the open cells
  `(x i, x (i+1))` by constants `u i` (no condition at the breakpoints).
* `eventually_primeSum_tail_frac_le`: tail with `h ≤ C + G·{x}` on `[X, ∞)`:
  `∑_{p ≤ n/X} h(n/p) log p ≤ n (C/X + G/(2(X−1))) + o(n)`.
* `eventually_primeSum_lemma5_le`: the combination used in Lemma 5 (step part on `[x_0, X]`
  plus tail).
-/

open Filter Topology Finset Real
open scoped Chebyshev

namespace ZetaIrr.PNT

/-- `primeSum w c d = ∑_{p prime, c < p ≤ d} w p · log p`. -/
noncomputable def primeSum (w : ℕ → ℝ) (c d : ℝ) : ℝ :=
  ∑ p ∈ (Ioc 0 ⌊d⌋₊).filter (fun p : ℕ => p.Prime ∧ c < (p : ℝ)), w p * Real.log p

lemma mem_primeSum_filter {c d : ℝ} (hd : 0 ≤ d) {p : ℕ} :
    p ∈ (Ioc 0 ⌊d⌋₊).filter (fun p : ℕ => p.Prime ∧ c < (p : ℝ)) ↔
      p.Prime ∧ c < (p : ℝ) ∧ (p : ℝ) ≤ d := by
  simp only [mem_filter, mem_Ioc, Nat.le_floor_iff hd]
  constructor
  · rintro ⟨⟨-, h1⟩, h2, h3⟩
    exact ⟨h2, h3, h1⟩
  · rintro ⟨h2, h3, h1⟩
    exact ⟨⟨h2.pos, h1⟩, h2, h3⟩

/-- Conversion to a sum over any finset `s` that contains every prime in `(c, d]`. -/
theorem primeSum_eq_sum_filter (w : ℕ → ℝ) {c d : ℝ} (hd : 0 ≤ d) (s : Finset ℕ)
    (hs : ∀ p : ℕ, p.Prime → c < (p : ℝ) → (p : ℝ) ≤ d → p ∈ s) :
    primeSum w c d =
      ∑ p ∈ s.filter (fun p : ℕ => p.Prime ∧ c < (p : ℝ) ∧ (p : ℝ) ≤ d), w p * Real.log p := by
  unfold primeSum
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  rw [mem_primeSum_filter hd, mem_filter]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hs p h1 h2 h3, h1, h2, h3⟩
  · rintro ⟨-, h⟩
    exact h

lemma primeSum_self (w : ℕ → ℝ) (c : ℝ) : primeSum w c c = 0 := by
  unfold primeSum
  apply Finset.sum_eq_zero
  intro p hp
  rcases le_or_gt 0 c with hc | hc
  · rw [mem_primeSum_filter hc] at hp
    exact absurd hp.2.2 (not_le.mpr hp.2.1)
  · simp [Nat.floor_eq_zero.mpr (hc.trans one_pos)] at hp

/-- Splitting `(c, e] = (c, d] ∪ (d, e]`. -/
theorem primeSum_add (w : ℕ → ℝ) {c d e : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hde : d ≤ e) :
    primeSum w c d + primeSum w d e = primeSum w c e := by
  have hd : 0 ≤ d := hc.trans hcd
  have he : 0 ≤ e := hd.trans hde
  unfold primeSum
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Ioc 0 ⌊e⌋₊).filter (fun p : ℕ => p.Prime ∧ c < (p : ℝ))) (fun p : ℕ => (p : ℝ) ≤ d)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, mem_Ioc, Nat.le_floor_iff hd, Nat.le_floor_iff he]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩
      exact ⟨⟨⟨h0, h1.trans hde⟩, h2, h3⟩, h1⟩
    · rintro ⟨⟨⟨h0, -⟩, h2, h3⟩, h1⟩
      exact ⟨⟨h0, h1⟩, h2, h3⟩
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, mem_Ioc, Nat.le_floor_iff he, not_le]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩
      exact ⟨⟨⟨h0, h1⟩, h2, hcd.trans_lt h3⟩, h3⟩
    · rintro ⟨⟨⟨h0, h1⟩, h2, -⟩, h3⟩
      exact ⟨⟨h0, h1⟩, h2, h3⟩

/-- `∑_{p ≤ d} log p = θ d`. -/
theorem primeSum_one_zero (d : ℝ) : primeSum (fun _ => 1) 0 d = θ d := by
  unfold primeSum Chebyshev.theta
  simp only [one_mul]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨h, hp, -⟩
    exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨h, hp, by exact_mod_cast h.1⟩

/-- `∑_{c < p ≤ d} log p = θ d − θ c`. -/
theorem primeSum_one {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    primeSum (fun _ => 1) c d = θ d - θ c := by
  have := primeSum_add (fun _ => 1) le_rfl hc hcd
  rw [primeSum_one_zero, primeSum_one_zero] at this
  linarith

theorem primeSum_const (u : ℝ) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    primeSum (fun _ => u) c d = u * (θ d - θ c) := by
  rw [← primeSum_one hc hcd]
  unfold primeSum
  rw [Finset.mul_sum]
  simp

theorem primeSum_mono {w w' : ℕ → ℝ} {c d : ℝ} (hd : 0 ≤ d)
    (h : ∀ p : ℕ, p.Prime → c < (p : ℝ) → (p : ℝ) ≤ d → w p ≤ w' p) :
    primeSum w c d ≤ primeSum w' c d := by
  unfold primeSum
  apply Finset.sum_le_sum
  intro p hp
  rw [mem_primeSum_filter hd] at hp
  exact mul_le_mul_of_nonneg_right (h p hp.1 hp.2.1 hp.2.2) (Real.log_natCast_nonneg p)

/-- A pointwise bound `w ≤ B` gives `primeSum w c d ≤ B (θ d − θ c)`. -/
theorem primeSum_le_mul_theta {w : ℕ → ℝ} {B c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    (h : ∀ p : ℕ, p.Prime → c < (p : ℝ) → (p : ℝ) ≤ d → w p ≤ B) :
    primeSum w c d ≤ B * (θ d - θ c) := by
  rw [← primeSum_const B hc hcd]
  exact primeSum_mono (hc.trans hcd) h

/-- One cell, finite form: if `w ≤ u` at primes in `(c, d)`, and the possible prime `p = d`
contributes at most `K` beyond `u log p`, then `primeSum w c d ≤ u (θ d − θ c) + K`. -/
theorem primeSum_le_cell (w : ℕ → ℝ) {c d u K : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hK : 0 ≤ K)
    (hw : ∀ p : ℕ, p.Prime → c < (p : ℝ) → (p : ℝ) < d → w p ≤ u)
    (hwd : ∀ p : ℕ, p.Prime → (p : ℝ) = d → (w p - u) * Real.log p ≤ K) :
    primeSum w c d ≤ u * (θ d - θ c) + K := by
  have hd : 0 ≤ d := hc.trans hcd
  rw [← primeSum_const u hc hcd]
  unfold primeSum
  set S := (Ioc 0 ⌊d⌋₊).filter (fun p : ℕ => p.Prime ∧ c < (p : ℝ)) with hS
  have key : ∀ p ∈ S, w p * Real.log p ≤
      u * Real.log p + (if (p : ℝ) = d then K else 0) := by
    intro p hp
    rw [hS, mem_primeSum_filter hd] at hp
    obtain ⟨hpp, hcp, hpd⟩ := hp
    rcases hpd.lt_or_eq with hlt | heq
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hlt.ne), add_zero]
      exact mul_le_mul_of_nonneg_right (hw p hpp hcp hlt) (Real.log_natCast_nonneg p)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true heq)]
      have := hwd p hpp heq
      nlinarith
  have hcard : (S.filter (fun p : ℕ => (p : ℝ) = d)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [mem_filter] at ha hb
    exact_mod_cast ha.2.trans hb.2.symm
  calc ∑ p ∈ S, w p * Real.log p
      ≤ ∑ p ∈ S, (u * Real.log p + (if (p : ℝ) = d then K else 0)) := sum_le_sum key
    _ = ∑ p ∈ S, u * Real.log p + ∑ p ∈ S, (if (p : ℝ) = d then K else 0) := sum_add_distrib
    _ ≤ ∑ p ∈ S, u * Real.log p + K := by
        gcongr
        rw [Finset.sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
        calc ((S.filter (fun p : ℕ => (p : ℝ) = d)).card : ℝ) * K ≤ 1 * K := by
              gcongr
              exact_mod_cast hcard
          _ = K := one_mul K

/-! ### Limits -/

lemma tendsto_log_nat_div_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) / a) / n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) / a) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const ha
  have h2 := (Real.tendsto_pow_log_div_mul_add_atTop a 0 1 ha.ne').comp h1
  refine h2.congr' ?_
  filter_upwards with n
  simp only [Function.comp_apply, pow_one, add_zero]
  congr 1
  field_simp

/-! ### Cell and step-function sums -/

/-- One cell, asymptotic upper form. `h ≤ u` is needed only on the open interval `(a, b)`. -/
theorem eventually_primeSum_cell_le (h : ℝ → ℝ) {a b u : ℝ} (ha : 0 < a) (hab : a < b)
    (hh : ∀ y, a < y → y < b → h y ≤ u) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      primeSum (fun p => h ((n : ℝ) / p)) ((n : ℝ) / b) ((n : ℝ) / a) ≤
        n * (u * (1 / a - 1 / b)) + ε * n := by
  have hb : 0 < b := ha.trans hab
  set E := |h a - u|
  have hT : Tendsto (fun n : ℕ => u * ((θ ((n : ℝ) / a) / n - θ ((n : ℝ) / b) / n) -
      (1 / a - 1 / b)) + E * (Real.log ((n : ℝ) / a) / n)) atTop (𝓝 0) := by
    have h1 := ((theta_nat_div_tendsto ha).sub (theta_nat_div_tendsto hb)).sub_const (1 / a - 1 / b)
    rw [sub_self] at h1
    have h2 := tendsto_log_nat_div_div ha
    simpa using (h1.const_mul u).add (h2.const_mul E)
  filter_upwards [hT.eventually (Iio_mem_nhds hε), eventually_ge_atTop ⌈a⌉₊,
    eventually_gt_atTop 0] with n hn hna hn0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hna' : a ≤ (n : ℝ) := Nat.ceil_le.mp hna
  have hlog : 0 ≤ Real.log ((n : ℝ) / a) := Real.log_nonneg ((one_le_div ha).mpr hna')
  have hcell := primeSum_le_cell (fun p => h ((n : ℝ) / p)) (c := (n : ℝ) / b) (d := (n : ℝ) / a)
    (u := u) (K := E * Real.log ((n : ℝ) / a)) (div_nonneg hn0'.le hb.le)
    (div_le_div_of_nonneg_left hn0'.le ha hab.le) (mul_nonneg (abs_nonneg _) hlog) ?_ ?_
  · have hlt : u * ((θ ((n : ℝ) / a) / n - θ ((n : ℝ) / b) / n) - (1 / a - 1 / b)) +
        E * (Real.log ((n : ℝ) / a) / n) < ε := hn
    have e1 : (n : ℝ) * (u * ((θ ((n : ℝ) / a) / n - θ ((n : ℝ) / b) / n) - (1 / a - 1 / b)) +
        E * (Real.log ((n : ℝ) / a) / n)) = u * (θ ((n : ℝ) / a) - θ ((n : ℝ) / b)) +
        E * Real.log ((n : ℝ) / a) - n * (u * (1 / a - 1 / b)) := by
      field_simp
      ring
    have h3 := mul_lt_mul_of_pos_left hlt hn0'
    rw [e1] at h3
    linarith
  · intro p hp hcp hpd
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    apply hh
    · rw [lt_div_iff₀ hp0]
      rw [lt_div_iff₀ ha] at hpd
      linarith [mul_comm a (p : ℝ)]
    · rw [div_lt_iff₀ hp0]
      rw [div_lt_iff₀ hb] at hcp
      linarith [mul_comm b (p : ℝ)]
  · intro p hp hpd
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpa : (n : ℝ) / p = a := by
      rw [hpd]
      field_simp
    rw [hpa, hpd]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hlog

lemma le_of_chain {x : ℕ → ℝ} {L : ℕ} (hx : ∀ i < L, x i < x (i + 1)) :
    ∀ i ≤ L, x 0 ≤ x i
  | 0, _ => le_rfl
  | i + 1, hi => (le_of_chain hx i (by omega)).trans (hx i (by omega)).le

/-- **(b), step function, upper form.** Breakpoints `x 0 < x 1 < … < x L` with `x 0 > 0`; on each
open cell `(x i, x (i+1))` the weight satisfies `h ≤ u i`. Nothing is assumed at the breakpoints
(the at most `L + 1` primes with `n/p` a breakpoint cost `O(log n)` each). -/
theorem eventually_primeSum_step_le (h : ℝ → ℝ) (x u : ℕ → ℝ) (L : ℕ) (hx0 : 0 < x 0)
    (hx : ∀ i < L, x i < x (i + 1))
    (hh : ∀ i < L, ∀ y, x i < y → y < x (i + 1) → h y ≤ u i) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      primeSum (fun p => h ((n : ℝ) / p)) ((n : ℝ) / x L) ((n : ℝ) / x 0) ≤
        n * ∑ i ∈ range L, u i * (1 / x i - 1 / x (i + 1)) + ε * n := by
  induction L generalizing ε with
  | zero =>
    filter_upwards with n
    rw [primeSum_self]
    simp only [range_zero, sum_empty, mul_zero, zero_add]
    exact mul_nonneg hε.le n.cast_nonneg
  | succ L ih =>
    have ih' := ih (fun i hi => hx i (by omega)) (fun i hi => hh i (by omega)) (half_pos hε)
    have hxL : x 0 ≤ x L := le_of_chain hx L (by omega)
    have hxL1 : x L < x (L + 1) := hx L (by omega)
    have cell := eventually_primeSum_cell_le h (hx0.trans_le hxL) hxL1 (hh L (by omega))
      (half_pos hε)
    filter_upwards [ih', cell] with n h1 h2
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    rw [← primeSum_add _ (div_nonneg hn0 (hx0.trans_le (hxL.trans hxL1.le)).le)
      (div_le_div_of_nonneg_left hn0 (hx0.trans_le hxL) hxL1.le)
      (div_le_div_of_nonneg_left hn0 hx0 hxL), sum_range_succ, mul_add]
    linarith

/-! ### The tail with `h ≤ C + G·{x}` on `[X, ∞)` -/

lemma sum_range_succ_cast (K : ℕ) :
    ∑ j ∈ range K, ((j : ℝ) + 1) = (K : ℝ) * (K + 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- One unit interval `[m, m+1]`, cut into `K` equal cells. -/
theorem eventually_primeSum_unit_frac_le (h : ℝ → ℝ) (C G : ℝ) (hG : 0 ≤ G) (m : ℕ)
    (hm : 1 ≤ m) (K : ℕ) (hK : 0 < K)
    (hh : ∀ y, (m : ℝ) ≤ y → y ≤ m + 1 → h y ≤ C + G * Int.fract y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      primeSum (fun p => h ((n : ℝ) / p)) ((n : ℝ) / (m + 1)) ((n : ℝ) / m) ≤
        n * (C * (1 / m - 1 / (m + 1)) + G * (((K : ℝ) + 1) / (2 * K)) / (m : ℝ) ^ 2) +
          ε * n := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  set x : ℕ → ℝ := fun j => (m : ℝ) + j / K with hxdef
  set u : ℕ → ℝ := fun j => C + G * (((j : ℝ) + 1) / K) with hudef
  have hx0 : x 0 = m := by simp [hxdef]
  have hxK : x K = m + 1 := by simp [hxdef, div_self hK'.ne']
  have hxs : ∀ j : ℕ, x (j + 1) - x j = 1 / K := by
    intro j
    simp only [hxdef]
    push_cast
    ring
  have hxm : ∀ j : ℕ, (m : ℝ) ≤ x j := fun j =>
    le_add_of_nonneg_right (div_nonneg j.cast_nonneg hK'.le)
  have hchain : ∀ i < K, x i < x (i + 1) := by
    intro i _
    have := hxs i
    have : (0 : ℝ) < 1 / K := by positivity
    linarith
  have hcell : ∀ i < K, ∀ y, x i < y → y < x (i + 1) → h y ≤ u i := by
    intro i hi y hy1 hy2
    have hmy : (m : ℝ) ≤ y := (hxm i).trans hy1.le
    have hy3 : y ≤ m + 1 := by
      have h1 : ((i : ℝ) + 1) / K ≤ 1 := by
        rw [div_le_one hK']
        exact_mod_cast Nat.succ_le_of_lt hi
      have h2 : x (i + 1) = m + ((i : ℝ) + 1) / K := by simp [hxdef]
      linarith
    have hfr : Int.fract y ≤ y - m := by
      have : ((m : ℤ) : ℝ) ≤ y := by exact_mod_cast hmy
      have hfl : (m : ℤ) ≤ ⌊y⌋ := Int.le_floor.mpr this
      rw [Int.fract]
      have : ((m : ℤ) : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hfl
      push_cast at this
      linarith
    have hyx : y - m < ((i : ℝ) + 1) / K := by
      have : x (i + 1) = m + ((i : ℝ) + 1) / K := by simp [hxdef]
      linarith
    calc h y ≤ C + G * Int.fract y := hh y hmy hy3
      _ ≤ u i := by
        simp only [hudef]
        gcongr
        linarith
  have hx0' : 0 < x 0 := by rw [hx0]; linarith
  filter_upwards [eventually_primeSum_step_le h x u K hx0' hchain hcell hε] with n hn
  rw [hx0, hxK] at hn
  refine hn.trans ?_
  gcongr
  -- the Riemann sum of the majorant
  have hsplit : ∀ j ∈ range K, u j * (1 / x j - 1 / x (j + 1)) =
      C * (1 / x j - 1 / x (j + 1)) + G * (((j : ℝ) + 1) / K) * (1 / x j - 1 / x (j + 1)) := by
    intro j _
    simp only [hudef]
    ring
  rw [sum_congr rfl hsplit, sum_add_distrib, ← mul_sum,
    sum_range_sub' (fun j => 1 / x j), hx0, hxK]
  gcongr ?_ + ?_
  · exact le_rfl
  have hterm : ∀ j ∈ range K, G * (((j : ℝ) + 1) / K) * (1 / x j - 1 / x (j + 1)) ≤
      G / ((K : ℝ) ^ 2 * (m : ℝ) ^ 2) * ((j : ℝ) + 1) := by
    intro j _
    have hxj : (m : ℝ) ≤ x j := hxm j
    have hxj1 : (m : ℝ) ≤ x (j + 1) := hxm (j + 1)
    have hpos : (0 : ℝ) < m := by linarith
    have hxj0 : 0 < x j := hpos.trans_le hxj
    have hxj10 : 0 < x (j + 1) := hpos.trans_le hxj1
    have e : 1 / x j - 1 / x (j + 1) = 1 / (K * (x j * x (j + 1))) := by
      rw [div_sub_div _ _ hxj0.ne' hxj10.ne', one_mul, mul_one, hxs j, div_div]
    rw [e]
    have hle : 1 / ((K : ℝ) * (x j * x (j + 1))) ≤ 1 / (K * (m : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (m : ℝ) ^ 2 ≤ x j * x (j + 1) := by nlinarith
      exact mul_le_mul_of_nonneg_left this hK'.le
    have hj : (0 : ℝ) ≤ G * (((j : ℝ) + 1) / K) := by positivity
    calc G * (((j : ℝ) + 1) / K) * (1 / ((K : ℝ) * (x j * x (j + 1))))
        ≤ G * (((j : ℝ) + 1) / K) * (1 / (K * (m : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hle hj
      _ = G / ((K : ℝ) ^ 2 * (m : ℝ) ^ 2) * ((j : ℝ) + 1) := by
          field_simp
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← mul_sum, sum_range_succ_cast]
  field_simp

/-- Blocks `[X, M]` (integers), induction on `M`. -/
theorem eventually_primeSum_block_frac_le (h : ℝ → ℝ) (C G : ℝ) (hG : 0 ≤ G) (X : ℕ)
    (hX : 2 ≤ X) (K : ℕ) (hK : 0 < K)
    (hh : ∀ y, (X : ℝ) ≤ y → h y ≤ C + G * Int.fract y) :
    ∀ M : ℕ, X ≤ M → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      primeSum (fun p => h ((n : ℝ) / p)) ((n : ℝ) / M) ((n : ℝ) / X) ≤
        n * (C * (1 / X - 1 / M) +
          G * (((K : ℝ) + 1) / (2 * K)) * (1 / ((X : ℝ) - 1) - 1 / ((M : ℝ) - 1))) + ε * n := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    intro ε hε
    filter_upwards with n
    rw [primeSum_self]
    simp only [sub_self, mul_zero, add_zero, zero_add]
    exact mul_nonneg hε.le n.cast_nonneg
  | succ M hXM ih =>
    intro ε hε
    have hM1 : 1 ≤ M := by omega
    have hX' : (2 : ℝ) ≤ X := by exact_mod_cast hX
    have hXM' : (X : ℝ) ≤ M := by exact_mod_cast hXM
    have unit := eventually_primeSum_unit_frac_le h C G hG M hM1 K hK
      (fun y hy1 _ => hh y (hXM'.trans hy1)) (half_pos hε)
    filter_upwards [ih (ε / 2) (half_pos hε), unit] with n h1 h2
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hMpos : (0 : ℝ) < M := by linarith
    push_cast
    rw [← primeSum_add _ (div_nonneg hn0 (by linarith))
      (div_le_div_of_nonneg_left hn0 hMpos (by linarith))
      (div_le_div_of_nonneg_left hn0 (by linarith) hXM')]
    -- arithmetic: 1/M² ≤ 1/(M−1) − 1/M
    have hM2 : (2 : ℝ) ≤ M := hX'.trans hXM'
    have key : 1 / (M : ℝ) ^ 2 ≤ 1 / ((M : ℝ) - 1) - 1 / M := by
      have h1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
      rw [div_sub_div _ _ h1.ne' hMpos.ne', one_mul, mul_one, sub_sub_cancel]
      apply one_div_le_one_div_of_le (mul_pos h1 hMpos)
      nlinarith
    have hKf : (0 : ℝ) ≤ G * (((K : ℝ) + 1) / (2 * K)) := by positivity
    have key2 : G * (((K : ℝ) + 1) / (2 * K)) / (M : ℝ) ^ 2 ≤
        G * (((K : ℝ) + 1) / (2 * K)) * (1 / ((M : ℝ) - 1) - 1 / M) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left key hKf
    have e1 : (M : ℝ) + 1 - 1 = M := by ring
    rw [e1]
    have key3 := mul_le_mul_of_nonneg_left key2 hn0
    nlinarith

/-- **Tail** with `h ≤ C + G·{x}` on `[X, ∞)` (`X ≥ 2` an integer, `C, G ≥ 0`):
`∑_{p ≤ n/X} h(n/p) log p ≤ n (C/X + G/(2(X−1))) + ε n` for all large `n`.
(For Lemma 5: `C = 33`, the uniform bound of `Z7/CertA/Tail.lean`.) -/
theorem eventually_primeSum_tail_frac_le (h : ℝ → ℝ) (C G : ℝ) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (X : ℕ) (hX : 2 ≤ X) (hh : ∀ y, (X : ℝ) ≤ y → h y ≤ C + G * Int.fract y)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      primeSum (fun p => h ((n : ℝ) / p)) 0 ((n : ℝ) / X) ≤
        n * (C / X + G / (2 * ((X : ℝ) - 1))) + ε * n := by
  have hX' : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hX1 : (0 : ℝ) < (X : ℝ) - 1 := by linarith
  -- choice of K: G/(2K(X−1)) ≤ ε/4
  set K : ℕ := ⌈2 * G / (ε * ((X : ℝ) - 1))⌉₊ + 1 with hKdef
  have hK : 0 < K := Nat.succ_pos _
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hKbig : 2 * G / (ε * ((X : ℝ) - 1)) ≤ K := by
    have := Nat.le_ceil (2 * G / (ε * ((X : ℝ) - 1)))
    rw [hKdef]
    push_cast
    linarith
  have hKterm : G / (2 * K * ((X : ℝ) - 1)) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hKbig
    nlinarith
  -- choice of M: 3(C+G)/M ≤ ε/4
  set M : ℕ := X + ⌈12 * (C + G) / ε⌉₊ with hMdef
  have hXM : X ≤ M := Nat.le_add_right _ _
  have hM' : (X : ℝ) ≤ M := by exact_mod_cast hXM
  have hMpos : (0 : ℝ) < M := by linarith
  have hMbig : 12 * (C + G) / ε ≤ M := by
    have := Nat.le_ceil (12 * (C + G) / ε)
    rw [hMdef]
    push_cast
    linarith
  have hMterm : 3 * (C + G) / M ≤ ε / 4 := by
    rw [div_le_iff₀ hMpos]
    rw [div_le_iff₀ hε] at hMbig
    nlinarith
  have block := eventually_primeSum_block_frac_le h C G hG X hX K hK hh M hXM (ε / 4)
    (by positivity)
  filter_upwards [block] with n hblock
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  -- far tail p ≤ n/M
  have hfar : primeSum (fun p => h ((n : ℝ) / p)) 0 ((n : ℝ) / M) ≤ 3 * (C + G) / M * n := by
    have hd : (0 : ℝ) ≤ n / M := div_nonneg hn0 hMpos.le
    have h1 := primeSum_le_mul_theta (w := fun p => h ((n : ℝ) / p)) (B := C + G) le_rfl hd
      (by
        intro p hp _ hpd
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
        have hy : (M : ℝ) ≤ n / p := by
          rw [le_div_iff₀ hp0]
          rw [le_div_iff₀ hMpos] at hpd
          linarith [mul_comm (M : ℝ) p]
        calc h ((n : ℝ) / p) ≤ C + G * Int.fract ((n : ℝ) / p) := hh _ (hM'.trans hy)
          _ ≤ C + G * 1 := by gcongr; exact (Int.fract_lt_one _).le
          _ = C + G := by ring)
    rw [Chebyshev.theta_zero, sub_zero] at h1
    have h2 := Chebyshev.theta_le_log4_mul_x hd
    have hlog4 : Real.log 4 ≤ 3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    have hθ : θ ((n : ℝ) / M) ≤ 3 * ((n : ℝ) / M) :=
      h2.trans (mul_le_mul_of_nonneg_right hlog4 hd)
    have hCG : 0 ≤ C + G := add_nonneg hC hG
    calc primeSum (fun p => h ((n : ℝ) / p)) 0 ((n : ℝ) / M) ≤ (C + G) * θ ((n : ℝ) / M) := h1
      _ ≤ (C + G) * (3 * ((n : ℝ) / M)) := mul_le_mul_of_nonneg_left hθ hCG
      _ = 3 * (C + G) / M * n := by ring
  rw [← primeSum_add _ le_rfl (div_nonneg hn0 hMpos.le)
    (div_le_div_of_nonneg_left hn0 (by linarith) hM')]
  -- the block coefficient is at most C/X + G/(2(X−1)) + ε/4
  have hcoef : C * (1 / X - 1 / M) +
      G * (((K : ℝ) + 1) / (2 * K)) * (1 / ((X : ℝ) - 1) - 1 / ((M : ℝ) - 1)) ≤
      C / X + G / (2 * ((X : ℝ) - 1)) + ε / 4 := by
    have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
    have a1 : C * (1 / X - 1 / M) ≤ C / X := by
      have : 0 ≤ C * (1 / M) := by positivity
      rw [mul_sub]
      linarith [show C * (1 / (X : ℝ)) = C / X by ring]
    have hGK : 0 ≤ G * (((K : ℝ) + 1) / (2 * K)) := by positivity
    have a2 : G * (((K : ℝ) + 1) / (2 * K)) * (1 / ((X : ℝ) - 1) - 1 / ((M : ℝ) - 1)) ≤
        G * (((K : ℝ) + 1) / (2 * K)) * (1 / ((X : ℝ) - 1)) := by
      apply mul_le_mul_of_nonneg_left _ hGK
      have : 0 ≤ 1 / ((M : ℝ) - 1) := by positivity
      linarith
    have a3 : G * (((K : ℝ) + 1) / (2 * K)) * (1 / ((X : ℝ) - 1)) =
        G / (2 * ((X : ℝ) - 1)) + G / (2 * K * ((X : ℝ) - 1)) := by
      field_simp
    linarith
  have hcoef' := mul_le_mul_of_nonneg_left hcoef hn0
  nlinarith

/-! ### The combination used in Lemma 5 -/

/-- **Lemma 5, PNT step (packaged).** Step majorant `u` on the cells of `x 0 < … < x L = X` and the
tail majorant `C + G·{x}` on `[X, ∞)` give
`∑_{p ≤ n/x₀} h(n/p) log p ≤ n (∑_i u_i (1/x_i − 1/x_{i+1}) + C/X + G/(2(X−1))) + ε n`. -/
theorem eventually_primeSum_lemma5_le (h : ℝ → ℝ) (x u : ℕ → ℝ) (L : ℕ) (hx0 : 0 < x 0)
    (hx : ∀ i < L, x i < x (i + 1))
    (hh : ∀ i < L, ∀ y, x i < y → y < x (i + 1) → h y ≤ u i)
    (C G : ℝ) (hC : 0 ≤ C) (hG : 0 ≤ G) (X : ℕ) (hX : 2 ≤ X) (hxL : x L = X)
    (htail : ∀ y, (X : ℝ) ≤ y → h y ≤ C + G * Int.fract y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      primeSum (fun p => h ((n : ℝ) / p)) 0 ((n : ℝ) / x 0) ≤
        n * (∑ i ∈ range L, u i * (1 / x i - 1 / x (i + 1)) + C / X +
          G / (2 * ((X : ℝ) - 1))) + ε * n := by
  have hstep := eventually_primeSum_step_le h x u L hx0 hx hh (half_pos hε)
  have htl := eventually_primeSum_tail_frac_le h C G hC hG X hX htail (half_pos hε)
  filter_upwards [hstep, htl] with n h1 h2
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hxL0 : x 0 ≤ x L := le_of_chain hx L le_rfl
  rw [hxL] at h1 hxL0
  have hXpos : (0 : ℝ) < X := hx0.trans_le hxL0
  rw [← primeSum_add _ le_rfl (div_nonneg hn0 hXpos.le)
    (div_le_div_of_nonneg_left hn0 hx0 hxL0)]
  nlinarith

end ZetaIrr.PNT
