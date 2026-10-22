/-
# Verified enclosures of `log`, `arctan`, `π`, `Complex.arg` and `Complex.log`

* `log`: argument reduction `q = 2^k m` with `m ∈ [2/3, 4/3]`, then the series of `log (1 - x)`
  with Mathlib's explicit tail bound `Real.abs_log_sub_add_sum_range_le`; `log 2` by the same
  series at `x = 1/2`. On intervals: monotonicity, after outward rounding of the endpoints.
* `arctan`: the series `Real.hasSum_arctan` with a geometric tail bound, after reduction to
  `|x| ≤ 1/2` via `arctan x = π/4 + arctan ((x-1)/(x+1))` and `arctan x = π/2 - arctan (1/x)`.
  On intervals: monotonicity.
* `π`: Mathlib's `Real.pi_gt_d20`, `Real.pi_lt_d20`.
* `Complex.arg` on a box: `arctan (im / re)` if `re > 0`; `±π/2 - arctan (re / im)` if `im ≷ 0`
  (proved here from `Complex.tan_arg`-type identities). Boxes meeting the cut get `top`.
* `Complex.log` on a box: `(½ log normSq, arg)`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Interval.CBox
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ZetaIrr.Interval

open IV Finset

/-! ## `log` -/

/-- `Σ_{i<n} x^(i+1)/(i+1)`. -/
def lser (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => lser x n + x ^ (n + 1) / (n + 1)

lemma lser_cast (x : ℚ) (n : ℕ) :
    ((lser x n : ℚ) : ℝ) = ∑ i ∈ range n, (x : ℝ) ^ (i + 1) / (i + 1) := by
  induction n with
  | zero => simp [lser]
  | succ n ih => rw [lser, sum_range_succ, ← ih]; push_cast; ring

/-- Enclosure of `log (1 - x)` (for `|x| < 1`). -/
def logOneSub (x : ℚ) (n : ℕ) : IV :=
  if |x| < 1 then
    ival (-lser x n - |x| ^ (n + 1) / (1 - |x|)) (-lser x n + |x| ^ (n + 1) / (1 - |x|))
  else top

lemma mem_logOneSub (x : ℚ) (n : ℕ) : (logOneSub x n).mem (Real.log (1 - x)) := by
  unfold logOneSub
  split_ifs with hx
  · have hx' : |(x : ℝ)| < 1 := by exact_mod_cast hx
    have h := Real.abs_log_sub_add_sum_range_le hx' n
    rw [← lser_cast, abs_le] at h
    simp only [mem, Rat.cast_sub, Rat.cast_add, Rat.cast_neg, Rat.cast_div, Rat.cast_pow,
      Rat.cast_abs, Rat.cast_one]
    constructor <;> linarith [h.1, h.2]
  · trivial

/-- Series enclosure of `log 2`. -/
def log2S : IV := (logOneSub (1 / 2) 110).neg

lemma mem_log2S : log2S.mem (Real.log 2) := by
  have h := mem_neg (mem_logOneSub (1 / 2) 110)
  have : Real.log 2 = -Real.log (1 - ((1 / 2 : ℚ) : ℝ)) := by
    rw [show (1 : ℝ) - ((1 / 2 : ℚ) : ℝ) = (2 : ℝ)⁻¹ by push_cast; norm_num, Real.log_inv, neg_neg]
  rw [this]; exact h

/-- Dyadic enclosure of `log 2` (width `2^{-100}`), checked against the series. -/
def log2I : IV :=
  ival (878668439483319573618263538048 / 2 ^ 100) (878668439483319573618263538049 / 2 ^ 100)

lemma log2S_lo : log2S.loGe (878668439483319573618263538048 / 2 ^ 100) = true := by decide +kernel
lemma log2S_hi : log2S.hiLe (878668439483319573618263538049 / 2 ^ 100) = true := by decide +kernel

lemma mem_log2I : log2I.mem (Real.log 2) :=
  ⟨ge_of_loGe mem_log2S log2S_lo, le_of_hiLe mem_log2S log2S_hi⟩

/-- Exponent `k` with `q / 2^k ∈ [2/3, 4/3]` (for `q > 0`; any `k` is sound). -/
def kOf (q : ℚ) : ℤ :=
  let k0 : ℤ := (q.num.natAbs.log2 : ℤ) - (q.den.log2 : ℤ)
  if 4 / 3 < q / 2 ^ k0 then k0 + 1 else if q / 2 ^ k0 < 2 / 3 then k0 - 1 else k0

/-- Enclosure of `log q` at a rational point. -/
def logPt (n : ℕ) (q : ℚ) : IV :=
  if 0 < q then (log2I.smul (kOf q : ℚ)).add (logOneSub (1 - q / 2 ^ kOf q) n) else top

lemma mem_logPt (n : ℕ) (q : ℚ) : (logPt n q).mem (Real.log q) := by
  unfold logPt
  split_ifs with hq
  · set k := kOf q
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hsplit : Real.log q = (k : ℝ) * Real.log 2 + Real.log (1 - ((1 - q / 2 ^ k : ℚ) : ℝ)) := by
      have : (1 : ℝ) - ((1 - q / 2 ^ k : ℚ) : ℝ) = (q : ℝ) / 2 ^ k := by push_cast; ring
      rw [this, Real.log_div hq'.ne' h2.ne', Real.log_zpow]; ring
    rw [hsplit]
    have := mem_smul (k : ℚ) mem_log2I
    push_cast at this
    exact mem_add this (mem_logOneSub _ n)
  · trivial

/-- Narrow-interval `log`: only `log a` is evaluated; `log b ≤ log a + (b - a)/a`. -/
def logIVn (n : ℕ) (a b : ℚ) : IV :=
  match logPt n a with
  | ival l h => ival l (h + (b - a) / a)
  | top => top

lemma mem_logIVn (n : ℕ) {a b : ℚ} (ha : 0 < a) {x : ℝ} (hx : (ival a b).mem x) :
    (logIVn n a b).mem (Real.log x) := by
  obtain ⟨h1, h2⟩ := hx
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  unfold logIVn
  have hA := mem_logPt n a
  generalize logPt n a = A at hA ⊢
  cases A with
  | top => trivial
  | ival l u =>
    refine ⟨hA.1.trans (Real.log_le_log ha' h1), ?_⟩
    have hb : 0 < (b : ℝ) := ha'.trans_le (h1.trans h2)
    have hlb : Real.log b - Real.log a ≤ ((b : ℝ) - a) / a := by
      rw [← Real.log_div hb.ne' ha'.ne']
      have := Real.log_le_sub_one_of_pos (div_pos hb ha')
      rw [sub_div, div_self ha'.ne'] at *; exact this
    have := Real.log_le_log (ha'.trans_le h1) h2
    push_cast
    linarith [hA.2]

/-- Wide-interval `log`: both endpoints evaluated. -/
def logIVw (n : ℕ) (a b : ℚ) : IV :=
  match logPt n a, logPt n b with
  | ival l _, ival _ h => ival l h
  | _, _ => top

lemma mem_logIVw (n : ℕ) {a b : ℚ} (ha : 0 < a) {x : ℝ} (hx : (ival a b).mem x) :
    (logIVw n a b).mem (Real.log x) := by
  obtain ⟨h1, h2⟩ := hx
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  unfold logIVw
  have hA := mem_logPt n a
  have hB := mem_logPt n b
  generalize logPt n a = A at hA ⊢
  generalize logPt n b = B at hB ⊢
  cases A with
  | top => trivial
  | ival l l' =>
    cases B with
    | top => trivial
    | ival u u' =>
      exact ⟨hA.1.trans (Real.log_le_log ha' h1),
        (Real.log_le_log (ha'.trans_le h1) h2).trans hB.2⟩

/-- Enclosure of `log` on an interval whose endpoints are already the evaluation points. -/
def logIV' (n : ℕ) : IV → IV
  | top => top
  | ival a b =>
    if 0 < a then (if b - a ≤ a / 2 ^ 20 then logIVn n a b else logIVw n a b) else top

lemma mem_logIV' (n : ℕ) {I : IV} {x : ℝ} (hx : I.mem x) : (logIV' n I).mem (Real.log x) := by
  cases I with
  | top => trivial
  | ival a b =>
    simp only [logIV']
    split_ifs with ha hw
    · exact mem_logIVn n ha hx
    · exact mem_logIVw n ha hx
    · trivial

/-- Enclosure of `log` on an interval (endpoints rounded outward to `2^{-p}` first). -/
def logIV (p n : ℕ) (I : IV) : IV := logIV' n (I.round p)

lemma mem_logIV (p n : ℕ) {I : IV} {x : ℝ} (hx : I.mem x) : (logIV p n I).mem (Real.log x) :=
  mem_logIV' n (mem_round p hx)

/-! ## `π` -/

def piI : IV := ival (314159265358979323846 / 10 ^ 20) (314159265358979323847 / 10 ^ 20)

lemma mem_piI : piI.mem Real.pi := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor
  · push_cast; norm_num at h1 ⊢; linarith
  · push_cast; norm_num at h2 ⊢; linarith

/-! ## `arctan` -/

/-- `Σ_{k<n} (-1)^k x^(2k+1)/(2k+1)`. -/
def aser (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => aser x n + (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1)

lemma aser_cast (x : ℚ) (n : ℕ) :
    ((aser x n : ℚ) : ℝ) = ∑ k ∈ range n, (-1 : ℝ) ^ k * (x : ℝ) ^ (2 * k + 1) / ↑(2 * k + 1) := by
  induction n with
  | zero => simp [aser]
  | succ n ih => rw [aser, sum_range_succ, ← ih]; push_cast; ring

/-- Tail bound for the arctan series. -/
lemma abs_arctan_sub_partial_le {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    |Real.arctan x - ∑ k ∈ range n, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ↑(2 * k + 1)|
      ≤ |x| ^ (2 * n + 1) * (1 - x ^ 2)⁻¹ := by
  have h := Real.hasSum_arctan (x := x) (by simpa [Real.norm_eq_abs] using hx)
  have ht := (hasSum_nat_add_iff' n).2 h
  have hx2 : x ^ 2 < 1 := by
    have := sq_abs x; nlinarith [abs_nonneg x]
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg x) hx2).mul_left (|x| ^ (2 * n + 1))
  have := ht.norm_le_of_bounded hg (fun k => by
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow]
    have hk : (1 : ℝ) ≤ |((2 * (k + n) + 1 : ℕ) : ℝ)| := by
      rw [Nat.abs_cast]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    calc |x| ^ (2 * (k + n) + 1) / |((2 * (k + n) + 1 : ℕ) : ℝ)| ≤ |x| ^ (2 * (k + n) + 1) :=
          div_le_self (by positivity) hk
      _ = |x| ^ (2 * n + 1) * (x ^ 2) ^ k := by
          rw [← sq_abs x, ← pow_mul, ← pow_add]; ring_nf)
  simpa [Real.norm_eq_abs] using this

/-- Enclosure of `arctan x` by the series directly (for `x² < 1`). -/
def atanSmall (n : ℕ) (x : ℚ) : IV :=
  if x ^ 2 < 1 then
    ival (aser x n - |x| ^ (2 * n + 1) / (1 - x ^ 2)) (aser x n + |x| ^ (2 * n + 1) / (1 - x ^ 2))
  else top

lemma mem_atanSmall (n : ℕ) (x : ℚ) : (atanSmall n x).mem (Real.arctan x) := by
  unfold atanSmall
  split_ifs with hx
  · have hx2 : (x : ℝ) ^ 2 < 1 := by exact_mod_cast hx
    have hx' : |(x : ℝ)| < 1 := by
      rw [← sq_lt_one_iff_abs_lt_one]; exact hx2
    have h := abs_arctan_sub_partial_le hx' n
    rw [← aser_cast, abs_le] at h
    simp only [mem, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_abs,
      Rat.cast_one]
    rw [div_eq_mul_inv]
    constructor <;> linarith [h.1, h.2]
  · trivial

lemma arctan_eq_quarter_add {x : ℝ} (hx : 0 < x) :
    Real.arctan x = Real.pi / 4 + Real.arctan ((x - 1) / (x + 1)) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hy : 1 * ((x - 1) / (x + 1)) < 1 := by
    rw [one_mul, div_lt_one hx1]; linarith
  rw [← Real.arctan_one, Real.arctan_add hy]
  congr 1
  field_simp
  ring

lemma arctan_eq_half_sub {x : ℝ} (hx : 0 < x) :
    Real.arctan x = Real.pi / 2 - Real.arctan (1 / x) := by
  rw [one_div, Real.arctan_inv_of_pos hx]; ring

/-- `arctan x` for `x > 0`, by reduction. -/
def atanPos (n : ℕ) (x : ℚ) : IV :=
  if x ≤ 2 then (piI.smul (1 / 4)).add (atanSmall n ((x - 1) / (x + 1)))
  else (piI.smul (1 / 2)).sub (atanSmall n (1 / x))

lemma mem_atanPos (n : ℕ) {x : ℚ} (hx : 0 < x) : (atanPos n x).mem (Real.arctan x) := by
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hpi4 := mem_smul (1 / 4) mem_piI
  have hpi2 := mem_smul (1 / 2) mem_piI
  unfold atanPos
  split_ifs with h2
  · rw [arctan_eq_quarter_add hx']
    have := mem_add hpi4 (mem_atanSmall n ((x - 1) / (x + 1)))
    push_cast at this ⊢
    convert this using 1; ring
  · rw [arctan_eq_half_sub hx']
    have := mem_sub hpi2 (mem_atanSmall n (1 / x))
    push_cast at this ⊢
    convert this using 1; ring

/-- Enclosure of `arctan x` at a rational point. -/
def atanPt (n : ℕ) (x : ℚ) : IV :=
  if x ^ 2 ≤ 1 / 4 then atanSmall n x
  else if 0 < x then atanPos n x else (atanPos n (-x)).neg

lemma mem_atanPt (n : ℕ) (x : ℚ) : (atanPt n x).mem (Real.arctan x) := by
  unfold atanPt
  split_ifs with h1 h2
  · exact mem_atanSmall n x
  · exact mem_atanPos n h2
  · have hx : 0 < -x := by
      rcases lt_trichotomy x 0 with h | h | h
      · linarith
      · subst h; norm_num at h1
      · exact absurd h h2
    have := mem_neg (mem_atanPos n hx)
    push_cast at this
    rwa [Real.arctan_neg, neg_neg] at this

/-- `arctan` is `1`-Lipschitz. -/
lemma arctan_sub_le {x y : ℝ} (h : x ≤ y) : Real.arctan y - Real.arctan x ≤ y - x := by
  have := image_sub_le_mul_sub_of_deriv_le Real.differentiable_arctan (C := 1)
    (fun t => by
      rw [Real.deriv_arctan]
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg t]) h
  linarith

/-- Enclosure of `arctan` on an interval with given endpoints (one evaluation if narrow). -/
def atanIV' (n : ℕ) : IV → IV
  | top => top
  | ival a b =>
    if b - a ≤ 1 / 2 ^ 20 then
      match atanPt n a with
      | ival l h => ival l (h + (b - a))
      | top => top
    else
      match atanPt n a, atanPt n b with
      | ival l _, ival _ h => ival l h
      | _, _ => top

lemma mem_atanIV' (n : ℕ) {I : IV} {x : ℝ} (hx : I.mem x) : (atanIV' n I).mem (Real.arctan x) := by
  cases I with
  | top => trivial
  | ival a b =>
    obtain ⟨h1, h2⟩ := hx
    simp only [atanIV']
    have hA := mem_atanPt n a
    have hB := mem_atanPt n b
    split_ifs
    · generalize atanPt n a = A at hA ⊢
      cases A with
      | top => trivial
      | ival l u =>
        refine ⟨hA.1.trans (Real.arctan_mono h1), ?_⟩
        have hlip := arctan_sub_le (h1.trans h2)
        have := Real.arctan_mono h2
        push_cast
        linarith [hA.2]
    · generalize atanPt n a = A at hA ⊢
      generalize atanPt n b = B at hB ⊢
      cases A with
      | top => trivial
      | ival l l' =>
        cases B with
        | top => trivial
        | ival u u' =>
          exact ⟨hA.1.trans (Real.arctan_mono h1), (Real.arctan_mono h2).trans hB.2⟩

/-- Enclosure of `arctan` on an interval (endpoints rounded outward to `2^{-p}` first). -/
def atanIV (p n : ℕ) (I : IV) : IV := atanIV' n (I.round p)

lemma mem_atanIV (p n : ℕ) {I : IV} {x : ℝ} (hx : I.mem x) :
    (atanIV p n I).mem (Real.arctan x) :=
  mem_atanIV' n (mem_round p hx)

/-! ## `Complex.arg` -/

lemma arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.arg z = Real.arctan (z.im / z.re) := by
  have h1 : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  rw [abs_lt] at h1
  rw [← Complex.tan_arg, Real.arctan_tan h1.1 h1.2]

lemma arg_eq_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.arg z = Real.pi / 2 - Real.arctan (z.re / z.im) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hsin : 0 < Real.sin (Complex.arg z) := by rw [Complex.sin_arg]; positivity
  have ha0 : 0 < Complex.arg z := by
    rcases (Complex.arg_nonneg_iff.2 hz.le).lt_or_eq with h | h
    · exact h
    · rw [← h, Real.sin_zero] at hsin; exact absurd hsin (lt_irrefl 0)
  have haπ : Complex.arg z < Real.pi := by
    rcases (Complex.arg_le_pi z).lt_or_eq with h | h
    · exact h
    · rw [h, Real.sin_pi] at hsin; exact absurd hsin (lt_irrefl 0)
  have htan : Real.tan (Complex.arg z - Real.pi / 2) = -(z.re / z.im) := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two,
      Complex.cos_arg hz0, Complex.sin_arg]
    field_simp
  have := Real.arctan_tan (x := Complex.arg z - Real.pi / 2) (by linarith) (by linarith)
  rw [htan, Real.arctan_neg] at this
  linarith

lemma arg_eq_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.arg z = -(Real.pi / 2) - Real.arctan (z.re / z.im) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have ha0 : Complex.arg z < 0 := Complex.arg_neg_iff.2 hz
  have haπ : -Real.pi < Complex.arg z := Complex.neg_pi_lt_arg z
  have hsin : Real.sin (Complex.arg z) ≠ 0 := by
    rw [Complex.sin_arg]
    exact div_ne_zero hz.ne (norm_ne_zero_iff.2 hz0)
  have htan : Real.tan (Complex.arg z + Real.pi / 2) = -(z.re / z.im) := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
      Complex.cos_arg hz0, Complex.sin_arg]
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz0
    field_simp
  have := Real.arctan_tan (x := Complex.arg z + Real.pi / 2) (by linarith) (by linarith)
  rw [htan, Real.arctan_neg] at this
  linarith

/-- Enclosure of `arg` on a box not meeting the closed negative real axis. -/
def argCB (p n : ℕ) (B : CB) : IV :=
  if B.re.loGt 0 then atanIV p n (B.im.div B.re)
  else if B.im.loGt 0 then (piI.smul (1 / 2)).sub (atanIV p n (B.re.div B.im))
  else if B.im.hiLt 0 then (piI.smul (-1 / 2)).sub (atanIV p n (B.re.div B.im))
  else top

lemma mem_argCB (p n : ℕ) {B : CB} {z : ℂ} (hz : B.mem z) : (argCB p n B).mem (Complex.arg z) := by
  unfold argCB
  split_ifs with h1 h2 h3
  · rw [arg_eq_arctan_of_re_pos (by exact_mod_cast gt_of_loGt hz.1 h1)]
    exact mem_atanIV p n (mem_div hz.2 hz.1)
  · rw [arg_eq_of_im_pos (by exact_mod_cast gt_of_loGt hz.2 h2)]
    have := mem_sub (mem_smul (1 / 2) mem_piI) (mem_atanIV p n (mem_div hz.1 hz.2))
    push_cast at this; convert this using 1; ring
  · rw [arg_eq_of_im_neg (by exact_mod_cast lt_of_hiLt hz.2 h3)]
    have := mem_sub (mem_smul (-1 / 2) mem_piI) (mem_atanIV p n (mem_div hz.1 hz.2))
    push_cast at this; convert this using 1; ring
  · trivial

/-! ## `Complex.log` -/

/-- Enclosure of the principal `Complex.log` on a box. -/
def clogCB (p n : ℕ) (B : CB) : CB :=
  ⟨((logIV p n (CB.normSq B)).smul (1 / 2)).round p, (argCB p n B).round p⟩

lemma mem_clogCB (p n : ℕ) {B : CB} {z : ℂ} (hz : B.mem z) :
    (clogCB p n B).mem (Complex.log z) := by
  refine ⟨?_, ?_⟩
  · change (((logIV p n (CB.normSq B)).smul (1 / 2)).round p).mem (Complex.log z).re
    refine mem_round p ?_
    rw [Complex.log_re, Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg z)]
    have := mem_smul (1 / 2) (mem_logIV p n (CB.mem_normSq hz))
    push_cast at this; convert this using 1; ring
  · change ((argCB p n B).round p).mem (Complex.log z).im
    rw [Complex.log_im]; exact mem_round p (mem_argCB p n hz)

end ZetaIrr.Interval
