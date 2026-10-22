/-
# Verified rational interval arithmetic

An interval is either `IV.top` (no information: every real is a member) or `IV.ival lo hi` with
rational endpoints, meaning `{x : ℝ | lo ≤ x ≤ hi}`. Operations never fail: when an operation
cannot produce a finite enclosure (e.g. `inv` of an interval containing `0`), it returns `top`.
This makes every correctness theorem unconditional:

    I.mem x → J.mem y → (I.op J).mem (x op y).

Endpoints are exact rationals; `IV.round p` rounds outward to the grid `2^{-p} ℤ` to control
their size. Final certified inequalities are read off with the Boolean checks `hiLe`, `loGe`, …,
whose soundness lemmas turn `check = true` (proved by `decide`) into real inequalities.

Status: complete (no `sorry`).
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ZetaIrr.Interval

/-- A rational interval, or `top` (the whole real line). -/
inductive IV where
  | top : IV
  | ival (lo hi : ℚ) : IV
  deriving DecidableEq, Repr

namespace IV

/-- Membership of a real number. -/
def mem : IV → ℝ → Prop
  | top, _ => True
  | ival a b, x => (a : ℝ) ≤ x ∧ x ≤ (b : ℝ)

@[simp] lemma mem_top (x : ℝ) : top.mem x := trivial

lemma mem_ival {a b : ℚ} {x : ℝ} : (ival a b).mem x ↔ (a : ℝ) ≤ x ∧ x ≤ (b : ℝ) := Iff.rfl

/-! ## Constructors and operations -/

def ofRat (q : ℚ) : IV := ival q q

def neg : IV → IV
  | top => top
  | ival a b => ival (-b) (-a)

def add : IV → IV → IV
  | ival a b, ival c d => ival (a + c) (b + d)
  | _, _ => top

def sub (I J : IV) : IV := add I (neg J)

/-- Product: min / max of the four corner products. -/
def mul : IV → IV → IV
  | ival a b, ival c d =>
      ival (min (min (a * c) (a * d)) (min (b * c) (b * d)))
           (max (max (a * c) (a * d)) (max (b * c) (b * d)))
  | _, _ => top

/-- Multiplication by a rational constant. -/
def smul (q : ℚ) : IV → IV
  | top => top
  | ival a b => if 0 ≤ q then ival (q * a) (q * b) else ival (q * b) (q * a)

/-- Reciprocal; `top` unless the interval excludes `0`. -/
def inv : IV → IV
  | top => top
  | ival a b => if 0 < a ∨ b < 0 then ival (1 / b) (1 / a) else top

def div (I J : IV) : IV := mul I (inv J)

/-- Square (tighter than `mul I I`). -/
def sq : IV → IV
  | top => top
  | ival a b =>
      if 0 ≤ a then ival (a * a) (b * b)
      else if b ≤ 0 then ival (b * b) (a * a)
      else ival 0 (max (a * a) (b * b))

/-- Union hull. -/
def join : IV → IV → IV
  | ival a b, ival c d => ival (min a c) (max b d)
  | _, _ => top

/-- Widen by a rational radius `e ≥ 0` (only used with `e ≥ 0`; for `e < 0` it may shrink). -/
def widen (e : ℚ) : IV → IV
  | top => top
  | ival a b => ival (a - e) (b + e)

/-- Outward rounding to the grid `2^{-p} ℤ`. -/
def round (p : ℕ) : IV → IV
  | top => top
  | ival a b => ival ((⌊a * 2 ^ p⌋ : ℚ) / 2 ^ p) ((⌈b * 2 ^ p⌉ : ℚ) / 2 ^ p)

/-! ## Boolean checks -/

/-- `I ≤ q` everywhere. -/
def hiLe (I : IV) (q : ℚ) : Bool :=
  match I with
  | top => false
  | ival _ b => decide (b ≤ q)

def hiLt (I : IV) (q : ℚ) : Bool :=
  match I with
  | top => false
  | ival _ b => decide (b < q)

def loGe (I : IV) (q : ℚ) : Bool :=
  match I with
  | top => false
  | ival a _ => decide (q ≤ a)

def loGt (I : IV) (q : ℚ) : Bool :=
  match I with
  | top => false
  | ival a _ => decide (q < a)

/-- The upper endpoint (or `0` for `top`; only meaningful together with a `hiLe`-type check). -/
def hiOr0 : IV → ℚ
  | top => 0
  | ival _ b => b

def loOr0 : IV → ℚ
  | top => 0
  | ival a _ => a

/-- `|x| ≤ q` on the interval. -/
def absLe (I : IV) (q : ℚ) : Bool :=
  match I with
  | top => false
  | ival a b => decide (-q ≤ a ∧ b ≤ q)

/-! ## Soundness of the checks -/

lemma le_of_hiLe {I : IV} {x : ℝ} {q : ℚ} (hx : I.mem x) (h : I.hiLe q = true) : x ≤ q := by
  cases I with
  | top => simp [hiLe] at h
  | ival a b =>
    simp only [hiLe, decide_eq_true_eq] at h
    exact hx.2.trans (by exact_mod_cast h)

lemma lt_of_hiLt {I : IV} {x : ℝ} {q : ℚ} (hx : I.mem x) (h : I.hiLt q = true) : x < q := by
  cases I with
  | top => simp [hiLt] at h
  | ival a b =>
    simp only [hiLt, decide_eq_true_eq] at h
    exact hx.2.trans_lt (by exact_mod_cast h)

lemma ge_of_loGe {I : IV} {x : ℝ} {q : ℚ} (hx : I.mem x) (h : I.loGe q = true) : (q : ℝ) ≤ x := by
  cases I with
  | top => simp [loGe] at h
  | ival a b =>
    simp only [loGe, decide_eq_true_eq] at h
    exact (by exact_mod_cast h : (q : ℝ) ≤ a).trans hx.1

lemma gt_of_loGt {I : IV} {x : ℝ} {q : ℚ} (hx : I.mem x) (h : I.loGt q = true) : (q : ℝ) < x := by
  cases I with
  | top => simp [loGt] at h
  | ival a b =>
    simp only [loGt, decide_eq_true_eq] at h
    exact (by exact_mod_cast h : (q : ℝ) < a).trans_le hx.1

lemma abs_le_of_absLe {I : IV} {x : ℝ} {q : ℚ} (hx : I.mem x) (h : I.absLe q = true) :
    |x| ≤ q := by
  cases I with
  | top => simp [absLe] at h
  | ival a b =>
    simp only [absLe, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : ((-q : ℚ) : ℝ) ≤ a := by exact_mod_cast h1
    have h2' : (b : ℝ) ≤ q := by exact_mod_cast h2
    push_cast at h1'
    rw [abs_le]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma mem_ival_of_hiLe {I : IV} {x : ℝ} (hx : I.mem x) (h : I.hiLe I.hiOr0 = true) :
    x ≤ (I.hiOr0 : ℝ) := le_of_hiLe hx h

/-! ## Soundness of the operations -/

lemma mem_ofRat (q : ℚ) : (ofRat q).mem (q : ℝ) := ⟨le_rfl, le_rfl⟩

lemma mem_neg {I : IV} {x : ℝ} (hx : I.mem x) : I.neg.mem (-x) := by
  cases I with
  | top => trivial
  | ival a b =>
    obtain ⟨h1, h2⟩ := hx
    simp only [neg, mem, Rat.cast_neg]
    constructor <;> linarith

lemma mem_add {I J : IV} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) : (I.add J).mem (x + y) := by
  cases I with
  | top => cases J <;> trivial
  | ival a b =>
    cases J with
    | top => trivial
    | ival c d =>
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      simp only [add, mem, Rat.cast_add]
      constructor <;> linarith

lemma mem_sub {I J : IV} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) : (I.sub J).mem (x - y) := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

/-- One-variable corner lemma: `x ↦ x y` is monotone or antitone. -/
lemma mul_between {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · have : a * y ≤ x * y := mul_le_mul_of_nonneg_right h1 hy
    have : x * y ≤ b * y := mul_le_mul_of_nonneg_right h2 hy
    exact ⟨(min_le_left _ _).trans (by linarith), by linarith [le_max_right (a * y) (b * y)]⟩
  · have : x * y ≤ a * y := mul_le_mul_of_nonpos_right h1 hy
    have : b * y ≤ x * y := mul_le_mul_of_nonpos_right h2 hy
    exact ⟨(min_le_right _ _).trans (by linarith), by linarith [le_max_left (a * y) (b * y)]⟩

lemma mem_mul {I J : IV} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) : (I.mul J).mem (x * y) := by
  cases I with
  | top => cases J <;> trivial
  | ival a b =>
    cases J with
    | top => trivial
    | ival c d =>
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      simp only [mul, mem, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
      obtain ⟨hl, hu⟩ := mul_between (y := y) h1 h2
      -- a*y between a*c, a*d ; b*y between b*c, b*d
      obtain ⟨ha1, ha2⟩ := mul_between (y := (a : ℝ)) h3 h4
      obtain ⟨hb1, hb2⟩ := mul_between (y := (b : ℝ)) h3 h4
      rw [mul_comm (c : ℝ) a, mul_comm (d : ℝ) a, mul_comm y a] at ha1 ha2
      rw [mul_comm (c : ℝ) b, mul_comm (d : ℝ) b, mul_comm y b] at hb1 hb2
      constructor
      · refine le_trans ?_ hl
        refine le_min ?_ ?_
        · exact (min_le_left _ _).trans ha1
        · exact (min_le_right _ _).trans hb1
      · refine hu.trans ?_
        refine max_le ?_ ?_
        · exact ha2.trans (le_max_left _ _)
        · exact hb2.trans (le_max_right _ _)

lemma mem_smul (q : ℚ) {I : IV} {x : ℝ} (hx : I.mem x) : (I.smul q).mem ((q : ℝ) * x) := by
  cases I with
  | top => trivial
  | ival a b =>
    obtain ⟨h1, h2⟩ := hx
    simp only [smul]
    split_ifs with hq
    · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
      simp only [mem, Rat.cast_mul]
      exact ⟨mul_le_mul_of_nonneg_left h1 hq', mul_le_mul_of_nonneg_left h2 hq'⟩
    · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.1 hq))
      simp only [mem, Rat.cast_mul]
      exact ⟨mul_le_mul_of_nonpos_left h2 hq', mul_le_mul_of_nonpos_left h1 hq'⟩

lemma mem_inv {I : IV} {x : ℝ} (hx : I.mem x) : I.inv.mem x⁻¹ := by
  cases I with
  | top => trivial
  | ival a b =>
    obtain ⟨h1, h2⟩ := hx
    simp only [inv]
    split_ifs with h
    · simp only [mem, one_div, Rat.cast_inv]
      rcases h with h | h
      · have ha : (0 : ℝ) < a := by exact_mod_cast h
        have hx0 : 0 < x := ha.trans_le h1
        exact ⟨inv_anti₀ hx0 h2, inv_anti₀ ha h1⟩
      · have hb : (b : ℝ) < 0 := by exact_mod_cast h
        have hx0 : x < 0 := h2.trans_lt hb
        exact ⟨(inv_le_inv_of_neg hb hx0).2 h2, (inv_le_inv_of_neg hx0 (h1.trans_lt hx0)).2 h1⟩
    · trivial

lemma mem_div {I J : IV} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) : (I.div J).mem (x / y) := by
  rw [div_eq_mul_inv]; exact mem_mul hx (mem_inv hy)

lemma mem_sq {I : IV} {x : ℝ} (hx : I.mem x) : I.sq.mem (x ^ 2) := by
  cases I with
  | top => trivial
  | ival a b =>
    obtain ⟨h1, h2⟩ := hx
    simp only [sq]
    split_ifs with ha hb
    · have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
      simp only [mem, Rat.cast_mul]
      constructor <;> nlinarith
    · have hb' : (b : ℝ) ≤ 0 := by exact_mod_cast hb
      simp only [mem, Rat.cast_mul]
      constructor <;> nlinarith
    · simp only [mem, Rat.cast_max, Rat.cast_mul, Rat.cast_zero]
      refine ⟨sq_nonneg x, ?_⟩
      have ha' : (a : ℝ) < 0 := by exact_mod_cast (not_le.1 ha)
      have hb' : (0 : ℝ) < b := by exact_mod_cast (not_le.1 hb)
      rcases le_total 0 x with hx0 | hx0
      · exact le_trans (by nlinarith) (le_max_right _ _)
      · exact le_trans (by nlinarith) (le_max_left _ _)

lemma mem_join_left {I J : IV} {x : ℝ} (hx : I.mem x) : (I.join J).mem x := by
  cases I with
  | top => cases J <;> trivial
  | ival a b =>
    cases J with
    | top => trivial
    | ival c d =>
      obtain ⟨h1, h2⟩ := hx
      simp only [join, mem, Rat.cast_min, Rat.cast_max]
      exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩

lemma mem_join_right {I J : IV} {x : ℝ} (hx : J.mem x) : (I.join J).mem x := by
  cases I with
  | top => cases J <;> trivial
  | ival a b =>
    cases J with
    | top => trivial
    | ival c d =>
      obtain ⟨h1, h2⟩ := hx
      simp only [join, mem, Rat.cast_min, Rat.cast_max]
      exact ⟨(min_le_right _ _).trans h1, h2.trans (le_max_right _ _)⟩

/-- Widening by `e`: if `|x - y| ≤ e` and `y ∈ I` then `x ∈ widen e I`. -/
lemma mem_widen {I : IV} {x y : ℝ} {e : ℚ} (hy : I.mem y) (hxy : |x - y| ≤ e) :
    (I.widen e).mem x := by
  cases I with
  | top => trivial
  | ival a b =>
    obtain ⟨h1, h2⟩ := hy
    rw [abs_le] at hxy
    simp only [widen, mem, Rat.cast_sub, Rat.cast_add]
    constructor <;> linarith [hxy.1, hxy.2]

lemma mem_round (p : ℕ) {I : IV} {x : ℝ} (hx : I.mem x) : (I.round p).mem x := by
  cases I with
  | top => trivial
  | ival a b =>
    obtain ⟨h1, h2⟩ := hx
    simp only [round, mem]
    have hp : (0 : ℚ) < 2 ^ p := by positivity
    constructor
    · have : (⌊a * 2 ^ p⌋ : ℚ) / 2 ^ p ≤ a := by
        rw [div_le_iff₀ hp]; exact Int.floor_le _
      exact (by exact_mod_cast this : (((⌊a * 2 ^ p⌋ : ℚ) / 2 ^ p : ℚ) : ℝ) ≤ a).trans h1
    · have : b ≤ (⌈b * 2 ^ p⌉ : ℚ) / 2 ^ p := by
        rw [le_div_iff₀ hp]; exact Int.le_ceil _
      exact h2.trans (by exact_mod_cast this)

/-- Monotone image: if `F` is monotone on the real line and `F a ∈ Ia`, `F b ∈ Ib`, then for
`x ∈ [a, b]`, `F x ∈ ival (lo Ia) (hi Ib)`. Used for `log`, `arctan`. -/
lemma mem_of_monotoneOn {F : ℝ → ℝ} {S : Set ℝ} (hF : MonotoneOn F S) {a b : ℚ} {x : ℝ}
    (ha : (a : ℝ) ∈ S) (hb : (b : ℝ) ∈ S) (hxS : x ∈ S) (hx : (ival a b).mem x)
    {lo hi : ℚ} (hlo : (lo : ℝ) ≤ F a) (hhi : F b ≤ hi) : (ival lo hi).mem (F x) :=
  ⟨hlo.trans (hF ha hxS hx.1), (hF hxS hb hx.2).trans hhi⟩

end IV

end ZetaIrr.Interval
