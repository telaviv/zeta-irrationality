/-
# Chunked polyline checks and a cheap sector check (generic over the factor list)

Machinery for splitting the kernel-checked contour certificates of `Interval/Polyline.lean` into
small `decide +kernel` pieces, so that they can live in separate files and build in parallel:

* `lastPt a pts` — the last vertex of the polyline `a, pts₀, pts₁, …`;
* `polyChk_append`: `polyChk a (l₁ ++ l₂) = polyChk a l₁ && polyChk (lastPt a l₁) l₂`;
* `sectorQ` / `sector_of_sectorQ`: the sector condition of (S4) (`|α_i| ≥ a`, `|arg α_i| ≤ A`) on a
  box, as `sectorB` but skipping the (expensive) arctan whenever `Re α_i ≥ 0` on the box, since then
  `|arg α_i| ≤ π/2 < 63/40 ≤ A` (requires `A ≥ 63/40`);
* `polySectorQ` / `poly_sectorQ` / `polySectorQ_append`: the same along a polyline, plus
  `Re z > -1/2` (the e-factor), as `polySector`.

Used by the I3 saddle certificate (PROOF_BETA §6.3, (S2), (S4)); nothing here is I3-specific.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Interval.Polyline

namespace ZetaIrr.Fam.Interval

open Complex Metric Real ZetaIrr.Interval ZetaIrr.Interval.IV

/-! ## Polyline chunks -/

/-- The last vertex of the polyline `a, pts₀, pts₁, …`. -/
def lastPt (a : ℚ × ℚ) : List (ℚ × ℚ) → ℚ × ℚ
  | [] => a
  | b :: rest => lastPt b rest

lemma polyChk_append (p n : ℕ) (l : List Fac) (T : ℚ) (a : ℚ × ℚ) (l₁ l₂ : List (ℚ × ℚ)) :
    polyChk p n l T a (l₁ ++ l₂) = (polyChk p n l T a l₁ && polyChk p n l T (lastPt a l₁) l₂) := by
  induction l₁ generalizing a with
  | nil => simp [polyChk, lastPt]
  | cons b rest ih => simp [polyChk, lastPt, ih, Bool.and_assoc]

lemma onPoly_append {a : ℚ × ℚ} {l₁ l₂ : List (ℚ × ℚ)} {z : ℂ} (h : onPoly a (l₁ ++ l₂) z) :
    onPoly a l₁ z ∨ onPoly (lastPt a l₁) l₂ z := by
  induction l₁ generalizing a with
  | nil => right; simpa [lastPt] using h
  | cons b rest ih =>
    rcases h with h | h
    · left; left; exact h
    · rcases ih h with h' | h'
      · left; right; exact h'
      · right; simpa [lastPt] using h'

/-! ## The cheap sector check -/

/-- Sector check for one factor: `|α| ≥ amin`, and either `Re α ≥ 0` (then `|arg α| ≤ π/2`, and
`π/2 < 63/40 ≤ A`) or the interval `arg α` is within `[-A, A]`. -/
def facSecOK (p n : ℕ) (amin A : ℚ) (f : Fac) (B : CB) : Bool :=
  (f.αB B).normGe amin &&
    (((f.αB B).re.loGe 0 && decide (63 / 40 ≤ A)) || (argCB p n (f.αB B)).absLe A)

/-- `facSecOK` for every factor of the list. -/
def sectorQ (p n : ℕ) (amin A : ℚ) : List Fac → CB → Bool
  | [], _ => true
  | f :: l, B => facSecOK p n amin A f B && sectorQ p n amin A l B

lemma abs_arg_le_of_re_nonneg {z : ℂ} {A : ℚ} (hz : 0 ≤ z.re) (hA : (63 / 40 : ℚ) ≤ A) :
    |arg z| ≤ A := by
  have h1 := Complex.abs_arg_le_pi_div_two_iff.2 hz
  have h2 := Real.pi_lt_d2
  have h3 : ((63 / 40 : ℚ) : ℝ) ≤ A := by exact_mod_cast hA
  push_cast at h3
  linarith

theorem facSecOK_sound (p n : ℕ) (amin A : ℚ) {f : Fac} {B : CB} {z : ℂ} (hz : B.mem z)
    (h : facSecOK p n amin A f B = true) : (amin : ℝ) ≤ ‖f.α z‖ ∧ |arg (f.α z)| ≤ A := by
  simp only [facSecOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hα := f.mem_αB hz
  refine ⟨CB.le_norm_of_normGe hα h1, ?_⟩
  rcases h2 with ⟨h3, h4⟩ | h3
  · have := ge_of_loGe hα.1 h3
    push_cast at this
    exact abs_arg_le_of_re_nonneg this h4
  · exact abs_le_of_absLe (mem_argCB p n hα) h3

theorem sector_of_sectorQ (p n : ℕ) (amin A : ℚ) {l : List Fac} {B : CB} {z : ℂ} (hz : B.mem z)
    (h : sectorQ p n amin A l B = true) :
    ∀ f ∈ l, (amin : ℝ) ≤ ‖f.α z‖ ∧ |arg (f.α z)| ≤ A := by
  induction l with
  | nil => intro f hf; simp at hf
  | cons f0 l ih =>
    simp only [sectorQ, Bool.and_eq_true] at h
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · exact facSecOK_sound p n amin A hz h.1
    · exact ih h.2 f hf

/-- Sector check (`sectorQ`) on every segment box of a polyline, plus `Re(2z+1) > 0`. -/
def polySectorQ (p n : ℕ) (amin A : ℚ) (l : List Fac) : (ℚ × ℚ) → List (ℚ × ℚ) → Bool
  | _, [] => true
  | a, b :: rest => sectorQ p n amin A l (segBox a b) && (segBox a b).re.loGt (-1 / 2)
      && polySectorQ p n amin A l b rest

theorem poly_sectorQ (p n : ℕ) (amin A : ℚ) (l : List Fac) (a : ℚ × ℚ) (pts : List (ℚ × ℚ))
    (h : polySectorQ p n amin A l a pts = true) :
    ∀ z, onPoly a pts z → (∀ f ∈ l, (amin : ℝ) ≤ ‖f.α z‖ ∧ |arg (f.α z)| ≤ A) ∧ -1 / 2 < z.re := by
  induction pts generalizing a with
  | nil => intro z hz; exact hz.elim
  | cons b rest ih =>
    simp only [polySectorQ, Bool.and_eq_true] at h
    intro z hz
    rcases hz with hz | hz
    · have hb := mem_segBox hz
      refine ⟨sector_of_sectorQ p n amin A hb h.1.1, ?_⟩
      have := gt_of_loGt hb.1 h.1.2
      push_cast at this; exact this
    · exact ih b h.2 z hz

lemma polySectorQ_append (p n : ℕ) (amin A : ℚ) (l : List Fac) (a : ℚ × ℚ)
    (l₁ l₂ : List (ℚ × ℚ)) :
    polySectorQ p n amin A l a (l₁ ++ l₂) =
      (polySectorQ p n amin A l a l₁ && polySectorQ p n amin A l (lastPt a l₁) l₂) := by
  induction l₁ generalizing a with
  | nil => simp [polySectorQ, lastPt]
  | cons b rest ih => simp [polySectorQ, lastPt, ih, Bool.and_assoc]

end ZetaIrr.Fam.Interval
