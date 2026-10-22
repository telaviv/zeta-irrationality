/-
# The A-certificate for instance Z7: the isolated computational fact and its reductions

Lemma 5 for Z7. This file contains *no* computation. It isolates the single computational fact
of the Z7 A-certificate as a `Prop`:

* `CertFact : Prop := ABody 400 + tail 400 ≤ Acert` — the A-certificate;
* `UnitsFact : Prop := bodyUnits 400 = 778841997893779320302794447562` — the rounded-body form
  (proved in `Z7/CertAK/CertCompute.lean`);
* `certFact_of_units : UnitsFact → CertFact` (proved here; exact rational arithmetic).

Numbers (from the generator `scripts/certA/`; `scripts/certA/z7_model.py` mirrors the Lean
definitions in Python, and an independent exact-rational implementation of Lemma 5 gives the
same value): `bodyUnits 400 =
778841997893779320302794447562` (units of `2^-96`), `A_body ≤ 9.8303681`,
`tail 400 = 33/400 + G/798`, and `bodyUnits/2^96 + tail = Acert =
11757994664484187722611840743096153/1185451381619680151243401356902400` exactly (`≈ 9.9185803`).
The event list has 30,138 points (30,137 intervals).
-/
import ZetaIrrational.Z7.CertA.Defs

namespace ZetaIrr.Z7.CertA

/-- Each exact term is at most its rounded-up value. -/
lemma pairSum_le_units :
    ∀ l : List ℚ, pairSum (fun a b => eStar ((a + b) / 2) * (1 / a - 1 / b)) l ≤
      ((pairSum termUnits l : ℤ) : ℚ) / 2 ^ 96
  | [] => by simp [pairSum]
  | [_] => by simp [pairSum]
  | a :: b :: l => by
    have ih := pairSum_le_units (b :: l)
    have h96 : (0 : ℚ) < 2 ^ 96 := by positivity
    have hterm : eStar ((a + b) / 2) * (1 / a - 1 / b) ≤ ((termUnits a b : ℤ) : ℚ) / 2 ^ 96 := by
      rw [le_div_iff₀ h96]; exact Int.le_ceil _
    change eStar ((a + b) / 2) * (1 / a - 1 / b) +
        pairSum (fun a b => eStar ((a + b) / 2) * (1 / a - 1 / b)) (b :: l) ≤
      ((termUnits a b + pairSum termUnits (b :: l) : ℤ) : ℚ) / 2 ^ 96
    rw [Int.cast_add, add_div ((termUnits a b : ℤ) : ℚ) ((pairSum termUnits (b :: l) : ℤ) : ℚ)]
    linarith

lemma ABody_le_units (X : ℕ) : ABody X ≤ ((bodyUnits X : ℤ) : ℚ) / 2 ^ 96 :=
  pairSum_le_units (events X)

/-- **The isolated computational fact for Z7** (the A-certificate): `A_body + E_tail/X + G/(2(X-1)) ≤ Acert`
with `X = 400`, `E_tail = S + 15 = 33`, where `A_body = Σ_ℓ e*(mid_ℓ)(1/x_{ℓ-1} - 1/x_ℓ)` over the
event intervals in `[1, 400]`. -/
def CertFact : Prop := ABody 400 + tail 400 ≤ Acert

/-- The rounded-body form of the computation. -/
def UnitsFact : Prop := bodyUnits 400 = 778841997893779320302794447562

/-- The rounded body value and the tail add up to `Acert` exactly. -/
lemma units_add_tail_eq :
    ((778841997893779320302794447562 : ℤ) : ℚ) / 2 ^ 96 + tail 400 = Acert := by
  norm_num [tail, G, Acert]

/-- `UnitsFact` implies `CertFact`. -/
theorem certFact_of_units (h : UnitsFact) : CertFact := by
  have h1 := ABody_le_units 400
  rw [show bodyUnits 400 = 778841997893779320302794447562 from h] at h1
  have h2 := units_add_tail_eq
  unfold CertFact
  linarith

end ZetaIrr.Z7.CertA
