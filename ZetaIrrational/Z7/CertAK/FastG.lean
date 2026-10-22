/-
# The A-certificate for Z7: a fast form of `e*` for kernel evaluation

`eStarInt x` (`Z7/CertA/Defs.lean`) is a max over the offsets `o` and `right ∈ {false, true}` of
`cand … r_i right`, where `cand` takes several passes over the block data with `Int` arithmetic.
Here `candG` computes the same value from one pass (`blockStep`) over the block data as natural
numbers, accumulating
* `tP = Σ m [r_i < r_b]`, `tN = Σ m ([r_i < r_a] + e_b)` (so `T = K_T + tP - tN`),
* `s0 = Σ m [block contains the candidate at k = 0]`,
* `h1 = #{blocks containing a valid candidate k ≥ 1}`,
so that the kernel does only `Nat` primitive operations per block (it has GMP-backed `Nat`
operations but none for `Int`), plus a few `Int` operations per candidate.

Main results: `cand_eq_G`, `eStarInt_eq_G`, `termUnits_eq_G : termUnits = termUnitsG`.

Status: complete (no `sorry`).
-/
import ZetaIrrational.Z7.CertA.Sound

namespace ZetaIrr.Z7.CertA

/-! ## The fast form -/

/-- Natural-number block data `(m, q_a, r_a, q_b, r_b)`. -/
abbrev BD := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The accumulator `(tP, tN, s0, h1)`. -/
abbrev AC := ℕ × ℕ × ℕ × ℕ

/-- `e_b ∈ {0, 1}` as a natural number. -/
def ebN (ri rb : ℕ) (right : Bool) : ℕ := cond right 1 (cond (Nat.beq ri rb) 0 1)

/-- `[b]` as a natural number. -/
def bN (b : Bool) : ℕ := cond b 1 0

/-- One block's contribution to the accumulator. `nc = [the candidate k = q_X is invalid]`. -/
def blockStep (ri : ℕ) (right : Bool) (nc qX : ℕ) (acc : AC) (e : BD) : AC :=
  let m := e.1
  let qa := e.2.1
  let ra := e.2.2.1
  let qb := e.2.2.2.1
  let rb := e.2.2.2.2
  let la := Nat.blt ri ra
  let lbN := bN (Nat.blt ri rb)
  let eb := ebN ri rb right
  let L := Nat.add qa (bN la)
  let L1 := cond (Nat.beq L 0) 1 L
  (Nat.add acc.1 (Nat.mul m lbN),
   Nat.add acc.2.1 (Nat.add (cond la m 0) (Nat.mul m eb)),
   Nat.add acc.2.2.1 (cond (Nat.beq qa 0 && Nat.ble ra ri && Nat.ble eb (Nat.add qb lbN)) m 0),
   Nat.add acc.2.2.2 (cond (Nat.blt 0 m && Nat.ble (Nat.add L1 eb) (Nat.add qb lbN) &&
     Nat.ble (Nat.add L1 nc) qX) 1 0))

/-- The block data as natural numbers. -/
def rsOf (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) : List BD :=
  pre.map fun e => (e.1.toNat, e.2.1.1.toNat, e.2.1.2.toNat, e.2.2.1.toNat, e.2.2.2.toNat)

/-- `K_T = Σ m (1 + q_b - q_a)`. -/
def KTof (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) : ℤ := (pre.map fun e => e.1 * (1 + e.2.2.1 - e.2.1.1)).sum

/-- `cand` in fast form. -/
def candG (KT K : ℤ) (rs : List BD) (rn r2 r3 qX rX ri : ℕ) (right : Bool) : ℤ :=
  let nc := cond (cond right (Nat.blt ri rX) (Nat.ble ri rX)) 0 1
  let a := rs.foldl (blockStep ri right nc qX) (0, 0, 0, 0)
  let posN := a.1 + 5 * bN (Nat.blt ri rn) + 5 * bN (Nat.blt ri r2) + 5 * ebN ri r3 right
  let negN := a.2.1 + 5 * bN (Nat.blt ri r3) + 5 * ebN ri r2 right
  let V : ℤ := K + (posN : ℤ) - (negN : ℤ)
  max (if a.2.2.1 = 0 then 0 else if 1 + (a.2.1 : ℤ) + (a.2.2.1 : ℤ) ≤ KT + (a.1 : ℤ) then V - 1
      else 0)
    (if 0 < a.2.2.2 then V + 4 else 0)

/-- Fast `eStarInt`. -/
def eStarIntG (x : ℚ) : ℤ :=
  let P := x.num
  let Q : ℤ := x.den
  let pre := preOf P Q
  let qn := qrOf P Q (-220)
  let q2 := qrOf P Q 240
  let q3 := qrOf P Q 460
  let KT := KTof pre
  let K := KT - 5 * (q3.1 - q2.1 - qn.1)
  let rs := rsOf pre
  let qX := (P / Q).toNat
  let rX := (240 * (P % Q)).toNat
  offsets.foldl (fun acc o =>
      let ri := (qrOf P Q o).2.toNat
      max acc (max (candG KT K rs qn.2.toNat q2.2.toNat q3.2.toNat qX rX ri false)
        (candG KT K rs qn.2.toNat q2.2.toNat q3.2.toNat qX rX ri true)))
    0

/-- Fast `eStar`. -/
def eStarG (x : ℚ) : ℚ := if 1 ≤ x then (eStarIntG x : ℚ) - G * ⌊x⌋ else 0

/-- Fast `termUnits`. -/
def termUnitsG (a b : ℚ) : ℤ := ⌈eStarG ((a + b) / 2) * (1 / a - 1 / b) * 2 ^ 96⌉

/-! ## Proofs -/

lemma blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by rw [Nat.blt_eq]; exact h
lemma blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff, Ne, Nat.blt_eq]; exact h
lemma beq_t {a b : ℕ} (h : a = b) : Nat.beq a b = true := by rw [Nat.beq_eq]; exact h
lemma beq_f {a b : ℕ} (h : ¬ a = b) : Nat.beq a b = false := by
  rw [Bool.eq_false_iff, Ne, Nat.beq_eq]; exact h
lemma ble_t {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := by rw [Nat.ble_eq]; exact h
lemma ble_f {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  rw [Bool.eq_false_iff, Ne, Nat.ble_eq]; exact h

/-- The block data are nonnegative. -/
def PreNN (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) : Prop :=
  ∀ e ∈ pre, 0 ≤ e.1 ∧ 0 ≤ e.2.1.1 ∧ 0 ≤ e.2.1.2 ∧ 0 ≤ e.2.2.1 ∧ 0 ≤ e.2.2.2

lemma bN_lt (a b : ℕ) : (bN (Nat.blt a b) : ℤ) = if (a : ℤ) < b then 1 else 0 := by
  unfold bN
  by_cases h : a < b
  · have : Nat.blt a b = true := blt_t h
    rw [this, if_pos (by exact_mod_cast h)]; rfl
  · have : Nat.blt a b = false := blt_f h
    rw [this, if_neg (by exact_mod_cast h)]; rfl

lemma ebN_eq (ri rb : ℕ) (right : Bool) :
    (ebN ri rb right : ℤ) = ebAt (ri : ℤ) right ((0 : ℤ), (rb : ℤ)) := by
  unfold ebN ebAt
  cases right
  · by_cases h : ri = rb
    · have : Nat.beq ri rb = true := beq_t h
      simp [this, h]
    · have : Nat.beq ri rb = false := beq_f h
      simp [this, h]
  · simp

lemma ebAt_snd (ri : ℤ) (right : Bool) (q : ℤ × ℤ) : ebAt ri right q = ebAt ri right (0, q.2) := by
  unfold ebAt; rfl

/-- The accumulator in closed form. -/
lemma foldl_blockStep (ri : ℕ) (right : Bool) (nc qX : ℕ) :
    ∀ (l : List BD) (acc : AC), l.foldl (blockStep ri right nc qX) acc =
      (acc.1 + (l.map fun e => e.1 * bN (Nat.blt ri e.2.2.2.2)).sum,
       acc.2.1 + (l.map fun e => cond (Nat.blt ri e.2.2.1) e.1 0 + e.1 * ebN ri e.2.2.2.2 right).sum,
       acc.2.2.1 + (l.map fun e => cond (Nat.beq e.2.1 0 && Nat.ble e.2.2.1 ri &&
          Nat.ble (ebN ri e.2.2.2.2 right) (e.2.2.2.1 + bN (Nat.blt ri e.2.2.2.2))) e.1 0).sum,
       acc.2.2.2 + (l.map fun e =>
          cond (Nat.blt 0 e.1 &&
            Nat.ble (cond (Nat.beq (e.2.1 + bN (Nat.blt ri e.2.2.1)) 0) 1
              (e.2.1 + bN (Nat.blt ri e.2.2.1)) + ebN ri e.2.2.2.2 right)
              (e.2.2.2.1 + bN (Nat.blt ri e.2.2.2.2)) &&
            Nat.ble (cond (Nat.beq (e.2.1 + bN (Nat.blt ri e.2.2.1)) 0) 1
              (e.2.1 + bN (Nat.blt ri e.2.2.1)) + nc) qX) 1 0).sum)
  | [], acc => by simp
  | e :: l, acc => by
    rw [List.foldl_cons, foldl_blockStep ri right nc qX l]
    simp only [blockStep, Nat.add_eq, Nat.mul_eq, List.map_cons, List.sum_cons]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

/-- Per block, `T`-part. -/
lemma Tterm (ri : ℕ) (right : Bool) (e : ℤ × (ℤ × ℤ) × (ℤ × ℤ))
    (he : 0 ≤ e.1 ∧ 0 ≤ e.2.1.1 ∧ 0 ≤ e.2.1.2 ∧ 0 ≤ e.2.2.1 ∧ 0 ≤ e.2.2.2) :
    e.1 * (1 + flAt 0 ri e.2.1 - clAt 0 ri right e.2.2) =
      e.1 * (1 + e.2.2.1 - e.2.1.1) + ((e.1.toNat * bN (Nat.blt ri e.2.2.2.toNat) : ℕ) : ℤ) -
        ((cond (Nat.blt ri e.2.1.2.toNat) e.1.toNat 0 + e.1.toNat * ebN ri e.2.2.2.toNat right : ℕ) : ℤ) := by
  obtain ⟨m, ⟨qa, ra⟩, ⟨qb, rb⟩⟩ := e
  obtain ⟨hm, hqa, hra, hqb, hrb⟩ := he
  simp only at hm hqa hra hqb hrb ⊢
  lift m to ℕ using hm
  lift ra to ℕ using hra
  lift rb to ℕ using hrb
  simp only [Int.toNat_natCast, flAt, clAt, ebAt, ebN, bN, Bool.cond_eq_ite, Nat.blt_eq, Nat.beq_eq]
  by_cases h1 : ri < ra <;> by_cases h2 : ri < rb <;> by_cases h3 : ri = rb <;> cases right <;>
    simp only [h1, h2, h3, Nat.cast_lt, Nat.cast_inj, ite_false,
      Bool.false_eq_true, true_and, and_true] <;>
    ((try split_ifs) <;> first | (push_cast; ring1) | (exfalso; omega))

lemma Tval_eq (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (hpre : PreNN pre) (ri : ℕ) (right : Bool) :
    Tval pre ri right = KTof pre +
      (((rsOf pre).map fun e => e.1 * bN (Nat.blt ri e.2.2.2.2)).sum : ℕ) -
      (((rsOf pre).map fun e => cond (Nat.blt ri e.2.2.1) e.1 0 + e.1 * ebN ri e.2.2.2.2 right).sum : ℕ) := by
  induction pre with
  | nil => simp [Tval, KTof, rsOf]
  | cons e pre ih =>
    have ih' := ih (fun e' he' => hpre e' (List.mem_cons_of_mem _ he'))
    have h1 := Tterm ri right e (hpre e List.mem_cons_self)
    simp only [Tval, KTof, rsOf, List.map_cons, List.sum_cons] at ih' ⊢
    push_cast at ih' h1 ⊢
    rw [h1, ih']
    ring

/-- Per block, `S(0)`-part. -/
lemma Sterm (ri : ℕ) (right : Bool) (e : ℤ × (ℤ × ℤ) × (ℤ × ℤ))
    (he : 0 ≤ e.1 ∧ 0 ≤ e.2.1.1 ∧ 0 ≤ e.2.1.2 ∧ 0 ≤ e.2.2.1 ∧ 0 ≤ e.2.2.2) :
    blockS e.1 (flAt 0 ri e.2.1) (clAt 0 ri right e.2.2) =
      ((cond (Nat.beq e.2.1.1.toNat 0 && Nat.ble e.2.1.2.toNat ri &&
          Nat.ble (ebN ri e.2.2.2.toNat right) (e.2.2.1.toNat + bN (Nat.blt ri e.2.2.2.toNat)))
          e.1.toNat 0 : ℕ) : ℤ) := by
  obtain ⟨m, ⟨qa, ra⟩, ⟨qb, rb⟩⟩ := e
  obtain ⟨hm, hqa, hra, hqb, hrb⟩ := he
  simp only at hm hqa hra hqb hrb ⊢
  lift m to ℕ using hm
  lift qa to ℕ using hqa
  lift ra to ℕ using hra
  lift qb to ℕ using hqb
  lift rb to ℕ using hrb
  simp only [Int.toNat_natCast, blockS, flAt, clAt, ebAt, ebN, bN, Bool.cond_eq_ite, Nat.blt_eq,
    Nat.beq_eq, Nat.ble_eq, Bool.and_eq_true]
  by_cases h1 : ri < ra <;> by_cases h2 : ri < rb <;> by_cases h3 : ri = rb <;> cases right <;>
    simp only [h1, h2, h3, Nat.cast_lt, Nat.cast_inj, ite_false,
      Bool.false_eq_true, true_and, and_true] <;>
    ((try split_ifs) <;> first | rfl | omega | (exfalso; omega))

lemma S0_eq (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (hpre : PreNN pre) (ri : ℕ) (right : Bool) :
    (pre.map fun e => blockS e.1 (flAt 0 ri e.2.1) (clAt 0 ri right e.2.2)).sum =
      (((rsOf pre).map fun e => cond (Nat.beq e.2.1 0 && Nat.ble e.2.2.1 ri &&
          Nat.ble (ebN ri e.2.2.2.2 right) (e.2.2.2.1 + bN (Nat.blt ri e.2.2.2.2))) e.1 0).sum : ℕ) := by
  induction pre with
  | nil => simp [rsOf]
  | cons e pre ih =>
    have ih' := ih (fun e' he' => hpre e' (List.mem_cons_of_mem _ he'))
    have h1 := Sterm ri right e (hpre e List.mem_cons_self)
    simp only [rsOf, List.map_cons, List.sum_cons] at ih' ⊢
    push_cast at ih' h1 ⊢
    rw [h1, ih']

/-- Per block, the `has1` test. -/
lemma Hterm (ri : ℕ) (right : Bool) (nc qX : ℕ) (e : ℤ × (ℤ × ℤ) × (ℤ × ℤ))
    (he : 0 ≤ e.1 ∧ 0 ≤ e.2.1.1 ∧ 0 ≤ e.2.1.2 ∧ 0 ≤ e.2.2.1 ∧ 0 ≤ e.2.2.2) (k : ℤ)
    (hk : k = (qX : ℤ) - nc) :
    decide (0 < e.1 ∧
      max 1 (e.2.1.1 + (if (ri : ℤ) < e.2.1.2 then 1 else 0)) ≤
        e.2.2.1 + (if (ri : ℤ) < e.2.2.2 then 1 else 0) - ebAt ri right e.2.2 ∧
      max 1 (e.2.1.1 + (if (ri : ℤ) < e.2.1.2 then 1 else 0)) ≤ k) =
    (Nat.blt 0 e.1.toNat &&
      Nat.ble (cond (Nat.beq (e.2.1.1.toNat + bN (Nat.blt ri e.2.1.2.toNat)) 0) 1
        (e.2.1.1.toNat + bN (Nat.blt ri e.2.1.2.toNat)) + ebN ri e.2.2.2.toNat right)
        (e.2.2.1.toNat + bN (Nat.blt ri e.2.2.2.toNat)) &&
      Nat.ble (cond (Nat.beq (e.2.1.1.toNat + bN (Nat.blt ri e.2.1.2.toNat)) 0) 1
        (e.2.1.1.toNat + bN (Nat.blt ri e.2.1.2.toNat)) + nc) qX) := by
  obtain ⟨m, ⟨qa, ra⟩, ⟨qb, rb⟩⟩ := e
  obtain ⟨hm, hqa, hra, hqb, hrb⟩ := he
  simp only at hm hqa hra hqb hrb ⊢
  lift m to ℕ using hm
  lift qa to ℕ using hqa
  lift ra to ℕ using hra
  lift qb to ℕ using hqb
  lift rb to ℕ using hrb
  subst hk
  rw [Bool.eq_iff_iff]
  simp only [Int.toNat_natCast, decide_eq_true_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
    Nat.beq_eq, bN, ebN, ebAt, Bool.cond_eq_ite, max_le_iff]
  split_ifs <;> push_cast at * <;> omega

lemma has1_eq (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (hpre : PreNN pre) (qX rX : ℤ) (hqX : 0 ≤ qX)
    (hrX : 0 ≤ rX) (ri : ℕ) (right : Bool) :
    has1 pre qX rX ri right = decide (0 < ((rsOf pre).map fun e =>
          cond (Nat.blt 0 e.1 &&
            Nat.ble (cond (Nat.beq (e.2.1 + bN (Nat.blt ri e.2.2.1)) 0) 1
              (e.2.1 + bN (Nat.blt ri e.2.2.1)) + ebN ri e.2.2.2.2 right)
              (e.2.2.2.1 + bN (Nat.blt ri e.2.2.2.2)) &&
            Nat.ble (cond (Nat.beq (e.2.1 + bN (Nat.blt ri e.2.2.1)) 0) 1
              (e.2.1 + bN (Nat.blt ri e.2.2.1)) +
                cond (cond right (Nat.blt ri rX.toNat) (Nat.ble ri rX.toNat)) 0 1) qX.toNat) 1 0).sum) := by
  set nc := cond (cond right (Nat.blt ri rX.toNat) (Nat.ble ri rX.toNat)) 0 1 with hnc
  have hk : kmax qX rX ri right = (qX.toNat : ℤ) - nc := by
    lift qX to ℕ using hqX
    lift rX to ℕ using hrX
    unfold kmax
    simp only [Int.toNat_natCast, hnc]
    cases right
    · by_cases h : ri ≤ rX
      · have : Nat.ble ri rX = true := ble_t h
        simp [this, h]
      · have : Nat.ble ri rX = false := ble_f h
        simp [this, h]
    · by_cases h : ri < rX
      · have : Nat.blt ri rX = true := blt_t h
        simp [this, h]
      · have : Nat.blt ri rX = false := blt_f h
        simp [this, h]
  unfold has1
  induction pre with
  | nil => simp [rsOf]
  | cons e pre ih =>
    have ih' := ih (fun e' he' => hpre e' (List.mem_cons_of_mem _ he'))
    have h1 := Hterm ri right nc qX.toNat e (hpre e List.mem_cons_self) _ hk
    simp only [rsOf, List.map_cons, List.sum_cons, List.any_cons] at ih' ⊢
    rw [h1, ih']
    cases (Nat.blt 0 e.1.toNat && _ && _) <;> simp

/-- `phiAt` at `k = 0` in terms of `S(0)`, `T` and `c`. -/
lemma phiAt_zero (pre : List (ℤ × (ℤ × ℤ) × (ℤ × ℤ))) (qn q2 q3 : ℤ × ℤ) (ri : ℤ) (right : Bool) :
    phiAt pre qn q2 q3 0 ri right =
      let S := (pre.map fun e => blockS e.1 (flAt 0 ri e.2.1) (clAt 0 ri right e.2.2)).sum
      if S = 0 then 0 else if 1 ≤ Tval pre ri right - S then
        Tval pre ri right - 1 - cval qn q2 q3 ri right else 0 := by
  have h1 := sum_SP pre 0 ri right
  have h2 := c_shift qn q2 q3 0 ri right
  unfold phiAt
  simp only
  split_ifs <;> first | rfl | (exfalso; omega) | omega

lemma cval_eq (qn q2 q3 : ℤ × ℤ) (h1 : 0 ≤ qn.2) (h2 : 0 ≤ q2.2) (h3 : 0 ≤ q3.2) (ri : ℕ)
    (right : Bool) :
    cval qn q2 q3 ri right = 5 * (q3.1 - q2.1 - qn.1) - 5 * (bN (Nat.blt ri qn.2.toNat) : ℤ)
      - 5 * (bN (Nat.blt ri q2.2.toNat) : ℤ) + 5 * (ebN ri q2.2.toNat right : ℤ)
      + 5 * (bN (Nat.blt ri q3.2.toNat) : ℤ) - 5 * (ebN ri q3.2.toNat right : ℤ) := by
  obtain ⟨a1, r1⟩ := qn
  obtain ⟨a2, r2⟩ := q2
  obtain ⟨a3, r3⟩ := q3
  simp only at h1 h2 h3 ⊢
  lift r1 to ℕ using h1
  lift r2 to ℕ using h2
  lift r3 to ℕ using h3
  simp only [Int.toNat_natCast, bN_lt, ebN_eq]
  unfold cval clAt flAt
  rw [ebAt_snd ri right (a2, (r2 : ℤ)), ebAt_snd ri right (a3, (r3 : ℤ))]
  ring

lemma qrOf_nonneg (P Q : ℤ) (hP : 0 ≤ P) (hQ : 0 < Q) (o : ℤ) (ho : 0 ≤ o) :
    0 ≤ (qrOf P Q o).1 ∧ 0 ≤ (qrOf P Q o).2 := by
  unfold qrOf
  exact ⟨Int.ediv_nonneg (by positivity) (by omega), Int.emod_nonneg _ (by omega)⟩

lemma preOf_nn (P Q : ℤ) (hP : 0 ≤ P) (hQ : 0 < Q) : PreNN (preOf P Q) := by
  intro e he
  unfold preOf at he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
  have hd : b.1 ≤ 80 := by
    have := (blocks_bounds b hb).2; omega
  have ha := qrOf_nonneg P Q hP hQ (aOff b.1) (by unfold aOff; positivity)
  have hb' := qrOf_nonneg P Q hP hQ (bOff b.1) (by unfold bOff; omega)
  exact ⟨by positivity, ha.1, ha.2, hb'.1, hb'.2⟩

/-- **`cand = candG`** for the data of `x = P/Q > 0`. -/
theorem cand_eq_G (P Q : ℤ) (hP : 0 ≤ P) (hQ : 0 < Q) (ri : ℕ) (right : Bool) :
    cand (preOf P Q) (qrOf P Q (-220)) (qrOf P Q 240) (qrOf P Q 460) (P / Q) (240 * (P % Q)) ri
        right =
      candG (KTof (preOf P Q)) (KTof (preOf P Q) - 5 * ((qrOf P Q 460).1 - (qrOf P Q 240).1 -
          (qrOf P Q (-220)).1)) (rsOf (preOf P Q)) (qrOf P Q (-220)).2.toNat
        (qrOf P Q 240).2.toNat (qrOf P Q 460).2.toNat (P / Q).toNat (240 * (P % Q)).toNat ri right := by
  have hpre := preOf_nn P Q hP hQ
  have hn := qrOf_spec P Q hQ (-220)
  have h2 := qrOf_spec P Q hQ 240
  have h3 := qrOf_spec P Q hQ 460
  have hqX : 0 ≤ P / Q := Int.ediv_nonneg hP hQ.le
  have hrX : 0 ≤ 240 * (P % Q) := by have := Int.emod_nonneg P hQ.ne'; omega
  unfold cand candG
  simp only
  rw [foldl_blockStep]
  simp only [zero_add]
  rw [phiAt_zero, has1_eq _ hpre _ _ hqX hrX, S0_eq _ hpre, Tval_eq _ hpre,
    cval_eq _ _ _ hn.2.1 h2.2.1 h3.2.1]
  simp only [decide_eq_true_eq, Nat.cast_eq_zero]
  push_cast
  split_ifs <;> first | rfl | ring1 | omega | (exfalso; omega)

theorem eStarInt_eq_G (x : ℚ) (hx : 0 < x) : eStarInt x = eStarIntG x := by
  have hP : 0 ≤ x.num := (Rat.num_pos.2 hx).le
  have hQ : (0 : ℤ) < (x.den : ℤ) := by exact_mod_cast x.den_pos
  unfold eStarInt eStarIntG
  simp only
  apply List.foldl_ext
  intro acc o _
  have h0 := (qrOf_spec x.num x.den hQ o).2.1
  have e : (qrOf x.num x.den o).2 = (((qrOf x.num x.den o).2.toNat : ℕ) : ℤ) :=
    (Int.toNat_of_nonneg h0).symm
  rw [e, cand_eq_G _ _ hP hQ _ false, cand_eq_G _ _ hP hQ _ true]
  simp only [Int.toNat_natCast]

theorem eStar_eq_G (x : ℚ) : eStar x = eStarG x := by
  unfold eStar eStarG
  split_ifs with h
  · rw [eStarInt_eq_G x (by linarith)]
  · rfl

theorem termUnits_eq_G : termUnits = termUnitsG := by
  funext a b
  unfold termUnits termUnitsG
  rw [eStar_eq_G]

end ZetaIrr.Z7.CertA
