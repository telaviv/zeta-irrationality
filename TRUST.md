# What you have to trust

## Axioms

`lake env lean Axioms.lean` prints, for the main theorem and each of its main ingredients,

```
'ZetaIrr.Z7.oneOfZeta7To21' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms, the same ones Mathlib uses. The project contains no `sorry`, no `axiom`
declaration, no `native_decide` and no `implemented_by`, so nothing relies on the compiler. The A-certificate and the
saddle-point certificate are decidable statements about rational data, proved by `decide +kernel`; every proof is
checked by the kernel.

## The statement

The kernel checks the proof. It cannot check that the statement means what we claim, so read this definition:

| file | definition |
|---|---|
| `ZetaIrrational/Statement.lean` | `OneOfZeta7To21 := ∃ j ∈ ({7, 9, 11, 13, 15, 17, 19, 21} : Finset ℕ), Irrational (riemannZeta j).re` |

`riemannZeta : ℂ → ℂ` and `Irrational` (`x ∉ Set.range ((↑) : ℚ → ℝ)`) are Mathlib's; `j : ℕ` is cast to `ℂ`.
Nothing from this project occurs in the statement. (Mathlib's `zeta_nat_eq_tsum_of_gt_one` shows `riemannZeta j` is
the series `∑' n, 1/n^j`; `Defs.lean` uses it to pass to the real series `zetaR` used internally.)

## Generated files

Some Lean files contain large literal data produced by scripts. The scripts and their output are **untrusted
inputs**: every claim about the data is re-proved by the kernel, so a wrong value makes the build fail; it cannot make
a false theorem true.

| data | Lean files | generator |
|---|---|---|
| A-certificate (30,138 event points, 30,137 intervals, 133 sorting windows, 1,029 chunk sums) | `Z7/CertAK/EvData.lean`, `EvWin*.lean`, `EvSorted.lean`, `EvSum*.lean`, `CertCompute.lean` | `scripts/certA/GenCertA_Z7.lean` (`#eval`) + `scripts/certA/gen_certA_files.py` |
| saddle point, steepest-descent polyline, top ray | `Z7/Interval/ConstZ7.lean`, `PolyDataZ7.lean` | `scripts/saddle/gen_saddle_Z7.py` (mpmath, RK4 trace + greedy simplification) |

## How the A-certificate is kernel-checked

Same route as `lean_beta` (see its TRUST.md). The specification (`Z7/CertA/Defs.lean`: the bracket of PROOF_ZETA §5.1,
`eStar`, and `events` built with `List.mergeSort`) is what the soundness proofs use. The kernel evaluates equivalent
forms instead, each with a general proof:
* `Z7/CertAK/FastG.lean`: `termUnits = termUnitsG`, a closed form of e* in `Nat` arithmetic (about 0.4 s per point in
  the kernel);
* `Z7/CertAK/EvSort.lean`, `Windows.lean`: a structural merge sort; if each window's sort equals a literal list and
  the concatenation is strictly increasing, that concatenation is `events 400`; `pairSum` splits over chunks.

`CertCompute.lean` assembles these into `bodyUnits 400 = 778841997893779320302794447562` (units of 2⁻⁹⁶).

## Cross-checks outside Lean

Not needed for correctness, but they agree:
- **A-certificate.** `bodyUnits 400 · 2⁻⁹⁶ + 33/400 + G/798` equals the exact fraction
  A = 11757994664484187722611840743096153/1185451381619680151243401356902400 ≈ 9.9185803 printed by the independent
  Python implementation `handoff/zeta7/f4_certA_exact.py` (`f4_final.log`).
- **Saddle certificate.** The Lean enclosure Re Ω ∈ [−10.1167486, −10.1167485] and sin(240 Im Ω) ≈ −0.932 agree with
  the Arb certificate `handoff/zeta7/f5_saddle_cert.py`.

## Cost

With Mathlib cached (`lake exe cache get`), on a 32-core desktop with 32 GB RAM:
- the A-certificate (`Z7/CertAK`) takes about 30 min wall at `LEAN_NUM_THREADS=12` (about 3.3 CPU-hours of chunk sums);
- the saddle certificate (`Z7/Interval`) takes about 5 min wall;
- the rest takes about 15 min.

On Windows, run Lake with `LEAN_NUM_THREADS=8` (or 12). With the default of one job per core, the parallel Lean
processes fail with "failed to read file ….olean" or exit code 0xC0000142; this is a resource limit, not a proof
error.
