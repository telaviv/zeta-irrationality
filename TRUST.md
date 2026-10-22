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

Options that change elaboration but not what the kernel checks: `maxRecDepth` and `Elab.async false` in the
certificate files, and `backward.isDefEq.respectTransparency false` in a few lemmas of the vendored PNT port
(`PNT/Port/Wiener.lean`). There is no `debug.*` option, no `maxHeartbeats 0`, no custom `macro`/`syntax`/`elab`, and no
file imports `Lean` itself.

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

The specification (`Z7/CertA/Defs.lean`: the step function `eStar`, and `events` built with `List.mergeSort`) is what
the soundness proofs use. The kernel cannot evaluate it directly: `List.mergeSort` is well-founded recursion, and the
naive `eStar` is slow. So the proof goes through equivalent forms, each with a general proof:

| step | file | statement |
|---|---|---|
| fast e* | `Z7/CertAK/FastG.lean` | `termUnits = termUnitsG`: e* is a maximum of closed forms in `Nat` arithmetic (about 0.4 s per point in the kernel) |
| sort | `Z7/CertAK/EvSort.lean` | `msort`, a structural merge sort that permutes its input whatever the comparator |
| windows | `Z7/CertAK/Windows.lean` | if each window's sort equals a literal list and their concatenation is strictly increasing, that concatenation is `events 400` |
| chunks | `Z7/CertAK/Windows.lean` | `pairSum` over concatenated chunks equals the sum of the chunk sums |

The generated files check each window, the monotonicity of the concatenation and each chunk sum by `decide +kernel`, and
`CertCompute.lean` assembles them into `bodyUnits 400 = 778841997893779320302794447562` (units of 2⁻⁹⁶).

## Cross-checks outside Lean

These are not needed for correctness, but they agree:
- **A-certificate.** `bodyUnits 400 · 2⁻⁹⁶ + 33/400 + G/798` equals
  A = 11757994664484187722611840743096153/1185451381619680151243401356902400 ≈ 9.9185803 exactly, the value of an
  independent exact-rational Python implementation (not included here). `scripts/certA/z7_model.py` mirrors the Lean
  algorithm in Python and reproduces it.
- **Saddle certificate.** The Lean enclosure Re Ω ∈ [−10.1167486, −10.1167485] and sin(240 Im Ω) ≈ −0.932 agree with an
  independent ball-arithmetic (Arb) computation (not included here).

## Independent kernel checks

Besides `lake build`, the proof was replayed by two kernels (on the build of an earlier commit whose Lean code differs
from this one only in comments and two lemma names):
- **Lean's kernel, `leanchecker`** (shipped with the toolchain), one module at a time:
  `lake env leanchecker <Module>` replays the declarations each module adds. Run it per module: without a module argument
  it replays every module at once and needs far more memory than a desktop has. 134 of the 141 modules were replayed,
  including `ZetaIrrational.Z7.MainUnconditional`, `Z7.CertAK.CertCompute` and `Z7.Interval.SaddleDataZ7`, with no
  error. The A-certificate modules need about 9 GB each.
- **An independent kernel, `nanoda`** (Rust; also shipped with the toolchain), on a `leanexport` dump of the closure of
  `ZetaIrr.Z7.oneOfZeta7To21` (81,055 declarations; the only axioms are `propext`, `Quot.sound` and
  `Classical.choice`). The closure is too large for one run on a 32 GB machine, so it was checked in passes, each with a
  different set of theorems replaced by axioms of the same name and type (sound because no check depends on the proof of
  a theorem). 60,465 of the 61,819 theorems were checked, including the main theorem, `bodyUnits_400` with its
  assembly, and every obligation of the saddle certificate, with no error.

Every theorem was accepted by at least one of the two kernels, and they never disagreed.

## Cost

With Mathlib cached (`lake exe cache get`), on a 32-core desktop with 32 GB RAM:
- the A-certificate (`Z7/CertAK`) takes about 30 min wall at `LEAN_NUM_THREADS=12` (about 3.3 CPU-hours of chunk sums);
- the saddle certificate (`Z7/Interval`) takes about 5 min wall;
- everything else takes about 15 min wall.

On Windows, keep `LEAN_NUM_THREADS` at 8–12. With one job per core, the parallel Lean processes fail with
"failed to read file ….olean" or exit code 0xC0000142; this is a resource limit, not a proof error.
