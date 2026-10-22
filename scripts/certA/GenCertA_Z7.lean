/-
# Generator for the A-certificate data files (`ZetaIrrational/Z7/CertAK/Ev*.lean`).

Run from the repository root: `lake env lean scripts/certA/GenCertA_Z7.lean` (writes `scripts/certA/gen_Z7.txt`),
then `python scripts/certA/gen_certA_files.py Z7`. The output is untrusted: every claim in the generated
files is re-checked by `decide +kernel`.
-/
import ZetaIrrational.Z7.CertAK.Windows
import ZetaIrrational.Z7.CertAK.FastG
namespace ZetaIrr.Z7.CertA

def chunksOf (n : ℕ) : ℕ → List ℚ → List (List ℚ)
  | 0, _ => []
  | _, [] => []
  | f + 1, l => l.take n :: chunksOf n f (l.drop n)

def qs (q : ℚ) : String := if q.den = 1 then s!"{q.num}" else s!"{q.num}/{q.den}"

def genOut : IO Unit := do
  let h ← IO.FS.Handle.mk "scripts/certA/gen_Z7.txt" IO.FS.Mode.write
  let mut tot : ℤ := 0
  for j in List.range 133 do
    let l := win j
    let cs := chunksOf 32 1000 l
    h.putStrLn s!"W {j} {l.length} {(l.head? == some (bnd j))}"
    let nk := cs.length
    for k in List.range nk do
      let c := cs.getD k []
      let nxt := if k + 1 < nk then (cs.getD (k+1) []).headD 0 else bnd (j + 1)
      let v := pairSum termUnitsG (c ++ [nxt])
      tot := tot + v
      h.putStrLn s!"C {v} {String.intercalate " " (c.map qs)}"
  h.putStrLn s!"T {tot}"
  h.flush

#eval genOut
end ZetaIrr.Z7.CertA
