import SparseCubes.CertificateKernel
import Mathlib.Tactic.IntervalCases

namespace SparseCubes.Certificate

def slice (n : Nat) (p : Tower (n+1)) (i : Nat) : Tower n :=
  (p[i]?).getD (pzero n)

/-- A finite list of per-slice checks certifies the polynomial at the outer level. -/
theorem of_slices {n N : Nat} (p : Tower (n+1)) (bound : p.length ≤ N)
    (check : ∀ i, i < N → isZero n (slice n p i) = true) :
    isZero (n+1) p = true := by
  change p.all (isZero n) = true
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp ha
  simpa only [slice, List.getElem?_eq_getElem hi, Option.getD_some] using
    check i (lt_of_lt_of_le hi bound)

end SparseCubes.Certificate
