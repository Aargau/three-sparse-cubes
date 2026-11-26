import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

namespace SparseCubes
open Polynomial
open scoped BigOperators

noncomputable section

/-- Applying the shifted Euler operator multiplies a monomial of degree k by k-z. -/
def euler (z : ℝ) (P : ℝ[X]) : ℝ[X] := X * derivative P - C z * P

def moment (z r : ℝ) : ℕ → ℝ[X] → ℝ
  | 0, P => P.eval r
  | n+1, P => moment z r n (euler z P)

theorem euler_add (z : ℝ) (P Q : ℝ[X]) : euler z (P+Q) = euler z P + euler z Q := by
  simp only [euler, map_add, mul_add]
  ring

theorem euler_C_mul (z t : ℝ) (P : ℝ[X]) : euler z (C t * P) = C t * euler z P := by
  simp only [euler, derivative_C_mul]
  ring

theorem moment_add (z r : ℝ) (n : ℕ) (P Q : ℝ[X]) :
    moment z r n (P+Q) = moment z r n P + moment z r n Q := by
  induction n generalizing P Q with
  | zero => simp [moment]
  | succ n ih => simp only [moment, euler_add, ih]

theorem moment_C_mul (z r : ℝ) (n : ℕ) (t : ℝ) (P : ℝ[X]) :
    moment z r n (C t * P) = t * moment z r n P := by
  induction n generalizing P with
  | zero => simp [moment]
  | succ n ih => simp only [moment, euler_C_mul, ih]

theorem moment_zero (z r : ℝ) (n : ℕ) : moment z r n 0 = 0 := by
  simpa using moment_C_mul z r n 0 0

theorem moment_sum {ι : Type*} (z r : ℝ) (n : ℕ) (I : Finset ι) (P : ι → ℝ[X]) :
    moment z r n (∑ i ∈ I, P i) = ∑ i ∈ I, moment z r n (P i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [moment_zero]
  | insert i I hi ih => simp [hi, moment_add, ih]

theorem euler_term (z t : ℝ) (k : ℕ) :
    euler z (C t * X^k) = C ((k:ℝ)-z) * (C t * X^k) := by
  cases k with
  | zero => simp [euler]
  | succ k =>
    rw [euler, derivative_C_mul_X_pow]
    simp only [Nat.add_one_sub_one, pow_succ,
      Nat.cast_succ, map_sub, map_add, map_mul, map_one]
    ring

theorem moment_term (z r t : ℝ) (k n : ℕ) :
    moment z r n (C t * X^k) = t * r^k * ((k:ℝ)-z)^n := by
  induction n with
  | zero => simp [moment]
  | succ n ih => rw [moment, euler_term, moment_C_mul, ih, pow_succ]; ring

theorem moment_eq_zero_of_dvd {P : ℝ[X]} (z r : ℝ) (n : ℕ)
    (h : (X - C r)^(n+1) ∣ P) : moment z r n P = 0 := by
  induction n generalizing P with
  | zero =>
    have h' : X - C r ∣ P := by simpa using h
    simpa [moment, Polynomial.IsRoot] using (dvd_iff_isRoot.mp h')
  | succ n ih =>
    apply ih
    apply dvd_sub
    · apply dvd_mul_of_dvd_right
      simpa using pow_sub_one_dvd_derivative_of_pow_dvd h
    · apply dvd_mul_of_dvd_right
      exact (pow_dvd_pow (X - C r) (by omega : n+1 ≤ n+1+1)).trans h

theorem moment_eq_zero_of_lt_rootMultiplicity (z r : ℝ) (P : ℝ[X]) {n : ℕ}
    (h : n < P.rootMultiplicity r) : moment z r n P = 0 :=
  moment_eq_zero_of_dvd z r n
    ((pow_dvd_pow (X-C r) h).trans (P.pow_rootMultiplicity_dvd r))

theorem moment_eq_support_sum (z r : ℝ) (n : ℕ) (P : ℝ[X]) :
    moment z r n P = ∑ k ∈ P.support, P.coeff k * r^k * ((k:ℝ)-z)^n := by
  conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
  simp only [moment_sum, moment_term]

/-- The first support.card Euler moments determine a polynomial at any nonzero node. -/
theorem eq_zero_of_moments (z r : ℝ) (hr : r ≠ 0) (P : ℝ[X])
    (h : ∀ n < P.support.card, moment z r n P = 0) : P = 0 := by
  classical
  let e := P.support.equivFin.symm
  let f (i : Fin P.support.card) : ℝ := ((e i).1:ℝ) - z
  let v (i : Fin P.support.card) : ℝ := P.coeff (e i).1 * r^(e i).1
  have hf : Function.Injective f := by
    intro i j hij
    have hcast : ((e i).1 : ℝ) = ((e j).1 : ℝ) := sub_left_inj.mp hij
    apply e.injective
    apply Subtype.ext
    exact_mod_cast hcast
  have hv : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf (by
    intro i
    have ha := h i i.isLt
    rw [moment_eq_support_sum, ← Finset.sum_attach] at ha
    rwa [show (∑ j, v j * f j ^ (i:ℕ)) = _ from
      Equiv.sum_comp e (fun k => P.coeff k.1 * r^k.1 * ((k.1:ℝ)-z)^(i:ℕ))])
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro k
  by_cases hk : k ∈ P.support
  · have he := congrFun hv (e.symm ⟨k,hk⟩)
    simpa [v, hr] using he
  · simpa using (Polynomial.notMem_support_iff.mp hk)

theorem rootMultiplicity_lt_support_card (r : ℝ) (hr : r ≠ 0) (P : ℝ[X]) (hP : P ≠ 0) :
    P.rootMultiplicity r < P.support.card := by
  by_contra! h
  exact hP (eq_zero_of_moments 0 r hr P (fun n hn =>
    moment_eq_zero_of_lt_rootMultiplicity 0 r P (lt_of_lt_of_le hn h)))

end
end SparseCubes
