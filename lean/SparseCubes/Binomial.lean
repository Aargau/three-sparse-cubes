import SparseCubes.Moments

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section

structure Arm where
  left : ℕ
  right : ℕ
  A : ℝ
  B : ℝ

def Arm.poly (g : Arm) : ℝ[X] := C g.A * X^g.left + C g.B * X^g.right

theorem exists_arm_of_support_le_two (P : ℝ[X]) (h : P.support.card ≤ 2) :
    ∃ g : Arm, g.poly = P := by
  rcases (show P.support.card = 0 ∨ P.support.card = 1 ∨ P.support.card = 2 by omega) with h0|h1|h2
  · have hz : P = 0 := by simpa using h0
    exact ⟨⟨0,0,0,0⟩, by simp [Arm.poly, hz]⟩
  · obtain ⟨k,hk⟩ := Finset.card_eq_one.mp h1
    refine ⟨⟨k,0,P.coeff k,0⟩, ?_⟩
    simpa [Arm.poly,hk] using P.as_sum_support_C_mul_X_pow.symm
  · obtain ⟨k,l,hkl,hkl'⟩ := Finset.card_eq_two.mp h2
    refine ⟨⟨k,l,P.coeff k,P.coeff l⟩, ?_⟩
    simpa [Arm.poly,hkl',hkl] using P.as_sum_support_C_mul_X_pow.symm

theorem arm_cube (g : Arm) : g.poly^3 =
    C (g.A^3) * X^(g.left+g.left+g.left) +
    C (3*g.A^2*g.B) * X^(g.left+g.left+g.right) +
    C (3*g.A*g.B^2) * X^(g.left+g.right+g.right) +
    C (g.B^3) * X^(g.right+g.right+g.right) := by
  simp only [Arm.poly, pow_add, map_mul, map_pow, map_ofNat]
  ring

/-- Cubing two weighted frequencies gives four weighted frequencies. -/
def cubeFour (A B a b : ℝ) (n : ℕ) : ℝ :=
    A^3 * (3*a)^n + 3*A^2*B*(2*a+b)^n + 3*A*B^2*(a+2*b)^n + B^3*(3*b)^n

def Arm.leftMass (g : Arm) (r : ℝ) : ℝ := g.A*r^g.left
def Arm.rightMass (g : Arm) (r : ℝ) : ℝ := g.B*r^g.right

theorem moment_arm_cube (g : Arm) (r t : ℝ) (n : ℕ) :
    moment (3*t) r n (g.poly^3) =
    cubeFour (g.leftMass r) (g.rightMass r) ((g.left:ℝ)-t) ((g.right:ℝ)-t) n := by
  rw [arm_cube]
  simp only [moment_add, moment_term]
  simp only [cubeFour, Arm.leftMass, Arm.rightMass, pow_add,
    Nat.cast_add]
  ring

theorem support_add_card_le (P Q : ℝ[X]) :
    (P+Q).support.card ≤ P.support.card + Q.support.card :=
  (Finset.card_le_card Polynomial.support_add).trans (Finset.card_union_le _ _)

theorem support_one_term (a : ℝ) (k : ℕ) : (C a * X^k).support.card ≤ 1 := by
  simpa using Finset.card_le_card (Polynomial.support_C_mul_X_pow_subset k a)

theorem support_cube_le_four (g : Arm) : (g.poly^3).support.card ≤ 4 := by
  rw [arm_cube]
  calc
    _ ≤ _ := support_add_card_le _ _
    _ ≤ _ := Nat.add_le_add_right (support_add_card_le _ _) _
    _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (support_add_card_le _ _) _) _
    _ ≤ 4 := by
      have h := support_one_term
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (h _ _) (h _ _)) (h _ _)) (h _ _)

theorem support_C_mul_card_le (a : ℝ) (P : ℝ[X]) : (C a*P).support.card ≤ P.support.card := by
  apply Finset.card_le_card
  intro k hk
  contrapose! hk
  apply Polynomial.notMem_support_iff.mpr
  rw [Polynomial.coeff_C_mul, Polynomial.notMem_support_iff.mp hk, mul_zero]

theorem support_small_cube (P : ℝ[X]) (h : P.support.card ≤ 1) : (P^3).support.card ≤ 1 := by
  rcases (show P.support.card = 0 ∨ P.support.card = 1 by omega) with h0|h1
  · have hz : P = 0 := by simpa using h0
    simp [hz]
  · obtain ⟨k,hk⟩ := Finset.card_eq_one.mp h1
    have hP : P = monomial k (P.coeff k) := by simpa [hk] using P.as_sum_support
    conv_lhs => rw [hP, monomial_pow]
    simpa using Finset.card_le_card (Polynomial.support_monomial_subset (k*3) (P.coeff k^3))

/-- The exact board conclusion when at least one input has at most one term. -/
theorem bound_of_one_small_input (s : Fin 3 → ℝ) (g : Fin 3 → ℝ[X])
    (hg : ∀ i, (g i).support.card ≤ 2) (hs : ∃ i, (g i).support.card ≤ 1)
    (hP : (∑ i, C (s i) * g i ^ 3) ≠ 0) (r : ℝ) (hr : 0 < r) :
    rootMultiplicity r (∑ i, C (s i) * g i ^ 3) ≤ 9 := by
  have each (i : Fin 3) : (C (s i)*g i^3).support.card ≤ 4 := by
    obtain ⟨a,ha⟩ := exists_arm_of_support_le_two (g i) (hg i)
    exact (support_C_mul_card_le _ _).trans (ha ▸ support_cube_le_four a)
  obtain ⟨i,hi⟩ := hs
  have small := (support_C_mul_card_le (s i) (g i ^ 3)).trans (support_small_cube (g i) hi)
  have card : (∑ j, C (s j) * g j^3).support.card ≤ 9 := by
    rw [Fin.sum_univ_three]
    have hab := support_add_card_le (C (s 0)*g 0^3) (C (s 1)*g 1^3)
    have hall := support_add_card_le (C (s 0)*g 0^3+C (s 1)*g 1^3) (C (s 2)*g 2^3)
    have h0 := each 0
    have h1 := each 1
    have h2 := each 2
    fin_cases i <;> dsimp at small <;> omega
  exact (rootMultiplicity_lt_support_card r hr.ne' _ hP).le.trans card

end
end SparseCubes
