import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SparseCubes

theorem mixtureWeights (u v w : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hs : u+v+w=0) :
    ∃ p : ℝ, p ≠ 0 ∧ 1-p ≠ 0 ∧
      ∀ a b c : ℝ, u*a+v*b+w*c = 0 → p*a+(1-p)*b=c := by
  refine ⟨-u/w, div_ne_zero (neg_ne_zero.mpr hu) hw, ?_, ?_⟩
  · intro h
    field_simp at h
    apply hv
    linarith
  · intro a b c h
    field_simp
    linear_combination -h + b*hs

/-- Three nonzero weights annihilating the constant and first moments force either
all three nodes to agree or all three to be distinct. -/
theorem three_nodes (m x : Fin 3 → ℝ) (hm : ∀ i, m i ≠ 0)
    (hm0 : m 0+m 1+m 2=0) (hm1 : m 0*x 0+m 1*x 1+m 2*x 2=0) :
    (∀ i, x i = x 0) ∨ Function.Injective x := by
  have h01 (h : x 0=x 1) : x 2=x 0 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left (hm 2)
    rw [← h] at hm1
    linear_combination hm1 - x 0*hm0
  have h02 (h : x 0=x 2) : x 1=x 0 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left (hm 1)
    rw [← h] at hm1
    linear_combination hm1 - x 0*hm0
  have h12 (h : x 1=x 2) : x 0=x 1 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left (hm 0)
    rw [← h] at hm1
    linear_combination hm1 - x 1*hm0
  by_cases a : x 0=x 1
  · exact Or.inl (by intro i; fin_cases i <;> first | rfl | exact a.symm | exact h01 a)
  by_cases b : x 0=x 2
  · exact (a (h02 b).symm).elim
  by_cases c : x 1=x 2
  · exact (a (h12 c)).elim
  right
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact (a hij).elim | exact (a hij.symm).elim | exact (b hij).elim | exact (b hij.symm).elim | exact (c hij).elim | exact (c hij.symm).elim

end SparseCubes
