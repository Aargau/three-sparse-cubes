import SparseCubes.CertificatePolynomials
import SparseCubes.Data.CurvedRow0
import SparseCubes.Data.CurvedRow1
import SparseCubes.Data.CurvedRow2
import SparseCubes.Data.CurvedRow3
import SparseCubes.Data.CurvedRow4
import SparseCubes.Data.CurvedRow5
import SparseCubes.Data.CurvedRow6
import Mathlib.Tactic.NormNum

namespace SparseCubes.Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

private theorem total_checked : isZero 5 w1Sum = true := by
  apply of_slices (N := 7)
  · decide
  · intro i hi
    interval_cases i
    · exact w1Row0_checked
    · exact w1Row1_checked
    · exact w1Row2_checked
    · exact w1Row3_checked
    · exact w1Row4_checked
    · exact w1Row5_checked
    · exact w1Row6_checked

private theorem g0_eval (b c d e j : ℝ) :
    interp 5 w1P0 (point b c d e j) = w1G0 b c d e j := by
  simp only [interp, value, point, w1P0, w1G0, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g1_eval (b c d e j : ℝ) :
    interp 5 w1P1 (point b c d e j) = w1G1 b c d e j := by
  simp only [interp, value, point, w1P1, w1G1, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g2_eval (b c d e j : ℝ) :
    interp 5 w1P2 (point b c d e j) = w1G2 b c d e j := by
  simp only [interp, value, point, w1P2, w1G2, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g3_eval (b c d e j : ℝ) :
    interp 5 w1P3 (point b c d e j) = w1G3 b c d e j := by
  simp only [interp, value, point, w1P3, w1G3, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g4_eval (b c d e j : ℝ) :
    interp 5 w1P4 (point b c d e j) = w1G4 b c d e j := by
  simp only [interp, value, point, w1P4, w1G4, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g5_eval (b c d e j : ℝ) :
    interp 5 w1P5 (point b c d e j) = w1G5 b c d e j := by
  simp only [interp, value, point, w1P5, w1G5, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem negH_eval (b c d e j : ℝ) :
    interp 5 w1NegH (point b c d e j) = -(w1Den : ℝ) * chartH b c d e j := by
  simp only [interp, value, point, w1NegH, w1Den, chartH, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  ring

theorem w1_excludes (b c d e j : ℝ)
    (h0 : w1G0 b c d e j = 0)
    (h1 : w1G1 b c d e j = 0)
    (h2 : w1G2 b c d e j = 0)
    (h3 : w1G3 b c d e j = 0)
    (h4 : w1G4 b c d e j = 0)
    (h5 : w1G5 b c d e j = 0) :
    chartH b c d e j = 0 := by
  have h := interp_of_isZero 5 w1Sum (point b c d e j) total_checked
  simp only [w1Sum, interp_add, interp_mul, negH_eval, g0_eval, h0, g1_eval, h1, g2_eval, h2, g3_eval, h3, g4_eval, h4, g5_eval, h5, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num [w1Den])

end SparseCubes.Certificate
