import SparseCubes.CertificatePolynomials
import SparseCubes.Data.Chart0
import Mathlib.Tactic.NormNum

namespace SparseCubes.Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

private def total : Tower 5 := (add 5 (add 5 (add 5 (add 5 (add 5 (add 5 w0NegH (mul 5 w0C0 w0P0)) (mul 5 w0C1 w0P1)) (mul 5 w0C2 w0P2)) (mul 5 w0C3 w0P3)) (mul 5 w0C4 w0P4)) (mul 5 w0C5 w0P5))

private theorem total_checked : isZero 5 total = true := by
  rfl

private theorem g0_eval (b c d e j : ℝ) :
    interp 5 w0P0 (point b c d e j) = w0G0 b c d e j := by
  simp only [interp, value, point, w0P0, w0G0, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g1_eval (b c d e j : ℝ) :
    interp 5 w0P1 (point b c d e j) = w0G1 b c d e j := by
  simp only [interp, value, point, w0P1, w0G1, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g2_eval (b c d e j : ℝ) :
    interp 5 w0P2 (point b c d e j) = w0G2 b c d e j := by
  simp only [interp, value, point, w0P2, w0G2, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g3_eval (b c d e j : ℝ) :
    interp 5 w0P3 (point b c d e j) = w0G3 b c d e j := by
  simp only [interp, value, point, w0P3, w0G3, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g4_eval (b c d e j : ℝ) :
    interp 5 w0P4 (point b c d e j) = w0G4 b c d e j := by
  simp only [interp, value, point, w0P4, w0G4, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem g5_eval (b c d e j : ℝ) :
    interp 5 w0P5 (point b c d e j) = w0G5 b c d e j := by
  simp only [interp, value, point, w0P5, w0G5, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  <;> ring

private theorem negH_eval (b c d e j : ℝ) :
    interp 5 w0NegH (point b c d e j) = -(w0Den : ℝ) * chartH b c d e j := by
  simp only [interp, value, point, w0NegH, w0Den, chartH, Int.cast_ofNat, Int.cast_neg, mul_zero, add_zero, zero_add, mul_one]
  ring

theorem w0_excludes (b c d e j : ℝ)
    (h0 : w0G0 b c d e j = 0)
    (h1 : w0G1 b c d e j = 0)
    (h2 : w0G2 b c d e j = 0)
    (h3 : w0G3 b c d e j = 0)
    (h4 : w0G4 b c d e j = 0)
    (h5 : w0G5 b c d e j = 0) :
    chartH b c d e j = 0 := by
  have h := interp_of_isZero 5 total (point b c d e j) total_checked
  simp only [total, interp_add, interp_mul, negH_eval, g0_eval, h0, g1_eval, h1, g2_eval, h2, g3_eval, h3, g4_eval, h4, g5_eval, h5, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (by norm_num [w0Den])

end SparseCubes.Certificate
