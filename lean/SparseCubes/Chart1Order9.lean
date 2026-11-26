import SparseCubes.Chart1Coefficients

namespace SparseCubes.Chart.Chart1
open SparseCubes.Certificate Reflection

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def diff9u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm5l)) (add 5 (mul 5 pc (mul 5 pr3l (mul 5 pnine pm5k))) (add 5 (mul 5 pb (mul 5 pr3l pm5l)) (add 5 (mul 5 pr3u pm5u) (add 5 (mul 5 pc (mul 5 pr2k pm6l)) (add 5 (mul 5 pc (mul 5 pr2l (mul 5 pnine pm6k))) (add 5 (mul 5 pb (mul 5 pr2l pm6l)) (add 5 (mul 5 pr2u pm6u) (add 5 (mul 5 pc (mul 5 pr1k pm7l)) (add 5 (mul 5 pc (mul 5 pr1l (mul 5 pnine pm7k))) (add 5 (mul 5 pb (mul 5 pr1l pm7l)) (add 5 (mul 5 pr1u pm7u) (add 5 (mul 5 pc (mul 5 pr0k pm8l)) (add 5 (mul 5 pc (mul 5 pr0l (mul 5 pnine pm8k))) (add 5 (mul 5 pb (mul 5 pr0l pm8l)) (add 5 (mul 5 pr0u pm8u) (neg 5 pm9u)))))))))))))))))
private theorem zero9u : isZero 5 diff9u = true := by rfl
private theorem correct9u (b c d e j : ℝ) : (m9 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m8 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j)).u := by
  have h := interp_of_isZero 5 diff9u (point b c d e j) zero9u
  simp only [diff9u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8k_unscaled,eval_m8l,eval_m8u,eval_m9u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  have scalem8k : (m8 b c d e j).k = 9*Certificate.w1G4 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem5k,scalem6k,scalem7k,scalem8k]
  linear_combination -h

private def diff9l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k (mul 5 pnine pm5k))) (add 5 (mul 5 pr3l pm5u) (add 5 (mul 5 pr3u pm5l) (add 5 (mul 5 pc (mul 5 pr2k (mul 5 pnine pm6k))) (add 5 (mul 5 pr2l pm6u) (add 5 (mul 5 pr2u pm6l) (add 5 (mul 5 pc (mul 5 pr1k (mul 5 pnine pm7k))) (add 5 (mul 5 pr1l pm7u) (add 5 (mul 5 pr1u pm7l) (add 5 (mul 5 pc (mul 5 pr0k (mul 5 pnine pm8k))) (add 5 (mul 5 pr0l pm8u) (add 5 (mul 5 pr0u pm8l) (neg 5 pm9l)))))))))))))
private theorem zero9l : isZero 5 diff9l = true := by rfl
private theorem correct9l (b c d e j : ℝ) : (m9 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m8 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j)).l := by
  have h := interp_of_isZero 5 diff9l (point b c d e j) zero9l
  simp only [diff9l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8k_unscaled,eval_m8l,eval_m8u,eval_m9l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  have scalem8k : (m8 b c d e j).k = 9*Certificate.w1G4 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem5k,scalem6k,scalem7k,scalem8k]
  linear_combination -h

private def diff9k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k (mul 5 pnine pm5k)))) (add 5 (mul 5 pr3l pm5l) (add 5 (mul 5 pr3k pm5u) (add 5 (mul 5 pr3u (mul 5 pnine pm5k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k (mul 5 pnine pm6k)))) (add 5 (mul 5 pr2l pm6l) (add 5 (mul 5 pr2k pm6u) (add 5 (mul 5 pr2u (mul 5 pnine pm6k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k (mul 5 pnine pm7k)))) (add 5 (mul 5 pr1l pm7l) (add 5 (mul 5 pr1k pm7u) (add 5 (mul 5 pr1u (mul 5 pnine pm7k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm8k)))) (add 5 (mul 5 pr0l pm8l) (add 5 (mul 5 pr0k pm8u) (add 5 (mul 5 pr0u (mul 5 pnine pm8k)) (neg 5 (mul 5 pnine pm9k))))))))))))))))))
private theorem zero9k : isZero 5 diff9k = true := by rfl
private theorem correct9k (b c d e j : ℝ) : (m9 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m8 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j)).k := by
  have h := interp_of_isZero 5 diff9k (point b c d e j) zero9k
  simp only [diff9k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8k_unscaled,eval_m8l,eval_m8u,eval_m9k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  have scalem8k : (m8 b c d e j).k = 9*Certificate.w1G4 b c d e j := rfl
  have scalem9k : (m9 b c d e j).k = 9*Certificate.w1G5 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem5k,scalem6k,scalem7k,scalem8k,scalem9k]
  linear_combination -h

theorem step9 (b c d e j : ℝ) : m9 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m8 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) :=
  rep_ext (correct9u b c d e j) (correct9l b c d e j) (correct9k b c d e j)

end SparseCubes.Chart.Chart1
