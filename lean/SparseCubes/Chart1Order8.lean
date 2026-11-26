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

private def diff8u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm4l)) (add 5 (mul 5 pc (mul 5 pr3l (mul 5 pnine pm4k))) (add 5 (mul 5 pb (mul 5 pr3l pm4l)) (add 5 (mul 5 pr3u pm4u) (add 5 (mul 5 pc (mul 5 pr2k pm5l)) (add 5 (mul 5 pc (mul 5 pr2l (mul 5 pnine pm5k))) (add 5 (mul 5 pb (mul 5 pr2l pm5l)) (add 5 (mul 5 pr2u pm5u) (add 5 (mul 5 pc (mul 5 pr1k pm6l)) (add 5 (mul 5 pc (mul 5 pr1l (mul 5 pnine pm6k))) (add 5 (mul 5 pb (mul 5 pr1l pm6l)) (add 5 (mul 5 pr1u pm6u) (add 5 (mul 5 pc (mul 5 pr0k pm7l)) (add 5 (mul 5 pc (mul 5 pr0l (mul 5 pnine pm7k))) (add 5 (mul 5 pb (mul 5 pr0l pm7l)) (add 5 (mul 5 pr0u pm7u) (neg 5 pm8u)))))))))))))))))
private theorem zero8u : isZero 5 diff8u = true := by rfl
private theorem correct8u (b c d e j : ℝ) : (m8 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j)).u := by
  have h := interp_of_isZero 5 diff8u (point b c d e j) zero8u
  simp only [diff8u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k,scalem7k]
  linear_combination -h

private def diff8l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k (mul 5 pnine pm4k))) (add 5 (mul 5 pr3l pm4u) (add 5 (mul 5 pr3u pm4l) (add 5 (mul 5 pc (mul 5 pr2k (mul 5 pnine pm5k))) (add 5 (mul 5 pr2l pm5u) (add 5 (mul 5 pr2u pm5l) (add 5 (mul 5 pc (mul 5 pr1k (mul 5 pnine pm6k))) (add 5 (mul 5 pr1l pm6u) (add 5 (mul 5 pr1u pm6l) (add 5 (mul 5 pc (mul 5 pr0k (mul 5 pnine pm7k))) (add 5 (mul 5 pr0l pm7u) (add 5 (mul 5 pr0u pm7l) (neg 5 pm8l)))))))))))))
private theorem zero8l : isZero 5 diff8l = true := by rfl
private theorem correct8l (b c d e j : ℝ) : (m8 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j)).l := by
  have h := interp_of_isZero 5 diff8l (point b c d e j) zero8l
  simp only [diff8l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k,scalem7k]
  linear_combination -h

private def diff8k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k (mul 5 pnine pm4k)))) (add 5 (mul 5 pr3l pm4l) (add 5 (mul 5 pr3k pm4u) (add 5 (mul 5 pr3u (mul 5 pnine pm4k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k (mul 5 pnine pm5k)))) (add 5 (mul 5 pr2l pm5l) (add 5 (mul 5 pr2k pm5u) (add 5 (mul 5 pr2u (mul 5 pnine pm5k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k (mul 5 pnine pm6k)))) (add 5 (mul 5 pr1l pm6l) (add 5 (mul 5 pr1k pm6u) (add 5 (mul 5 pr1u (mul 5 pnine pm6k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm7k)))) (add 5 (mul 5 pr0l pm7l) (add 5 (mul 5 pr0k pm7u) (add 5 (mul 5 pr0u (mul 5 pnine pm7k)) (neg 5 (mul 5 pnine pm8k))))))))))))))))))
private theorem zero8k : isZero 5 diff8k = true := by rfl
private theorem correct8k (b c d e j : ℝ) : (m8 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j)).k := by
  have h := interp_of_isZero 5 diff8k (point b c d e j) zero8k
  simp only [diff8k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_m7l,eval_m7u,eval_m8k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  have scalem8k : (m8 b c d e j).k = 9*Certificate.w1G4 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k,scalem7k,scalem8k]
  linear_combination -h

theorem step8 (b c d e j : ℝ) : m8 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m7 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) :=
  rep_ext (correct8u b c d e j) (correct8l b c d e j) (correct8k b c d e j)

end SparseCubes.Chart.Chart1
