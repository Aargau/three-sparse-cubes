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

private def diff7u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm3l)) (add 5 (mul 5 pc (mul 5 pr3l pm3k)) (add 5 (mul 5 pb (mul 5 pr3l pm3l)) (add 5 (mul 5 pr3u pm3u) (add 5 (mul 5 pc (mul 5 pr2k pm4l)) (add 5 (mul 5 pc (mul 5 pr2l (mul 5 pnine pm4k))) (add 5 (mul 5 pb (mul 5 pr2l pm4l)) (add 5 (mul 5 pr2u pm4u) (add 5 (mul 5 pc (mul 5 pr1k pm5l)) (add 5 (mul 5 pc (mul 5 pr1l (mul 5 pnine pm5k))) (add 5 (mul 5 pb (mul 5 pr1l pm5l)) (add 5 (mul 5 pr1u pm5u) (add 5 (mul 5 pc (mul 5 pr0k pm6l)) (add 5 (mul 5 pc (mul 5 pr0l (mul 5 pnine pm6k))) (add 5 (mul 5 pb (mul 5 pr0l pm6l)) (add 5 (mul 5 pr0u pm6u) (neg 5 pm7u)))))))))))))))))
private theorem zero7u : isZero 5 diff7u = true := by rfl
private theorem correct7u (b c d e j : ℝ) : (m7 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j)).u := by
  have h := interp_of_isZero 5 diff7u (point b c d e j) zero7u
  simp only [diff7u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k]
  linear_combination -h

private def diff7l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm3k)) (add 5 (mul 5 pr3l pm3u) (add 5 (mul 5 pr3u pm3l) (add 5 (mul 5 pc (mul 5 pr2k (mul 5 pnine pm4k))) (add 5 (mul 5 pr2l pm4u) (add 5 (mul 5 pr2u pm4l) (add 5 (mul 5 pc (mul 5 pr1k (mul 5 pnine pm5k))) (add 5 (mul 5 pr1l pm5u) (add 5 (mul 5 pr1u pm5l) (add 5 (mul 5 pc (mul 5 pr0k (mul 5 pnine pm6k))) (add 5 (mul 5 pr0l pm6u) (add 5 (mul 5 pr0u pm6l) (neg 5 pm7l)))))))))))))
private theorem zero7l : isZero 5 diff7l = true := by rfl
private theorem correct7l (b c d e j : ℝ) : (m7 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j)).l := by
  have h := interp_of_isZero 5 diff7l (point b c d e j) zero7l
  simp only [diff7l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k]
  linear_combination -h

private def diff7k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k pm3k))) (add 5 (mul 5 pr3l pm3l) (add 5 (mul 5 pr3k pm3u) (add 5 (mul 5 pr3u pm3k) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k (mul 5 pnine pm4k)))) (add 5 (mul 5 pr2l pm4l) (add 5 (mul 5 pr2k pm4u) (add 5 (mul 5 pr2u (mul 5 pnine pm4k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k (mul 5 pnine pm5k)))) (add 5 (mul 5 pr1l pm5l) (add 5 (mul 5 pr1k pm5u) (add 5 (mul 5 pr1u (mul 5 pnine pm5k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm6k)))) (add 5 (mul 5 pr0l pm6l) (add 5 (mul 5 pr0k pm6u) (add 5 (mul 5 pr0u (mul 5 pnine pm6k)) (neg 5 (mul 5 pnine pm7k))))))))))))))))))
private theorem zero7k : isZero 5 diff7k = true := by rfl
private theorem correct7k (b c d e j : ℝ) : (m7 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j)).k := by
  have h := interp_of_isZero 5 diff7k (point b c d e j) zero7k
  simp only [diff7k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_m6l,eval_m6u,eval_m7k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  have scalem7k : (m7 b c d e j).k = 9*Certificate.w1G3 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k,scalem7k]
  linear_combination -h

theorem step7 (b c d e j : ℝ) : m7 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m6 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) :=
  rep_ext (correct7u b c d e j) (correct7l b c d e j) (correct7k b c d e j)

end SparseCubes.Chart.Chart1
