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

private def diff6u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm2l)) (add 5 (mul 5 pc (mul 5 pr3l pm2k)) (add 5 (mul 5 pb (mul 5 pr3l pm2l)) (add 5 (mul 5 pr3u pm2u) (add 5 (mul 5 pc (mul 5 pr2k pm3l)) (add 5 (mul 5 pc (mul 5 pr2l pm3k)) (add 5 (mul 5 pb (mul 5 pr2l pm3l)) (add 5 (mul 5 pr2u pm3u) (add 5 (mul 5 pc (mul 5 pr1k pm4l)) (add 5 (mul 5 pc (mul 5 pr1l (mul 5 pnine pm4k))) (add 5 (mul 5 pb (mul 5 pr1l pm4l)) (add 5 (mul 5 pr1u pm4u) (add 5 (mul 5 pc (mul 5 pr0k pm5l)) (add 5 (mul 5 pc (mul 5 pr0l (mul 5 pnine pm5k))) (add 5 (mul 5 pb (mul 5 pr0l pm5l)) (add 5 (mul 5 pr0u pm5u) (neg 5 pm6u)))))))))))))))))
private theorem zero6u : isZero 5 diff6u = true := by rfl
private theorem correct6u (b c d e j : ℝ) : (m6 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j)).u := by
  have h := interp_of_isZero 5 diff6u (point b c d e j) zero6u
  simp only [diff6u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k]
  linear_combination -h

private def diff6l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm2k)) (add 5 (mul 5 pr3l pm2u) (add 5 (mul 5 pr3u pm2l) (add 5 (mul 5 pc (mul 5 pr2k pm3k)) (add 5 (mul 5 pr2l pm3u) (add 5 (mul 5 pr2u pm3l) (add 5 (mul 5 pc (mul 5 pr1k (mul 5 pnine pm4k))) (add 5 (mul 5 pr1l pm4u) (add 5 (mul 5 pr1u pm4l) (add 5 (mul 5 pc (mul 5 pr0k (mul 5 pnine pm5k))) (add 5 (mul 5 pr0l pm5u) (add 5 (mul 5 pr0u pm5l) (neg 5 pm6l)))))))))))))
private theorem zero6l : isZero 5 diff6l = true := by rfl
private theorem correct6l (b c d e j : ℝ) : (m6 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j)).l := by
  have h := interp_of_isZero 5 diff6l (point b c d e j) zero6l
  simp only [diff6l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k]
  linear_combination -h

private def diff6k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k pm2k))) (add 5 (mul 5 pr3l pm2l) (add 5 (mul 5 pr3k pm2u) (add 5 (mul 5 pr3u pm2k) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k pm3k))) (add 5 (mul 5 pr2l pm3l) (add 5 (mul 5 pr2k pm3u) (add 5 (mul 5 pr2u pm3k) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k (mul 5 pnine pm4k)))) (add 5 (mul 5 pr1l pm4l) (add 5 (mul 5 pr1k pm4u) (add 5 (mul 5 pr1u (mul 5 pnine pm4k)) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm5k)))) (add 5 (mul 5 pr0l pm5l) (add 5 (mul 5 pr0k pm5u) (add 5 (mul 5 pr0u (mul 5 pnine pm5k)) (neg 5 (mul 5 pnine pm6k))))))))))))))))))
private theorem zero6k : isZero 5 diff6k = true := by rfl
private theorem correct6k (b c d e j : ℝ) : (m6 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j)).k := by
  have h := interp_of_isZero 5 diff6k (point b c d e j) zero6k
  simp only [diff6k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_m5l,eval_m5u,eval_m6k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  have scalem6k : (m6 b c d e j).k = 9*Certificate.w1G2 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k,scalem6k]
  linear_combination -h

theorem step6 (b c d e j : ℝ) : m6 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m5 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) :=
  rep_ext (correct6u b c d e j) (correct6l b c d e j) (correct6k b c d e j)

end SparseCubes.Chart.Chart1
