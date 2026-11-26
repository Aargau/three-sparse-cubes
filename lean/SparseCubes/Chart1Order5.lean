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

private def diff5u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm1l)) (add 5 (mul 5 pc (mul 5 pr3l pm1k)) (add 5 (mul 5 pb (mul 5 pr3l pm1l)) (add 5 (mul 5 pr3u pm1u) (add 5 (mul 5 pc (mul 5 pr2k pm2l)) (add 5 (mul 5 pc (mul 5 pr2l pm2k)) (add 5 (mul 5 pb (mul 5 pr2l pm2l)) (add 5 (mul 5 pr2u pm2u) (add 5 (mul 5 pc (mul 5 pr1k pm3l)) (add 5 (mul 5 pc (mul 5 pr1l pm3k)) (add 5 (mul 5 pb (mul 5 pr1l pm3l)) (add 5 (mul 5 pr1u pm3u) (add 5 (mul 5 pc (mul 5 pr0k pm4l)) (add 5 (mul 5 pc (mul 5 pr0l (mul 5 pnine pm4k))) (add 5 (mul 5 pb (mul 5 pr0l pm4l)) (add 5 (mul 5 pr0u pm4u) (neg 5 pm5u)))))))))))))))))
private theorem zero5u : isZero 5 diff5u = true := by rfl
private theorem correct5u (b c d e j : ℝ) : (m5 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j)).u := by
  have h := interp_of_isZero 5 diff5u (point b c d e j) zero5u
  simp only [diff5u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k]
  linear_combination -h

private def diff5l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm1k)) (add 5 (mul 5 pr3l pm1u) (add 5 (mul 5 pr3u pm1l) (add 5 (mul 5 pc (mul 5 pr2k pm2k)) (add 5 (mul 5 pr2l pm2u) (add 5 (mul 5 pr2u pm2l) (add 5 (mul 5 pc (mul 5 pr1k pm3k)) (add 5 (mul 5 pr1l pm3u) (add 5 (mul 5 pr1u pm3l) (add 5 (mul 5 pc (mul 5 pr0k (mul 5 pnine pm4k))) (add 5 (mul 5 pr0l pm4u) (add 5 (mul 5 pr0u pm4l) (neg 5 pm5l)))))))))))))
private theorem zero5l : isZero 5 diff5l = true := by rfl
private theorem correct5l (b c d e j : ℝ) : (m5 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j)).l := by
  have h := interp_of_isZero 5 diff5l (point b c d e j) zero5l
  simp only [diff5l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k]
  linear_combination -h

private def diff5k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k pm1k))) (add 5 (mul 5 pr3l pm1l) (add 5 (mul 5 pr3k pm1u) (add 5 (mul 5 pr3u pm1k) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k pm2k))) (add 5 (mul 5 pr2l pm2l) (add 5 (mul 5 pr2k pm2u) (add 5 (mul 5 pr2u pm2k) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k pm3k))) (add 5 (mul 5 pr1l pm3l) (add 5 (mul 5 pr1k pm3u) (add 5 (mul 5 pr1u pm3k) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k (mul 5 pnine pm4k)))) (add 5 (mul 5 pr0l pm4l) (add 5 (mul 5 pr0k pm4u) (add 5 (mul 5 pr0u (mul 5 pnine pm4k)) (neg 5 (mul 5 pnine pm5k))))))))))))))))))
private theorem zero5k : isZero 5 diff5k = true := by rfl
private theorem correct5k (b c d e j : ℝ) : (m5 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j)).k := by
  have h := interp_of_isZero 5 diff5k (point b c d e j) zero5k
  simp only [diff5k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_m4l,eval_m4u,eval_m5k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  have scalem5k : (m5 b c d e j).k = 9*Certificate.w1G1 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k,scalem5k]
  linear_combination -h

theorem step5 (b c d e j : ℝ) : m5 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m4 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) :=
  rep_ext (correct5u b c d e j) (correct5l b c d e j) (correct5k b c d e j)

end SparseCubes.Chart.Chart1
