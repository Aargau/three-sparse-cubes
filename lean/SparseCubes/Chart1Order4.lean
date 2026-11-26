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

private def diff4u : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm0l)) (add 5 (mul 5 pc (mul 5 pr3l pm0k)) (add 5 (mul 5 pb (mul 5 pr3l pm0l)) (add 5 (mul 5 pr3u pm0u) (add 5 (mul 5 pc (mul 5 pr2k pm1l)) (add 5 (mul 5 pc (mul 5 pr2l pm1k)) (add 5 (mul 5 pb (mul 5 pr2l pm1l)) (add 5 (mul 5 pr2u pm1u) (add 5 (mul 5 pc (mul 5 pr1k pm2l)) (add 5 (mul 5 pc (mul 5 pr1l pm2k)) (add 5 (mul 5 pb (mul 5 pr1l pm2l)) (add 5 (mul 5 pr1u pm2u) (add 5 (mul 5 pc (mul 5 pr0k pm3l)) (add 5 (mul 5 pc (mul 5 pr0l pm3k)) (add 5 (mul 5 pb (mul 5 pr0l pm3l)) (add 5 (mul 5 pr0u pm3u) (neg 5 pm4u)))))))))))))))))
private theorem zero4u : isZero 5 diff4u = true := by rfl
private theorem correct4u (b c d e j : ℝ) : (m4 b c d e j).u = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j)).u := by
  have h := interp_of_isZero 5 diff4u (point b c d e j) zero4u
  simp only [diff4u,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_c,eval_m0k,eval_m0l,eval_m0u,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4u,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  simp only [linear4,Rep.add,Rep.mul]
  linear_combination -h

private def diff4l : Tower 5 := (add 5 (mul 5 pc (mul 5 pr3k pm0k)) (add 5 (mul 5 pr3l pm0u) (add 5 (mul 5 pr3u pm0l) (add 5 (mul 5 pc (mul 5 pr2k pm1k)) (add 5 (mul 5 pr2l pm1u) (add 5 (mul 5 pr2u pm1l) (add 5 (mul 5 pc (mul 5 pr1k pm2k)) (add 5 (mul 5 pr1l pm2u) (add 5 (mul 5 pr1u pm2l) (add 5 (mul 5 pc (mul 5 pr0k pm3k)) (add 5 (mul 5 pr0l pm3u) (add 5 (mul 5 pr0u pm3l) (neg 5 pm4l)))))))))))))
private theorem zero4l : isZero 5 diff4l = true := by rfl
private theorem correct4l (b c d e j : ℝ) : (m4 b c d e j).l = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j)).l := by
  have h := interp_of_isZero 5 diff4l (point b c d e j) zero4l
  simp only [diff4l,interp_add,eval_neg,interp_mul,eval_nine,eval_c,eval_m0k,eval_m0l,eval_m0u,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4l,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  simp only [linear4,Rep.add,Rep.mul]
  linear_combination -h

private def diff4k : Tower 5 := (add 5 (neg 5 (mul 5 pb (mul 5 pr3k pm0k))) (add 5 (mul 5 pr3l pm0l) (add 5 (mul 5 pr3k pm0u) (add 5 (mul 5 pr3u pm0k) (add 5 (neg 5 (mul 5 pb (mul 5 pr2k pm1k))) (add 5 (mul 5 pr2l pm1l) (add 5 (mul 5 pr2k pm1u) (add 5 (mul 5 pr2u pm1k) (add 5 (neg 5 (mul 5 pb (mul 5 pr1k pm2k))) (add 5 (mul 5 pr1l pm2l) (add 5 (mul 5 pr1k pm2u) (add 5 (mul 5 pr1u pm2k) (add 5 (neg 5 (mul 5 pb (mul 5 pr0k pm3k))) (add 5 (mul 5 pr0l pm3l) (add 5 (mul 5 pr0k pm3u) (add 5 (mul 5 pr0u pm3k) (neg 5 (mul 5 pnine pm4k))))))))))))))))))
private theorem zero4k : isZero 5 diff4k = true := by rfl
private theorem correct4k (b c d e j : ℝ) : (m4 b c d e j).k = (linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j)).k := by
  have h := interp_of_isZero 5 diff4k (point b c d e j) zero4k
  simp only [diff4k,interp_add,eval_neg,interp_mul,eval_nine,eval_b,eval_m0k,eval_m0l,eval_m0u,eval_m1k,eval_m1l,eval_m1u,eval_m2k,eval_m2l,eval_m2u,eval_m3k,eval_m3l,eval_m3u,eval_m4k_unscaled,eval_r0k,eval_r0l,eval_r0u,eval_r1k,eval_r1l,eval_r1u,eval_r2k,eval_r2l,eval_r2u,eval_r3k,eval_r3l,eval_r3u] at h
  have scalem4k : (m4 b c d e j).k = 9*Certificate.w1G0 b c d e j := rfl
  simp only [linear4,Rep.add,Rep.mul,scalem4k]
  linear_combination -h

theorem step4 (b c d e j : ℝ) : m4 b c d e j = linear4 b c (r0 b c d e j) (r1 b c d e j) (r2 b c d e j) (r3 b c d e j) (m3 b c d e j) (m2 b c d e j) (m1 b c d e j) (m0 b c d e j) :=
  rep_ext (correct4u b c d e j) (correct4l b c d e j) (correct4k b c d e j)

end SparseCubes.Chart.Chart1
