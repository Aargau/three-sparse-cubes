import SparseCubes.Chart0Steps
import SparseCubes.Certificate0

namespace SparseCubes.Chart.Chart0

variable (b c d e j z : ℝ)

theorem ev0 (hz : z^3=b*z+c) : (m0 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 0 := by
  rw [base0]
  exact eval_initialRep b c d e j 0 z hz 0

theorem ev1 (hz : z^3=b*z+c) : (m1 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 1 := by
  rw [base1]
  exact eval_initialRep b c d e j 0 z hz 1

theorem ev2 (hz : z^3=b*z+c) : (m2 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 2 := by
  rw [base2]
  exact eval_initialRep b c d e j 0 z hz 2

theorem ev3 (hz : z^3=b*z+c) : (m3 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 3 := by
  rw [base3]
  exact eval_initialRep b c d e j 0 z hz 3

theorem ev4 (hz : z^3=b*z+c) : (m4 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 4 := by
  rw [step4,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 0 _ _ _ _ (ev3 b c d e j z hz) (ev2 b c d e j z hz) (ev1 b c d e j z hz) (ev0 b c d e j z hz)

theorem ev5 (hz : z^3=b*z+c) : (m5 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 5 := by
  rw [step5,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 1 _ _ _ _ (ev4 b c d e j z hz) (ev3 b c d e j z hz) (ev2 b c d e j z hz) (ev1 b c d e j z hz)

theorem ev6 (hz : z^3=b*z+c) : (m6 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 6 := by
  rw [step6,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 2 _ _ _ _ (ev5 b c d e j z hz) (ev4 b c d e j z hz) (ev3 b c d e j z hz) (ev2 b c d e j z hz)

theorem ev7 (hz : z^3=b*z+c) : (m7 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 7 := by
  rw [step7,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 3 _ _ _ _ (ev6 b c d e j z hz) (ev5 b c d e j z hz) (ev4 b c d e j z hz) (ev3 b c d e j z hz)

theorem ev8 (hz : z^3=b*z+c) : (m8 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 8 := by
  rw [step8,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 4 _ _ _ _ (ev7 b c d e j z hz) (ev6 b c d e j z hz) (ev5 b c d e j z hz) (ev4 b c d e j z hz)

theorem ev9 (hz : z^3=b*z+c) : (m9 b c d e j).eval b z = rawMoment z (variance b d e z) (skew b d e j 0 z) 9 := by
  rw [step9,rec0,rec1,rec2,rec3]
  exact raw_step b c d e j 0 z hz 5 _ _ _ _ (ev8 b c d e j z hz) (ev7 b c d e j z hz) (ev6 b c d e j z hz) (ev5 b c d e j z hz)

theorem excludes : Case 0 := by
  intro m x d e j hx hc hv hraw hm
  let b := coeffB x
  let c := coeffC x
  have h0 := hraw 0 (by decide)
  change mass m (fun _ => 1) = 0 at h0
  have h1m := hraw 1 (by decide)
  have h1 : mass m x = 0 := by
    simp only [mass,Fin.sum_univ_three,rawMoment] at h1m ⊢
    linear_combination (1/3:ℝ)*h1m
  have hk := mass_quadratic_ne m x b hm hx h0 h1
  apply chartH_ne x d e j hc hx hv
  apply Certificate.w0_excludes
  · have h : mass m (fun i => (m4 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 4) :=
               congrArg (mass m) (funext (fun i => ev4 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 4 (by decide)
    rw [mass_rep m x b (m4 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G0 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m5 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 5) :=
               congrArg (mass m) (funext (fun i => ev5 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 5 (by decide)
    rw [mass_rep m x b (m5 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G1 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m6 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 6) :=
               congrArg (mass m) (funext (fun i => ev6 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 6 (by decide)
    rw [mass_rep m x b (m6 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G2 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m7 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 7) :=
               congrArg (mass m) (funext (fun i => ev7 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 7 (by decide)
    rw [mass_rep m x b (m7 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G3 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m8 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 8) :=
               congrArg (mass m) (funext (fun i => ev8 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 8 (by decide)
    rw [mass_rep m x b (m8 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G4 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)
  · have h : mass m (fun i => (m9 b c d e j).eval b (x i))=0 := by
      calc _ = mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j 0 (x i)) 9) :=
               congrArg (mass m) (funext (fun i => ev9 b c d e j (x i) (mean_cubic x hc i)))
           _ = 0 := hraw 9 (by decide)
    rw [mass_rep m x b (m9 b c d e j) h0 h1] at h
    have hk0 := (mul_eq_zero.mp h).resolve_right hk
    change 9*Certificate.w0G5 b c d e j = 0 at hk0
    exact (mul_eq_zero.mp hk0).resolve_left (by norm_num)

end SparseCubes.Chart.Chart0
