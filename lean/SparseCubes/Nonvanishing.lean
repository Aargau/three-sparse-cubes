import SparseCubes.Arms

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section

/-- An all-nonvanishing tenfold root either gives the zero polynomial or
satisfies the full distinct-mean chart, including the open-set hypotheses. -/
theorem nonvanishing_cases (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hn : ∀ i, (g i).value r ≠ 0)
    (hl : LowMoments s g r) :
    total s g = 0 ∨ ∃ m x v u : Fin 3 → ℝ,
      (∀ i, m i ≠ 0) ∧ Function.Injective x ∧ (∀ i, v i ≠ 0) ∧
      (∑ i, x i) = 0 ∧ ∀ n < 10, ∑ i, m i * Chart.rawMoment (x i) (v i) (u i) n = 0 := by
  let t : ℝ := ((g 0).mean r+(g 1).mean r+(g 2).mean r)/3
  let x : Fin 3 → ℝ := fun i => (g i).mean r-t
  let m : Fin 3 → ℝ := fun i => s i*((g i).value r)^3
  let v : Fin 3 → ℝ := fun i => (g i).variance r
  let u : Fin 3 → ℝ := fun i => (g i).skew r
  have hm (i) : m i ≠ 0 := mul_ne_zero (hs i) (pow_ne_zero _ (hn i))
  have H (n : ℕ) (hn' : n<10) : ∑ i, m i * Chart.rawMoment (x i) (v i) (u i) n = 0 :=
    normalized_low s g r hn hl t n hn'
  have h0 : m 0+m 1+m 2=0 := by simpa only [Fin.sum_univ_three, Chart.rawMoment,mul_one] using H 0 (by decide)
  have h1 : m 0*x 0+m 1*x 1+m 2*x 2=0 := by
    have h := H 1 (by decide)
    simp only [Fin.sum_univ_three, Chart.rawMoment] at h
    linarith only [h]
  rcases three_nodes m x hm h0 h1 with he|hd
  · left
    apply same_mean_zero s g r hr hs hg hn _ hl
    intro i
    exact sub_left_inj.mp (he i)
  · right
    refine ⟨m,x,v,u,hm,hd,fun i => Arm.variance_ne _ _ hr (hg i) (hn i),?_,H⟩
    simp only [Fin.sum_univ_three,x,t]
    ring

end
end SparseCubes
