import SparseCubes.Arms
import SparseCubes.DegenerateArms

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section

theorem Arm.vanWeight_ne (g : Arm) (r : ℝ) (hr : r ≠ 0) (hg : g.Genuine) :
    g.vanWeight r ≠ 0 := by
  have hne : (g.left:ℝ) ≠ g.right := by exact_mod_cast hg.2.2
  exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero hg.1 (pow_ne_zero _ hr)) (sub_ne_zero.mpr hne))

theorem arm_eval (g : Arm) (r : ℝ) : g.poly.eval r = g.value r := by
  simp [Arm.poly, Arm.value, Arm.leftMass, Arm.rightMass]

theorem zero_of_third_vanishes (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hz : (g 2).value r = 0)
    (hl : LowMoments s g r) : total s g = 0 := by
  have hv (i) := mul_ne_zero (hs i) (Arm.vanWeight_ne (g i) r hr (hg i))
  have hsum (n : ℕ) (hn : n<10) (t : ℝ) := hl n hn t
  simp only [Fin.sum_univ_three] at hsum
  have hval := hsum 0 (by decide) 0
  simp only [moment, eval_pow, arm_eval, hz, zero_pow (by decide : 3 ≠ 0), mul_zero,add_zero] at hval
  by_cases h0 : (g 0).value r = 0
  · have h1 : (g 1).value r = 0 := by
      simpa [h0, hs 1] using hval
    have H := allVanishing_arms _ _ _ _ _ _ r h0 h1 hz (hv 0) (hv 1) (hv 2) hsum
    apply eq_zero_of_moments 0 r hr
    intro n _
    simp only [total, moment_sum, moment_C_mul]
    simpa only [Fin.sum_univ_three] using H n
  · have h1 : (g 1).value r ≠ 0 := by
      intro h1
      simpa [h1,hs 0,h0] using hval
    exact (oneVanishing_arms _ _ _ _ _ _ r h0 h1 hz (hs 0) (hs 1) (hv 2)
      (Arm.variance_ne _ _ hr (hg 0) h0) hsum).elim

theorem zero_of_any_vanishes (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hz : ∃ i, (g i).value r = 0)
    (hl : LowMoments s g r) : total s g = 0 := by
  obtain ⟨i, hi⟩ := hz
  let e := Equiv.swap i (2 : Fin 3)
  rw [← total_perm s g e]
  apply zero_of_third_vanishes (s ∘ e) (g ∘ e) r hr (fun j => hs _) (fun j => hg _)
  · simpa [e,Function.comp_def] using hi
  · exact low_perm s g r hl e

end
end SparseCubes
