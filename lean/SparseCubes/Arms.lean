import SparseCubes.Normalized
import SparseCubes.Algebra
import SparseCubes.Degenerate

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section

def Arm.value (g : Arm) (r : ℝ) : ℝ := g.leftMass r + g.rightMass r
def Arm.Genuine (g : Arm) : Prop := g.A ≠ 0 ∧ g.B ≠ 0 ∧ g.left ≠ g.right

theorem genuine_arm (P : ℝ[X]) (h : P.support.card = 2) :
    ∃ g : Arm, g.poly = P ∧ g.Genuine := by
  obtain ⟨k,l,hkl,hs⟩ := Finset.card_eq_two.mp h
  refine ⟨⟨k,l,P.coeff k,P.coeff l⟩, ?_, ?_⟩
  · simpa [Arm.poly,hs,hkl] using P.as_sum_support_C_mul_X_pow.symm
  · exact ⟨Polynomial.mem_support_iff.mp (by simp [hs]),
      Polynomial.mem_support_iff.mp (by simp [hs]), hkl⟩

theorem Arm.variance_ne (g : Arm) (r : ℝ) (hr : r ≠ 0) (hg : g.Genuine)
    (hval : g.value r ≠ 0) : g.variance r ≠ 0 := by
  have hL : g.leftMass r ≠ 0 := mul_ne_zero hg.1 (pow_ne_zero _ hr)
  have hR : g.rightMass r ≠ 0 := mul_ne_zero hg.2.1 (pow_ne_zero _ hr)
  have hn : (g.left:ℝ) ≠ g.right := by exact_mod_cast hg.2.2
  have hsum : g.leftMass r + g.rightMass r ≠ 0 := hval
  have ha : 1 - g.leftMass r/(g.leftMass r+g.rightMass r) ≠ 0 := by
    rw [← div_self hsum, ← sub_div]
    simpa using div_ne_zero hR hsum
  exact mul_ne_zero (mul_ne_zero (div_ne_zero hL hsum) ha) (pow_ne_zero _ (sub_ne_zero.mpr hn))

def total (s : Fin 3 → ℝ) (g : Fin 3 → Arm) : ℝ[X] :=
    ∑ i, C (s i) * (g i).poly^3

def LowMoments (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) : Prop :=
    ∀ n < 10, ∀ t : ℝ, (∑ i, s i * moment (3*t) r n ((g i).poly^3)) = 0

theorem low_of_ten (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ)
    (h : 10 ≤ (total s g).rootMultiplicity r) : LowMoments s g r := by
  intro n hn t
  simpa only [total, moment_sum, moment_C_mul] using
    moment_eq_zero_of_lt_rootMultiplicity (3*t) r (total s g) (lt_of_lt_of_le hn h)

theorem low_perm (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (h : LowMoments s g r)
    (e : Equiv.Perm (Fin 3)) : LowMoments (s ∘ e) (g ∘ e) r := by
  intro n hn t
  exact (Equiv.sum_comp e (fun i => s i * moment (3*t) r n ((g i).poly^3))).trans (h n hn t)

theorem total_perm (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (e : Equiv.Perm (Fin 3)) :
    total (s ∘ e) (g ∘ e) = total s g :=
  Equiv.sum_comp e (fun i => C (s i) * (g i).poly^3)

/-- The scalar moment data for all nonvanishing arms, with an arbitrary frequency origin. -/
theorem normalized_low (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ)
    (hn : ∀ i, (g i).value r ≠ 0) (h : LowMoments s g r) (t : ℝ) (n : ℕ) (hlt : n < 10) :
    (∑ i, (s i * ((g i).value r)^3) *
      Chart.rawMoment ((g i).mean r-t) ((g i).variance r) ((g i).skew r) n) = 0 := by
  convert h n hlt t using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [arm_normalized _ _ _ _ (hn i)]
  simp only [Arm.value, mul_assoc]

theorem centered_raw (s v : ℝ) (n : ℕ) (hn : n ≤ 6) :
    Chart.rawMoment 0 v s n = centeredCubeMoment n s v := by
  interval_cases n <;> norm_num [Chart.rawMoment, centeredCubeMoment] <;> ring

/-- When all three nonvanishing arms have the same mean, the ten constraints
force the signed polynomial itself to vanish. -/
theorem same_mean_zero (s : Fin 3 → ℝ) (g : Fin 3 → Arm) (r : ℝ) (hr : r ≠ 0)
    (hs : ∀ i, s i ≠ 0) (hg : ∀ i, (g i).Genuine) (hn : ∀ i, (g i).value r ≠ 0)
    (he : ∀ i, (g i).mean r = (g 0).mean r) (hl : LowMoments s g r) : total s g = 0 := by
  let m := fun i => s i * ((g i).value r)^3
  let V := fun i => (g i).variance r
  let S := fun i => (g i).skew r
  have hm (i) : m i ≠ 0 := mul_ne_zero (hs i) (pow_ne_zero _ (hn i))
  have hv (i) := Arm.variance_ne (g i) r hr (hg i) (hn i)
  have hraw (n : ℕ) (hlt : n < 10) :
      m 0 * Chart.rawMoment 0 (V 0) (S 0) n + m 1 * Chart.rawMoment 0 (V 1) (S 1) n +
      m 2 * Chart.rawMoment 0 (V 2) (S 2) n = 0 := by
    simpa only [Fin.sum_univ_three, he, sub_self, m, V, S] using
      normalized_low s g r hn hl ((g 0).mean r) n hlt
  have hm0 : m 0 + m 1 + m 2 = 0 := by simpa [Chart.rawMoment] using hraw 0 (by decide)
  obtain ⟨p,hp,hq,hmix⟩ := mixtureWeights _ _ _ (hm 0) (hm 1) (hm 2) hm0
  obtain ⟨hS0,hS1,hV0,hV1⟩ := equalMean_mixture p (S 0) (S 1) (S 2) (V 0) (V 1) (V 2)
    hp hq (hv 0) (hv 1) (hv 2) (by
      intro n hn'
      apply hmix
      simpa only [← centered_raw _ _ n hn'] using hraw n (by omega))
  apply eq_zero_of_moments (3*(g 0).mean r) r hr
  intro n _
  simp only [total, moment_sum, moment_C_mul]
  simp only [Fin.sum_univ_three]
  rw [arm_normalized _ _ _ _ (hn 0), arm_normalized _ _ _ _ (hn 1),
      arm_normalized _ _ _ _ (hn 2), he 1, he 2, sub_self]
  simp only [← mul_assoc]
  change m 0 * ((Chart.rawMoment 0 (V 0) (S 0) n)) +
    m 1 * (Chart.rawMoment 0 (V 1) (S 1) n) + m 2 * (Chart.rawMoment 0 (V 2) (S 2) n) = 0
  rw [hS0,hS1,hV0,hV1,← add_mul,← add_mul,hm0,zero_mul]

end
end SparseCubes
