import SparseCubes.Degenerate
import SparseCubes.Normalized
import SparseCubes.Algebra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace SparseCubes
open Polynomial
noncomputable section

/-- The signed first exponential derivative, cubed, supplies the mass after a triple zero. -/
def Arm.vanWeight (g : Arm) (r : ℝ) := (g.leftMass r*((g.left:ℝ)-g.right))^3
def Arm.vanMean (g : Arm) : ℝ := 3*((g.left:ℝ)+g.right)/2
def Arm.vanVariance (g : Arm) : ℝ := ((g.left:ℝ)-g.right)^2/4

theorem centeredCubeMoment_raw (n : ℕ) (hn : n≤9) (s v : ℝ) :
    Chart.rawMoment 0 v s n = centeredCubeMoment n s v := by
  interval_cases n <;> norm_num [Chart.rawMoment,centeredCubeMoment] <;> ring

theorem arm_vanMoment (g : Arm) (r t : ℝ) (hg : g.leftMass r+g.rightMass r=0)
    (n : ℕ) (hn : n≤6) :
    moment (3*t) r (n+3) (g.poly^3) = g.vanWeight r*
      (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3))*uniformCubeMoment n (g.vanMean-3*t) g.vanVariance := by
  have hr : g.rightMass r = -g.leftMass r := by linarith
  rw [moment_arm_cube,hr]
  interval_cases n <;> norm_num [cubeFour,Arm.vanWeight,Arm.vanMean,Arm.vanVariance,uniformCubeMoment] <;> ring

theorem arm_vanMoment_low (g : Arm) (r t : ℝ) (hg : g.leftMass r+g.rightMass r=0)
    (n : ℕ) (hn : n<3) : moment (3*t) r n (g.poly^3)=0 := by
  have hr : g.rightMass r = -g.leftMass r := by linarith
  rw [moment_arm_cube,hr]
  interval_cases n <;> simp [cubeFour] <;> ring

private def vanishingSequence (m v : ℝ) : ℕ → ℝ
  | 0 | 1 | 2 => 0
  | 3 => 6
  | n+4 =>
    let s := 2*m/3
    let p := (m/3)^2-v
    let k := 3*s
    let o := 9*p
    let i := 2*s^2+p
    2*k*vanishingSequence m v (n+3) - (k^2+o+i)*vanishingSequence m v (n+2) +
      k*(o+i)*vanishingSequence m v (n+1) - o*i*vanishingSequence m v n

private theorem vanishingSequence_four (A a b : ℝ) (n : ℕ) :
    cubeFour A (-A) a b n = (A*(a-b))^3*vanishingSequence (3*(a+b)/2) ((a-b)^2/4) n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 | 3 => simp [cubeFour,vanishingSequence]; ring
    | n+4 =>
      rw [cubeFour_step,vanishingSequence]
      rw [ih (n+3) (by omega),ih (n+2) (by omega),ih (n+1) (by omega),ih n (by omega)]
      ring

private theorem arm_vanMoment_all (g : Arm) (r : ℝ) (hg : g.leftMass r+g.rightMass r=0)
    (n : ℕ) : moment 0 r n (g.poly^3) =
      g.vanWeight r * vanishingSequence g.vanMean g.vanVariance n := by
  have hr : g.rightMass r = -g.leftMass r := by linarith
  simpa [hr,vanishingSequence_four,Arm.vanWeight,Arm.vanMean,Arm.vanVariance]
    using moment_arm_cube g r 0 n

/-- If all three arms vanish at the root, ten zero moments force all moments to vanish. -/
theorem allVanishing_arms (a b c : Arm) (u v w r : ℝ)
    (ha : a.leftMass r+a.rightMass r=0) (hb : b.leftMass r+b.rightMass r=0)
    (hc : c.leftMass r+c.rightMass r=0)
    (hu : u*a.vanWeight r≠0) (hv : v*b.vanWeight r≠0) (hw : w*c.vanWeight r≠0)
    (H : ∀ n : ℕ, n<10 → ∀ t : ℝ, u*moment (3*t) r n (a.poly^3) +
        v*moment (3*t) r n (b.poly^3) + w*moment (3*t) r n (c.poly^3)=0) :
    ∀ n : ℕ, u*moment 0 r n (a.poly^3) + v*moment 0 r n (b.poly^3) +
      w*moment 0 r n (c.poly^3)=0 := by
  have U (n : ℕ) (hn : n≤6) :
      (u*a.vanWeight r)*uniformCubeMoment n a.vanMean a.vanVariance +
      (v*b.vanWeight r)*uniformCubeMoment n b.vanMean b.vanVariance +
      (w*c.vanWeight r)*uniformCubeMoment n c.vanMean c.vanVariance=0 := by
    have e := H (n+3) (by omega) 0
    rw [arm_vanMoment a r 0 ha n hn,arm_vanMoment b r 0 hb n hn,arm_vanMoment c r 0 hc n hn] at e
    simp only [mul_zero,sub_zero] at e
    have hfac : (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3))≠0 := by positivity
    apply (mul_eq_zero.mp ?_).resolve_left hfac
    linear_combination e
  have sumw := U 0 (by decide)
  simp only [uniformCubeMoment,mul_one] at sumw
  obtain ⟨p,hp,hq,hm⟩ := mixtureWeights _ _ _ hu hv hw sumw
  obtain ⟨haM,hbM,haV,hbV⟩ := threeVanish_mixture p _ _ _ _ _ _ hp hq (fun n hn => hm _ _ _ (U n hn))
  intro n
  rw [arm_vanMoment_all _ _ ha,arm_vanMoment_all _ _ hb,arm_vanMoment_all _ _ hc,haM,hbM,haV,hbV]
  linear_combination vanishingSequence c.vanMean c.vanVariance n * sumw

/-- Two nonvanishing arms and a single vanishing arm cannot have ten zero moments. -/
theorem oneVanishing_arms (a b c : Arm) (u v w r : ℝ)
    (ha : a.leftMass r+a.rightMass r≠0) (hb : b.leftMass r+b.rightMass r≠0)
    (hc : c.leftMass r+c.rightMass r=0)
    (hu : u≠0) (hv : v≠0) (hw : w*c.vanWeight r≠0) (hvar : a.variance r≠0)
    (H : ∀ n : ℕ, n<10 → ∀ t : ℝ, u*moment (3*t) r n (a.poly^3) +
        v*moment (3*t) r n (b.poly^3) + w*moment (3*t) r n (c.poly^3)=0) : False := by
  let A := u*(a.leftMass r + a.rightMass r)^3
  let B := v*(b.leftMass r + b.rightMass r)^3
  let C := w*c.vanWeight r
  have hA : A≠0 := mul_ne_zero hu (pow_ne_zero _ ha)
  have hB : B≠0 := mul_ne_zero hv (pow_ne_zero _ hb)
  have raw (n : ℕ) (hn : n<10) (t : ℝ) :
      A*Chart.rawMoment (a.mean r-t) (a.variance r) (a.skew r) n +
      B*Chart.rawMoment (b.mean r-t) (b.variance r) (b.skew r) n +
      w*moment (3*t) r n (c.poly^3)=0 := by
    have e := H n hn t
    rw [arm_normalized a r t n ha,arm_normalized b r t n hb] at e
    dsimp [A,B]; linear_combination e
  have h0 := raw 0 (by decide) 0
  rw [arm_vanMoment_low _ _ _ hc _ (by decide)] at h0
  simp only [Chart.rawMoment, mul_one,mul_zero,add_zero] at h0
  have Bval : B= -A := by linarith
  have h1 := raw 1 (by decide) 0
  rw [arm_vanMoment_low _ _ _ hc _ (by decide),Bval] at h1
  simp only [Chart.rawMoment, sub_zero,mul_zero,add_zero] at h1
  have sameMean : b.mean r=a.mean r := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hA
    linear_combination -h1/3
  have centered (n : ℕ) (hn : n<10) :
      A*centeredCubeMoment n (a.skew r) (a.variance r) -
      A*centeredCubeMoment n (b.skew r) (b.variance r) +
      w*moment (3*a.mean r) r n (c.poly^3)=0 := by
    have e := raw n hn (a.mean r)
    rw [Bval,sameMean] at e
    simp only [sub_self,centeredCubeMoment_raw n (by omega)] at e
    linear_combination e
  have h2 := centered 2 (by decide)
  rw [arm_vanMoment_low _ _ _ hc _ (by decide)] at h2
  simp only [centeredCubeMoment,mul_zero,add_zero] at h2
  have sameVar : b.variance r=a.variance r := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp ?_).resolve_left hA
    linear_combination -h2/3
  let h := (a.skew r+b.skew r)/2
  let d := (a.skew r-b.skew r)/2
  have sa : h+d=a.skew r := by dsimp [h,d]; ring
  have sb : h-d=b.skew r := by dsimp [h,d]; ring
  have e3 := centered 3 (by decide)
  rw [arm_vanMoment _ _ _ hc 0 (by decide),sameVar] at e3
  norm_num [centeredCubeMoment,uniformCubeMoment] at e3
  have relation : C = -A*(a.variance r)*d := by dsimp [C,d]; linear_combination e3/6
  have hd : d≠0 := by
    intro h0
    exact hw (show C=0 by rw [relation,h0,mul_zero])
  apply oneVanish_excludes h d (a.variance r) (c.vanMean-3*a.mean r) c.vanVariance hd hvar
  intro n hn
  have e := centered (n+3) (by omega)
  rw [arm_vanMoment _ _ _ hc n hn,sameVar] at e
  rw [sa,sb]
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp ?_).resolve_left hA
  dsimp [C] at relation
  linear_combination e -
    (((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)*uniformCubeMoment n (c.vanMean-3*a.mean r) c.vanVariance)*relation

end
end SparseCubes
