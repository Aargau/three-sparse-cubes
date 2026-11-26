import SparseCubes.Binomial
import SparseCubes.ChartMoment

namespace SparseCubes
noncomputable section

/-- The fourth-order equation shared by the frequencies of a binomial cube. -/
theorem cubeFour_step (A B a b : ℝ) (n : ℕ) :
    cubeFour A B a b (n+4) =
      2*(3*(a+b))*cubeFour A B a b (n+3) -
      ((3*(a+b))^2 + 9*(a*b) + (2*(a+b)^2+a*b))*cubeFour A B a b (n+2) +
      (3*(a+b))*(9*(a*b)+(2*(a+b)^2+a*b))*cubeFour A B a b (n+1) -
      (9*(a*b))*(2*(a+b)^2+a*b)*cubeFour A B a b n := by
  simp only [cubeFour, pow_add]
  ring

/-- The chart recurrence is exactly the four-frequency expansion for a normalized binomial. -/
theorem normalized_cubeFour (A a b : ℝ) (n : ℕ) :
    cubeFour A (1-A) a b n = Chart.rawMoment (A*a+(1-A)*b)
      (A*(1-A)*(a-b)^2) (a+b-2*(A*a+(1-A)*b)) n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 | 3 => simp only [cubeFour, Chart.rawMoment]; ring
    | n+4 =>
      rw [cubeFour_step, Chart.rawMoment]
      simp only [show 2*(A*a+(1-A)*b)+(a+b-2*(A*a+(1-A)*b)) = a+b by ring,
        show (A*a+(1-A)*b)^2 + (A*a+(1-A)*b)*(a+b-2*(A*a+(1-A)*b)) -
          A*(1-A)*(a-b)^2 = a*b by ring]
      rw [ih (n+3) (by omega), ih (n+2) (by omega), ih (n+1) (by omega), ih n (by omega)]

theorem cubeFour_scale (k A B a b : ℝ) (n : ℕ) :
    cubeFour (k*A) (k*B) a b n = k^3*cubeFour A B a b n := by
  unfold cubeFour
  ring

/-- Centered variance, unchanged by frequency translation. -/
def Arm.variance (g : Arm) (r : ℝ) : ℝ :=
  let t := g.leftMass r / (g.leftMass r + g.rightMass r)
  t*(1-t)*((g.left:ℝ)-g.right)^2

def Arm.mean (g : Arm) (r : ℝ) : ℝ :=
  let t := g.leftMass r / (g.leftMass r + g.rightMass r)
  t*g.left+(1-t)*g.right

def Arm.skew (g : Arm) (r : ℝ) : ℝ := (g.left:ℝ)+g.right-2*g.mean r

theorem arm_normalized (g : Arm) (r t : ℝ) (n : ℕ)
    (hne : g.leftMass r + g.rightMass r ≠ 0) :
    moment (3*t) r n (g.poly^3) =
      (g.leftMass r + g.rightMass r)^3 *
      Chart.rawMoment (g.mean r-t) (g.variance r) (g.skew r) n := by
  let L := g.leftMass r
  let R := g.rightMass r
  let a := L/(L+R)
  have hL : (L+R)*a=L := by dsimp [a,L,R]; field_simp
  have hR : (L+R)*(1-a)=R := by linear_combination -hL
  rw [moment_arm_cube]
  calc
    _ = cubeFour ((L+R)*a) ((L+R)*(1-a)) ((g.left:ℝ)-t) ((g.right:ℝ)-t) n := by rw [hL,hR]
    _ = _ := by
      rw [cubeFour_scale, normalized_cubeFour]
      apply congrArg ((L+R)^3 * ·)
      congr 1 <;> dsimp [Arm.mean, Arm.skew, Arm.variance, a, L, R] <;> ring

end
end SparseCubes
