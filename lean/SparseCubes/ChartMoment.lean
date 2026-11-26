import Mathlib.Basic.Real.Basic

namespace SparseCubes.Chart

/-- Raw Euler moments of the cube of a normalized binomial. The binomial has
mean `x`, centered variance `v`, and centered frequency sum `s`. -/
def rawMoment (x v s : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 3*x
  | 2 => 9*x^2+3*v
  | 3 => 27*x^3+27*x*v+3*v*s
  | n+4 =>
    let t := 2*x+s
    let p := x^2+x*s-v
    let a := 3*t
    let o := 9*p
    let i := 2*t^2+p
    2*a*rawMoment x v s (n+3) - (a^2+o+i)*rawMoment x v s (n+2) +
      a*(o+i)*rawMoment x v s (n+1) - o*i*rawMoment x v s n

end SparseCubes.Chart
