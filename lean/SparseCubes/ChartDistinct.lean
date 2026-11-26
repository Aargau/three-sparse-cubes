import SparseCubes.Chart0Case
import SparseCubes.Chart1Case

namespace SparseCubes.Chart

/-- No three genuine binomials with centered, distinct means can cancel through order nine. -/
theorem distinct_mean_excludes (m x v s : Fin 3 → ℝ) (hm : ∀ i, m i ≠ 0)
    (hx : Function.Injective x) (hv : ∀ i, v i ≠ 0) (hc : ∑ i, x i=0)
    (hz : ∀ n < 10, mass m (fun i => rawMoment (x i) (v i) (s i) n)=0) : False :=
  center_distinct_of_cases Chart0.excludes Chart1.excludes m x v s hm hx hv hc hz

end SparseCubes.Chart
