import SparseCubes.ChartMoment
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SparseCubes.Chart

/-- Integral coordinates in the cubic algebra on `1,X,X²-b`. -/
structure Rep where
  u : ℝ
  l : ℝ
  k : ℝ

namespace Rep

def eval (b z : ℝ) (r : Rep) : ℝ := r.u+r.l*z+r.k*(z^2-b)
def add (r t : Rep) : Rep := ⟨r.u+t.u,r.l+t.l,r.k+t.k⟩
def scale (a : ℝ) (r : Rep) : Rep := ⟨a*r.u,a*r.l,a*r.k⟩
def mul (b c : ℝ) (r t : Rep) : Rep :=
  ⟨r.u*t.u+b*r.l*t.l+c*(r.l*t.k+r.k*t.l),
   r.u*t.l+r.l*t.u+c*r.k*t.k,
   r.u*t.k+r.k*t.u+r.l*t.l-b*r.k*t.k⟩

@[simp] theorem eval_add (b z : ℝ) (r t : Rep) :
    (r.add t).eval b z = r.eval b z + t.eval b z := by
  simp only [eval,add]; ring

@[simp] theorem eval_scale (b z a : ℝ) (r : Rep) :
    (r.scale a).eval b z = a*r.eval b z := by
  simp only [eval,scale]; ring

theorem eval_mul (b c z : ℝ) (hz : z^3=b*z+c) (r t : Rep) :
    (mul b c r t).eval b z = r.eval b z * t.eval b z := by
  simp only [eval,mul]
  linear_combination -(r.l*t.k+r.k*t.l+z*r.k*t.k)*hz

end Rep

/-- The signed functional on the three means. -/
def mass (m f : Fin 3 → ℝ) := ∑ i, m i * f i

theorem mass_rep (m x : Fin 3 → ℝ) (b : ℝ) (r : Rep)
    (h0 : mass m (fun _ => 1)=0) (h1 : mass m x=0) :
    mass m (fun i => r.eval b (x i)) = r.k*mass m (fun i => (x i)^2-b) := by
  simp only [mass, Fin.sum_univ_three, Rep.eval, mul_one] at *
  linear_combination r.u*h0+r.l*h1

theorem mass_quadratic_ne (m x : Fin 3 → ℝ) (b : ℝ) (hm : m 2 ≠ 0)
    (hx : Function.Injective x) (h0 : mass m (fun _ => 1)=0) (h1 : mass m x=0) :
    mass m (fun i => (x i)^2-b) ≠ 0 := by
  intro h2
  have hc : m 2 * (x 2-x 0) * (x 2-x 1) = 0 := by
    simp only [mass, Fin.sum_univ_three, mul_one] at *
    linear_combination h2 - (x 0+x 1)*h1 + (b+x 0*x 1)*h0
  exact (mul_ne_zero (mul_ne_zero hm (sub_ne_zero.mpr (hx.ne (by decide))))
    (sub_ne_zero.mpr (hx.ne (by decide)))) hc

theorem affine_of_mass_zero (m x f : Fin 3 → ℝ) (hm : m 2 ≠ 0)
    (hx : Function.Injective x) (h0 : mass m (fun _ => 1)=0)
    (h1 : mass m x=0) (hf : mass m f=0) :
    ∃ a t : ℝ, ∀ i, f i = a+t*x i := by
  let t := (f 1-f 0)/(x 1-x 0)
  let a := f 0-t*x 0
  have h10 : x 1-x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (by decide))
  have ha : f 0 = a+t*x 0 := by dsimp [a]; ring
  have hb : f 1 = a+t*x 1 := by
    dsimp [a,t]
    field_simp
    ring
  refine ⟨a,t,?_⟩
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · have hh : m 2 * (f 2 - (a+t*x 2)) = 0 := by
      simp only [mass, Fin.sum_univ_three, mul_one] at h0 h1 hf
      linear_combination hf-a*h0-t*h1-m 0*ha-m 1*hb
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hm)

theorem interpolate (m x f : Fin 3 → ℝ) (b : ℝ) (hm : m 2 ≠ 0)
    (hx : Function.Injective x) (h0 : mass m (fun _ => 1)=0)
    (h1 : mass m x=0) : ∃ r : Rep, ∀ i, f i = r.eval b (x i) := by
  let K := fun i => (x i)^2-b
  let q := mass m f / mass m K
  have hk : mass m K ≠ 0 := mass_quadratic_ne m x b hm hx h0 h1
  have hq : q * mass m K = mass m f := div_mul_cancel₀ _ hk
  have hsub : mass m (fun i => f i-q*K i) = 0 := by
    simp only [mass, Fin.sum_univ_three] at hq ⊢
    linear_combination -hq
  obtain ⟨a,t,hr⟩ := affine_of_mass_zero m x _ hm hx h0 h1 hsub
  refine ⟨⟨a,t,q⟩,fun i => ?_⟩
  simpa only [Rep.eval,← add_assoc] using (sub_eq_iff_eq_add.mp (hr i))

def coeffB (x : Fin 3 → ℝ) := -(x 0*x 1+x 0*x 2+x 1*x 2)
def coeffC (x : Fin 3 → ℝ) := x 0*x 1*x 2

theorem mean_cubic (x : Fin 3 → ℝ) (h : ∑ i, x i = 0) (i : Fin 3) :
    (x i)^3 = coeffB x*x i+coeffC x := by
  simp only [Fin.sum_univ_three] at h
  unfold coeffB coeffC
  fin_cases i
  · change (x 0)^3 = -(x 0*x 1+x 0*x 2+x 1*x 2)*x 0+x 0*x 1*x 2
    linear_combination (x 0)^2*h
  · change (x 1)^3 = -(x 0*x 1+x 0*x 2+x 1*x 2)*x 1+x 0*x 1*x 2
    linear_combination (x 1)^2*h
  · change (x 2)^3 = -(x 0*x 1+x 0*x 2+x 1*x 2)*x 2+x 0*x 1*x 2
    linear_combination (x 2)^2*h

theorem discriminant_ne (x : Fin 3 → ℝ) (hx : Function.Injective x) (h : ∑ i, x i = 0) :
    4*(coeffB x)^3-27*(coeffC x)^2 ≠ 0 := by
  have hz : x 2 = -x 0-x 1 := by simp only [Fin.sum_univ_three] at h; linarith
  have hd : 4*(coeffB x)^3-27*(coeffC x)^2 =
      ((x 0-x 1)*(x 0-x 2)*(x 1-x 2))^2 := by
    simp only [coeffB,coeffC,hz]; ring
  rw [hd]
  exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hx.ne (by decide)))
    (sub_ne_zero.mpr (hx.ne (by decide)))) (sub_ne_zero.mpr (hx.ne (by decide))))

end SparseCubes.Chart
namespace SparseCubes.Chart

def variance (b d e z : ℝ) := 3*(d+e*z-(z^2-b))
def skew (b d e j w z : ℝ) := (d+b)*w+e*(j+9)+j*z+w*(z^2-b)

/-- The second and third raw moments determine two of the six interpolation coefficients. -/
theorem chart_parameters (m x v s : Fin 3 → ℝ) (hm : m 2 ≠ 0)
    (hx : Function.Injective x) (hc : ∑ i, x i = 0)
    (h0 : mass m (fun _ => 1)=0) (h1 : mass m x=0)
    (h2 : mass m (fun i => rawMoment (x i) (v i) (s i) 2)=0)
    (h3 : mass m (fun i => rawMoment (x i) (v i) (s i) 3)=0) :
    ∃ d e j w : ℝ, (∀ i, v i = variance (coeffB x) d e (x i)) ∧
      ∀ i, s i = skew (coeffB x) d e j w (x i) := by
  let b := coeffB x
  let c := coeffC x
  obtain ⟨vr,hv⟩ := interpolate m x v b hm hx h0 h1
  obtain ⟨sr,hs⟩ := interpolate m x s b hm hx h0 h1
  have hk := mass_quadratic_ne m x b hm hx h0 h1
  let r2 : Rep := ⟨9*b+3*vr.u,3*vr.l,9+3*vr.k⟩
  have he2 (i) : rawMoment (x i) (v i) (s i) 2 = r2.eval b (x i) := by
    rw [rawMoment,hv i]; simp only [r2,Rep.eval]; ring
  simp_rw [he2] at h2
  rw [mass_rep m x b r2 h0 h1] at h2
  have hvk : vr.k = -3 := by
    have := (mul_eq_zero.mp h2).resolve_right hk
    change 9+3*vr.k = 0 at this
    linarith
  let d := vr.u/3
  let e := vr.l/3
  let V : Rep := ⟨3*d,3*e,-3⟩
  let X : Rep := ⟨0,1,0⟩
  have hve (i) : v i = V.eval b (x i) := by
    rw [hv i]; simp only [V,Rep.eval,d,e,hvk]; ring
  let r3 := Rep.add (Rep.scale 27 (Rep.mul b c (Rep.mul b c X X) X))
    (Rep.add (Rep.scale 27 (Rep.mul b c X V)) (Rep.scale 3 (Rep.mul b c V sr)))
  have he3 (i) : rawMoment (x i) (v i) (s i) 3 = r3.eval b (x i) := by
    have hroot : (x i)^3=b*x i+c := mean_cubic x hc i
    rw [rawMoment,hve i,hs i]
    simp only [r3,Rep.eval_add,Rep.eval_scale,Rep.eval_mul _ _ _ hroot]
    simp only [X,Rep.eval]
    ring
  simp_rw [he3] at h3
  rw [mass_rep m x b r3 h0 h1] at h3
  have hsr := (mul_eq_zero.mp h3).resolve_right hk
  have hu : sr.u = (d+b)*sr.k+e*(sr.l+9) := by
    simp only [r3, Rep.add, Rep.scale, Rep.mul, X, V] at hsr
    linear_combination (-1/9:ℝ)*hsr
  refine ⟨d,e,sr.l,sr.k,?_,?_⟩
  · intro i
    rw [hve i]; simp only [V,Rep.eval,variance,b]; ring
  · intro i
    rw [hs i]; simp only [Rep.eval,hu,skew,b]

theorem rawMoment_scale (t x v s : ℝ) (n : ℕ) :
    rawMoment (t*x) (t^2*v) (t*s) n = t^n*rawMoment x v s n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 | 1 | 2 | 3 => simp only [rawMoment]; ring
    | n+4 =>
      simp only [rawMoment]
      rw [ih (n+3) (by omega),ih (n+2) (by omega),ih (n+1) (by omega),ih n (by omega)]
      simp only [pow_add]
      ring

theorem variance_scale (t b d e z : ℝ) :
    variance (t^2*b) (t^2*d) (t*e) (t*z) = t^2 * variance b d e z := by
  unfold variance; ring

theorem skew_scale_to_one (w b d e j z : ℝ) :
    skew (w^2*b) (w^2*d) (w*e) j 1 (w*z) = w * skew b d e j w z := by
  unfold skew; ring

end SparseCubes.Chart
