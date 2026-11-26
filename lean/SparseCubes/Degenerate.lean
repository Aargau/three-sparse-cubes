module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace SparseCubes

/-- Euler moments of a normalized binomial cube after translating its binomial mean to zero. -/
def centeredCubeMoment : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, _, _ => 0
  | 2, _, v => 3*v
  | 3, s, v => 3*s*v
  | 4, s, v => 3*v*(s^2 + 7*v)
  | 5, s, v => 3*s*v*(s^2 + 22*v)
  | 6, s, v => 3*v*(s^4 + 53*s^2*v + 61*v^2)
  | 7, s, v => 3*s*v*(s^4 + 116*s^2*v + 367*v^2)
  | 8, s, v => 3*v*(s^6 + 243*s^4*v + 1518*s^2*v^2 + 547*v^3)
  | 9, s, v => 3*s*v*(s^6 + 498*s^4*v + 5394*s^2*v^2 + 4924*v^3)
  | _, _, _ => 0

/-- Moments through order six after a vanishing binomial cube loses its triple zero. -/
noncomputable def uniformCubeMoment : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, m, _ => m
  | 2, m, v => m^2+v
  | 3, m, v => m^3+3*m*v
  | 4, m, v => m^4+6*m^2*v+13*v^2/5
  | 5, m, v => m^5+10*m^3*v+13*m*v^2
  | 6, m, v => m^6+15*m^4*v+39*m^2*v^2+205*v^3/21
  | _, _, _ => 0

set_option maxHeartbeats 4000000 in
/-- A difference of two centered cube jets, with the same nonzero variance and
different skews, cannot match a normalized vanishing cube through order nine. -/
theorem oneVanish_excludes (h d v m b : ℝ) (hd : d ≠ 0) (hv : v ≠ 0)
    (H : ∀ n : ℕ, n ≤ 6 → centeredCubeMoment (n+3) (h+d) v -
      centeredCubeMoment (n+3) (h-d) v =
      v*d*((n:ℝ)+1)*((n:ℝ)+2)*((n:ℝ)+3)*uniformCubeMoment n m b) : False := by
  have eqn (n : ℕ) (hn : n ≤ 6) := H n hn
  have H1 := eqn 1 (by decide)
  have H2 := eqn 2 (by decide)
  have H3 := eqn 3 (by decide)
  have H4 := eqn 4 (by decide)
  have H6 := eqn 6 (by decide)
  norm_num [centeredCubeMoment,uniformCubeMoment] at H1 H2 H3 H4 H6
  have recover {x : ℝ} (hx : v*d*x=0) : x=0 :=
    (mul_eq_zero.mp hx).resolve_left (mul_ne_zero hv hd)
  have hm : m=h/2 := by
    apply sub_eq_zero.mp
    apply recover
    linear_combination -H1/24
  subst m
  have hb : b=(d^2+3*h^2+22*v)/10-(h/2)^2 := by
    apply sub_eq_zero.mp
    apply recover
    linear_combination -H2/60
  subst b
  have h3 : h*(d^2+40*v)=0 := by apply recover; linear_combination H3/6
  have hh : h=0 := by
    rcases mul_eq_zero.mp h3 with h0|h0
    · exact h0
    · have vv : v= -d^2/40 := by linarith
      subst v
      have h4 : 18549*d^4+14720*d^2*h^2+400*h^4=0 := by
        apply recover
        linear_combination -(5000:ℝ)/3 * H4
      have hpos : 0 < 18549*d^4+14720*d^2*h^2+400*h^4 := by
        have hd4 : 0 < d^4 := by positivity
        positivity
      linarith
  subst h
  let u := v/d^2
  have hu : v=u*d^2 := by dsimp [u]; field_simp
  rw [hu] at H4 H6
  have dropPower (n : ℕ) (z : ℝ) (hz : v*d*d^n*z=0) : z=0 :=
    (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (mul_ne_zero hv hd) (pow_ne_zero _ hd))
  have ce : 816*u^2-844*u-1=0 := by
    apply dropPower 4
    rw [hu]
    linear_combination -(50:ℝ)/27 * H4
  have cf : -1-2466*u-23352*u^2+21152*u^3=0 := by
    apply dropPower 6
    rw [hu]
    linear_combination -(25:ℝ)/27 * H6
  have impossible : (1:ℝ)=0 := by
    linear_combination ((272665144*u^2-301217806*u-31440989)/20553750)*ce +
      ((10887239-10518852*u)/20553750)*cf
  norm_num at impossible

end SparseCubes


namespace SparseCubes

/-- A simultaneous affine transformation of the two frequencies preserves a mixture's moment equalities. -/
theorem uniformCubeMatch_affine (p m₁ m₂ m₃ v₁ v₂ v₃ a b : ℝ)
    (H : ∀ n : ℕ, n ≤ 6 → p*uniformCubeMoment n m₁ v₁ +
       (1-p)*uniformCubeMoment n m₂ v₂ = uniformCubeMoment n m₃ v₃) :
    ∀ n : ℕ, n ≤ 6 → p*uniformCubeMoment n (a*m₁+b) (a^2*v₁) +
       (1-p)*uniformCubeMoment n (a*m₂+b) (a^2*v₂) =
       uniformCubeMoment n (a*m₃+b) (a^2*v₃) := by
  have h1 := H 1 (by decide)
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  have h4 := H 4 (by decide)
  have h5 := H 5 (by decide)
  have h6 := H 6 (by decide)
  simp [uniformCubeMoment] at h1 h2 h3 h4 h5 h6
  intro n hn
  interval_cases n <;> simp only [uniformCubeMoment]
  · ring
  · linear_combination 1*a^1*b^0*h1
  · linear_combination 2*a^1*b^1*h1 + 1*a^2*b^0*h2
  · linear_combination 3*a^1*b^2*h1 + 3*a^2*b^1*h2 + 1*a^3*b^0*h3
  · linear_combination 4*a^1*b^3*h1 + 6*a^2*b^2*h2 + 4*a^3*b^1*h3 + 1*a^4*b^0*h4
  · linear_combination 5*a^1*b^4*h1 + 10*a^2*b^3*h2 + 10*a^3*b^2*h3 + 5*a^4*b^1*h4 + 1*a^5*b^0*h5
  · linear_combination 6*a^1*b^5*h1 + 15*a^2*b^4*h2 + 20*a^3*b^3*h3 + 15*a^4*b^2*h4 + 6*a^5*b^1*h5 + 1*a^6*b^0*h6

private theorem uniform_normalized_excludes (p v₁ v₂ v₃ : ℝ) (hp : p ≠ 0) (hq : 1-p ≠ 0)
    (H : ∀ n : ℕ, n ≤ 6 → p*uniformCubeMoment n (1-p) v₁ +
       (1-p)*uniformCubeMoment n (-p) v₂ = uniformCubeMoment n 0 v₃) : False := by
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  have h4 := H 4 (by decide)
  have h5 := H 5 (by decide)
  have h6 := H 6 (by decide)
  norm_num [uniformCubeMoment] at h2 h3 h4 h5 h6
  have cancel {z : ℝ} (e : p*(1-p)*z=0) : z=0 :=
    (mul_eq_zero.mp e).resolve_left (mul_ne_zero hp hq)
  have v1e : v₁=v₂+(2*p-1)/3 := by
    apply sub_eq_zero.mp
    apply cancel
    linear_combination h3/3
  subst v₁
  have v3e : v₃ = v₂ + p*(2*p-1)/3+p*(1-p) := by linear_combination -h2
  subst v₃
  have v2e : v₂=(8*p^2-11*p+8)/9 := by
    apply sub_eq_zero.mp
    apply cancel
    linear_combination (5:ℝ)/4*h4
  subst v₂
  have prodzero : (p-2)*(p+1)*(2*p-1)=0 := by
    apply cancel
    linear_combination (27:ℝ)/4*h5
  rcases mul_eq_zero.mp prodzero with hh | hh
  · rcases mul_eq_zero.mp hh with hh | hh
    · have pp : p=2 := by linarith
      rw [pp] at h6; norm_num at h6
    · have pp : p= -1 := by linarith
      rw [pp] at h6; norm_num at h6
  · have pp : p=1/2 := by linarith
    rw [pp] at h6; norm_num at h6

/-- A mixture with both weights nonzero can match a single
normalized vanishing cube through order six only at identical means and variances. -/
theorem threeVanish_mixture (p m₁ m₂ m₃ v₁ v₂ v₃ : ℝ) (hp : p ≠ 0) (hq : 1-p ≠ 0)
    (H : ∀ n : ℕ, n ≤ 6 → p*uniformCubeMoment n m₁ v₁ +
       (1-p)*uniformCubeMoment n m₂ v₂ = uniformCubeMoment n m₃ v₃) :
    m₁=m₃ ∧ m₂=m₃ ∧ v₁=v₃ ∧ v₂=v₃ := by
  have h1 := H 1 (by decide)
  simp [uniformCubeMoment] at h1
  by_cases he : m₁=m₂
  · subst m₁
    have hm : m₂=m₃ := by linear_combination h1
    rw [← hm] at H ⊢
    have U := uniformCubeMatch_affine p m₂ m₂ m₂ v₁ v₂ v₃ 1 (-m₂) H
    have h2 := U 2 (by decide)
    have h4 := U 4 (by decide)
    norm_num [uniformCubeMoment] at h2 h4
    have ve : v₃=p*v₁+(1-p)*v₂ := by linear_combination -h2
    subst v₃
    have sq0 : p*(1-p)*(v₁-v₂)^2=0 := by linear_combination (5:ℝ)/13*h4
    have vv : v₁=v₂ := by
      have sq := (mul_eq_zero.mp sq0).resolve_left (mul_ne_zero hp hq)
      nlinarith [sq_nonneg (v₁-v₂)]
    subst v₁
    exact ⟨rfl,rfl,by ring,by ring⟩
  · have hd : m₁-m₂≠0 := sub_ne_zero.mpr he
    let a := (m₁-m₂)⁻¹
    have am₁ : a*m₁ + -(a*m₃) = 1-p := by dsimp [a]; field_simp; linear_combination h1
    have am₂ : a*m₂ + -(a*m₃) = -p := by dsimp [a]; field_simp; linear_combination h1
    have U := uniformCubeMatch_affine p m₁ m₂ m₃ v₁ v₂ v₃ a (-(a*m₃)) H
    simp only [am₁,am₂,add_neg_cancel] at U
    exact (uniform_normalized_excludes p _ _ _ hp hq U).elim

end SparseCubes


namespace SparseCubes

private def sixthObstruction (p z : ℝ) :=
  783*p^2*z^2 - 783*p^2*z + 196*p^2 + 782*p*z^3 - 1956*p*z^2 +
  782*p*z + 196*z^4 - 783*z^3 + 783*z^2

private theorem sixthObstruction_ne (p z : ℝ) (hz : z≠0) (hz' : 1-z≠0) :
    sixthObstruction p z ≠ 0 := by
  intro he
  have hi : 4*(783*z^2-783*z+196)*sixthObstruction p z =
      (2*(783*z^2-783*z+196)*p + 782*z^3-1956*z^2+782*z)^2 +
      2348*z^2*(1-z)^2*(z^2-z+1) := by unfold sixthObstruction; ring
  have hpos : 0 < z^2-z+1 := by nlinarith [sq_nonneg (z-1/2)]
  have hterm : 0 < 2348*z^2*(1-z)^2*(z^2-z+1) := by positivity
  rw [he, mul_zero] at hi
  nlinarith [sq_nonneg (2*(783*z^2-783*z+196)*p + 782*z^3-1956*z^2+782*z)]

set_option maxHeartbeats 8000000 in
private theorem equalMean_normalized_excludes (p z t V : ℝ)
    (hp : p≠0) (hq : 1-p≠0) (hz : z≠0) (hz' : 1-z≠0) (hv : V≠0)
    (H : ∀ n : ℕ, n≤6 → p*centeredCubeMoment n (t+1-z) (V*z/p) +
      (1-p)*centeredCubeMoment n (t-z) (V*(1-z)/(1-p)) = centeredCubeMoment n t V) : False := by
  have zero (n : ℕ) (hn : n≤6) := sub_eq_zero.mpr (H n hn)
  have h4 : p*(1-p)*z*(1-z)+7*V*(z-p)^2=0 := by
    calc
      _ = (p*(1-p)/(3*V)) * (p*centeredCubeMoment 4 (t+1-z) (V*z/p) +
        (1-p)*centeredCubeMoment 4 (t-z) (V*(1-z)/(1-p))-centeredCubeMoment 4 t V) := by
          simp only [centeredCubeMoment]; field_simp; ring
      _ = 0 := by rw [zero 4 (by decide),mul_zero]
  have diff : z-p≠0 := by
    intro he
    rw [he] at h4
    have hnon : p*(1-p)*z*(1-z)≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hp hq) hz) hz'
    exact hnon (by simpa using h4)
  have vval : V= -(p*(1-p)*z*(1-z))/(7*(z-p)^2) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero _ diff))).2
    linear_combination h4
  have h5 : p*t+14*p*z-7*p-t*z+8*z^2-15*z=0 := by
    calc
      _ = (7*(z-p)/(3*V*z*(1-z))) * (p*centeredCubeMoment 5 (t+1-z) (V*z/p) +
        (1-p)*centeredCubeMoment 5 (t-z) (V*(1-z)/(1-p))-centeredCubeMoment 5 t V) := by
          rw [vval]; simp only [centeredCubeMoment]; field_simp [hp,hq,hz,hz',diff]; ring
      _ = 0 := by rw [zero 5 (by decide),mul_zero]
  have tval : t=(14*p*z-7*p+8*z^2-15*z)/(z-p) := by
    apply (eq_div_iff diff).2
    linear_combination -h5
  apply sixthObstruction_ne p z hz hz'
  calc
    _ = (-49*(z-p)^2/(36*V*z*(1-z))) * (p*centeredCubeMoment 6 (t+1-z) (V*z/p) +
       (1-p)*centeredCubeMoment 6 (t-z) (V*(1-z)/(1-p))-centeredCubeMoment 6 t V) := by
        rw [vval,tval]; simp only [centeredCubeMoment,sixthObstruction]
        field_simp [hp,hq,hz,hz',diff]; ring
    _ = 0 := by rw [zero 6 (by decide),mul_zero]

theorem centeredCubeMoment_scale (n : ℕ) (hn : n≤6) (s v a : ℝ) :
    centeredCubeMoment n (a*s) (a^2*v) = a^n*centeredCubeMoment n s v := by
  interval_cases n <;> simp only [centeredCubeMoment] <;> ring

set_option maxHeartbeats 2000000 in
/-- Three nonzero-variance binomials with the same logarithmic derivative can
match their cubed moments through order six only when their centered parameters agree. -/
theorem equalMean_mixture (p s₁ s₂ s₃ v₁ v₂ v₃ : ℝ)
    (hp : p≠0) (hq : 1-p≠0) (hv1 : v₁≠0) (hv2 : v₂≠0) (hv3 : v₃≠0)
    (H : ∀ n : ℕ, n≤6 → p*centeredCubeMoment n s₁ v₁ +
      (1-p)*centeredCubeMoment n s₂ v₂ = centeredCubeMoment n s₃ v₃) :
    s₁=s₃ ∧ s₂=s₃ ∧ v₁=v₃ ∧ v₂=v₃ := by
  have h2 := H 2 (by decide)
  have h3 := H 3 (by decide)
  have h4 := H 4 (by decide)
  simp only [centeredCubeMoment] at h2 h3 h4
  have v3 : v₃=p*v₁+(1-p)*v₂ := by linear_combination -h2/3
  by_cases he : s₁=s₂
  · subst s₁
    have hs : (s₂-s₃)*v₃=0 := by linear_combination h3/3-s₂*h2/3
    have same := sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hv3)
    subst s₂
    rw [v3] at h4
    have sv : p*(1-p)*(v₁-v₂)^2=0 := by linear_combination h4/21
    have dif := (mul_eq_zero.mp sv).resolve_left (mul_ne_zero hp hq)
    have vv : v₁=v₂ := by nlinarith [sq_nonneg (v₁-v₂)]
    subst v₁
    have vv3 : v₂=v₃ := by linear_combination -v3
    exact ⟨rfl,rfl,vv3,vv3⟩
  · have hd : s₁-s₂≠0 := sub_ne_zero.mpr he
    let a := (s₁-s₂)⁻¹
    let z := p*v₁/v₃
    let t := a*s₃
    let V := a^2*v₃
    have ha : a≠0 := inv_ne_zero hd
    have hz : z≠0 := div_ne_zero (mul_ne_zero hp hv1) hv3
    have wz : 1-z=(1-p)*v₂/v₃ := by dsimp [z]; field_simp; linear_combination v3
    have hz' : 1-z≠0 := by rw [wz]; exact div_ne_zero (mul_ne_zero hq hv2) hv3
    have hV : V≠0 := mul_ne_zero (pow_ne_zero _ ha) hv3
    have am1 : t+1-z=a*s₁ := by
      dsimp [t,a,z]; field_simp; linear_combination -h3/3 + s₂*h2/3
    have am2 : t-z=a*s₂ := by
      dsimp [t,a,z]; field_simp; linear_combination -h3/3 + s₂*h2/3
    have av1 : V*z/p=a^2*v₁ := by dsimp [V,z]; field_simp
    have av2 : V*(1-z)/(1-p)=a^2*v₂ := by rw [wz]; dsimp [V]; field_simp
    apply (equalMean_normalized_excludes p z t V hp hq hz hz' hV ?_).elim
    intro n hn
    rw [am1, am2, av1, av2]
    change _ = centeredCubeMoment n (a*s₃) (a^2*v₃)
    rw [centeredCubeMoment_scale n hn, centeredCubeMoment_scale n hn, centeredCubeMoment_scale n hn]
    linear_combination a^n * H n hn

end SparseCubes
