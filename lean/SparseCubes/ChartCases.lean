import SparseCubes.Chart
import SparseCubes.CertificatePolynomials

namespace SparseCubes.Chart

def X : Rep := ⟨0,1,0⟩
def unit : Rep := ⟨1,0,0⟩
def V (d e : ℝ) : Rep := ⟨3*d,3*e,-3⟩
def S (b d e j w : ℝ) : Rep := ⟨(d+b)*w+e*(j+9),j,w⟩

theorem eval_unit (b z : ℝ) : unit.eval b z = 1 := by simp [unit,Rep.eval]

theorem eval_X (b z : ℝ) : X.eval b z = z := by simp [Rep.eval,X]
theorem eval_V (b d e z : ℝ) : (V d e).eval b z = variance b d e z := by
  simp only [Rep.eval,V,variance]; ring
theorem eval_S (b d e j w z : ℝ) : (S b d e j w).eval b z = skew b d e j w z := by rfl

def linear4 (b c : ℝ) (r0 r1 r2 r3 u0 u1 u2 u3 : Rep) : Rep :=
  ((Rep.mul b c r0 u0).add (Rep.mul b c r1 u1)).add
    ((Rep.mul b c r2 u2).add (Rep.mul b c r3 u3))

theorem eval_linear4 (b c z : ℝ) (hz : z^3=b*z+c) (r0 r1 r2 r3 u0 u1 u2 u3 : Rep) :
    (linear4 b c r0 r1 r2 r3 u0 u1 u2 u3).eval b z =
      r0.eval b z*u0.eval b z + r1.eval b z*u1.eval b z +
      r2.eval b z*u2.eval b z + r3.eval b z*u3.eval b z := by
  simp only [linear4,Rep.eval_add,Rep.eval_mul _ _ _ hz]; ring

theorem rep_ext {r s : Rep} (u : r.u=s.u) (l : r.l=s.l) (k : r.k=s.k) : r=s := by
  cases r; cases s; simp_all

/-- The target of the two explicit chart certificates is nonzero on the open stratum. -/
theorem chartH_ne (x : Fin 3 → ℝ) (d e j : ℝ) (hc : ∑ i, x i=0)
    (hx : Function.Injective x) (hv : ∀ i, variance (coeffB x) d e (x i) ≠ 0) :
    Certificate.chartH (coeffB x) (coeffC x) d e j ≠ 0 := by
  have hz : x 2 = -x 0-x 1 := by simp only [Fin.sum_univ_three] at hc; linarith
  have h : 27 * Certificate.chartH (coeffB x) (coeffC x) d e j =
      (4*(coeffB x)^3-27*(coeffC x)^2)*variance (coeffB x) d e (x 0)*
        variance (coeffB x) d e (x 1)*variance (coeffB x) d e (x 2) := by
    simp only [Certificate.chartH,variance,coeffB,coeffC,hz]
    ring
  intro hzero
  rw [hzero,mul_zero] at h
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (discriminant_ne x hx hc)
    (hv 0)) (hv 1)) (hv 2)) h.symm

def Case (w : ℝ) : Prop :=
  ∀ (m x : Fin 3 → ℝ) (d e j : ℝ), Function.Injective x → (∑ i, x i)=0 →
    (∀ i, variance (coeffB x) d e (x i) ≠ 0) →
    (∀ n < 10, mass m (fun i => rawMoment (x i) (variance (coeffB x) d e (x i))
        (skew (coeffB x) d e j w (x i)) n)=0) → m 2 ≠ 0 → False

theorem center_distinct_of_cases (case0 : Case 0) (case1 : Case 1)
    (m x v s : Fin 3 → ℝ) (hm : ∀ i, m i ≠ 0) (hx : Function.Injective x)
    (hv : ∀ i, v i ≠ 0) (hc : ∑ i, x i=0)
    (hz : ∀ n < 10, mass m (fun i => rawMoment (x i) (v i) (s i) n)=0) : False := by
  have h0 := hz 0 (by decide)
  change mass m (fun _ => 1)=0 at h0
  have hm1 := hz 1 (by decide)
  have h1 : mass m x = 0 := by
    simp only [mass,Fin.sum_univ_three,rawMoment] at hm1 ⊢
    linear_combination (1/3 : ℝ)*hm1
  obtain ⟨d,e,j,w,hv',hs'⟩ := chart_parameters m x v s (hm 2) hx hc h0 h1
    (hz 2 (by decide)) (hz 3 (by decide))
  let b := coeffB x
  have hvar i : variance b d e (x i) ≠ 0 := by rw [← hv' i]; exact hv i
  have hraw n (hn : n < 10) :
      mass m (fun i => rawMoment (x i) (variance b d e (x i)) (skew b d e j w (x i)) n)=0 := by
    simpa only [← hv',← hs',b] using hz n hn
  by_cases hw : w=0
  · subst w; exact case0 m x d e j hx hc hvar hraw (hm 2)
  · let y := fun i => w * x i
    have hy : Function.Injective y := fun a b h => hx (mul_left_cancel₀ hw h)
    have hyc : ∑ i, y i=0 := by simp only [y,← Finset.mul_sum,hc,mul_zero]
    have hb : coeffB y=w^2*b := by simp only [coeffB,y,b]; ring
    apply case1 m y (w^2*d) (w*e) j hy hyc
    · intro i
      rw [hb,show y i=w*x i from rfl,variance_scale]
      exact mul_ne_zero (pow_ne_zero _ hw) (hvar i)
    · intro n hn
      simp only [hb,y,variance_scale,skew_scale_to_one,rawMoment_scale]
      have h := hraw n hn
      simp only [mass,Fin.sum_univ_three] at h ⊢
      linear_combination w^n*h
    · exact hm 2

end SparseCubes.Chart
namespace SparseCubes.Chart

def initialRep (b c d e j w : ℝ) (n : Fin 4) : Rep :=
  let v := V d e
  let s := S b d e j w
  let x2 := Rep.mul b c X X
  let x3 := Rep.mul b c x2 X
  match n with
  | 0 => unit
  | 1 => Rep.scale 3 X
  | 2 => (Rep.scale 9 x2).add (Rep.scale 3 v)
  | 3 => ((Rep.scale 27 x3).add (Rep.scale 27 (Rep.mul b c X v))).add
      (Rep.scale 3 (Rep.mul b c v s))

def recRep (b c d e j w : ℝ) (n : Fin 4) : Rep :=
  let v := V d e
  let s := S b d e j w
  let t := (X.scale 2).add s
  let p := ((Rep.mul b c X X).add (Rep.mul b c X s)).add (v.scale (-1))
  let a := t.scale 3
  let o := p.scale 9
  let u := ((Rep.mul b c t t).scale 2).add p
  match n with
  | 0 => a.scale 2
  | 1 => (((Rep.mul b c a a).add o).add u).scale (-1)
  | 2 => Rep.mul b c a (o.add u)
  | 3 => (Rep.mul b c o u).scale (-1)

theorem eval_initialRep (b c d e j w z : ℝ) (hz : z^3=b*z+c) (n : Fin 4) :
    (initialRep b c d e j w n).eval b z =
      rawMoment z (variance b d e z) (skew b d e j w z) n := by
  fin_cases n <;> simp [initialRep,Rep.eval_add,Rep.eval_scale,Rep.eval_mul _ _ _ hz,
    eval_X,eval_V,eval_S,eval_unit,rawMoment] <;> ring

theorem raw_step (b c d e j w z : ℝ) (hz : z^3=b*z+c) (n : ℕ)
    (u0 u1 u2 u3 : Rep)
    (h0 : u0.eval b z = rawMoment z (variance b d e z) (skew b d e j w z) (n+3))
    (h1 : u1.eval b z = rawMoment z (variance b d e z) (skew b d e j w z) (n+2))
    (h2 : u2.eval b z = rawMoment z (variance b d e z) (skew b d e j w z) (n+1))
    (h3 : u3.eval b z = rawMoment z (variance b d e z) (skew b d e j w z) n) :
    (linear4 b c (recRep b c d e j w 0) (recRep b c d e j w 1)
        (recRep b c d e j w 2) (recRep b c d e j w 3) u0 u1 u2 u3).eval b z =
      rawMoment z (variance b d e z) (skew b d e j w z) (n+4) := by
  rw [eval_linear4 _ _ _ hz, h0,h1,h2,h3,rawMoment.eq_5]
  simp only [recRep,Rep.eval_add,Rep.eval_scale,Rep.eval_mul _ _ _ hz,eval_X,eval_V,eval_S]
  ring

end SparseCubes.Chart
