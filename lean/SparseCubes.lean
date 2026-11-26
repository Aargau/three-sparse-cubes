import SparseCubes.Nonvanishing
import SparseCubes.Vanishing
import SparseCubes.ChartDistinct

namespace SparseCubes
open Polynomial
open scoped BigOperators
noncomputable section

/-- Board L-gct-234. Every positive root of a nonzero signed sum of three
real binomial cubes has multiplicity at most nine. -/
theorem multiplicity_bound :
    ∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ),
      (∀ i, s i = 1 ∨ s i = -1) → (∀ i, (g i).support.card ≤ 2) →
      ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≠ 0 →
      ∀ x : ℝ, 0 < x → Polynomial.rootMultiplicity x
        ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≤ 9 := by
  intro s g hsign hsparse hP r hr
  classical
  by_cases hsmall : ∃ i, (g i).support.card ≤ 1
  · exact bound_of_one_small_input s g hsparse hsmall hP r hr
  have htwo (i) : (g i).support.card = 2 := by
    have h := hsparse i
    have h' : ¬(g i).support.card ≤ 1 := fun hi => hsmall ⟨i,hi⟩
    omega
  choose a hpoly hg using fun i => genuine_arm (g i) (htwo i)
  have htotal : total s a = ∑ i, C (s i) * g i^3 := by simp only [total,hpoly]
  have hne : total s a ≠ 0 := htotal ▸ hP
  have hs (i) : s i ≠ 0 := by rcases hsign i with hi|hi <;> rw [hi] <;> norm_num
  rw [← htotal]
  by_contra! h
  have hl := low_of_ten s a r h
  by_cases hz : ∃ i, (a i).value r = 0
  · exact hne (zero_of_any_vanishes s a r hr.ne' hs hg hz hl)
  have hn (i) : (a i).value r ≠ 0 := fun hi => hz ⟨i,hi⟩
  rcases nonvanishing_cases s a r hr.ne' hs hg hn hl with hzero|⟨m,x,v,u,hm,hx,hv,hc,hw⟩
  · exact hne hzero
  · exact Chart.distinct_mean_excludes m x v u hm hx hv hc hw

end
end SparseCubes

namespace PEqualNP.Outside

theorem L_gct_234 : ∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) → (∀ i, (g i).support.card ≤ 2) → ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≠ 0 → ∀ x : ℝ, 0 < x → Polynomial.rootMultiplicity x ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≤ 9 := SparseCubes.multiplicity_bound

end PEqualNP.Outside
