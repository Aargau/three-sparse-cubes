import SparseCubes

-- Exact statement from the public L-gct-234 record, checked by type ascription.
example : ∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) → (∀ i, (g i).support.card ≤ 2) → ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≠ 0 → ∀ x : ℝ, 0 < x → Polynomial.rootMultiplicity x ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≤ 9 := PEqualNP.Outside.L_gct_234

#print axioms PEqualNP.Outside.L_gct_234
