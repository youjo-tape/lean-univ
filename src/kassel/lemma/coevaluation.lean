import algebra.category.FinVect

open_locale big_operators

variables
  (K: Type*) [field K]
  (V: Type*) [add_comm_group V] [module K V] [finite_dimensional K V]
  (ι: Type*) [fintype ι] [decidable_eq ι]
  (bV: basis ι K V)

lemma coevaluation_well_defined:
  (coevaluation K V) (1: K) = ∑ (i: B), bV i ⊗ₜ[K] bV.coord i := sorry