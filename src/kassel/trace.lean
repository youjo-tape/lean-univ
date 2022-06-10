import algebra.category.FinVect
open category_theory

namespace kassel

universes u
variables
  (K: Type u) [field K]
  [symmetric_category (FinVect K)]

noncomputable def trace {V} (f: V ⟶ V)
  := FinVect.FinVect_coevaluation K V
  ≫ (f ⊗ 𝟙 _)
  ≫ (β_ _ _).hom
  ≫ FinVect.FinVect_evaluation K V

end kassel