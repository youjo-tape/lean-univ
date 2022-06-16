import algebra.category.FinVect
import linear_algebra.trace
import linear_algebra.tensor_product
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

def lambda {U U' V V': FinVect K} (f: U ⟶ U') (g: V ⟶ V')
  := tensor_product.map f g
#check lambda

#check linear_map.trace K

end kassel