import algebra.category.FinVect
import category_theory.monoidal.braided
import kassel.Tangle

open category_theory

namespace kassel

universes v u
variables
  {C: Type u}
  [category.{v} C]
  [monoidal_category C]
  [right_rigid_category C]
  [symmetric_category C]

def trace {V: C} (f: V ⟶ V) := η_ _ _ ≫ (f ⊗ 𝟙 (Vᘁ)) ≫ (β_ _ _).hom ≫ ε_ _ _

-- variables (K: Type u) [field K] (V: FinVect K)
variable (V: C)

structure enhanced_R_matrix :=
  (c: V ⊗ V ≅ V ⊗ V)
  (μ: V ≅ V)
  (relation_1:
       (𝟙 V ⊗ c.hom) ≫ (α_ V V V).inv
    ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ V V V).hom
    ≫ (𝟙 V ⊗ c.hom)
  =                    (α_ V V V).inv
    ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ V V V).hom
    ≫ (𝟙 V ⊗ c.hom) ≫ (α_ V V V).inv
    ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ V V V).hom
  )
  (relation_2: c.hom ≫ (μ.hom ⊗ μ.hom) = (μ.hom ⊗ μ.hom) ≫ c.inv)
  -- relation_3 (p.306 4.1.b): tr₂ の定義 (p.31) に現れる λ (p.26) が isomorphism であることを言うには FinVect 性が必要 (p.27 Theorem II.2.1)
  -- relation_4 (4.1.c): ⁺ の定義 (p.30) が FinVect じゃないとむずかしそう
variable (R: enhanced_R_matrix V)

end kassel