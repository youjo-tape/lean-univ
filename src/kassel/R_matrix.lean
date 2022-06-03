import algebra.category.FinVect
import category_theory.monoidal.functor
import kassel.Tangle

variables (K: Type) [field K] (V: FinVect K)

structure enhanced_R_matrix :=
  (c: V ⊗ V ≅ V ⊗ V)
  (μ: V ≅ V)
--  (relation_1: (𝟙 V ⊗ c.hom) ≫ (α_ _ _ _).inv ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ c.hom) = (α_ _ _ _).inv ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ c.hom) ≫ (α_ _ _ _).inv ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom)
  (relation_2: c.hom ≫ (μ.hom ⊗ μ.hom) = (μ.hom ⊗ μ.hom) ≫ c.inv)

variable (R: enhanced_R_matrix K V)

example: ∃ F: category_theory.monoidal_functor Tangle (FinVect K),
  (F.obj ↓ = V) ∧
  (F.obj ↑ = FinVect.FinVect_dual K V) ∧
  (F.map ⟦β ↓ ↓⟧ = R.c.hom)
:= begin
  sorry,
end