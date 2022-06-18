import category_theory.monoidal.rigid.basic

namespace kassel
open category_theory

universes v u
variables
  (C: Type u)
  [category.{v} C]
  [monoidal_category.{v} C]
  [right_rigid_category.{v} C]

-- * Show that `X ⊗ Y` and `Yᘁ ⊗ Xᘁ` form an exact pairing.

@[simp] def has_right_dual_tensor_coevaluation {X Y: C} := η_ X Xᘁ ≫ ((ρ_ X).inv ⊗ 𝟙 Xᘁ) ≫ ((𝟙 X ⊗ η_ Y Yᘁ) ⊗ 𝟙 Xᘁ) ≫ ((α_ X Y Yᘁ).inv ⊗ 𝟙 Xᘁ) ≫ (α_ (X ⊗ Y) Yᘁ Xᘁ).hom
@[simp] def has_right_dual_tensor_evaluation {X Y: C} := (α_ (Yᘁ ⊗ Xᘁ) X Y).inv ≫ ((α_ Yᘁ Xᘁ X).hom ⊗ 𝟙 Y) ≫ ((𝟙 Yᘁ ⊗ ε_ X Xᘁ) ⊗ 𝟙 Y) ≫ ((ρ_ Yᘁ).hom ⊗ 𝟙 Y) ≫ ε_ Y Yᘁ

lemma coevaluation_evaluation {X Y: C}:
  (𝟙 (Yᘁ ⊗ Xᘁ) ⊗ has_right_dual_tensor_coevaluation C) ≫ (α_ (Yᘁ ⊗ Xᘁ) (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).inv
  ≫ (has_right_dual_tensor_evaluation C ⊗ 𝟙 (Yᘁ ⊗ Xᘁ)) = (α_ _ _ _).hom
  ≫ (𝟙 _ ⊗ ((𝟙 _ ⊗ η_ X Xᘁ) ≫ (α_ _ _ _).inv ≫ (ε_ X Xᘁ ⊗ 𝟙 _))) ≫ (α_ _ _ _).inv
  ≫ (((𝟙 _ ⊗ η_ Y Yᘁ) ≫ (α_ _ _ _).inv ≫ (ε_ Y Yᘁ ⊗ 𝟙 _)) ⊗ 𝟙 _)
  ≫ (α_ _ _ _).hom := sorry

instance has_right_dual_tensor {X Y: C}: has_right_dual (X ⊗ Y) := {
  right_dual := Yᘁ ⊗ Xᘁ,
  exact := {
    coevaluation := has_right_dual_tensor_coevaluation C,
    evaluation := has_right_dual_tensor_evaluation C,
    coevaluation_evaluation' := sorry,
    evaluation_coevaluation' := sorry
  }
}

/-
  (𝟙 (Yᘁ ⊗ Xᘁ) ⊗ η_ X Xᘁ)
≫ (𝟙 (Yᘁ ⊗ Xᘁ) ⊗ 𝟙 X ⊗ (λ_ Xᘁ).inv)
≫ (𝟙 (Yᘁ ⊗ Xᘁ) ⊗ 𝟙 X ⊗ η_ Y Yᘁ ⊗ 𝟙 Xᘁ)
≫ (𝟙 (Yᘁ ⊗ Xᘁ) ⊗ (α_ X (Y ⊗ Yᘁ) Xᘁ).inv)
≫ (𝟙 (Yᘁ ⊗ Xᘁ) ⊗ (α_ X Y Yᘁ).inv ⊗ 𝟙 Xᘁ)
≫ (𝟙 (Yᘁ ⊗ Xᘁ) ⊗ (α_ (X ⊗ Y) Yᘁ Xᘁ).hom)
≫ (α_ (Yᘁ ⊗ Xᘁ) (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).inv
≫ ((α_ (Yᘁ ⊗ Xᘁ) X Y).inv ⊗ 𝟙 (Yᘁ ⊗ Xᘁ))
≫ (α_ ((Yᘁ ⊗ Xᘁ) ⊗ X) Y (Yᘁ ⊗ Xᘁ)).hom
≫ ((α_ Yᘁ Xᘁ X).hom ⊗ 𝟙 (Y ⊗ Yᘁ ⊗ Xᘁ))
≫ (α_ (Yᘁ ⊗ Xᘁ ⊗ X) Y (Yᘁ ⊗ Xᘁ)).inv
≫ ((α_ Yᘁ (Xᘁ ⊗ X) Y).hom ⊗ 𝟙 (Yᘁ ⊗ Xᘁ))
≫ (α_ Yᘁ ((Xᘁ ⊗ X) ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom
≫ (𝟙 Yᘁ ⊗ (α_ (Xᘁ ⊗ X) Y (Yᘁ ⊗ Xᘁ)).hom)
≫ (𝟙 Yᘁ ⊗ ε_ X Xᘁ ⊗ 𝟙 (Y ⊗ Yᘁ ⊗ Xᘁ))
≫ (𝟙 Yᘁ ⊗ (α_ (𝟙_ C) Y (Yᘁ ⊗ Xᘁ)).inv)
≫ (𝟙 Yᘁ ⊗ (λ_ Y).hom ⊗ 𝟙 (Yᘁ ⊗ Xᘁ))
≫ (α_ Yᘁ Y (Yᘁ ⊗ Xᘁ)).inv
≫ (ε_ Y Yᘁ ⊗ 𝟙 (Yᘁ ⊗ Xᘁ))
= (α_ Yᘁ Xᘁ (𝟙_ C)).hom 
≫ (𝟙 Yᘁ ⊗ (ρ_ Xᘁ).hom)
≫ (λ_ (Yᘁ ⊗ Xᘁ)).inv
-/

-- * Define pivotal categories (rigid categories equipped with a natural isomorphism `ᘁᘁ ≅ 𝟙 C`).
-- 参考: https://tqft.net/web/research/students/SamQuinn/thesis.pdf

class right_pivotal_category :=
  (right_pivotor: Π X: C, Xᘁᘁ ≅ X)
  (notation `φ_` := right_pivotor)
  -- (pivotor_monoidal_naturality: ∀ {X Y: C}, (φ_ X).hom ⊗ (φ_ Y).hom = (φ_ (X ⊗ Y)).hom ≫ _)

open right_pivotal_category
notation `φ_` := right_pivotor

end kassel
