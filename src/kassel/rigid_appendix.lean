import category_theory.monoidal.rigid

-- https://tqft.net/web/research/students/SamQuinn/thesis.pdf

namespace kassel
open category_theory

universes v u
variables
  (C: Type u)
  [category.{v} C]
  [monoidal_category.{v} C]
  [right_rigid_category.{v} C]

lemma right_rigid_tensor_iso {X Y: C}: (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ := {
  hom := begin  end 
}

class right_pivotal_category :=
  (right_pivotor: Π X: C, Xᘁᘁ ≅ X)
  (notation `φ_` := right_pivotor)
  -- (pivotor_monoidal_naturality: ∀ {X Y: C}, (φ_ X).hom ⊗ (φ_ Y).hom = (φ_ (X ⊗ Y)).hom ≫ _)

open right_pivotal_category
notation `φ_` := right_pivotor

end kassel
