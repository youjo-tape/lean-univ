import category_theory.monoidal.rigid
import category_theory.monoidal.braided
import algebra.module.linear_map
import algebra.category.Module.basic
import algebra.category.FinVect

-- import data.complex.basic
variables (K: Type) [field K]
open_locale tensor_product

inductive tangle: Type
  | id: tangle
  | of(x: bool): tangle
  | tensor: tangle → tangle → tangle

local infix ` ++ ` := tangle.tensor

namespace tangle

@[simp] def flip: tangle → tangle
  | id := id
  | (of x) := of ¬x
  | (tensor a b) := tensor a.flip b.flip

@[simp] def reverse: tangle → tangle
  | (tensor a b) := tensor b.reverse a.reverse
  | a := a

@[simp] def rotate(a: tangle) := a.flip.reverse

--instance: add_comm_monoid (FinVect K) := sorry
--instance: module K (FinVect K) := sorry

/-
#check finite_dimensional_tensor_product
@[simp] def tensor_obj (M N : Module K): Module K := Module.of K (M ⊗[K] N)
@[simp] def product_obj (M N : Module K): Module K := Module.of K (M × N)
@[simp] def K_2: Module K := Module.of K (fin 2 → K)
#check matrix.mul_vec ![![0, 1], ![2, 3]]
-/

end tangle
open tangle

inductive hom: tangle → tangle → Type
  | id (a): hom a a
  | comp {a b c} (f: hom a b) (g: hom b c): hom a c
  | tensor {a b c d} (f: hom a b) (g: hom c d): hom (a ++ c) (b ++ d)
  | associator_hom (a b c): hom ((a ++ b) ++ c) (a ++ (b ++ c))
  | associator_inv (a b c): hom (a ++ (b ++ c)) ((a ++ b) ++ c)
  | left_unitor_hom (a): hom (id ++ a) a
  | left_unitor_inv (a): hom a (id ++ a)
  | right_unitor_hom (a): hom (a ++ id) a
  | right_unitor_inv (a): hom a (a ++ id)
  |   evaluation (a: tangle): hom (a ++ a.rotate) id
  | coevaluation (a: tangle): hom id (a.rotate ++ a)
  | braiding_hom (a b): hom (a ++ b) (b ++ a)
  | braiding_inv (a b): hom (b ++ a) (a ++ b)

local infix ` ⟶ᵐ `:10 := hom
local notation `𝟙` := hom.id
local infix ` ≫ `:80 := hom.comp
local infix ` ⊗ `:70 := hom.tensor
local notation `α` := hom.associator_hom
local notation `α⁻¹` := hom.associator_inv
local notation `ℓ` := hom.left_unitor_hom
local notation `ℓ⁻¹` := hom.left_unitor_inv
local notation `ρ` := hom.right_unitor_hom
local notation `ρ⁻¹` := hom.right_unitor_inv
local notation `ε` := hom.evaluation
local notation `η` := hom.coevaluation
local notation `β` := hom.braiding_hom
local notation `β⁻¹` := hom.braiding_inv

inductive hom_equiv : Π {X Y}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
  | refl {X Y} (f: X ⟶ᵐ Y): hom_equiv f f
  | symm {X Y} (f g: X ⟶ᵐ Y): hom_equiv f g → hom_equiv g f
  | trans {X Y} (f g h: X ⟶ᵐ Y): hom_equiv f g → hom_equiv g h → hom_equiv f h
  | comp {X Y Z} {f f': X ⟶ᵐ Y} {g g': Y ⟶ᵐ Z}:
    hom_equiv f f' → hom_equiv g g' → hom_equiv (f ≫ g) (f' ≫ g')
  | tensor {W X Y Z} {f f': W ⟶ᵐ X} {g g': Y ⟶ᵐ Z}:
    hom_equiv f f' → hom_equiv g g' → hom_equiv (f ⊗ g) (f' ⊗ g')
  | id_comp {X Y} (f: X ⟶ᵐ Y): hom_equiv (𝟙 X ≫ f) f
  | comp_id {X Y} (f: X ⟶ᵐ Y): hom_equiv (f ≫ 𝟙 Y) f
  | assoc {W X Y Z} (f: W ⟶ᵐ X) (g: X ⟶ᵐ Y) (h: Y ⟶ᵐ Z):
    hom_equiv ((f ≫ g) ≫ h) (f ≫ (g ≫ h))
  | tensor_id {X Y}: hom_equiv ((𝟙 X) ⊗ (𝟙 Y)) (𝟙 (X ++ Y))
  | tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (f₁: X₁ ⟶ᵐ Y₁) (f₂: X₂ ⟶ᵐ Y₂) (g₁: Y₁ ⟶ᵐ Z₁) (g₂: Y₂ ⟶ᵐ Z₂):
    hom_equiv ((f₁ ≫ g₁) ⊗ (f₂ ≫ g₂)) ((f₁ ⊗ f₂) ≫ (g₁ ⊗ g₂))
  | associator_hom_inv {X Y Z}: hom_equiv (α X Y Z ≫ α⁻¹ X Y Z) (𝟙 ((X ++ Y) ++ Z))
  | associator_inv_hom {X Y Z}: hom_equiv (α⁻¹ X Y Z ≫ α X Y Z) (𝟙 (X ++ (Y ++ Z)))
  | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁: X₁ ⟶ᵐ Y₁) (f₂: X₂ ⟶ᵐ Y₂) (f₃: X₃ ⟶ᵐ Y₃) :
    hom_equiv (((f₁ ⊗ f₂) ⊗ f₃) ≫ α Y₁ Y₂ Y₃) (α X₁ X₂ X₃ ≫ (f₁ ⊗ (f₂ ⊗ f₃)))
  | left_unitor_hom_inv {X}: hom_equiv (ℓ X ≫ ℓ⁻¹ X) (𝟙 (id ++ X))
  | left_unitor_inv_hom {X}: hom_equiv (ℓ⁻¹ X ≫ ℓ X) (𝟙 X)
  | left_unitor_naturality {X Y} (f: X ⟶ᵐ Y): hom_equiv ((𝟙 id ⊗ f) ≫ ℓ Y) (ℓ X ≫ f)
  | right_unitor_hom_inv {X}: hom_equiv (ρ X ≫ ρ⁻¹ X) (𝟙 (X ++ id))
  | right_unitor_inv_hom {X}: hom_equiv (ρ⁻¹ X ≫ ρ X) (𝟙 X)
  | right_unitor_naturality {X Y} (f: X ⟶ᵐ Y): hom_equiv ((f ⊗ 𝟙 id) ≫ ρ Y) (ρ X ≫ f)
  | pentagon {W X Y Z}: hom_equiv
    ((α W X Y ⊗ 𝟙 Z) ≫ (α W (X ++ Y) Z ≫ (𝟙 W ⊗ α X Y Z))) (α (W ++ X) Y Z ≫ α W X (Y ++ Z))
  | triangle {X Y}: hom_equiv (α X id Y ≫ (𝟙 X ⊗ ℓ Y)) (ρ X ⊗ 𝟙 Y)
  | evaluation_coevaluation {X}: hom_equiv
    ((η X ⊗ 𝟙 X.rotate) ≫ (α X.rotate X X.rotate ≫ (𝟙 _ ⊗ ε X))) (ℓ _ ≫ ρ⁻¹ _)
  | coevaluation_evaluation {X}: hom_equiv
    ((𝟙 X ⊗ η X) ≫ (α⁻¹ X X.rotate X ≫ (ε X ⊗ 𝟙 X))) (ρ X ≫ ℓ⁻¹ X)
  | braiding_hom_inv {X Y: tangle}: hom_equiv (β X Y ≫ β⁻¹ X Y) (𝟙 (X ++ Y))
  | braiding_inv_hom {X Y: tangle}: hom_equiv (β⁻¹ X Y ≫ β X Y) (𝟙 (Y ++ X))
  | braiding_naturality {X X' Y Y'} (f : X ⟶ᵐ Y) (g : X' ⟶ᵐ Y'):
    hom_equiv ((f ⊗ g) ≫ β Y Y') (β X X' ≫ (g ⊗ f))
  | hexagon_forward {X Y Z}: hom_equiv
    (α X Y Z ≫ (β X (Y ++ Z) ≫ α Y Z X)) ((β X Y ⊗ 𝟙 Z) ≫ (α Y X Z ≫ (𝟙 Y ⊗ β X Z)))
  | hexagon_reverse {X Y Z}: hom_equiv
    (α⁻¹ X Y Z ≫ (β (X ++ Y) Z ≫ α⁻¹ Z X Y)) ((𝟙 X ⊗ β Y Z) ≫ (α⁻¹ X Z Y ≫ (β X Z ⊗ 𝟙 Y)))

open hom_equiv

def setoid_hom (X Y): setoid (X ⟶ᵐ Y) := ⟨
  hom_equiv, ⟨hom_equiv.refl, hom_equiv.symm, hom_equiv.trans⟩
⟩
local attribute [instance] setoid_hom

instance tangle_category: category_theory.category tangle := {
  hom := λ X Y, quotient (setoid_hom X Y),
  id := λ X, ⟦𝟙 X⟧,
  comp := λ X Y Z, quotient.map₂ hom.comp $ by { intros f f' hf g g' hg, exact comp hf hg },
  id_comp' := by { rintro X Y ⟨f⟩, exact quotient.sound (id_comp f) },
  comp_id' := by { rintro X Y ⟨f⟩, exact quotient.sound (comp_id f) },
  assoc' := by { rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩, exact quotient.sound (assoc f g h) }
}

instance monoidal_category: category_theory.monoidal_category tangle := {
  tensor_obj := λ X Y, X ++ Y,
  tensor_hom := λ X₁ Y₁ X₂ Y₂, quotient.map₂ hom.tensor $ by {
    intros _ _ h₁ _ _ h₂, exact tensor h₁ h₂
  },
  tensor_id' := λ X Y, quotient.sound tensor_id,
  tensor_comp' := λ X₁ Y₁ Z₁ X₂ Y₂ Z₂, by {
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩, exact quotient.sound (tensor_comp f₁ f₂ g₁ g₂),
  },
  tensor_unit := id,
  associator := λ X Y Z, ⟨
    ⟦α X Y Z⟧, ⟦α⁻¹ X Y Z⟧,
    quotient.sound associator_hom_inv, quotient.sound associator_inv_hom
  ⟩,
  associator_naturality' := λ X₁ X₂ X₃ Y₁ Y₂ Y₃, by {
    rintro ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩, exact quotient.sound (associator_naturality f₁ f₂ f₃)
  },
  left_unitor := λ X, ⟨
    ⟦ℓ X⟧, ⟦ℓ⁻¹ X⟧,
    quotient.sound left_unitor_hom_inv, quotient.sound left_unitor_inv_hom
  ⟩,
  left_unitor_naturality' := λ X Y, by {
    rintro ⟨f⟩, exact quotient.sound (left_unitor_naturality f)
  },
  right_unitor := λ X, ⟨
    ⟦ρ X⟧, ⟦ρ⁻¹ X⟧,
    quotient.sound right_unitor_hom_inv, quotient.sound right_unitor_inv_hom
  ⟩,
  right_unitor_naturality' := λ X Y, by {
    rintro ⟨f⟩, exact quotient.sound (right_unitor_naturality f)
  },
  pentagon' := λ W X Y Z, quotient.sound pentagon,
  triangle' := λ X Y, quotient.sound triangle
}

instance left_rigid_category: category_theory.left_rigid_category tangle := {
  left_dual := λ X, {
    left_dual := X.rotate,
    exact := {
      evaluation := ⟦ε X⟧,
      coevaluation := ⟦η X⟧,
      evaluation_coevaluation' := quotient.sound hom_equiv.evaluation_coevaluation,
      coevaluation_evaluation' := quotient.sound hom_equiv.coevaluation_evaluation
    }
  }
}

instance braided_category: category_theory.braided_category tangle := {
  braiding := λ X Y, {
    hom := ⟦β X Y⟧,
    inv := ⟦β⁻¹ X Y⟧,
    hom_inv_id' := quotient.sound hom_equiv.braiding_hom_inv,
    inv_hom_id' := quotient.sound hom_equiv.braiding_inv_hom
  },
  braiding_naturality' := λ W X Y Z,
    by { rintro ⟨f⟩ ⟨g⟩, exact quotient.sound (hom_equiv.braiding_naturality f g)},
  hexagon_forward' := λ X Y Z, quotient.sound (hom_equiv.hexagon_forward),
  hexagon_reverse' := λ X Y Z, quotient.sound (hom_equiv.hexagon_reverse)
}

abbreviation down := of tt
abbreviation up := of ff
abbreviation vert  := 𝟙 down
abbreviation vert' := 𝟙 up
abbreviation cap  := η down
abbreviation cap' := η up
abbreviation cup  := ε down
abbreviation cup' := ε up
abbreviation over  := β down down
abbreviation under := β⁻¹ down down

local notation `↓` := vert
local notation `↑` := vert'
local notation `∩↓` := cap
local notation `∩↑` := cap'
local notation `∪↓` := cup'
local notation `∪↑` := cup
local notation `↓\↓` := over
local notation `↓/↓` := under

#check ∩↓ ⊗ ↓ ⊗ ↑
#check ↑ ⊗ ↓\↓ ⊗ ↑
#check ↑ ⊗ ↓ ⊗ ∪↑

abbreviation rotate_left (X: down ++ down ⟶ᵐ down ++ down) := (ℓ⁻¹ _ ⊗ 𝟙 _)
  ≫ (∩↓ ⊗ ↓ ⊗ ↑) ≫ (α _ _ _ ⊗ 𝟙 _)
  ≫ (↑ ⊗ X ⊗ ↑) ≫ α _ _ _ ≫ (𝟙 _ ⊗ α _ _ _) ≫ α⁻¹ _ _ _
  ≫ (↑ ⊗ ↓ ⊗ ∪↑) ≫ ρ _

#check rotate_left over
#check rotate_left under

local notation `↓\↑` := rotate_left under
local notation `↓/↑` := rotate_left over

-- ローラン多項式環 or 体を複素数として t を 0 以外の数 (unit complex ?)