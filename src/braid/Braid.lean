import category_theory.monoidal.braided

inductive Braid: Type
  | node: Braid
  | tensor: Braid → Braid → Braid

namespace Braid
  notation `↓` := node
  infix ` ⊗ᵗ `:50 := tensor
end Braid
open Braid

inductive hom: Braid → Braid → Type
  | id: hom ↓ ↓
  | braiding_hom: hom (↓ ⊗ᵗ ↓) (↓ ⊗ᵗ ↓)
  | braiding_inv: hom (↓ ⊗ᵗ ↓) (↓ ⊗ᵗ ↓)
  | comp {X Y Z} (f: hom X Y) (g: hom Y Z): hom X Z
  | tensor {X₁ Y₁ X₂ Y₂} (f: hom X₁ Y₁) (g: hom X₂ Y₂): hom (X₁ ⊗ᵗ X₂) (Y₁ ⊗ᵗ Y₂)
  | associator_hom (X Y Z): hom ((X ⊗ᵗ Y) ⊗ᵗ Z) (X ⊗ᵗ (Y ⊗ᵗ Z))
  | associator_inv (X Y Z): hom (X ⊗ᵗ (Y ⊗ᵗ Z)) ((X ⊗ᵗ Y) ⊗ᵗ Z)

namespace hom
  infix ` ⟶ᵐ `: 10 := hom
  notation `𝟙` := hom.id
  notation `β` := hom.braiding_hom
  notation `β⁻¹` := hom.braiding_inv
  infix ` ≫ `: 60 := hom.comp
  infix ` ⊗ᵐ `: 70 := hom.tensor
  notation `α` := hom.associator_hom
  notation `α⁻¹` := hom.associator_inv

  def ids: Π X, X ⟶ᵐ X
    | ↓ := 𝟙
    | (X ⊗ᵗ Y) := ids X ⊗ᵐ ids Y
end hom
open hom

inductive hom_equiv: Π {X Y}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
  | refl {X Y} (f: X ⟶ᵐ Y): hom_equiv f f
  | symm {X Y} (f g: X ⟶ᵐ Y): hom_equiv f g → hom_equiv g f
  | trans {X Y} (f g h: X ⟶ᵐ Y): hom_equiv f g → hom_equiv g h → hom_equiv f h

  | comp {X Y Z} {f₁ f₂: X ⟶ᵐ Y} {g₁ g₂: Y ⟶ᵐ Z}: hom_equiv f₁ f₂ → hom_equiv g₁ g₂ → hom_equiv (f₁ ≫ g₁) (f₂ ≫ g₂)
  | id_comp {X Y} (f: X ⟶ᵐ Y): hom_equiv (ids X ≫ f) f
  | comp_id {X Y} (f: X ⟶ᵐ Y): hom_equiv (f ≫ ids Y) f
  | assoc {W X Y Z} (f: W ⟶ᵐ X) (g: X ⟶ᵐ Y) (h: Y ⟶ᵐ Z): hom_equiv ((f ≫ g) ≫ h) (f ≫ (g ≫ h))

namespace Braid
  @[instance] def setoid_hom (X Y): setoid (X ⟶ᵐ Y) := ⟨
    hom_equiv, ⟨hom_equiv.refl, hom_equiv.symm, hom_equiv.trans⟩
  ⟩

  @[instance] def category: category_theory.category Braid := {
    hom := λ X Y, quotient (setoid_hom X Y),
    id := λ X, ⟦ids X⟧,
    comp := λ X Y Z, quotient.map₂ hom.comp (λ _ _ hf _ _ hg, hom_equiv.comp hf hg),
    id_comp' := by rintro _ _ ⟨f⟩; exact quotient.sound (hom_equiv.id_comp f),
    comp_id' := by rintro _ _ ⟨f⟩; exact quotient.sound (hom_equiv.comp_id f),
    assoc' := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩; exact quotient.sound (hom_equiv.assoc f g h),
  }
end Braid