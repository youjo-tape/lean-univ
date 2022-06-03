import category_theory.monoidal.rigid
import category_theory.monoidal.braided
import data.nat.basic

inductive Tangle: Type
  | id: Tangle
  | of(x: bool): Tangle
  | tensor: Tangle → Tangle → Tangle

namespace Tangle
  infix ` ⊗ᵗ `:50 := Tangle.tensor
  notation `↓` := Tangle.of tt
  notation `↑` := Tangle.of ff

  @[simp] def flip: Tangle → Tangle
    | id := id
    | (of x) := of ¬x
    | (a ⊗ᵗ b) := a.flip ⊗ᵗ b.flip

  @[simp] def reverse: Tangle → Tangle
    | (a ⊗ᵗ b) := b.reverse ⊗ᵗ a.reverse
    | a := a

  @[simp] def rotate (a: Tangle) := a.flip.reverse
  @[simp] def rotate_rotate (a: Tangle): a.rotate.rotate = a := by induction a; tidy

  inductive hom: Tangle → Tangle → Type
    | id (a): hom a a
    | comp {a b c} (f: hom a b) (g: hom b c): hom a c
    | tensor {a b c d} (f: hom a b) (g: hom c d): hom (a ⊗ᵗ c) (b ⊗ᵗ d)
    | associator_hom (a b c): hom ((a ⊗ᵗ b) ⊗ᵗ c) (a ⊗ᵗ (b ⊗ᵗ c))
    | associator_inv (a b c): hom (a ⊗ᵗ (b ⊗ᵗ c)) ((a ⊗ᵗ b) ⊗ᵗ c)
    | left_unitor_hom (a): hom (id ⊗ᵗ a) a
    | left_unitor_inv (a): hom a (id ⊗ᵗ a)
    | right_unitor_hom (a): hom (a ⊗ᵗ id) a
    | right_unitor_inv (a): hom a (a ⊗ᵗ id)
    | evaluation (a): hom (a ⊗ᵗ a.rotate) id
    | coevaluation (a: Tangle): hom id (a.rotate ⊗ᵗ a)
    | braiding_hom (a b): hom (a ⊗ᵗ b) (b ⊗ᵗ a)
    | braiding_inv (a b): hom (b ⊗ᵗ a) (a ⊗ᵗ b)

  infix ` ⟶ᵐ `: 10 := hom
  local infix ` ≫ `: 60 := hom.comp
  infix ` ⊗ᵐ `: 70 := hom.tensor
  notation `𝟙` := hom.id
  notation `α` := hom.associator_hom
  notation `α⁻¹` := hom.associator_inv
  notation `ℓ` := hom.left_unitor_hom
  notation `ℓ⁻¹` := hom.left_unitor_inv
  notation `ρ` := hom.right_unitor_hom
  notation `ρ⁻¹` := hom.right_unitor_inv
  notation `ε` := hom.evaluation
  notation `η` := hom.coevaluation
  notation `β` := hom.braiding_hom
  notation `β⁻¹` := hom.braiding_inv

  inductive hom_equiv: Π {X Y}, (X ⟶ᵐ Y) → (X ⟶ᵐ Y) → Prop
    | refl {X Y} (f: X ⟶ᵐ Y): hom_equiv f f
    | symm {X Y} (f g: X ⟶ᵐ Y): hom_equiv f g → hom_equiv g f
    | trans {X Y} (f g h: X ⟶ᵐ Y): hom_equiv f g → hom_equiv g h → hom_equiv f h

    | comp {X Y Z} {f₁ f₂: X ⟶ᵐ Y} {g₁ g₂: Y ⟶ᵐ Z}: hom_equiv f₁ f₂ → hom_equiv g₁ g₂ → hom_equiv (f₁ ≫ g₁) (f₂ ≫ g₂)
    | id_comp {X Y} (f: X ⟶ᵐ Y): hom_equiv (𝟙 X ≫ f) f
    | comp_id {X Y} (f: X ⟶ᵐ Y): hom_equiv (f ≫ 𝟙 Y) f
    | assoc {W X Y Z} (f: W ⟶ᵐ X) (g: X ⟶ᵐ Y) (h: Y ⟶ᵐ Z): hom_equiv ((f ≫ g) ≫ h) (f ≫ (g ≫ h))

    | tensor {X₁ Y₁ X₂ Y₂} {f₁ g₁: X₁ ⟶ᵐ Y₁} {f₂ g₂: X₂ ⟶ᵐ Y₂}: hom_equiv f₁ g₁ → hom_equiv f₂ g₂ → hom_equiv (f₁ ⊗ᵐ f₂) (g₁ ⊗ᵐ g₂)
    | tensor_id {X Y}: hom_equiv (𝟙 X ⊗ᵐ 𝟙 Y) (𝟙 (X ⊗ᵗ Y))
    | tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂} (f₁: X₁ ⟶ᵐ Y₁) (f₂: X₂ ⟶ᵐ Y₂) (g₁: Y₁ ⟶ᵐ Z₁) (g₂: Y₂ ⟶ᵐ Z₂): hom_equiv ((f₁ ≫ g₁) ⊗ᵐ (f₂ ≫ g₂)) ((f₁ ⊗ᵐ f₂) ≫ (g₁ ⊗ᵐ g₂))
    | associator_hom_inv {X Y Z}: hom_equiv (α X Y Z ≫ α⁻¹ X Y Z) (𝟙 ((X ⊗ᵗ Y) ⊗ᵗ Z))
    | associator_inv_hom {X Y Z}: hom_equiv (α⁻¹ X Y Z ≫ α X Y Z) (𝟙 (X ⊗ᵗ (Y ⊗ᵗ Z)))
    | associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} (f₁: X₁ ⟶ᵐ Y₁) (f₂: X₂ ⟶ᵐ Y₂) (f₃: X₃ ⟶ᵐ Y₃): hom_equiv (((f₁ ⊗ᵐ f₂) ⊗ᵐ f₃) ≫ α Y₁ Y₂ Y₃) (α X₁ X₂ X₃ ≫ (f₁ ⊗ᵐ (f₂ ⊗ᵐ f₃)))
    | left_unitor_hom_inv {X}: hom_equiv (ℓ X ≫ ℓ⁻¹ X) (𝟙 (id ⊗ᵗ X))
    | left_unitor_inv_hom {X}: hom_equiv (ℓ⁻¹ X ≫ ℓ X) (𝟙 X)
    | left_unitor_naturality {X Y} (f: X ⟶ᵐ Y): hom_equiv ((𝟙 id ⊗ᵐ f) ≫ ℓ Y) (ℓ X ≫ f)
    | right_unitor_hom_inv {X}: hom_equiv (ρ X ≫ ρ⁻¹ X) (𝟙 (X ⊗ᵗ id))
    | right_unitor_inv_hom {X}: hom_equiv (ρ⁻¹ X ≫ ρ X) (𝟙 X)
    | right_unitor_naturality {X Y} (f: X ⟶ᵐ Y): hom_equiv ((f ⊗ᵐ 𝟙 id) ≫ ρ Y) (ρ X ≫ f)
    | pentagon {W X Y Z}: hom_equiv ((α W X Y ⊗ᵐ 𝟙 Z) ≫ (α W (X ⊗ᵗ Y) Z ≫ (𝟙 W ⊗ᵐ α X Y Z))) (α (W ⊗ᵗ X) Y Z ≫ α W X (Y ⊗ᵗ Z))
    | triangle {X Y}: hom_equiv (α X id Y ≫ (𝟙 X ⊗ᵐ ℓ Y)) (ρ X ⊗ᵐ 𝟙 Y)

    | relation_1_1: hom_equiv (ρ⁻¹ _ ≫ 𝟙 ↓ ⊗ᵐ η ↓ ≫ α⁻¹ _ _ _ ≫ ε ↓ ⊗ᵐ 𝟙 ↓ ≫ ℓ _) (𝟙 ↓)
    | relation_1_2: hom_equiv (ℓ⁻¹ _ ≫ η ↑ ⊗ᵐ 𝟙 ↓ ≫ α _ _ _ ≫ 𝟙 ↓ ⊗ᵐ ε ↑ ≫ ρ _) (𝟙 ↓)
    | relation_2_1: hom_equiv (ρ⁻¹ _ ≫ 𝟙 ↑ ⊗ᵐ η ↑ ≫ α⁻¹ _ _ _ ≫ ε ↑ ⊗ᵐ 𝟙 ↑ ≫ ℓ _) (𝟙 ↑)
    | relation_2_2: hom_equiv (ℓ⁻¹ _ ≫ η ↓ ⊗ᵐ 𝟙 ↑ ≫ α _ _ _ ≫ 𝟙 ↑ ⊗ᵐ ε ↓ ≫ ρ _) (𝟙 ↑)
    | relation_3_1: hom_equiv (              ℓ⁻¹ _ ≫ α⁻¹ _ _ _
      ≫ η ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑                 ≫ ρ⁻¹ _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ η ↓ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑   ≫ (α⁻¹ _ _ _ ⊗ᵐ 𝟙 _ ≫ α _ _ _) ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ β ↓ ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ≫ (α _ _ _ ≫ 𝟙 _ ⊗ᵐ α _ _ _ ≫ α⁻¹ _ _ _) ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ ε ↓ ⊗ᵐ 𝟙 ↑   ≫ ρ _ ⊗ᵐ 𝟙 _ ≫ α _ _ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ ε ↓                 ≫ ρ _
    ) (                                      ρ⁻¹ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ η ↑                 ≫ α⁻¹ _ _ _ ≫ ρ⁻¹ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ η ↑ ⊗ᵐ 𝟙 ↑   ≫ (α _ _ _ ≫ 𝟙 _ ⊗ᵐ α⁻¹ _ _ _ ≫ α⁻¹ _ _ _) ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ β ↓ ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ≫ (α⁻¹ _ _ _ ≫ α _ _ _ ⊗ᵐ 𝟙 _) ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ ε ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑   ≫ ρ _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _
      ≫ ε ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑                 ≫ α _ _ _ ≫ ℓ _
    )
    | relation_3_2: hom_equiv (                ℓ⁻¹ _ ≫ α⁻¹ _ _ _
      ≫ η ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑                   ≫ ρ⁻¹ _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ η ↓ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑     ≫ (α⁻¹ _ _ _ ⊗ᵐ 𝟙 _ ≫ α _ _ _) ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ β⁻¹ ↓ ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ≫ (α _ _ _ ≫ 𝟙 _ ⊗ᵐ α _ _ _ ≫ α⁻¹ _ _ _) ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ ε ↓ ⊗ᵐ 𝟙 ↑     ≫ ρ _ ⊗ᵐ 𝟙 _ ≫ α _ _ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ ε ↓                   ≫ ρ _
    ) (                                        ρ⁻¹ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ η ↑                   ≫ α⁻¹ _ _ _ ≫ ρ⁻¹ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ η ↑ ⊗ᵐ 𝟙 ↑     ≫ (α _ _ _ ≫ 𝟙 _ ⊗ᵐ α⁻¹ _ _ _ ≫ α⁻¹ _ _ _) ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ β⁻¹ ↓ ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ≫ (α⁻¹ _ _ _ ≫ α _ _ _ ⊗ᵐ 𝟙 _) ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ ε ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑     ≫ ρ _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _
      ≫ ε ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑                   ≫ α _ _ _ ≫ ℓ _
    )
    | relation_4_1: hom_equiv (β ↓ ↓ ≫ β⁻¹ ↓ ↓) (𝟙 _)
    | relation_4_2: hom_equiv (β⁻¹ ↓ ↓ ≫ β ↓ ↓) (𝟙 _)
    | relation_5: hom_equiv
      (α⁻¹ _ _ _ ≫ β ↓ ↓ ⊗ᵐ 𝟙 ↓ ≫ α _ _ _ ≫ 𝟙 ↓ ⊗ᵐ β ↓ ↓ ≫ α⁻¹ _ _ _ ≫ β ↓ ↓ ⊗ᵐ 𝟙 ↓)
      (𝟙 ↓ ⊗ᵐ β ↓ ↓ ≫ α⁻¹ _ _ _ ≫ β ↓ ↓ ⊗ᵐ 𝟙 ↓ ≫ α _ _ _ ≫ 𝟙 ↓ ⊗ᵐ β ↓ ↓ ≫ α⁻¹ _ _ _)
    | relation_6_1: hom_equiv (ρ⁻¹ _ ≫ 𝟙 ↓ ⊗ᵐ η ↑ ≫ α⁻¹ _ _ _ ≫ β ↓ ↓ ⊗ᵐ 𝟙 ↑ ≫ α _ _ _ ≫ 𝟙 ↓ ⊗ᵐ ε ↓ ≫ ρ _) (𝟙 ↓)
    | relation_6_2: hom_equiv (ρ⁻¹ _ ≫ 𝟙 ↓ ⊗ᵐ η ↑ ≫ α⁻¹ _ _ _ ≫ β⁻¹ ↓ ↓ ⊗ᵐ 𝟙 ↑ ≫ α _ _ _ ≫ 𝟙 ↓ ⊗ᵐ ε ↓ ≫ ρ _) (𝟙 ↓)
    | relation_7_1: hom_equiv (  ℓ⁻¹ _ ⊗ᵐ 𝟙 _
      ≫ η ↓ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑     ≫ α _ _ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ β⁻¹ ↓ ↓ ⊗ᵐ 𝟙 ↑ ≫ α⁻¹ _ _ _ ⊗ᵐ 𝟙 _ ≫ α _ _ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ ε ↓
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ η ↑     ≫ α⁻¹ _ _ _ ≫ α _ _ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ β ↓ ↓ ⊗ᵐ 𝟙 ↑   ≫ α⁻¹ _ _ _ ⊗ᵐ 𝟙 _
      ≫ ε ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑     ≫ ℓ _ ⊗ᵐ 𝟙 _
    ) (𝟙 ↓ ⊗ᵐ 𝟙 ↑)
    | relation_7_2: hom_equiv (  ℓ⁻¹ _ ⊗ᵐ 𝟙 _
      ≫ η ↓ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑     ≫ α _ _ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ β ↓ ↓ ⊗ᵐ 𝟙 ↑   ≫ α⁻¹ _ _ _ ⊗ᵐ 𝟙 _ ≫ α _ _ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ ε ↓
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ η ↑     ≫ α⁻¹ _ _ _ ≫ α _ _ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ β⁻¹ ↓ ↓ ⊗ᵐ 𝟙 ↑ ≫ α⁻¹ _ _ _ ⊗ᵐ 𝟙 _
      ≫ ε ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑     ≫ ℓ _ ⊗ᵐ 𝟙 _
    ) (𝟙 ↓ ⊗ᵐ 𝟙 ↑)
    | relation_8_1: hom_equiv (  ρ⁻¹ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ η ↑     ≫ α⁻¹ _ _ _ ≫ α _ _ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ β ↓ ↓ ⊗ᵐ 𝟙 ↑   ≫ α⁻¹ _ _ _ ⊗ᵐ 𝟙 _
      ≫ ε ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑
      ≫ η ↓ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑     ≫ α _ _ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ β⁻¹ ↓ ↓ ⊗ᵐ 𝟙 ↑ ≫ α⁻¹ _ _ _ ⊗ᵐ 𝟙 _ ≫ α _ _ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ ε ↓     ≫ ρ _
    ) (𝟙 ↑ ⊗ᵐ 𝟙 ↓)
    | relation_8_2: hom_equiv (  ρ⁻¹ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ η ↑     ≫ α⁻¹ _ _ _ ≫ α _ _ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ β⁻¹ ↓ ↓ ⊗ᵐ 𝟙 ↑ ≫ α⁻¹ _ _ _ ⊗ᵐ 𝟙 _
      ≫ ε ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑
      ≫ η ↓ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑     ≫ α _ _ _ ⊗ᵐ 𝟙 _
      ≫ 𝟙 ↑ ⊗ᵐ β ↓ ↓ ⊗ᵐ 𝟙 ↑   ≫ α⁻¹ _ _ _ ⊗ᵐ 𝟙 _ ≫ α _ _ _
      ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ ε ↓     ≫ ρ _
    ) (𝟙 ↑ ⊗ᵐ 𝟙 ↓)

  @[instance] def setoid_hom (X Y): setoid (X ⟶ᵐ Y) := ⟨
    hom_equiv, ⟨hom_equiv.refl, hom_equiv.symm, hom_equiv.trans⟩
  ⟩

  instance category: category_theory.category Tangle := {
    hom := λ X Y, quotient (setoid_hom X Y),
    id := λ X, ⟦𝟙 X⟧,
    comp := λ X Y Z, quotient.map₂ hom.comp (λ _ _ hf _ _ hg, hom_equiv.comp hf hg),
    id_comp' := by rintro _ _ ⟨f⟩; exact quotient.sound (hom_equiv.id_comp f),
    comp_id' := by rintro _ _ ⟨f⟩; exact quotient.sound (hom_equiv.comp_id f),
    assoc' := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩; exact quotient.sound (hom_equiv.assoc f g h),
  }

  instance monoidal_category: category_theory.monoidal_category Tangle := {
    tensor_obj := λ X Y, X ⊗ᵗ Y,
    tensor_hom := λ _ _ _ _, quotient.map₂ (⊗ᵐ) (λ _ _ h₁ _ _ h₂, hom_equiv.tensor h₁ h₂),
    tensor_id' := λ _ _, quotient.sound hom_equiv.tensor_id,
    tensor_comp' := by rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩; exact quotient.sound (hom_equiv.tensor_comp f₁ f₂ g₁ g₂),
    tensor_unit := id,
    associator := λ X Y Z, ⟨
      ⟦α X Y Z⟧, ⟦α⁻¹ X Y Z⟧,
      quotient.sound hom_equiv.associator_hom_inv,
      quotient.sound hom_equiv.associator_inv_hom,
    ⟩,
    associator_naturality' := by rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩; exact quotient.sound (hom_equiv.associator_naturality f₁ f₂ f₃),
    left_unitor := λ X, ⟨
      ⟦ℓ X⟧, ⟦ℓ⁻¹ X⟧,
      quotient.sound hom_equiv.left_unitor_hom_inv,
      quotient.sound hom_equiv.left_unitor_inv_hom,
    ⟩,
    left_unitor_naturality' := by rintro _ _ ⟨f⟩; exact quotient.sound (hom_equiv.left_unitor_naturality f),
    right_unitor := λ X, ⟨
      ⟦ρ X⟧, ⟦ρ⁻¹ X⟧,
      quotient.sound hom_equiv.right_unitor_hom_inv,
      quotient.sound hom_equiv.right_unitor_inv_hom,
    ⟩,
    right_unitor_naturality' := by rintro _ _ ⟨f⟩; exact quotient.sound (hom_equiv.right_unitor_naturality f),
    pentagon' := λ _ _ _ _, quotient.sound hom_equiv.pentagon,
    triangle' := λ _ _, quotient.sound hom_equiv.triangle,
  }

/-
  instance left_rigid_category: category_theory.left_rigid_category Tangle := {
    left_dual := λ X, {
      left_dual := X.rotate,
      exact := {
        evaluation := ⟦ε X⟧,
        coevaluation := ⟦η X⟧,
        evaluation_coevaluation' := quotient.sound hom_equiv.evaluation_coevaluation,
        coevaluation_evaluation' := quotient.sound hom_equiv.coevaluation_evaluation,
      }
    }
  }

  instance braided_category: category_theory.braided_category Tangle := {
    braiding := λ X Y, {
      hom := ⟦β X Y⟧,
      inv := ⟦β⁻¹ Y X⟧,
      hom_inv_id' := quotient.sound hom_equiv.braiding_hom_inv,
      inv_hom_id' := quotient.sound hom_equiv.braiding_inv_hom,
    },
    braiding_naturality' := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩; exact quotient.sound (hom_equiv.braiding_naturality f g),
    hexagon_forward' := λ X Y Z, quotient.sound (hom_equiv.hexagon_forward),
    hexagon_reverse' := λ X Y Z, quotient.sound (hom_equiv.hexagon_reverse),
  }
-/

end Tangle
