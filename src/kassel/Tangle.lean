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
end Tangle
open Tangle

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

namespace hom
  infix ` ⟶ᵐ `: 10 := hom
  infix ` ≫ `: 60 := hom.comp
  infix ` ⊗ᵐ `: 70 := hom.tensor
  notation `𝟙` := hom.id
  notation `α` := hom.associator_hom
  notation `α⁻¹` := hom.associator_inv
  notation `ℓ` := hom.left_unitor_hom
  notation `ℓ⁻¹` := hom.left_unitor_inv
  notation `ρ` := hom.right_unitor_hom
  notation `ρ⁻¹` := hom.right_unitor_inv
  notation `ε` := evaluation
  notation `η` := coevaluation
  notation `β` := braiding_hom
  notation `β⁻¹` := braiding_inv
end hom
open hom

/-
  associator, unitor の自動補完を試みる
  → associator はむずそうなので unitor だけでも……
-/

namespace Tangle
  @[simp] def remove_unit: Tangle → Tangle
    | (id ⊗ᵗ a) := a.remove_unit
    | (a ⊗ᵗ id) := a.remove_unit
    | (a ⊗ᵗ b) := a.remove_unit ⊗ᵗ b.remove_unit
    | a := a

  @[simp] def remove_unit_left (a): (id ⊗ᵗ a).remove_unit = a.remove_unit := by induction a; tidy
  @[simp] def remove_unit_right (a): (a ⊗ᵗ id).remove_unit = a.remove_unit := by induction a; tidy
  @[simp] def remove_unit_tensor (a b) [a ≠ id] [b ≠ id]: (a ⊗ᵗ b).remove_unit = (a.remove_unit ⊗ᵗ b.remove_unit) := begin
    induction b,
      contradiction,
      repeat {induction a, contradiction, simp, simp},
  end

  @[simp] def sorted: Tangle → Prop
    | (a ⊗ᵗ (b ⊗ᵗ c)) := false
    | (a ⊗ᵗ b) := a.sorted
    | _ := true

  @[simp] def tail: Tangle → Tangle
    | (a ⊗ᵗ b) := b.tail
    | a := a
  @[simp] def heads: Tangle → Tangle
    | (a ⊗ᵗ (b ⊗ᵗ c)) := a ⊗ᵗ (b ⊗ᵗ c).heads
    | (a ⊗ᵗ b) := a
    | _ := id

  @[simp] def heads_sizeof (a: Tangle) (h: 2 < a.sizeof): a.heads.sizeof < a.sizeof := begin
    sorry, /-induction a,
      simp at *, contradiction,
      simp at *,-/
  end

  @[simp] def sort: Tangle → Tangle
    | (a ⊗ᵗ b) :=
      have (a ⊗ᵗ b).heads.sizeof < 1 + a.sizeof + b.sizeof,
      from begin sorry, /-
        have h: 2 < (a ⊗ᵗ b).sizeof := by sorry,
        have h2 := heads_sizeof _ h, simp at h2,
        have h3 := has_lt.lt.trans,
        sorry, -- induction b, simp, -/
      end, ((a ⊗ᵗ b).heads).sort ⊗ᵗ (a ⊗ᵗ b).tail
    | a := a

-- nat.exists_eq_add_of_lt

  @[simp] def sort_sorted (a: Tangle): sorted a.sort := begin
    induction a with _ a b ha hb,
      repeat {simp}, induction b, simp,

  end

  /-
  @[simp] mutual def sort_aux, sort'
    with sort_aux: Tangle → Tangle → Tangle
    | a (b ⊗ᵗ c) := sort_aux (a ⊗ᵗ b) c
    | a b := a.sort' ⊗ᵗ b
    with sort': Tangle → Tangle
    | (a ⊗ᵗ b) := sort_aux a b
    | a := a
  -/
end Tangle

namespace hom
  @[simp] def unitor: Π a, a ⟶ᵐ a.remove_unit
    | (Tangle.id ⊗ᵗ a) := by simp; exact ℓ a ≫ unitor a
    | (a ⊗ᵗ Tangle.id) := by simp; exact ρ a ≫ unitor a
    | (of x ⊗ᵗ of y) := unitor _ ⊗ᵐ unitor _
    | (of x ⊗ᵗ (a ⊗ᵗ b)) := unitor _ ⊗ᵐ unitor _
    | ((a ⊗ᵗ b) ⊗ᵗ of x) := unitor _ ⊗ᵐ unitor _
    | ((a ⊗ᵗ b) ⊗ᵗ (c ⊗ᵗ d)) := unitor _ ⊗ᵐ unitor _
    | Tangle.id := 𝟙 _
    | (of x) := 𝟙 _

  @[simp] def sorter: Π a, a ⟶ᵐ a.sort
    | (a ⊗ᵗ (b ⊗ᵗ c)) := begin
      have f := 𝟙 a ⊗ᵐ sorter (b ⊗ᵗ c) ≫ α⁻¹ _ _ _ ≫ (sorter _ ⊗ᵐ 𝟙 _),
      have h: (a ⊗ᵗ (b ⊗ᵗ c).heads).sort ⊗ᵗ (b ⊗ᵗ c).tail = (a ⊗ᵗ (b ⊗ᵗ c)).sort := begin
        induction a, induction b, induction c,
          simp,
      end,
      rw h at f, exact f,
    end
    | (a ⊗ᵗ b) := 

  @[simp] def inverse: Π {a b}, (a ⟶ᵐ b) → (b ⟶ᵐ a)
    | _ _ (𝟙 _) := 𝟙 _
    | _ _ (f ≫ g) := g.inverse ≫ f.inverse
    | _ _ (f ⊗ᵐ g) := f.inverse ⊗ᵐ g.inverse
    | _ _ (α _ _ _) := α⁻¹ _ _ _
    | _ _ (α⁻¹ _ _ _) := α _ _ _
    | _ _ (ℓ _) := ℓ⁻¹ _
    | _ _ (ℓ⁻¹ _) := ℓ _
    | _ _ (ρ _) := ρ⁻¹ _
    | _ _ (ρ⁻¹ _) := ρ _
    | _ _ (ε a) := begin have f := η (a.rotate), simp only [rotate_rotate] at f, exact f, end
    | _ _ (η a) := begin have f := ε (a.rotate), simp only [rotate_rotate] at f, exact f, end
    | _ _ (β _ _) := β⁻¹ _ _
    | _ _ (β⁻¹ _ _) := β _ _

  @[simp] def unitor_inv (a) := (unitor a).inverse

  def normalize {a b} (f: a ⟶ᵐ b) := unitor_inv _ ≫ f ≫ unitor _
  notation `υ` := normalize
end hom

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

  | relation_1_1: hom_equiv (υ (𝟙 ↓ ⊗ᵐ η ↓ ≫ α⁻¹ _ _ _ ≫ ε ↓ ⊗ᵐ 𝟙 ↓)) (𝟙 ↓)
  | relation_1_2: hom_equiv (υ (η ↑ ⊗ᵐ 𝟙 ↓ ≫ α _ _ _ ≫ 𝟙 ↓ ⊗ᵐ ε ↑)) (𝟙 ↓)
  | relation_2_1: hom_equiv (υ (𝟙 ↑ ⊗ᵐ η ↑ ≫ α⁻¹ _ _ _ ≫ ε ↑ ⊗ᵐ 𝟙 ↑)) (𝟙 ↑)
  | relation_2_2: hom_equiv (υ (η ↓ ⊗ᵐ 𝟙 ↑ ≫ α _ _ _ ≫ 𝟙 ↑ ⊗ᵐ ε ↓)) (𝟙 ↑)
  | relation_3_1: hom_equiv (
    υ (η ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑) ≫ _
    ≫ υ (𝟙 ↑ ⊗ᵐ η ↓ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑) /- ≫ _
    ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ β ↓ ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ≫ _
    ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ ε ↓ ⊗ᵐ 𝟙 ↑ ≫ _
    ≫ 𝟙 ↑ ⊗ᵐ 𝟙 ↑ ⊗ᵐ ε ↓ ≫ ρ _-/
  ) (
    _
  )
#check 𝟙 ↑ ⊗ᵐ η ↓ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↑

namespace Tangle

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

end Tangle
