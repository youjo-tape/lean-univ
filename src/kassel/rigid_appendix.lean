import category_theory.monoidal.rigid.basic
import algebra.category.FinVect

namespace kassel
open category_theory
open category_theory.monoidal_category

universes v u

section
  variables
    (C: Type u)
    [category.{v} C]
    [monoidal_category.{v} C]
    [right_rigid_category.{v} C]

  -- * Show that `X ⊗ Y` and `Yᘁ ⊗ Xᘁ` form an exact pairing.

  lemma tensor_comp_id {X₁ X₂ Y₁ Y₂ Y₃: C} (f: X₁ ⟶ X₂) (g: Y₁ ⟶ Y₂) (h: Y₂ ⟶ Y₃):
  f ⊗ (g ≫ h) = (f ⊗ g) ≫ (𝟙 X₂ ⊗ h) := by rw ←category.comp_id f; rw tensor_comp; simp
  lemma comp_tensor_id {X₁ X₂ X₃ Y₁ Y₂: C} (f: X₁ ⟶ X₂) (g: X₂ ⟶ X₃) (h: Y₁ ⟶ Y₂):
  (f ≫ g) ⊗ h = (f ⊗ h) ≫ (g ⊗ 𝟙 Y₂) := by rw ←category.comp_id h; rw tensor_comp; simp
  
  def tensor_exact_pairing {X Y: C}: exact_pairing (X ⊗ Y) (Yᘁ ⊗ Xᘁ) := {
    coevaluation := η_ X Xᘁ ≫ (𝟙 _ ⊗ (λ_ _).inv) ≫ (𝟙 _ ⊗ η_ Y Yᘁ ⊗ 𝟙 _) ≫ (𝟙 _ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv,
    evaluation := (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (α_ _ _ _).inv) ≫ (𝟙 _ ⊗ ε_ X Xᘁ ⊗ 𝟙 _) ≫ (𝟙 _ ⊗ (λ_ _).hom) ≫ ε_ Y Yᘁ,
    coevaluation_evaluation' := begin
      simp only [category.assoc, tensor_comp_id, comp_tensor_id],
      slice_lhs 3 4 { rw ←id_tensor_comp, },
    end,
    evaluation_coevaluation' := sorry,
  }

  /-
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
  -/

  -- * Define pivotal categories (rigid categories equipped with a natural isomorphism `ᘁᘁ ≅ 𝟙 C`).
  -- 参考: https://tqft.net/web/research/students/SamQuinn/thesis.pdf

  class right_pivotal_category :=
    (right_pivotor: Π X: C, X ≅ Xᘁᘁ)
    (notation `φ_` := right_pivotor)
    (right_pivotor_naturality': ∀ {X Y: C} (f: X ⟶ Y), f ≫ (φ_ Y).hom = (φ_ X).hom ≫ fᘁᘁ)
    -- (pivotor_monoidal_naturality: ∀ {X Y: C}, (φ_ X).hom ⊗ (φ_ Y).hom = (φ_ (X ⊗ Y)).hom ≫ _)

  restate_axiom right_pivotal_category.right_pivotor_naturality'
  attribute [reassoc] right_pivotal_category.right_pivotor_naturality

  open right_pivotal_category
  notation `φ_` := right_pivotor

  variables (K: Type) [field K]
  instance: right_pivotal_category (FinVect K) := {
    right_pivotor := begin
      intro X,
      change X ≅ FinVect.FinVect_dual K (FinVect.FinVect_dual K X),
      sorry
    end,
    right_pivotor_naturality' := sorry
  }
end

section
  variables
    {C: Type u}
    [category.{v} C]
    [monoidal_category.{v} C]
    [right_rigid_category.{v} C]
    [right_pivotal_category C]
    (V: C)

  def coevaluation := η_ V Vᘁ
  def evaluation := ε_ V Vᘁ

  notation η_⁺ := coevaluation
  notation ε_⁺ := evaluation

  def coevaluation_rev := η_⁺ Vᘁ ≫ (𝟙 Vᘁ ⊗ (φ_ _).inv)
  def evaluation_rev := ((φ_ _).hom ⊗ 𝟙 Vᘁ) ≫ ε_⁺ Vᘁ

  notation η_⁻ := coevaluation_rev
  notation ε_⁻ := evaluation_rev

  lemma id_comp_comp_id {V₁ V₂: C} (f: V₁ ⟶ V₂): 𝟙 _ ≫ f = f ≫ 𝟙 _ := by simp

  lemma coevaluation_evaluation:
    (𝟙 Vᘁ ⊗ η_⁺ _) ≫ (α_ _ _ _).inv ≫ (ε_⁺ _ ⊗ 𝟙 Vᘁ) = (ρ_ _).hom ≫ (λ_ _).inv := by simp [coevaluation, evaluation, coevaluation_rev, evaluation_rev]

  lemma coevaluation_evaluation_rev:
    (𝟙 V ⊗ η_⁻ _) ≫ (α_ _ _ _).inv ≫ (ε_⁻ _ ⊗ 𝟙 V) = (ρ_ _).hom ≫ (λ_ _).inv := begin
    simp [coevaluation, evaluation, coevaluation_rev, evaluation_rev],
    slice_lhs 1 2 { rw [←tensor_comp, id_comp_comp_id, tensor_comp], },
    slice_lhs 1 1 { rw [←category.comp_id (φ_ V).hom, ←category.id_comp (η_ _ _), tensor_comp], },
    slice_lhs 3 4 { rw associator_inv_naturality, },
    slice_lhs 4 5 { rw [←tensor_comp, ←id_comp_comp_id, tensor_comp], },
    slice_lhs 5 6 { rw [←category.comp_id (ε_ _ _), ←category.id_comp (φ_ V).inv, tensor_comp], },
    simp,
  end

  lemma evaluation_coevaluation:
    (η_⁺ _ ⊗ 𝟙 V) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ ε_⁺ _) = (λ_ _).hom ≫ (ρ_ _).inv := by simp [coevaluation, evaluation, coevaluation_rev, evaluation_rev]

  lemma evaluation_coevaluation_rev:
    (η_⁻ _ ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 Vᘁ ⊗ ε_⁻ _) = (λ_ _).hom ≫ (ρ_ _).inv := begin
    simp [coevaluation, evaluation, coevaluation_rev, evaluation_rev],
    slice_lhs 3 4 { rw [←tensor_comp, ←tensor_comp, (φ_ _).inv_hom_id, category.comp_id, tensor_id, tensor_id], },
    simp,
  end
end

section
  open right_pivotal_category
  variables
    {C: Type u}
    [category.{v} C]
    [monoidal_category.{v} C]
    [right_rigid_category.{v} C]
    [right_pivotal_category C]

  lemma right_adjoint_mate_inv {X Y: C} (f: X ⟶ Y):
  (λ_ _).inv ≫ (η_⁺ _ ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ fᘁ) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ε_⁺ _) ≫ (ρ_ _).hom = f := begin
    simp [coevaluation, evaluation],
    simp [right_adjoint_mate],
    slice_lhs 8 10 { rw [←id_tensor_comp, ←id_tensor_comp, pentagon_inv, id_tensor_comp], }, simp,
    slice_lhs 11 12 { rw [associator_inv_conjugation, ←triangle_assoc_comp_right, comp_tensor_id], simp, },
    slice_lhs 10 12 { rw pentagon_inv, }, simp,
    slice_lhs 9 10 { rw associator_inv_naturality, },
    slice_lhs 10 11 { rw [←tensor_comp, id_comp_comp_id, tensor_comp], },
    slice_lhs 9 10 { rw [←associator_inv_naturality, ←id_tensor_comp_tensor_id (ε_ _ _) (ε_ _ _), id_tensor_comp], },
    slice_lhs 8 9 { rw [←id_tensor_comp, ←tensor_id, ←associator_inv_naturality, id_tensor_comp], },
    slice_lhs 7 8 { rw [←tensor_comp, ←tensor_comp, tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id _ f, tensor_comp, tensor_comp], },
    slice_lhs 6 7 { rw [←id_tensor_comp, ←id_tensor_comp], },
    slice_lhs 5 6 { rw [←id_tensor_comp, ←id_tensor_comp, exact_pairing.evaluation_coevaluation], }, simp,
    slice_lhs 4 5 { rw [←id_tensor_comp, ←id_tensor_comp, (λ_ _).inv_hom_id], },
    slice_lhs 5 6 { rw [←id_tensor_comp, ←id_tensor_comp, (ρ_ _).inv_hom_id], },
    slice_lhs 7 8 { rw [←id_tensor_comp, ←id_tensor_comp, (ρ_ _).inv_hom_id], }, simp,
    slice_lhs 3 4 { rw ←associator_naturality, },
    slice_lhs 2 3 { rw [tensor_id, tensor_id_comp_id_tensor, ←id_tensor_comp_tensor_id], },
    slice_lhs 3 5 { rw exact_pairing.evaluation_coevaluation, }, simp,
  end

  lemma right_adjoint_mate' {X Y: C} (f: X ⟶ Y):
  (λ_ _).inv ≫ (η_⁻ _ ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ε_⁻ _) ≫ (ρ_ _).hom = fᘁ := begin
    simp [coevaluation_rev, evaluation_rev],
    slice_lhs 4 6 {
      simp only [←tensor_comp, category.comp_id],
      simp [right_pivotor_naturality],
    },
    slice_lhs 3 4 { rw ←associator_naturality, },
    repeat { rw category.assoc, },
    rw right_adjoint_mate_inv,
  end
end

end kassel
