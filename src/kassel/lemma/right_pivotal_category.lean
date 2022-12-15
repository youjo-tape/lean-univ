import category_theory.monoidal.rigid.basic
import kassel.lemma.to_matrix

namespace kassel
open category_theory
open category_theory.monoidal_category

universes v u

section

variables
  {C: Type u}
  [category.{v} C]
  [monoidal_category.{v} C]
  [right_rigid_category.{v} C]

lemma congr_comp_left {X Y Z: C} (h: X ⟶ Y) (f g: Y ⟶ Z):
  f = g → h ≫ f = h ≫ g :=
by intro h; rw h

lemma congr_comp_right {X Y Z: C} (h: Y ⟶ Z) (f g: X ⟶ Y):
  f = g → f ≫ h = g ≫ h :=
by intro h; rw h

lemma congr_tensor_left {X₁ Y₁ X₂ Y₂: C} (h: X₁ ⟶ Y₁) (f g: X₂ ⟶ Y₂):
  f = g → h ⊗ f = h ⊗ g :=
by intro h; rw h

lemma congr_tensor_right {X₁ Y₁ X₂ Y₂: C} (h: X₂ ⟶ Y₂) (f g: X₁ ⟶ Y₁):
  f = g → f ⊗ h = g ⊗ h :=
by intro h; rw h

namespace iso

@[reassoc] lemma hom_dual_inv_dual_id {X Y: C} (f: X ≅ Y):
  (f.hom)ᘁ ≫ (f.inv)ᘁ = 𝟙 _ :=
by rw [←comp_right_adjoint_mate, iso.inv_hom_id, right_adjoint_mate_id]

@[reassoc] lemma inv_dual_hom_dual_id {X Y: C} (f: X ≅ Y):
  (f.inv)ᘁ ≫ (f.hom)ᘁ = 𝟙 _ :=
by rw [←comp_right_adjoint_mate, iso.hom_inv_id, right_adjoint_mate_id]

end iso

-- * Show that `X ⊗ Y` and `Yᘁ ⊗ Xᘁ` form an exact pairing.

@[instance] def tensor_exact_pairing (X Y: C): exact_pairing (X ⊗ Y) (Yᘁ ⊗ Xᘁ) := {
  coevaluation := η_ X Xᘁ ≫ ((ρ_ _).inv ⊗  𝟙 _) ≫ ((𝟙 _ ⊗ η_ Y Yᘁ) ⊗ 𝟙 _) ≫ ((α_ _ _ _).inv ⊗ 𝟙 _) ≫ (α_ _ _ _).hom,
  evaluation := (α_ _ _ _).inv ≫ ((α_ _ _ _).hom ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ ε_ X Xᘁ) ⊗ 𝟙 _) ≫ ((ρ_ _).hom ⊗ 𝟙 _) ≫ ε_ Y Yᘁ,
  coevaluation_evaluation' :=
  begin
    simp_rw [id_tensor_comp, comp_tensor_id, ←tensor_id, category.assoc],
    slice_lhs 2 3 {
      rw ←triangle_assoc_comp_left_inv,
      simp only [←tensor_comp],
      rw [category.assoc, ←associator_inv_naturality, ←id_tensor_comp_assoc],
      simp only [tensor_comp],
      rw [associator_inv_conjugation, associator_conjugation (𝟙 Yᘁ) _ _],
      rw [←category.id_comp ((λ_ Xᘁ).inv ≫ (η_ Y Yᘁ ⊗ 𝟙 Xᘁ)), ←category.comp_id ((λ_ Xᘁ).inv ≫ (η_ Y Yᘁ ⊗ 𝟙 Xᘁ))],
      simp only [tensor_comp, ←tensor_id],
    },
    slice_lhs 13 14 {
      simp only [←tensor_comp, category.comp_id],
      rw [associator_conjugation, associator_inv_conjugation _ _ (𝟙 Xᘁ)],
      rw [←category.id_comp ((𝟙 Yᘁ ⊗ ε_ X Xᘁ) ≫ (ρ_ Yᘁ).hom), ←category.comp_id ((𝟙 Yᘁ ⊗ ε_ X Xᘁ) ≫ (ρ_ Yᘁ).hom)],
      simp only [tensor_comp, ←tensor_id],
    },
    have h: ((α_ Yᘁ Xᘁ X).inv ⊗ (𝟙 Y ⊗ 𝟙 Yᘁ) ⊗ 𝟙 Xᘁ) ≫ (α_ (Yᘁ ⊗ Xᘁ) X ((Y ⊗ Yᘁ) ⊗ Xᘁ)).hom ≫ ((𝟙 Yᘁ ⊗ 𝟙 Xᘁ) ⊗ (α_ X (Y ⊗ Yᘁ) Xᘁ).inv) ≫ ((𝟙 Yᘁ ⊗ 𝟙 Xᘁ) ⊗ (α_ X Y Yᘁ).inv ⊗ 𝟙 Xᘁ) ≫ ((𝟙 Yᘁ ⊗ 𝟙 Xᘁ) ⊗ (α_ (X ⊗ Y) Yᘁ Xᘁ).hom) ≫ (α_ (Yᘁ ⊗ Xᘁ) (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).inv ≫ ((α_ (Yᘁ ⊗ Xᘁ) X Y).inv ⊗ 𝟙 Yᘁ ⊗ 𝟙 Xᘁ) ≫ (((α_ Yᘁ Xᘁ X).hom ⊗ 𝟙 Y) ⊗ 𝟙 Yᘁ ⊗ 𝟙 Xᘁ) ≫ (α_ (Yᘁ ⊗ Xᘁ ⊗ X) Y (Yᘁ ⊗ Xᘁ)).hom ≫ ((𝟙 Yᘁ ⊗ 𝟙 Xᘁ ⊗ 𝟙 X) ⊗ (α_ Y Yᘁ Xᘁ).inv) = 𝟙 _ := by coherence,
    slice_lhs 4 14 { rw [h, category.comp_id], }, clear h,
    slice_lhs 4 5 {
      simp only [tensor_id],
      rw eq.trans (id_tensor_comp_tensor_id _ _) (tensor_id_comp_id_tensor _ _).symm,
      simp only [id_tensor_comp, comp_tensor_id],
    },
    iterate 2 { rw associator_conjugation, },
    slice_lhs 3 6 { rw [←pentagon_hom_inv, iso.inv_hom_id_assoc], },
    slice_lhs 2 4 { simp only [←id_tensor_comp], rw exact_pairing.coevaluation_evaluation, },
    iterate 2 { rw associator_inv_conjugation, },
    slice_lhs 8 11 { rw [←pentagon_inv_inv_hom_assoc, iso.hom_inv_id_assoc, iso.hom_inv_id, category.comp_id], },
    slice_lhs 7 9 { simp only [←comp_tensor_id], rw exact_pairing.coevaluation_evaluation, },
    coherence,
  end,
  evaluation_coevaluation' :=
  begin
    simp_rw [id_tensor_comp, comp_tensor_id, ←tensor_id],
    slice_lhs 2 3 {
      simp only [←tensor_comp, category.comp_id],
      rw [associator_conjugation, associator_inv_conjugation (𝟙 Xᘁ) _ _],
      rw [←category.id_comp ((ρ_ X).inv ≫ (𝟙 X ⊗ η_ Y Yᘁ)), ←category.comp_id ((ρ_ X).inv ≫ (𝟙 X ⊗ η_ Y Yᘁ))],
      simp only [tensor_comp, ←tensor_id],
    },
    slice_lhs 12 13 {
      rw ←triangle,
      simp only [←tensor_comp],
      rw [associator_naturality_assoc, ←id_tensor_comp],
      simp only [tensor_comp],
      rw [associator_inv_conjugation, associator_conjugation _ _ (𝟙 Yᘁ)],
      rw [←category.id_comp ((ε_ X Xᘁ ⊗ 𝟙 Y) ≫ (λ_ Y).hom), ←category.comp_id ((ε_ X Xᘁ ⊗ 𝟙 Y) ≫ (λ_ Y).hom)],
      simp only [tensor_comp, ←tensor_id],
    },
    have h: ((𝟙 X ⊗ 𝟙 Y ⊗ 𝟙 Yᘁ) ⊗ (α_ Xᘁ X Y).hom) ≫ (α_ (X ⊗ Y ⊗ Yᘁ) Xᘁ (X ⊗ Y)).inv ≫ (((α_ X Y Yᘁ).inv ⊗ 𝟙 Xᘁ) ⊗ 𝟙 X ⊗ 𝟙 Y) ≫ ((α_ (X ⊗ Y) Yᘁ Xᘁ).hom ⊗ 𝟙 X ⊗ 𝟙 Y) ≫ (α_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) (X ⊗ Y)).hom ≫ ((𝟙 X ⊗ 𝟙 Y) ⊗ (α_ (Yᘁ ⊗ Xᘁ) X Y).inv) ≫ ((𝟙 X ⊗ 𝟙 Y) ⊗ (α_ Yᘁ Xᘁ X).hom ⊗ 𝟙 Y) ≫ ((𝟙 X ⊗ 𝟙 Y) ⊗ (α_ Yᘁ (Xᘁ ⊗ X) Y).hom) ≫ (α_ (X ⊗ Y) Yᘁ ((Xᘁ ⊗ X) ⊗ Y)).inv ≫ ((α_ X Y Yᘁ).hom ⊗ (𝟙 Xᘁ ⊗ 𝟙 X) ⊗ 𝟙 Y) = 𝟙 _ := by coherence,
    slice_lhs 4 14 { rw [h, category.comp_id], }, clear h,
    slice_lhs 4 5 {
      simp only [tensor_id],
      rw eq.trans (tensor_id_comp_id_tensor _ _) (id_tensor_comp_tensor_id _ _).symm,
      simp only [id_tensor_comp, comp_tensor_id],
    },
    iterate 2 { rw associator_inv_conjugation, },
    slice_lhs 3 6 { rw [←pentagon_inv_hom, iso.hom_inv_id_assoc], },
    slice_lhs 2 4 { simp only [←comp_tensor_id], rw exact_pairing.evaluation_coevaluation, },
    iterate 2 { rw associator_conjugation, },
    slice_lhs 8 11 { rw [pentagon_inv_inv_hom_assoc, iso.inv_hom_id, category.comp_id], },
    slice_lhs 7 9 { simp only [←id_tensor_comp], rw exact_pairing.evaluation_coevaluation, },
    coherence,
  end
}

def tensor_iso_dual_tensor_dual (X Y: C): (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ := {
  hom := (ρ_ _).inv ≫ (𝟙 _ ⊗ η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)) ≫ (α_ _ _ _).inv ≫ ((ε_ (X ⊗ Y) (X ⊗ Y)ᘁ) ⊗ 𝟙 Yᘁ ⊗ 𝟙 Xᘁ) ≫ (λ_ _).hom,
  inv := (ρ_ _).inv ≫ ((𝟙 Yᘁ ⊗ 𝟙 Xᘁ) ⊗ (η_ (X ⊗ Y) (X ⊗ Y)ᘁ)) ≫ (α_ _ _ _).inv ≫ (ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) ⊗ 𝟙 _) ≫ (λ_ _).hom,
  hom_inv_id' := begin
    rw right_unitor_inv_naturality_assoc,
    simp_rw comp_tensor_id,
    slice_lhs 6 7 { rw [tensor_id, eq.trans (tensor_id_comp_id_tensor _ _) (id_tensor_comp_tensor_id _ _).symm], },
    slice_lhs 7 8 { rw [←tensor_id, associator_inv_naturality], },
    slice_lhs 8 9 { rw [←comp_tensor_id, ←left_unitor_tensor', category.assoc, ←left_unitor_naturality], simp only [comp_tensor_id], },
    slice_lhs 9 11 { rw [unitors_equal, ←triangle], simp only [category.assoc], rw associator_naturality_assoc, },
    slice_lhs 2 6 { simp only [←tensor_comp, category.id_comp], rw [←category.comp_id (η_ _ (X ⊗ Y)ᘁ), tensor_comp], simp only [comp_tensor_id], },
    slice_lhs 6 9 { rw [tensor_id, category.id_comp, ←pentagon_hom_inv], },
    slice_lhs 5 6 { rw associator_naturality, },
    slice_lhs 6 9 { simp only [←tensor_comp, category.comp_id, ←category.assoc], rw [←category.id_comp (ε_ _ (X ⊗ Y)ᘁ), tensor_comp], simp only [id_tensor_comp], },
    
    slice_lhs 3 3 { rw [←tensor_id, associator_conjugation, associator_inv_conjugation (η_ _ _) _ _], },
    slice_lhs 10 10 { rw [←tensor_id, associator_conjugation, associator_inv_conjugation _ (ε_ _ _) _], },
    simp_rw id_tensor_comp,
    have h: (𝟙 (X ⊗ Y)ᘁ ⊗ (α_ ((X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ) (X ⊗ Y) (X ⊗ Y)ᘁ).hom) ≫ (α_ (X ⊗ Y)ᘁ ((X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ) ((X ⊗ Y) ⊗ (X ⊗ Y)ᘁ)).inv ≫ ((α_ (X ⊗ Y)ᘁ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).inv ⊗ 𝟙 ((X ⊗ Y) ⊗ (X ⊗ Y)ᘁ)) ≫ (α_ ((X ⊗ Y)ᘁ ⊗ X ⊗ Y) (Yᘁ ⊗ Xᘁ) ((X ⊗ Y) ⊗ (X ⊗ Y)ᘁ)).hom ≫ (𝟙 ((X ⊗ Y)ᘁ ⊗ X ⊗ Y) ⊗ (𝟙 Yᘁ ⊗ 𝟙 Xᘁ) ⊗ 𝟙 ((X ⊗ Y) ⊗ (X ⊗ Y)ᘁ)) ≫ (𝟙 ((X ⊗ Y)ᘁ ⊗ X ⊗ Y) ⊗ (α_ (Yᘁ ⊗ Xᘁ) (X ⊗ Y) (X ⊗ Y)ᘁ).inv) ≫ (α_ (X ⊗ Y)ᘁ (X ⊗ Y) (((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) ⊗ (X ⊗ Y)ᘁ)).hom ≫ (𝟙 (X ⊗ Y)ᘁ ⊗ (α_ (X ⊗ Y) ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) (X ⊗ Y)ᘁ).inv) = 𝟙 _ ⊗ (α_ _ _ _).hom ⊗ 𝟙 _ := by coherence,
    slice_lhs 6 13 { rw h, }, clear h,
    slice_lhs 5 7 {
      simp only [←id_tensor_comp, ←comp_tensor_id],
      rw exact_pairing.evaluation_coevaluation,
      simp only [id_tensor_comp, comp_tensor_id],
      rw [associator_inv_conjugation, ←triangle_assoc_comp_right, ←triangle_assoc_comp_left_inv],
      simp only [id_tensor_comp, comp_tensor_id],
    },
    slice_lhs 3 7 { rw ←pentagon_inv_hom_assoc, simp only [←comp_tensor_id], rw [iso.hom_inv_id_assoc, ←associator_inv_naturality], },
    slice_lhs 4 9 { rw iso.inv_hom_id_assoc, simp only [←id_tensor_comp_assoc], rw [iso.inv_hom_id, category.comp_id, associator_inv_naturality], },
    slice_lhs 2 3 { rw [←tensor_comp, iso.inv_hom_id, tensor_id, category.comp_id], },
    slice_lhs 4 5 { rw [←tensor_comp, iso.inv_hom_id, tensor_id, category.id_comp], },
    slice_lhs 2 4 { rw exact_pairing.coevaluation_evaluation, },
    coherence,
  end,
  inv_hom_id' := begin
    rw right_unitor_inv_naturality_assoc,
    simp_rw comp_tensor_id,
    slice_lhs 6 7 { rw [eq.trans (tensor_id_comp_id_tensor _ _) (id_tensor_comp_tensor_id _ _).symm], },
    slice_lhs 7 8 { rw [←tensor_id, associator_inv_naturality], },
    slice_lhs 8 9 { rw [tensor_id, ←comp_tensor_id, ←left_unitor_tensor', category.assoc, ←left_unitor_naturality], simp only [comp_tensor_id], },
    slice_lhs 9 11 { rw [unitors_equal, ←triangle], simp only [category.assoc], rw associator_naturality_assoc, },
    slice_lhs 2 6 { simp only [←tensor_comp, category.id_comp], rw [←category.comp_id (η_ _ (Yᘁ ⊗ Xᘁ)), tensor_comp], simp only [comp_tensor_id], },
    slice_lhs 6 9 { rw [tensor_id, category.id_comp, ←pentagon_hom_inv], },
    slice_lhs 5 6 { rw associator_naturality, },
    slice_lhs 6 9 { simp only [←tensor_comp, category.comp_id, ←category.assoc], rw [←category.id_comp (ε_ _ (Yᘁ ⊗ Xᘁ)), tensor_comp], simp only [id_tensor_comp], },
    
    slice_lhs 3 3 { rw [←tensor_id, associator_conjugation, associator_inv_conjugation (η_ _ _) _ _, tensor_id], },
    slice_lhs 10 10 { rw [←tensor_id, associator_conjugation, associator_inv_conjugation _ (ε_ _ _) _], },
    simp_rw id_tensor_comp,
    have h: (𝟙 (Yᘁ ⊗ Xᘁ) ⊗ (α_ ((X ⊗ Y) ⊗ (X ⊗ Y)ᘁ) (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).hom) ≫ (α_ (Yᘁ ⊗ Xᘁ) ((X ⊗ Y) ⊗ (X ⊗ Y)ᘁ) ((X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ)).inv ≫ ((α_ (Yᘁ ⊗ Xᘁ) (X ⊗ Y) (X ⊗ Y)ᘁ).inv ⊗ 𝟙 ((X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ)) ≫ (α_ ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) (X ⊗ Y)ᘁ ((X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ)).hom ≫ (𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) ⊗ 𝟙 (X ⊗ Y)ᘁ ⊗ 𝟙 ((X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ)) ≫ (𝟙 ((Yᘁ ⊗ Xᘁ) ⊗ X ⊗ Y) ⊗ (α_ (X ⊗ Y)ᘁ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).inv) ≫ (α_ (Yᘁ ⊗ Xᘁ) (X ⊗ Y) (((X ⊗ Y)ᘁ ⊗ X ⊗ Y) ⊗ Yᘁ ⊗ Xᘁ)).hom ≫ (𝟙 (Yᘁ ⊗ Xᘁ) ⊗ (α_ (X ⊗ Y) ((X ⊗ Y)ᘁ ⊗ X ⊗ Y) (Yᘁ ⊗ Xᘁ)).inv) = 𝟙 _ ⊗ (α_ _ _ _).hom ⊗ 𝟙 _ := by coherence,
    slice_lhs 6 13 { rw h, }, clear h,
    slice_lhs 5 7 {
      simp only [←id_tensor_comp, ←comp_tensor_id],
      rw exact_pairing.evaluation_coevaluation,
      simp only [id_tensor_comp, comp_tensor_id],
      rw [associator_inv_conjugation, ←triangle_assoc_comp_right, ←triangle_assoc_comp_left_inv],
      simp only [id_tensor_comp, comp_tensor_id],
    },
    slice_lhs 3 7 { rw ←pentagon_inv_hom_assoc, simp only [←comp_tensor_id], rw [iso.hom_inv_id_assoc, ←associator_inv_naturality], },
    slice_lhs 4 9 { rw iso.inv_hom_id_assoc, simp only [←id_tensor_comp_assoc], rw [iso.inv_hom_id, category.comp_id, associator_inv_naturality], },
    slice_lhs 2 3 { rw [←tensor_comp, iso.inv_hom_id, tensor_id, category.comp_id], },
    slice_lhs 4 5 { rw [←tensor_comp, iso.inv_hom_id, tensor_id, category.id_comp], },
    slice_lhs 2 4 { rw exact_pairing.coevaluation_evaluation, },
    coherence,
  end
}

notation `δ_` := tensor_iso_dual_tensor_dual

end

section right_pivotal_category

variables
  (C: Type u)
  [category.{v} C]
  [monoidal_category.{v} C]
  [right_rigid_category.{v} C]

-- * Define pivotal categories (rigid categories equipped with a natural isomorphism `ᘁᘁ ≅ 𝟙 C`).
-- 参考: https://tqft.net/web/research/students/SamQuinn/thesis.pdf

class right_pivotal_category :=
  (right_pivotor: Π X: C, X ≅ Xᘁᘁ)
  (notation `φ_` := right_pivotor)
  (right_pivotor_naturality': ∀ {X Y: C} (f: X ⟶ Y), f ≫ (φ_ Y).hom = (φ_ X).hom ≫ fᘁᘁ)
  (right_pivotor_tensor_naturality': ∀ {X Y: C}, (φ_ (X ⊗ Y)).hom = ((φ_ X).hom ⊗ (φ_ Y).hom) ≫ (δ_ _ _).inv ≫ ((δ_ _ _).hom)ᘁ)

restate_axiom right_pivotal_category.right_pivotor_naturality'
attribute [reassoc] right_pivotal_category.right_pivotor_naturality
restate_axiom right_pivotal_category.right_pivotor_tensor_naturality'
attribute [reassoc] right_pivotal_category.right_pivotor_tensor_naturality

open right_pivotal_category
notation `φ_` := right_pivotor

variable [right_pivotal_category.{v} C]

lemma right_pivotor_inv_naturality {X Y: C} (f: X ⟶ Y):
  (φ_ X).inv ≫ f = fᘁᘁ ≫ (φ_ Y).inv :=
begin
  rw ←(φ_ X).cancel_iso_hom_left,
  rw ←iso.cancel_iso_hom_right _ _ (φ_ Y),
  simp_rw [iso.hom_inv_id_assoc, category.assoc, iso.inv_hom_id, category.comp_id, right_pivotor_naturality],
end

lemma right_pivotor_inv_tensor_naturality (X Y: C):
  (φ_ (X ⊗ Y)).inv = ((δ_ _ _).inv)ᘁ ≫ (δ_ _ _).hom ≫ ((φ_ X).inv ⊗ (φ_ Y).inv) :=
begin
  rw [←(φ_ (X ⊗ Y)).cancel_iso_hom_left, iso.hom_inv_id, right_pivotor_tensor_naturality],
  simp_rw category.assoc,
  rw [iso.hom_dual_inv_dual_id_assoc, iso.inv_hom_id_assoc],
  simp_rw [←tensor_comp, iso.hom_inv_id, tensor_id],
end

namespace FinVect

variables {K: Type v} [field K]

noncomputable def right_pivotor (X: FinVect.{v} K): X ≅ Xᘁᘁ := {
  hom := right_pivotor.hom K X.obj,
  inv := right_pivotor.inv K X.obj,
  hom_inv_id' := by ext; simp [←module.eval_equiv_to_linear_map],
  inv_hom_id' := by ext; simp [←module.eval_equiv_to_linear_map]
}

namespace aux

variables
  (X Y: Type*)
  [add_comm_group X] [module K X] [finite_dimensional K X]
  [add_comm_group Y] [module K Y] [finite_dimensional K Y]
  (X' Y': Module.{u} K) (f': X' ⟶ Y')

variable (f: X →ₗ[K] Y)

#check (right_pivotor.hom K Y) ∘ₗ f

-- lemma right_pivotor_naturality' (f: X →ₗ[K] Y): ∘ₗ f

end aux

lemma right_pivotor_naturality (X Y: FinVect K) (f: X ⟶ Y):
  f ≫ (right_pivotor Y).hom = (right_pivotor X).hom ≫ fᘁᘁ :=
begin
  unfold_projs, dsimp [right_adjoint_mate],
  sorry,
end

lemma right_pivotor_tensor_naturality (X Y: FinVect K):
  (right_pivotor (X ⊗ Y)).hom = ((right_pivotor X).hom ⊗ (right_pivotor Y).hom) ≫ (δ_ _ _).inv ≫ ((δ_ _ _).hom)ᘁ :=
begin
  unfold_projs, dsimp [right_adjoint_mate],
  sorry,
end

noncomputable instance right_pivotal_category: right_pivotal_category (FinVect K) := {
  right_pivotor := right_pivotor,
  right_pivotor_naturality' := right_pivotor_naturality,
  right_pivotor_tensor_naturality' := right_pivotor_tensor_naturality
}

end FinVect

end right_pivotal_category

section

variables
  {C: Type u}
  [category.{v} C]
  [monoidal_category.{v} C]
  [right_rigid_category.{v} C]
  (V: C)

lemma coevaluation_tensor (X Y: C):
  η_ (X ⊗ Y) (X ⊗ Y)ᘁ = η_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) ≫ (𝟙 _ ⊗ (δ_ _ _).inv) :=
begin
  simp only [tensor_iso_dual_tensor_dual, id_tensor_comp],
  rw id_tensor_right_unitor_inv,
  slice_rhs 1 2 { rw right_unitor_inv_naturality, },
  slice_rhs 3 4 { rw ←associator_naturality, },
  slice_rhs 2 3 { simp only [tensor_id], rw [eq.trans (tensor_id_comp_id_tensor _ _) (id_tensor_comp_tensor_id _ _).symm], },
  slice_rhs 1 2 { rw [←unitors_inv_equal, ←left_unitor_inv_naturality], },
  slice_rhs 3 3 { rw [←tensor_id, associator_inv_conjugation], },
  slice_rhs 5 8 { rw [pentagon_hom_inv_assoc, iso.hom_inv_id_assoc, ←associator_naturality], },
  slice_rhs 4 6 { simp only [←comp_tensor_id], rw exact_pairing.evaluation_coevaluation, },
  conv_lhs { rw ←category.comp_id (η_ _ _) }, rw congr_comp_left,
  coherence,
end

lemma evaluation_tensor (X Y: C):
  ε_ (X ⊗ Y) (X ⊗ Y)ᘁ = ((δ_ _ _).hom ⊗ 𝟙 _) ≫ ε_ _ _ :=
begin
  simp only [tensor_iso_dual_tensor_dual, comp_tensor_id],
  rw ←left_unitor_tensor',
  slice_rhs 6 7 { rw ←left_unitor_naturality, },
  slice_rhs 4 5 { rw associator_naturality, },
  slice_rhs 5 6 { simp only [tensor_id], rw [eq.trans (tensor_id_comp_id_tensor _ _) (id_tensor_comp_tensor_id _ _).symm], },
  slice_rhs 6 7 { rw [unitors_equal, right_unitor_naturality], },
  slice_rhs 5 5 { rw [←tensor_id, associator_conjugation], },
  slice_rhs 3 5 { rw [←pentagon, ←comp_tensor_id_assoc (α_ (X ⊗ Y)ᘁ (X ⊗ Y) (Yᘁ ⊗ Xᘁ)).inv, iso.inv_hom_id], },
  slice_rhs 2 5 { simp only [←tensor_id, associator_naturality_assoc], simp only [tensor_id], rw category.id_comp, },
  slice_rhs 3 5 { simp only [←id_tensor_comp], rw exact_pairing.evaluation_coevaluation, },
  conv_lhs { rw ←category.id_comp (ε_ _ _) }, simp_rw ←category.assoc, rw congr_comp_right,
  coherence,
end

lemma coevaluation_dual_tensor (X Y: C):
  η_ (X ⊗ Y)ᘁ (X ⊗ Y)ᘁᘁ = η_ (Yᘁ ⊗ Xᘁ) (Yᘁ ⊗ Xᘁ)ᘁ ≫ ((δ_ X Y).inv ⊗ ((δ_ X Y).hom)ᘁ) :=
begin
  rw ←tensor_id_comp_id_tensor,
  slice_rhs 1 2 { rw ←coevaluation_comp_right_adjoint_mate, },
  slice_rhs 1 3 { rw [←id_tensor_comp, iso.inv_dual_hom_dual_id, tensor_id, category.comp_id], },
end

lemma evaluation_dual_tensor (X Y: C):
  ε_ (X ⊗ Y)ᘁ (X ⊗ Y)ᘁᘁ = (((δ_ X Y).inv)ᘁ ⊗ (δ_ X Y).hom) ≫ ε_ (Yᘁ ⊗ Xᘁ) (Yᘁ ⊗ Xᘁ)ᘁ :=
begin
  rw ←tensor_id_comp_id_tensor,
  slice_rhs 2 3 { rw ←right_adjoint_mate_comp_evaluation, },
  slice_rhs 1 3 { rw [←comp_tensor_id_assoc, iso.inv_dual_hom_dual_id, tensor_id, category.id_comp], },
end

def coevaluation' := η_ V Vᘁ
def evaluation' := ε_ V Vᘁ

notation η_⁺ := coevaluation'
notation ε_⁺ := evaluation'

variable [right_pivotal_category.{v} C]
open right_pivotal_category

def coevaluation_rev := η_⁺ Vᘁ ≫ (𝟙 Vᘁ ⊗ (φ_ _).inv)
def evaluation_rev := ((φ_ _).hom ⊗ 𝟙 Vᘁ) ≫ ε_⁺ Vᘁ

notation η_⁻ := coevaluation_rev
notation ε_⁻ := evaluation_rev

lemma id_comp_comp_id {V₁ V₂: C} (f: V₁ ⟶ V₂): 𝟙 _ ≫ f = f ≫ 𝟙 _ := by simp

@[reassoc] lemma coevaluation_evaluation:
  (𝟙 Vᘁ ⊗ η_⁺ _) ≫ (α_ _ _ _).inv ≫ (ε_⁺ _ ⊗ 𝟙 Vᘁ) = (ρ_ _).hom ≫ (λ_ _).inv := by simp [coevaluation', evaluation', coevaluation_rev, evaluation_rev]

@[reassoc] lemma coevaluation_evaluation_rev:
  (𝟙 V ⊗ η_⁻ _) ≫ (α_ _ _ _).inv ≫ (ε_⁻ _ ⊗ 𝟙 V) = (ρ_ _).hom ≫ (λ_ _).inv := begin
  simp [coevaluation', evaluation', coevaluation_rev, evaluation_rev],
  slice_lhs 1 2 { rw [←tensor_comp, id_comp_comp_id, tensor_comp], },
  slice_lhs 1 1 { rw [←category.comp_id (φ_ V).hom, ←category.id_comp (η_ _ _), tensor_comp], },
  slice_lhs 3 4 { rw associator_inv_naturality, },
  slice_lhs 4 5 { rw [←tensor_comp, ←id_comp_comp_id, tensor_comp], },
  slice_lhs 5 6 { rw [←category.comp_id (ε_ _ _), ←category.id_comp (φ_ V).inv, tensor_comp], },
  simp,
end

@[reassoc] lemma evaluation_coevaluation:
  (η_⁺ _ ⊗ 𝟙 V) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ ε_⁺ _) = (λ_ _).hom ≫ (ρ_ _).inv := by simp [coevaluation', evaluation', coevaluation_rev, evaluation_rev]

@[reassoc] lemma evaluation_coevaluation_rev:
  (η_⁻ _ ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 Vᘁ ⊗ ε_⁻ _) = (λ_ _).hom ≫ (ρ_ _).inv := begin
  simp [coevaluation', evaluation', coevaluation_rev, evaluation_rev],
  slice_lhs 3 4 { rw [←tensor_comp, ←tensor_comp, (φ_ _).inv_hom_id, category.comp_id, tensor_id, tensor_id], },
  simp,
end

@[reassoc] lemma coevaluation_hom_tensor (X Y: C):
  η_⁺ (X ⊗ Y) = η_⁺ X ≫ (𝟙 _ ⊗ (λ_ _).inv) ≫ (𝟙 _ ⊗ η_⁺ Y ⊗ 𝟙 _)  ≫ (𝟙 _ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫ (𝟙 _ ⊗ (δ_ _ _).inv) :=
begin
  simp only [coevaluation', coevaluation_tensor], unfold_projs,
  slice_lhs 2 2 { rw ←triangle_assoc_comp_left_inv, },
  slice_lhs 3 4 { rw [associator_conjugation, iso.inv_hom_id_assoc], },
  slice_lhs 4 6 { rw pentagon_inv_inv_hom, },
  simp_rw category.assoc,
end

@[reassoc] lemma evaluation_hom_tensor (X Y: C):
  ε_⁺ (X ⊗ Y) = ((δ_ _ _).hom ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (α_ _ _ _).inv) ≫ (𝟙 _ ⊗ ε_⁺ X ⊗ 𝟙 _) ≫ (𝟙 _ ⊗ (λ_ _).hom) ≫ ε_⁺ Y :=
begin
  simp only [evaluation', evaluation_tensor], unfold_projs,
  slice_lhs 4 4 { rw associator_conjugation, },
  slice_lhs 6 7 { rw triangle_assoc_comp_right, },
  slice_lhs 2 4 { rw ←pentagon_hom_inv, },
  simp_rw category.assoc,
end

@[reassoc] lemma coevaluation_rev_tensor (X Y: C):
  η_⁻ (X ⊗ Y) = η_⁻ Y ≫ (𝟙 _ ⊗ (λ_ _).inv) ≫ (𝟙 _ ⊗ η_⁻ X ⊗ 𝟙 _)  ≫ (𝟙 _ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫ ((δ_ _ _).inv ⊗ 𝟙 _) :=
begin
  simp only [coevaluation_rev, id_tensor_comp, comp_tensor_id],
  conv_lhs {
    rw [coevaluation', coevaluation_dual_tensor, ←coevaluation'],
    rw [category.assoc, ←tensor_comp, category.comp_id, coevaluation_hom_tensor],
  },
  slice_rhs 2 3 { rw [←tensor_comp, left_unitor_inv_naturality, tensor_comp], },
  slice_rhs 3 4 { rw [←tensor_comp, eq.trans (id_tensor_comp_tensor_id _ _) (tensor_id_comp_id_tensor _ _).symm, tensor_comp], },
  slice_rhs 4 5 { simp only [←tensor_comp, category.id_comp, category.comp_id], },
  slice_rhs 4 5 { rw [←tensor_comp, associator_naturality, tensor_comp], },
  slice_rhs 5 6 { rw associator_inv_naturality, },
  simp_rw category.assoc, iterate 5 { rw congr_comp_left, },
  simp_rw [←tensor_comp, tensor_id, category.comp_id], rw congr_tensor_left,
  rw [right_pivotor_inv_tensor_naturality, iso.hom_dual_inv_dual_id_assoc, iso.inv_hom_id_assoc],
end

@[reassoc] lemma evaluation_rev_tensor (X Y: C):
  ε_⁻ (X ⊗ Y) = (𝟙 _ ⊗ (δ_ _ _).hom) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (α_ _ _ _).inv) ≫ (𝟙 _ ⊗ ε_⁻ Y ⊗ 𝟙 _) ≫ (𝟙 _ ⊗ (λ_ _).hom) ≫ ε_⁻ X :=
begin
  simp only [evaluation_rev, id_tensor_comp, comp_tensor_id],
  conv_lhs {
    rw [evaluation', evaluation_dual_tensor, ←evaluation'],
    rw [←tensor_comp_assoc, category.id_comp, evaluation_hom_tensor],
  },
  slice_rhs 3 7 {
    simp only [←tensor_comp, category.id_comp],
    rw [category.comp_id, ←category.comp_id ((φ_ X).hom), tensor_comp],
    simp only [id_tensor_comp],
  },
  slice_rhs 3 4 { rw [←tensor_comp, ←associator_inv_naturality, tensor_comp], },
  slice_rhs 2 3 { rw ←associator_naturality, },
  simp_rw ←category.assoc, iterate 5 { rw congr_comp_right, },
  simp_rw [←tensor_comp, tensor_id, category.id_comp], rw congr_tensor_right,
  rw [right_pivotor_tensor_naturality],
  slice_lhs 3 5 { rw iso.hom_dual_inv_dual_id_assoc, },
  rw [iso.inv_hom_id, category.comp_id],
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
    simp [coevaluation', evaluation'],
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
  
  @[reassoc] lemma right_adjoint_mate {X Y: C} (f: X ⟶ Y):
    (ρ_ _).inv ≫ (𝟙 _ ⊗ η_⁺ _) ≫ (𝟙 _ ⊗ (f ⊗ 𝟙 _)) ≫ (α_ _ _ _).inv ≫ ((ε_⁺ _) ⊗ 𝟙 _) ≫ (λ_ _).hom = fᘁ :=
      by rw [coevaluation', evaluation', right_adjoint_mate]
  @[reassoc] lemma right_adjoint_mate_rev {X Y: C} (f: X ⟶ Y):
    (λ_ _).inv ≫ (η_⁻ _ ⊗ 𝟙 _) ≫ ((𝟙 _ ⊗ f) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ε_⁻ _) ≫ (ρ_ _).hom = fᘁ :=
  begin
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
