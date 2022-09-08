import kassel.Tangle
import category_theory.monoidal.braided
import algebra.category.FinVect
import kassel.rigid_appendix
import tactic.field_simp

open category_theory category_theory.monoidal_category
open kassel
namespace kassel

universes v u
variables
  {C: Type u}
  [category.{v} C]
  [monoidal_category.{v} C]
  [right_rigid_category.{v} C]
  [right_pivotal_category.{v} C]
  [braided_category.{v} C]

def flip (V W: C) := (β_ V W).hom
notation `τ_` := flip

def trace {V: C} (f: V ⟶ V) := η_⁺ _ ≫ (f ⊗ 𝟙 Vᘁ) ≫ ε_⁻ _

def trace_2 {V: C} (f: V ⊗ V ⟶ V ⊗ V)
  :=                  (ρ_ _).inv
  ≫ (𝟙 V ⊗ η_⁺ _) ≫ (α_ _ _ _).inv
  ≫ (f ⊗ 𝟙 Vᘁ)    ≫ (α_ _ _ _).hom
  ≫ (𝟙 V ⊗ ε_⁻ _) ≫ (ρ_ _).hom

def partial_transpose_1 {V₁ V₂ W₁ W₂: C} (f: V₁ ⊗ V₂ ⟶ W₁ ⊗ W₂)
  :=                            (𝟙 W₁ᘁ ⊗ (ρ_ _).inv)
  ≫ (𝟙 W₁ᘁ ⊗ 𝟙 V₂ ⊗ η_⁺ _)   ≫ (𝟙 W₁ᘁ ⊗ (α_ _ _ _).inv)
  ≫ (𝟙 W₁ᘁ ⊗ τ_ _ _ ⊗ 𝟙 V₁ᘁ) 
  ≫ (𝟙 W₁ᘁ ⊗ f ⊗ 𝟙 V₁ᘁ)      ≫ (𝟙 W₁ᘁ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv
  ≫ (ε_⁺ _ ⊗ 𝟙 W₂ ⊗ 𝟙 V₁ᘁ)   ≫ (λ_ _).hom
  ≫ τ_ _ _

postfix `⁺`:1025 := partial_transpose_1

structure enhanced_R_matrix (V: C) :=
  (c: V ⊗ V ≅ V ⊗ V)
  (μ: V ≅ V)
  (relation_1:
       (𝟙 V ⊗ c.hom) ≫ (α_ _ _ _).inv
    ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom
    ≫ (𝟙 V ⊗ c.hom) ≫ (α_ _ _ _).inv
  =                    (α_ _ _ _).inv
    ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom
    ≫ (𝟙 V ⊗ c.hom) ≫ (α_ _ _ _).inv
    ≫ (c.hom ⊗ 𝟙 V)
  )
  (relation_2: c.hom ≫ (μ.hom ⊗ μ.hom) = (μ.hom ⊗ μ.hom) ≫ c.hom)
  (relation_3_1: trace_2 (c.hom ≫ (𝟙 V ⊗ μ.hom)) = 𝟙 V)
  (relation_3_2: trace_2 (c.inv ≫ (𝟙 V ⊗ μ.hom)) = 𝟙 V)
  (relation_4_1: (τ_ _ _ ≫ c.inv)⁺ ≫ (𝟙 Vᘁ ⊗ μ.hom) ≫ (c.hom ≫ τ_ _ _)⁺ ≫ (𝟙 Vᘁ ⊗ μ.inv) = 𝟙 (Vᘁ ⊗ V))
  (relation_4_2: (τ_ _ _ ≫ c.hom)⁺ ≫ (𝟙 Vᘁ ⊗ μ.hom) ≫ (c.inv ≫ τ_ _ _)⁺ ≫ (𝟙 Vᘁ ⊗ μ.inv) = 𝟙 (Vᘁ ⊗ V))

/-
variables (V: C) (F: Tangle ⥤ C)

example: F.map ⟦β ↓ ↓⟧ ≫ F.map ⟦β⁻¹ ↓ ↓⟧ = 𝟙 _ := begin
  rw← F.map_comp',
  have h: (⟦β ↓ ↓⟧ ≫ ⟦β⁻¹ ↓ ↓⟧: ↓ ⊗ᵗ ↓ ⟶ ↓ ⊗ᵗ ↓) = ⟦β ↓ ↓ ≫ᵐ β⁻¹ ↓ ↓⟧,
  apply quotient.sound, exact Tangle.hom_equiv.refl _,
  rw h,
end
-/

variables (V: C) (R: enhanced_R_matrix V)

namespace enhanced_R_matrix
  lemma relation_2_c_inv: R.c.inv ≫ (R.μ.hom ⊗ R.μ.hom) = (R.μ.hom ⊗ R.μ.hom) ≫ R.c.inv :=
    by rw [iso.eq_comp_inv, category.assoc, iso.inv_comp_eq, R.relation_2]
end enhanced_R_matrix

@[simp] def functor_obj: Tangle → C
  | Tangle.id := 𝟙_ C
  | ↓ := V
  | ↑ := Vᘁ
  | (a ⊗ᵗ b) := functor_obj a ⊗ functor_obj b

/-
@[simp] lemma id_functor_obj_id: 𝟙 (functor_obj V Tangle.id) = 𝟙 (𝟙_ C) := by refl
@[simp] lemma id_functor_obj_hom: 𝟙 (functor_obj V ↓) = 𝟙 V := by refl
@[simp] lemma id_functor_obj_inv: 𝟙 (functor_obj V ↑) = 𝟙 Vᘁ := by refl
@[simp] lemma id_functor_obj_tensor {a b}: 𝟙 (functor_obj V (a ⊗ᵗ b)) = 𝟙 (functor_obj V a ⊗ functor_obj V b) := by refl
@[simp] lemma right_unitor_functor_obj_hom: ρ_ (functor_obj V ↓) = ρ_ V := by refl
@[simp] lemma right_unitor_functor_obj_inv: ρ_ (functor_obj V ↑) = ρ_ Vᘁ := by refl
@[simp] lemma right_unitor_functor_obj_tensor {a b}: ρ_ (functor_obj V (a ⊗ᵗ b)) = ρ_ (functor_obj V a ⊗ functor_obj V b) := by refl
@[simp] lemma left_unitor_functor_obj_hom: λ_ (functor_obj V ↓) = λ_ V := by refl
@[simp] lemma left_unitor_functor_obj_inv: λ_ (functor_obj V ↑) = λ_ Vᘁ := by refl
@[simp] lemma left_unitor_functor_obj_tensor {a b}: λ_ (functor_obj V (a ⊗ᵗ b)) = λ_ (functor_obj V a ⊗ functor_obj V b) := by refl
@[simp] lemma associator_functor_obj_hom_1 {a b}: α_ (functor_obj V ↓) a b = α_ V a b := by refl
@[simp] lemma associator_functor_obj_hom_2 {a b}: α_ a (functor_obj V ↓) b = α_ a V b := by refl
@[simp] lemma associator_functor_obj_hom_3 {a b}: α_ a b (functor_obj V ↓) = α_ a b V := by refl
@[simp] lemma associator_functor_obj_inv_1 {a b}: α_ (functor_obj V ↑) a b = α_ Vᘁ a b := by refl
@[simp] lemma associator_functor_obj_inv_2 {a b}: α_ a (functor_obj V ↑) b = α_ a Vᘁ b := by refl
@[simp] lemma associator_functor_obj_inv_3 {a b}: α_ a b (functor_obj V ↑) = α_ a b Vᘁ := by refl
-/

def functor_map: Π {X Y}, (X ⟶ᵐ Y) → (functor_obj V X ⟶ functor_obj V Y)
  | _ _ (𝟙ᵐ a) := 𝟙 (functor_obj V a)
  | _ _ (f ≫ᵐ g) := functor_map f ≫ functor_map g
  | _ _ (f ⊗ᵐ g) := functor_map f ⊗ functor_map g
  | _ _ (α _ _ _) := (α_ _ _ _).hom
  | _ _ (α⁻¹ _ _ _) := (α_ _ _ _).inv
  | _ _ (ℓ _) := (λ_ _).hom
  | _ _ (ℓ⁻¹ _) := (λ_ _).inv
  | _ _ (ρ _) := (ρ_ _).hom
  | _ _ (ρ⁻¹ _) := (ρ_ _).inv
  | _ _ η⁺ := η_⁺ V
  | _ _ η⁻ := η_⁻ _ ≫ (𝟙 Vᘁ ⊗ R.μ.inv)
  | _ _ ε⁺ := ε_⁺ _
  | _ _ ε⁻ := (R.μ.hom ⊗ 𝟙 Vᘁ) ≫ ε_⁻ V
  | _ _ β := R.c.hom
  | _ _ β⁻¹ := R.c.inv

namespace aux
  lemma functor_map_well_defined_1_1:
    functor_map V R (ρ⁻¹ _ ≫ᵐ 𝟙ᵐ _ ⊗ᵐ η⁻ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ ε⁻ ⊗ᵐ 𝟙ᵐ _ ≫ᵐ ℓ _) =
    functor_map V R (𝟙ᵐ _) :=
  begin
    simp_rw functor_map,
    change (ρ_ _).inv ≫ (𝟙 _ ⊗ η_⁻ V ≫ (𝟙 _ ⊗ R.μ.inv)) ≫ (α_ _ _ _).inv ≫ ((R.μ.hom ⊗ 𝟙 _) ≫ ε_⁻ V ⊗ 𝟙 _) ≫ (λ_ _).hom = 𝟙 _,
    simp_rw [id_tensor_comp, comp_tensor_id, category.assoc],
    
    rw ←associator_inv_naturality_assoc,
    iterate 2 { rw [←tensor_comp_assoc _ _ R.μ.hom _, id_comp_comp_id R.μ.hom, tensor_comp_assoc], },
    rw [tensor_id, tensor_id, category.id_comp],
    rw [←tensor_id_comp_id_tensor_assoc _ R.μ.hom, ←right_unitor_inv_naturality_assoc],

    rw associator_inv_naturality_assoc,
    rw [←tensor_comp_assoc, ←id_comp_comp_id, tensor_comp_assoc],
    rw [tensor_id, tensor_id, category.id_comp],
    rw [←tensor_id_comp_id_tensor_assoc R.μ.inv _, left_unitor_naturality],

    slice_lhs 3 5 { rw coevaluation_evaluation_rev, },
    simp_rw [category.assoc, iso.inv_hom_id_assoc],
    rw iso.hom_inv_id,
  end
  lemma functor_map_well_defined_1_2:
    functor_map V R (ℓ⁻¹ _ ≫ᵐ η⁺ ⊗ᵐ 𝟙ᵐ _ ≫ᵐ α _ _ _ ≫ᵐ 𝟙ᵐ _ ⊗ᵐ ε⁺ ≫ᵐ ρ _) = functor_map V R (𝟙ᵐ _) :=
  begin
    simp_rw functor_map,
    change (λ_ _).inv ≫ (η_⁺ V ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ ε_⁺ V) ≫ (ρ_ _).hom = 𝟙 _,
    rw [evaluation_coevaluation_assoc, iso.inv_hom_id_assoc, iso.inv_hom_id],
  end
  
  lemma functor_map_well_defined_2_1:
    functor_map V R (ρ⁻¹ _ ≫ᵐ 𝟙ᵐ _ ⊗ᵐ η⁺ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ ε⁺ ⊗ᵐ 𝟙ᵐ _ ≫ᵐ ℓ _) = functor_map V R (𝟙ᵐ _) :=
  begin
    simp_rw functor_map,
    change (ρ_ _).inv ≫ (𝟙 _ ⊗ η_⁺ V) ≫ (α_ _ _ _).inv ≫ (ε_⁺ V ⊗ 𝟙 _) ≫ (λ_ _).hom = 𝟙 _,
    rw [coevaluation_evaluation_assoc, iso.inv_hom_id_assoc, iso.inv_hom_id],
  end
  lemma functor_map_well_defined_2_2:
    functor_map V R (ℓ⁻¹ _ ≫ᵐ η⁻ ⊗ᵐ 𝟙ᵐ _ ≫ᵐ α _ _ _ ≫ᵐ 𝟙ᵐ _ ⊗ᵐ ε⁻ ≫ᵐ ρ _) = functor_map V R (𝟙ᵐ _) :=
  begin
    simp_rw functor_map,
    change (λ_ _).inv ≫ (η_⁻ V ≫ (𝟙 _ ⊗ R.μ.inv) ⊗ 𝟙 _) ≫ (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (R.μ.hom ⊗ 𝟙 _) ≫ ε_⁻ V) ≫ (ρ_ _).hom = 𝟙 _,
    simp_rw [id_tensor_comp, comp_tensor_id, category.assoc],
    rw associator_naturality_assoc,
    slice_lhs 4 5 { rw [←tensor_comp, ←tensor_comp, category.comp_id, iso.inv_hom_id, tensor_id, tensor_id], },
    rw category.id_comp,
    rw [evaluation_coevaluation_rev_assoc, iso.inv_hom_id_assoc, iso.inv_hom_id],
  end

  abbreviation functor_map_well_defined_3_lhs (b: ↓ ⊗ᵗ ↓ ⟶ᵐ ↓ ⊗ᵗ ↓) :=
    functor_map V R (                             ℓ⁻¹ _
      ≫ᵐ η⁻                   ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ ℓ⁻¹ _) ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑
      ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ η⁻ ⊗ᵐ 𝟙ᵐ ↓) ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ α _ _ _) ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ α⁻¹ _ _ _ ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ α _ _ _
      ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ b  ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ α _ _ _ ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ 𝟙ᵐ ↓ ⊗ᵐ α⁻¹ _ _ _
      ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ 𝟙ᵐ ↓ ⊗ᵐ ε⁻ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ 𝟙ᵐ ↓ ⊗ᵐ ℓ _
      ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ ε⁻                 ≫ᵐ ρ _
    )
  abbreviation functor_map_well_defined_3_rhs (b: ↓ ⊗ᵗ ↓ ⟶ᵐ ↓ ⊗ᵗ ↓) :=
    functor_map V R (                             ρ⁻¹ _
      ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ η⁺                 ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ 𝟙ᵐ ↓ ⊗ᵐ ℓ⁻¹ ↑
      ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ 𝟙ᵐ ↓ ⊗ᵐ η⁺ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ 𝟙ᵐ ↓ ⊗ᵐ α _ _ _ ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ α⁻¹ _ _ _
      ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑) ⊗ᵐ b  ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ α _ _ _ ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ α⁻¹ _ _ _) ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑
      ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ ε⁺ ⊗ᵐ 𝟙ᵐ ↓) ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ (𝟙ᵐ ↑ ⊗ᵐ ℓ _) ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑
      ≫ᵐ ε⁺                   ⊗ᵐ 𝟙ᵐ ↑ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ ℓ _
    )
  abbreviation functor_map_well_defined_3_mid (b: ↓ ⊗ᵗ ↓ ⟶ᵐ ↓ ⊗ᵗ ↓) :=
    (δ_ V V).inv ≫ (functor_map V R b)ᘁ ≫ (δ_ V V).hom

  lemma functor_map_well_defined_3_left (b: ↓ ⊗ᵗ ↓ ⟶ᵐ ↓ ⊗ᵗ ↓) (h: functor_map V R b ≫ (R.μ.hom ⊗ R.μ.hom) = (R.μ.hom ⊗ R.μ.hom) ≫ functor_map V R b):
    functor_map_well_defined_3_lhs V R b =
    functor_map_well_defined_3_mid V R b :=
  begin
    dunfold functor_map_well_defined_3_lhs,
    dunfold functor_map_well_defined_3_mid,
    simp_rw functor_map,
    change (λ_ _).inv ≫ (η_⁻ V ≫ (𝟙 _ ⊗ R.μ.inv) ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ ((𝟙 _ ⊗ (λ_ _).inv) ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ ((𝟙 _ ⊗ η_⁻ V ≫ (𝟙 _ ⊗ R.μ.inv) ⊗ 𝟙 _) ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ ((𝟙 _ ⊗ (α_ _ _ _).hom) ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ ((α_ _ _ _).inv ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ functor_map V R b ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ (α_ V V _).hom) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ 𝟙 _ ⊗ (α_ _ _ _).inv) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ 𝟙 _ ⊗ (R.μ.hom ⊗ 𝟙 _) ≫ ε_⁻ V ⊗ 𝟙 _) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ 𝟙 _ ⊗ (λ_ _).hom) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ (R.μ.hom ⊗ 𝟙 _) ≫ ε_⁻ V) ≫ (ρ_ _).hom = (δ_ _ _).inv ≫ (functor_map V R b)ᘁ ≫ (δ_ V V).hom,
    simp only [tensor_id, id_tensor_comp, comp_tensor_id, category.assoc],
    
    iterate 6 { rw [←tensor_comp_assoc _ (𝟙 (Vᘁ ⊗ Vᘁ)) _ (𝟙 (Vᘁ ⊗ Vᘁ)), category.comp_id], repeat { rw category.assoc, }, },
    rw [←tensor_comp_assoc _ R.μ.inv _ _, left_unitor_inv_naturality, tensor_comp_assoc],
    iterate 2 { rw [←tensor_comp_assoc _ (_ ⊗ R.μ.inv) _ _, ←tensor_comp _ R.μ.inv _ _, ←id_comp_comp_id R.μ.inv, tensor_comp, tensor_comp_assoc], },
    rw [←tensor_comp_assoc _ (_ ⊗ R.μ.inv) _ _, associator_naturality, tensor_comp_assoc],
    rw associator_inv_naturality,
    rw [tensor_id, id_tensor_comp_tensor_id_assoc, ←category.id_comp ((_ ⊗ 𝟙 Vᘁ) ⊗ (_ ⊗ R.μ.inv)), ←tensor_id],
    nth_rewrite 0 ←(δ_ _ _).inv_hom_id,
    rw [comp_tensor_id_assoc (δ_ _ _).inv _ _, ←coevaluation_rev_tensor_assoc],
    rw [tensor_id, tensor_id_comp_id_tensor, comp_tensor_id_assoc, associator_naturality_assoc],

    iterate 6 { nth_rewrite 1 ←tensor_comp_assoc (𝟙 (Vᘁ ⊗ Vᘁ)) _ (𝟙 (Vᘁ ⊗ Vᘁ)) _, rw category.comp_id, repeat { rw category.assoc, }, },
    rw [←tensor_comp_assoc _ _ _ ((R.μ.hom ⊗ 𝟙 _) ⊗ 𝟙 Vᘁ), ←associator_inv_naturality, tensor_comp_assoc],
    iterate 4 { rw [←tensor_comp_assoc _ _ R.μ.hom _, id_comp_comp_id R.μ.hom, tensor_comp_assoc], },
    rw [←associator_naturality_assoc R.μ.hom _ _, tensor_id, ←tensor_id_comp_id_tensor_assoc _ (R.μ.hom ⊗ _)],
    nth_rewrite 6 ←(δ_ _ _).inv_hom_id,
    rw [id_tensor_comp_assoc (δ_ _ _).inv _, tensor_id_comp_id_tensor_assoc],
    rw [tensor_id, category.id_comp, ←evaluation_rev_tensor],
    rw id_tensor_comp_assoc,

    iterate 3 { rw [←tensor_comp_assoc (δ_ _ _).hom _ _ _, ←id_comp_comp_id, tensor_comp_assoc], },
    rw [←id_tensor_comp_tensor_id_assoc _ (δ_ _ _).hom, right_unitor_naturality],
    simp_rw ←category.assoc, rw iso.cancel_iso_hom_right, simp_rw category.assoc,
    
    simp_rw ←associator_naturality_assoc,
    iterate 3 { rw [←tensor_comp_assoc _ _ _ (δ_ _ _).inv, id_comp_comp_id, tensor_comp_assoc], },
    rw [←id_tensor_comp_tensor_id_assoc (δ_ _ _).inv _, ←left_unitor_inv_naturality_assoc],
    rw iso.cancel_iso_inv_left,
    
    slice_lhs 3 5 { simp only [←tensor_comp, category.id_comp], },
    simp_rw category.assoc, rw right_adjoint_mate_rev,
    rw [h, ←tensor_iso_hom, ←tensor_iso_inv, iso.inv_hom_id_assoc],
  end
  lemma functor_map_well_defined_3_right (b: ↓ ⊗ᵗ ↓ ⟶ᵐ ↓ ⊗ᵗ ↓):
    functor_map_well_defined_3_rhs V R b =
    functor_map_well_defined_3_mid V R b :=
  begin
    dunfold functor_map_well_defined_3_rhs,
    dunfold functor_map_well_defined_3_mid,
    simp_rw functor_map,
    change (ρ_ _).inv ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ η_⁺ V) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ 𝟙 _ ⊗ (λ_ _).inv) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ 𝟙 _ ⊗ η_⁺ V ⊗ 𝟙 _) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ 𝟙 _ ⊗ (α_ _ _ _).hom) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ (α_ _ _ _).inv) ≫ ((𝟙 Vᘁ ⊗ 𝟙 _) ⊗ functor_map V R b ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ (α_ _ (V ⊗ V) _).inv ≫ ((α_ _ _ _).hom ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ ((𝟙 _ ⊗ (α_ _ _ _).inv) ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ ((𝟙 _ ⊗ ε_⁺ V ⊗ 𝟙 _) ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ ((𝟙 _ ⊗ (λ_ _).hom) ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ (ε_⁺ V ⊗ 𝟙 _ ⊗ 𝟙 Vᘁ) ≫ (λ_ _).hom = (δ_ V V).inv ≫ (functor_map V R b)ᘁ ≫ (δ_ V V).hom,
    simp only [tensor_id, id_tensor_comp, comp_tensor_id, category.assoc],
    
    iterate 4 { rw ←tensor_comp_assoc (𝟙 (Vᘁ ⊗ Vᘁ)) _ (𝟙 (Vᘁ ⊗ Vᘁ)) _, rw category.comp_id, }, repeat { rw category.assoc, },
    rw [←category.comp_id (α_ V V (Vᘁ ⊗ Vᘁ)).inv, ←tensor_id (V ⊗ V) (Vᘁ ⊗ Vᘁ)],
    nth_rewrite 1 ←(δ_ _ _).inv_hom_id, rw id_tensor_comp (δ_ V V).inv _,
    rw [←coevaluation_tensor_assoc, id_tensor_comp_assoc],

    iterate 4 { rw ←comp_tensor_id_assoc, }, repeat { rw category.assoc, },
    rw [←category.id_comp (α_ Vᘁ Vᘁ (V ⊗ V)).hom, ←tensor_id (Vᘁ ⊗ Vᘁ) (V ⊗ V)],
    nth_rewrite 4 ←(δ_ _ _).inv_hom_id, rw comp_tensor_id_assoc (δ_ V V).inv _, repeat { rw category.assoc, },
    rw [←evaluation_tensor, comp_tensor_id_assoc],

    rw ←associator_inv_naturality_assoc,
    iterate 3 { rw [←tensor_comp_assoc  _ _ (δ_ _ _).inv _, id_comp_comp_id, tensor_comp_assoc], },
    rw [←tensor_id_comp_id_tensor_assoc _ (δ_ _ _).inv, ←right_unitor_inv_naturality_assoc],
    rw iso.cancel_iso_inv_left,
    
    slice_lhs 3 5 { simp only [←tensor_comp, category.comp_id], rw @category.comp_id _ _ (V ⊗ V) (V ⊗ V) (functor_map V R b), }, simp_rw category.assoc,
    rw associator_inv_naturality_assoc,
    rw ←tensor_id_comp_id_tensor_assoc (δ_ V V).hom _,
    rw [←tensor_comp_assoc _ (δ_ _ _).hom _ _, ←id_comp_comp_id, tensor_comp_assoc],
    rw [←tensor_id_comp_id_tensor_assoc (δ_ V V).hom _, left_unitor_naturality],
    simp_rw ←category.assoc, rw iso.cancel_iso_hom_right, simp_rw category.assoc,

    simp_rw [tensor_id, category.id_comp],
    rw [←associator_inv_naturality_assoc], rw right_adjoint_mate,
  end
  lemma functor_map_well_defined_3_1:
    functor_map_well_defined_3_lhs V R β =
    functor_map_well_defined_3_rhs V R β :=
    eq.trans
      (functor_map_well_defined_3_left V R β (by rw [functor_map, R.relation_2]))
      (functor_map_well_defined_3_right V R β).symm
  lemma functor_map_well_defined_3_2:
    functor_map_well_defined_3_lhs V R β⁻¹ =
    functor_map_well_defined_3_rhs V R β⁻¹ :=
    eq.trans
      (functor_map_well_defined_3_left V R β⁻¹ (by rw [functor_map, enhanced_R_matrix.relation_2_c_inv]))
      (functor_map_well_defined_3_right V R β⁻¹).symm

  lemma functor_map_well_defined_4_1: functor_map V R (β ≫ᵐ β⁻¹) = functor_map V R (𝟙ᵐ (↓ ⊗ᵗ ↓)) := by simp [functor_map]
  lemma functor_map_well_defined_4_2: functor_map V R (β⁻¹ ≫ᵐ β) = functor_map V R (𝟙ᵐ (↓ ⊗ᵗ ↓)) := by simp [functor_map]

  lemma functor_map_well_defined_5:
  functor_map V R (α⁻¹ _ _ _ ≫ᵐ β ⊗ᵐ 𝟙ᵐ ↓ ≫ᵐ α _ _ _ ≫ᵐ 𝟙ᵐ ↓ ⊗ᵐ β ≫ᵐ α⁻¹ _ _ _ ≫ᵐ β ⊗ᵐ 𝟙ᵐ _) = functor_map V R (𝟙ᵐ ↓ ⊗ᵐ β ≫ᵐ α⁻¹ _ _ _ ≫ᵐ β ⊗ᵐ 𝟙ᵐ ↓ ≫ᵐ α _ _ _ ≫ᵐ 𝟙ᵐ ↓ ⊗ᵐ β ≫ᵐ α⁻¹ _ _ _) := begin
    simp [functor_map],
    change (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.c.hom) ≫ (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 V) = (𝟙 V ⊗ R.c.hom) ≫ (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.c.hom) ≫ (α_ _ _ _).inv,
    exact R.relation_1.symm,
  end

  lemma functor_map_well_defined_6_1:
  functor_map V R (ρ⁻¹ _ ≫ᵐ 𝟙ᵐ ↓ ⊗ᵐ η⁺ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ β ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ α _ _ _ ≫ᵐ 𝟙ᵐ ↓ ⊗ᵐ ε⁻ ≫ᵐ ρ _) = functor_map V R (𝟙ᵐ ↓) := begin
    simp [functor_map],
    change (ρ_ _).inv ≫ (𝟙 V ⊗ η_⁺ V) ≫ (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ≫ (𝟙 V ⊗ ε_⁻ V) ≫ (ρ_ _).hom = 𝟙 V,
    have h: trace_2 (R.c.hom ≫ (𝟙 V ⊗ R.μ.hom)) = (ρ_ _).inv ≫ (𝟙 V ⊗ η_⁺ V) ≫ (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ≫ (𝟙 V ⊗ ε_⁻ V) ≫ (ρ_ _).hom := by simp [functor_map, trace_2, coevaluation, evaluation, evaluation_rev],
    rw ←h,
    exact R.relation_3_1,
  end
  lemma functor_map_well_defined_6_2:
  functor_map V R (ρ⁻¹ _ ≫ᵐ 𝟙ᵐ ↓ ⊗ᵐ η⁺ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ β⁻¹ ⊗ᵐ 𝟙ᵐ ↑ ≫ᵐ α _ _ _ ≫ᵐ 𝟙ᵐ ↓ ⊗ᵐ ε⁻ ≫ᵐ ρ _) = functor_map V R (𝟙ᵐ ↓) := begin
    simp [functor_map],
    change (ρ_ _).inv ≫ (𝟙 V ⊗ η_⁺ V) ≫ (α_ _ _ _).inv ≫ (R.c.inv ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ≫ (𝟙 V ⊗ ε_⁻ V) ≫ (ρ_ _).hom = 𝟙 V,
    have h: trace_2 (R.c.inv ≫ (𝟙 V ⊗ R.μ.hom)) = (ρ_ _).inv ≫ (𝟙 V ⊗ η_⁺ V) ≫ (α_ _ _ _).inv ≫ (R.c.inv ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ≫ (𝟙 V ⊗ ε_⁻ V) ≫ (ρ_ _).hom := by simp [functor_map, trace_2, coevaluation, evaluation, evaluation_rev],
    rw ←h,
    exact R.relation_3_2,
  end

  -- lemma functor_map_well_defined_8_2:
  /-
  lemma functor_map_well_defined_7_1:
  functor_map V R (ℓ⁻¹ _ ⊗ᵐ 𝟙 ↑ ≫ᵐ η⁻ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑ ≫ᵐ α _ _ _ ⊗ᵐ 𝟙 ↑ ≫ᵐ 𝟙 ↑ ⊗ᵐ β⁻¹ ⊗ᵐ 𝟙 ↑ ≫ᵐ α⁻¹ _ _ _ ⊗ᵐ 𝟙 ↑ ≫ᵐ α _ _ _ ≫ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ ε⁻ ≫ᵐ 𝟙 ↑ ⊗ᵐ 𝟙 ↓ ⊗ᵐ η⁺ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ α _ _ _ ⊗ᵐ 𝟙 ↑ ≫ᵐ 𝟙 ↑ ⊗ᵐ β ⊗ᵐ 𝟙 ↑ ≫ᵐ α⁻¹ _ _ _ ⊗ᵐ 𝟙 ↑ ≫ᵐ ε⁺ ⊗ᵐ 𝟙 ↓ ⊗ᵐ 𝟙 ↑ ≫ᵐ ℓ _ ⊗ᵐ 𝟙 ↑) = functor_map V R (𝟙 ↓ ⊗ᵐ 𝟙 ↑) := begin
    simp only [functor_map, category.assoc, tensor_comp_id, comp_tensor_id],
    change ((λ_ _).inv ⊗ 𝟙 Vᘁ)
    ≫ ((η_⁻ V ⊗ 𝟙 V) ⊗ 𝟙 Vᘁ)
    ≫ (((𝟙 Vᘁ ⊗ R.μ.inv) ⊗ 𝟙 V) ⊗ 𝟙 Vᘁ)
    ≫ ((α_ _ _ _).hom ⊗ 𝟙 Vᘁ)
    ≫ ((𝟙 Vᘁ ⊗ R.c.inv) ⊗ 𝟙 Vᘁ)
    ≫ ((α_ _ _ _).inv ⊗ 𝟙 Vᘁ)
    ≫ (α_ _ _ _).hom
    ≫ ((𝟙 Vᘁ ⊗ 𝟙 V) ⊗ R.μ.hom ⊗ 𝟙 Vᘁ)
    ≫ (𝟙 (Vᘁ ⊗ V) ⊗ ε_⁻ V)
    ≫ ((𝟙 Vᘁ ⊗ 𝟙 V) ⊗ η_⁺ V)
    ≫ (α_ _ _ _).inv
    ≫ ((α_ _ _ _).hom ⊗ 𝟙 Vᘁ)
    ≫ ((𝟙 Vᘁ ⊗ R.c.hom) ⊗ 𝟙 Vᘁ)
    ≫ ((α_ _ _ _).inv ⊗ 𝟙 Vᘁ)
    ≫ ((ε_⁺ V ⊗ 𝟙 V) ⊗ 𝟙 Vᘁ)
    ≫ ((λ_ _).hom ⊗ 𝟙 Vᘁ)
    = 𝟙 V ⊗ 𝟙 Vᘁ,
  end
  -/
end aux

lemma functor_map_well_defined {X Y}: ∀ (f g: X ⟶ᵐ Y), f ≈ g → functor_map V R f = functor_map V R g := begin
  intros f g r, induction r,
  { refl, },
  { rw r_ih, },
  { rw [r_ih_ᾰ, r_ih_ᾰ_1], },
  { simp only [functor_map, r_ih_ᾰ, r_ih_ᾰ_1], },
  { simp only [functor_map, category.id_comp'], },
  { simp only [functor_map, category.comp_id'], },
  { simp only [functor_map, category.assoc'], },
  { simp only [functor_map, r_ih_ᾰ, r_ih_ᾰ_1], },
  { simp only [functor_map, monoidal_category.tensor_id'], refl, },
  { simp only [functor_map, monoidal_category.tensor_comp'], },
  { simp only [functor_map, (α_ _ _ _).hom_inv_id'], refl, },
  { simp only [functor_map, (α_ _ _ _).inv_hom_id'], refl, },
  { simp only [functor_map, monoidal_category.associator_naturality'], },
  { simp only [functor_map, (λ_ _).hom_inv_id'], refl, },
  { simp only [functor_map, (λ_ _).inv_hom_id'], },
  { simp only [functor_map, monoidal_category.left_unitor_naturality'], dsimp at *, simp at *, },
  { simp only [functor_map, (ρ_ _).hom_inv_id'], refl, },
  { simp only [functor_map, (ρ_ _).inv_hom_id'], },
  { simp only [functor_map, monoidal_category.right_unitor_naturality'], dsimp at *, simp at *, },
  { dsimp [functor_map], rw monoidal_category.pentagon', },
  { simp only [functor_map, monoidal_category.triangle'], dsimp at *, simp at *, },
  exact aux.functor_map_well_defined_1_1 _ _,
  exact aux.functor_map_well_defined_1_2 _ _,
  exact aux.functor_map_well_defined_2_1 _ _,
  exact aux.functor_map_well_defined_2_2 _ _,
  exact aux.functor_map_well_defined_3_1 _ _,
  exact aux.functor_map_well_defined_3_2 _ _,
  exact aux.functor_map_well_defined_4_1 _ _,
  exact aux.functor_map_well_defined_4_2 _ _,
  exact aux.functor_map_well_defined_5 _ _,
  exact aux.functor_map_well_defined_6_1 _ _,
  exact aux.functor_map_well_defined_6_2 _ _,
  sorry,
  sorry,
  sorry,
  sorry,
end

def functor (R: enhanced_R_matrix V): Tangle ⥤ C := {
  obj := functor_obj V,
  map := λ X Y f, quotient.lift_on' f (functor_map V R) (functor_map_well_defined V R)
}

lemma elems_bool2: fintype.elems (bool × bool) = {(tt, tt), (tt, ff), (ff, tt), (ff, ff)} := rfl

variables {K: Type} [field K]

lemma pow_mul_single (a: K) (n: ℕ): a ^ n * a = a ^ (n + 1) := by nth_rewrite 1 ←pow_one a; rw pow_add
lemma single_mul_pow (a: K) (n: ℕ): a * a ^ n = a ^ (1 + n) := by nth_rewrite 0 ←pow_one a; rw pow_add

@[simp] def linear_map_smul (V: FinVect K) (s: K): V →ₗ[K] V :=
  is_linear_map.mk' (λ x, s • x) (is_linear_map.is_linear_map_smul s)

@[simp] def V₂: FinVect K := ⟨⟨bool → K⟩, begin
  change finite_dimensional K (bool → K),
  exact finite_dimensional.finite_dimensional_pi K,
end⟩

variables (q: Kˣ)

@[simp] def jones_R_matrix: matrix (bool × bool) (bool × bool) K 
  | (ff, ff) (ff, ff) := q⁻¹
  | (ff, tt) (tt, ff) := (q⁻¹)^2
  | (tt, ff) (ff, tt) := (q⁻¹)^2
  | (tt, ff) (tt, ff) := q⁻¹ + -(q⁻¹)^3
  | (tt, tt) (tt, tt) := q⁻¹
  | _ _ := 0

@[simp] def jones_R_matrix_inv: matrix (bool × bool) (bool × bool) K
  | (ff, ff) (ff, ff) := q
  | (ff, tt) (ff, tt) := q + -q^3
  | (ff, tt) (tt, ff) := q^2
  | (tt, ff) (ff, tt) := q^2
  | (tt, tt) (tt, tt) := q
  | _ _ := 0

noncomputable def jones_R_hom :=
  matrix.to_lin
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    (jones_R_matrix q)

noncomputable def jones_R_inv :=
  matrix.to_lin
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    (jones_R_matrix_inv q)

lemma jones_R_hom_inv_id: (jones_R_hom q).comp (jones_R_inv q) = linear_map.id := begin
  rw [jones_R_hom, jones_R_inv, ←matrix.to_lin_mul],
  rw ←matrix.to_lin_one ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)),
  congr,
  rw matrix.mul,
  ext ⟨i₁, i₂⟩ ⟨k₁, k₂⟩,
  rw [matrix.dot_product, finset.univ, elems_bool2],
  simp,
  cases i₁,
    cases i₂,
      cases k₁,
        cases k₂, simp, simp,
        cases k₂, simp, simp,
      cases k₁,
        cases k₂, simp, simp,
        cases k₂, simp, simp,
    cases i₂,
      cases k₁,
        cases k₂, simp, {
          simp, field_simp,
          simp [right_distrib, ←pow_add, neg_mul, pow_mul_single, single_mul_pow],
          have: 3 + 2 + 2 = 7 := rfl, rw this,
          have: 1 + 2 + 2 = 5 := rfl, rw this,
          rw ←add_assoc, rw add_assoc ((q: K)^7) _ _,
          simp,
        },
        cases k₂, simp, simp,
      cases k₁,
        cases k₂, simp, simp,
        cases k₂, simp, simp,
end

noncomputable def jones_enhanced_R_matrix: @enhanced_R_matrix (FinVect K) _ _ _ _ _ V₂ := {
  c := {
    hom := jones_R_hom q,
    inv := jones_R_inv q,
    hom_inv_id' := jones_R_hom_inv_id q, -- ...
    /- begin
      change (jones_R_hom q).comp (jones_R_inv q) = 1,
    end, -/
    inv_hom_id' := sorry
  },
  μ := {
    hom := linear_map_smul V₂ ((q⁻¹)^2: K),
    inv := linear_map_smul V₂ (q^2: K),
    hom_inv_id' := by tidy,
    inv_hom_id' := by tidy
  },
  relation_1 := begin
    sorry,
  end,
  relation_2 := sorry,
  relation_3_1 := sorry,
  relation_3_2 := sorry,
  relation_4_1 := sorry,
  relation_4_2 := sorry
}

end kassel