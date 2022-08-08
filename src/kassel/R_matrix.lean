import kassel.Tangle
import category_theory.monoidal.braided
import algebra.category.FinVect
import kassel.rigid_appendix

open category_theory
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
  :=                            (𝟙 W₁ᘁ ⊗ (λ_ _).inv)
  ≫ (𝟙 W₁ᘁ ⊗ η_⁻ _ ⊗ 𝟙 V₂) ≫ (𝟙 W₁ᘁ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv
  ≫ (τ_ _ _ ⊗ f)           ≫ (α_ _ _ _).hom ≫ (𝟙 V₁ᘁ ⊗ (α_ _ _ _).inv)
  ≫ (𝟙 V₁ᘁ ⊗ ε_⁺ _ ⊗ 𝟙 W₂) ≫ (𝟙 V₁ᘁ ⊗ (λ_ _).hom)

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
  (relation_2: c.hom ≫ (μ.hom ⊗ μ.hom) = (μ.hom ⊗ μ.hom) ≫ c.inv)
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

@[simp] def functor_obj: Tangle → C
  | Tangle.id := 𝟙_ C
  | ↓ := V
  | ↑ := Vᘁ
  | (a ⊗ᵗ b) := functor_obj a ⊗ functor_obj b

def functor_map: Π {X Y}, (X ⟶ᵐ Y) → (functor_obj V X ⟶ functor_obj V Y)
  | _ _ (𝟙 a) := 𝟙 (functor_obj V a)
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

open category_theory.monoidal_category

namespace aux

  lemma functor_map_well_defined_1_1:
  functor_map V R (ρ⁻¹ _ ≫ᵐ 𝟙 _ ⊗ᵐ η⁻ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ ε⁻ ⊗ᵐ 𝟙 _ ≫ᵐ ℓ _) = functor_map V R (𝟙 _) := begin
    simp [functor_map],
    change (ρ_ V).inv ≫ (𝟙 V ⊗ η_⁻ V) ≫ (𝟙 V ⊗ 𝟙 Vᘁ ⊗ R.μ.inv) ≫ (α_ V Vᘁ V).inv ≫ (α_ V Vᘁ V).hom ≫ (R.μ.hom ⊗ 𝟙 (Vᘁ ⊗ V)) ≫ (α_ V Vᘁ V).inv ≫ (ε_⁻ V ⊗ 𝟙 V) ≫ (λ_ V).hom = 𝟙 V,
    slice_lhs 4 5 { rw (α_ _ _ _).inv_hom_id, },
    slice_lhs 4 5 { rw category.id_comp, },
    slice_lhs 3 4 { rw [←tensor_comp, id_comp_comp_id, tensor_comp, tensor_id V (_ ⊗ _), category.comp_id (R.μ.hom ⊗ 𝟙 Vᘁ ⊗ _)], },
    slice_lhs 2 3 { rw [←tensor_comp, id_comp_comp_id, tensor_comp], },
    slice_lhs 3 4 { rw associator_inv_naturality, },
    slice_lhs 4 5 { rw [←tensor_comp], change (𝟙 V ⊗ 𝟙 Vᘁ) ≫ ε_⁻ V ⊗ R.μ.inv ≫ 𝟙 V, rw [←id_comp_comp_id, tensor_comp, tensor_id, tensor_id, category.id_comp], },
    slice_lhs 2 2 { rw [←category.id_comp (R.μ.hom ⊗ _), ←tensor_id, ←tensor_comp, id_comp_comp_id, tensor_comp], },
    slice_lhs 5 5 { rw [←category.comp_id (_ ⊗ R.μ.inv), ←tensor_id, ←tensor_comp, ←id_comp_comp_id (R.μ.inv), tensor_comp], },
    slice_lhs 3 5 { rw coevaluation_evaluation_rev, },
    slice_lhs 2 3 { change (R.μ.hom ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ V).hom, rw right_unitor_naturality, },
    slice_lhs 4 5 { rw ←left_unitor_inv_naturality, },
    tidy,
  end
  lemma functor_map_well_defined_1_2:
  functor_map V R (ℓ⁻¹ _ ≫ᵐ η⁺ ⊗ᵐ 𝟙 _ ≫ᵐ α _ _ _ ≫ᵐ 𝟙 _ ⊗ᵐ ε⁺ ≫ᵐ ρ _) = functor_map V R (𝟙 _) := begin
    simp [functor_map],
    slice_lhs 2 4 { change (η_⁺ V ⊗ 𝟙 V) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ ε_⁺ V), rw evaluation_coevaluation, },
    tidy,
  end
  lemma functor_map_well_defined_2_1:
  functor_map V R (ρ⁻¹ _ ≫ᵐ 𝟙 _ ⊗ᵐ η⁺ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ ε⁺ ⊗ᵐ 𝟙 _ ≫ᵐ ℓ _) = functor_map V R (𝟙 _) := begin
    simp [functor_map],
    slice_lhs 2 4 { change (𝟙 Vᘁ ⊗ η_⁺ _) ≫ (α_ _ _ _).inv ≫ (ε_⁺ _ ⊗ 𝟙 Vᘁ), rw coevaluation_evaluation, },
    tidy,
  end
  lemma functor_map_well_defined_2_2:
  functor_map V R (ℓ⁻¹ _ ≫ᵐ η⁻ ⊗ᵐ 𝟙 _ ≫ᵐ α _ _ _ ≫ᵐ 𝟙 _ ⊗ᵐ ε⁻ ≫ᵐ ρ _) = functor_map V R (𝟙 _) := begin
    simp [functor_map],
    change (λ_ _).inv ≫ (η_⁻ _ ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 Vᘁ ⊗ R.μ.inv ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).inv ≫ (α_ _ _ _).hom ≫ (𝟙 Vᘁ ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ≫ (𝟙 Vᘁ ⊗ ε_⁻ _) ≫ (ρ_ _).hom = 𝟙 Vᘁ,
    slice_lhs 5 6 { rw (α_ _ _ _).inv_hom_id, },
    slice_lhs 5 6 { rw category.id_comp, },
    slice_lhs 4 5 { rw [←tensor_comp, ←tensor_comp, R.μ.inv_hom_id, category.comp_id, tensor_id, tensor_id], },
    slice_lhs 4 5 { rw category.id_comp, },
    slice_lhs 2 4 { rw evaluation_coevaluation_rev, },
    tidy,
  end

  lemma functor_map_well_defined_3_left (b: ↓ ⊗ᵗ ↓ ⟶ᵐ ↓ ⊗ᵗ ↓):
  functor_map V R (ℓ⁻¹ _ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ η⁻ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ ρ⁻¹ _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ 𝟙 ↑ ⊗ᵐ η⁻ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ (α⁻¹ _ _ _ ⊗ᵐ 𝟙 _ ≫ᵐ α _ _ _) ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ b ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ (α _ _ _ ≫ᵐ 𝟙 _ ⊗ᵐ α _ _ _ ≫ᵐ α⁻¹ _ _ _) ⊗ᵐ 𝟙 _ ≫ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ ε⁻ ⊗ᵐ 𝟙 _ ≫ᵐ ρ _ ⊗ᵐ 𝟙 _ ≫ᵐ α _ _ _ ≫ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ ε⁻ ≫ᵐ ρ _) = right_adjoint_mate (functor_map V R b) := begin
    simp only [functor_map, category.assoc, tensor_comp_id, comp_tensor_id],
    change (λ_ _).inv ≫ (α_ _ _ _).inv ≫ ((η_⁻ _ ⊗ 𝟙 Vᘁ) ⊗ 𝟙 Vᘁ) ≫ (((𝟙 Vᘁ ⊗ R.μ.inv) ⊗ 𝟙 Vᘁ) ⊗ 𝟙 Vᘁ) ≫ ((((ρ_ _).inv ⊗ 𝟙 V) ⊗ 𝟙 Vᘁ) ⊗ 𝟙 Vᘁ) ≫ ((((𝟙 Vᘁ ⊗ η_⁻ _) ⊗ 𝟙 V) ⊗ 𝟙 Vᘁ) ⊗ 𝟙 Vᘁ) ≫ ((((𝟙 Vᘁ ⊗ 𝟙 Vᘁ ⊗ R.μ.inv) ⊗ 𝟙 V) ⊗ 𝟙 Vᘁ) ⊗ 𝟙 Vᘁ) ≫ ((((α_ _ _ _).inv ⊗ 𝟙 V) ⊗ 𝟙 Vᘁ) ⊗ 𝟙 Vᘁ) ≫ (((α_ _ _ _).hom ⊗ 𝟙 Vᘁ) ⊗ 𝟙 Vᘁ) ≫ ((((𝟙 Vᘁ ⊗ 𝟙 Vᘁ) ⊗ functor_map V R b) ⊗ 𝟙 Vᘁ) ⊗ 𝟙 Vᘁ) ≫ ((α_ _ (V ⊗ V) _).hom ⊗ 𝟙 Vᘁ) ≫ ((𝟙 (Vᘁ ⊗ Vᘁ) ⊗ (α_ _ _ _).hom) ⊗ 𝟙 Vᘁ) ≫ ((α_ _ _ _).inv ⊗ 𝟙 Vᘁ) ≫ ((((𝟙 Vᘁ ⊗ 𝟙 Vᘁ) ⊗ 𝟙 V) ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ⊗ 𝟙 Vᘁ) ≫ ((𝟙 ((Vᘁ ⊗ Vᘁ) ⊗ V) ⊗ ε_⁻ _) ⊗ 𝟙 Vᘁ) ≫ ((ρ_ _).hom ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ ((𝟙 Vᘁ ⊗ 𝟙 Vᘁ) ⊗ R.μ.hom ⊗ 𝟙 Vᘁ)≫ (𝟙 (Vᘁ ⊗ Vᘁ) ⊗ ε_⁻ _) ≫ (ρ_ _).hom = 𝟙 (Vᘁ ⊗ Vᘁ),
  end

  lemma functor_map_well_defined_3 (b: ↓ ⊗ᵗ ↓ ⟶ᵐ ↓ ⊗ᵗ ↓):
  functor_map V R (ℓ⁻¹ _ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ η⁻ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ ρ⁻¹ _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ 𝟙 ↑ ⊗ᵐ η⁻ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ (α⁻¹ _ _ _ ⊗ᵐ 𝟙 _ ≫ᵐ α _ _ _) ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ b ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ (α _ _ _ ≫ᵐ 𝟙 _ ⊗ᵐ α _ _ _ ≫ᵐ α⁻¹ _ _ _) ⊗ᵐ 𝟙 _ ≫ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ ε⁻ ⊗ᵐ 𝟙 _ ≫ᵐ ρ _ ⊗ᵐ 𝟙 _ ≫ᵐ α _ _ _ ≫ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ ε⁻ ≫ᵐ ρ _) = functor_map V R (ρ⁻¹ _ ≫ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ η⁺ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ ρ⁻¹ _ ⊗ᵐ 𝟙 _ ≫ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ η⁺ ⊗ᵐ 𝟙 _ ≫ᵐ (α _ _ _ ≫ᵐ 𝟙 _ ⊗ᵐ α⁻¹ _ _ _ ≫ᵐ α⁻¹ _ _ _) ⊗ᵐ 𝟙 _ ≫ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ b ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ (α⁻¹ _ _ _ ≫ᵐ α _ _ _ ⊗ᵐ 𝟙 _) ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ 𝟙 _ ⊗ᵐ ε⁺ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ ρ _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ ε⁺ ⊗ᵐ 𝟙 _ ⊗ᵐ 𝟙 _ ≫ᵐ α _ _ _ ≫ᵐ ℓ _) := begin
    rw functor_map_well_defined_3_left,
    sorry,
  end
  lemma functor_map_well_defined_4_1: functor_map V R (β ≫ᵐ β⁻¹) = functor_map V R (𝟙 (↓ ⊗ᵗ ↓)) := by simp [functor_map]
  lemma functor_map_well_defined_4_2: functor_map V R (β⁻¹ ≫ᵐ β) = functor_map V R (𝟙 (↓ ⊗ᵗ ↓)) := by simp [functor_map]
  lemma functor_map_well_defined_5:
  functor_map V R (α⁻¹ _ _ _ ≫ᵐ β ⊗ᵐ 𝟙 ↓ ≫ᵐ α _ _ _ ≫ᵐ 𝟙 ↓ ⊗ᵐ β ≫ᵐ α⁻¹ _ _ _ ≫ᵐ β ⊗ᵐ 𝟙 _) = functor_map V R (𝟙 ↓ ⊗ᵐ β ≫ᵐ α⁻¹ _ _ _ ≫ᵐ β ⊗ᵐ 𝟙 ↓ ≫ᵐ α _ _ _ ≫ᵐ 𝟙 ↓ ⊗ᵐ β ≫ᵐ α⁻¹ _ _ _) := begin
    simp [functor_map],
    change (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.c.hom) ≫ (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 V) = (𝟙 V ⊗ R.c.hom) ≫ (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.c.hom) ≫ (α_ _ _ _).inv,
    exact R.relation_1.symm,
  end
  lemma functor_map_well_defined_6_1:
  functor_map V R (ρ⁻¹ _ ≫ᵐ 𝟙 ↓ ⊗ᵐ η⁺ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ β ⊗ᵐ 𝟙 ↑ ≫ᵐ α _ _ _ ≫ᵐ 𝟙 ↓ ⊗ᵐ ε⁻ ≫ᵐ ρ _) = functor_map V R (𝟙 ↓) := begin
    simp [functor_map],
    change (ρ_ _).inv ≫ (𝟙 V ⊗ η_⁺ V) ≫ (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ≫ (𝟙 V ⊗ ε_⁻ V) ≫ (ρ_ _).hom = 𝟙 V,
    have h: trace_2 (R.c.hom ≫ (𝟙 V ⊗ R.μ.hom)) = (ρ_ _).inv ≫ (𝟙 V ⊗ η_⁺ V) ≫ (α_ _ _ _).inv ≫ (R.c.hom ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ≫ (𝟙 V ⊗ ε_⁻ V) ≫ (ρ_ _).hom := by simp [functor_map, trace_2, coevaluation, evaluation, evaluation_rev],
    rw ←h,
    exact R.relation_3_1,
  end
  lemma functor_map_well_defined_6_2:
  functor_map V R (ρ⁻¹ _ ≫ᵐ 𝟙 ↓ ⊗ᵐ η⁺ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ β⁻¹ ⊗ᵐ 𝟙 ↑ ≫ᵐ α _ _ _ ≫ᵐ 𝟙 ↓ ⊗ᵐ ε⁻ ≫ᵐ ρ _) = functor_map V R (𝟙 ↓) := begin
    simp [functor_map],
    change (ρ_ _).inv ≫ (𝟙 V ⊗ η_⁺ V) ≫ (α_ _ _ _).inv ≫ (R.c.inv ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ≫ (𝟙 V ⊗ ε_⁻ V) ≫ (ρ_ _).hom = 𝟙 V,
    have h: trace_2 (R.c.inv ≫ (𝟙 V ⊗ R.μ.hom)) = (ρ_ _).inv ≫ (𝟙 V ⊗ η_⁺ V) ≫ (α_ _ _ _).inv ≫ (R.c.inv ⊗ 𝟙 Vᘁ) ≫ (α_ _ _ _).hom ≫ (𝟙 V ⊗ R.μ.hom ⊗ 𝟙 Vᘁ) ≫ (𝟙 V ⊗ ε_⁻ V) ≫ (ρ_ _).hom := by simp [functor_map, trace_2, coevaluation, evaluation, evaluation_rev],
    rw ←h,
    exact R.relation_3_2,
  end
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
  exact aux.functor_map_well_defined_3 _ _ β,
  exact aux.functor_map_well_defined_3 _ _ β⁻¹,
  exact aux.functor_map_well_defined_4_1 _ _,
  exact aux.functor_map_well_defined_4_2 _ _,
  exact aux.functor_map_well_defined_5 _ _,
  exact aux.functor_map_well_defined_6_1 _ _,
  exact aux.functor_map_well_defined_6_2 _ _,
  exact aux.functor_map_well_defined_7_1 _ _,
  sorry,
  sorry,
  sorry,
end

def functor (R: enhanced_R_matrix V): Tangle ⥤ C := {
  obj := functor_obj V,
  map := λ X Y f, quotient.lift_on' f (functor_map V R) (functor_map_well_defined V R)
}

variables {K: Type} [field K]

@[simp] def linear_map_smul (V: FinVect K) (s: K): V →ₗ[K] V :=
  is_linear_map.mk' (λ x, s • x) (is_linear_map.is_linear_map_smul s)

@[simp] def V₂: FinVect K := ⟨⟨bool → K⟩, begin
  change finite_dimensional K (bool → K),
  exact finite_dimensional.finite_dimensional_pi K,
end⟩

variables (q: Kˣ)
include q

open_locale tensor_product

@[simp] def jones_R_aux : Π (i j: bool), (bool → K) ⊗[K] (bool → K)
| ff ff := q⁻¹ • (function.update 0 ff 1) ⊗ₜ[K] (function.update 0 ff 1)
| ff tt := (q⁻¹)^2 • (function.update 0 tt 1) ⊗ₜ[K] (function.update 0 ff 1)
| tt ff := (q⁻¹)^2 • (function.update 0 ff 1) ⊗ₜ[K] (function.update 0 tt 1) + (q⁻¹ - (q⁻¹)^3 : K) • (function.update 0 tt 1) ⊗ₜ[K] (function.update 0 ff 1)
| tt tt := q⁻¹ • (function.update 0 tt 1) ⊗ₜ[K] (function.update 0 tt 1)

@[simp] def jones_R_inv_aux: Π (i j: bool), (bool → K) ⊗[K] (bool → K)
| ff ff := q • (function.update 0 ff 1) ⊗ₜ[K] (function.update 0 ff 1)
| ff tt := (q - q^3 : K) • (function.update 0 ff 1) ⊗ₜ[K] (function.update 0 tt 1) + q^2 • (function.update 0 tt 1) ⊗ₜ[K] (function.update 0 ff 1)
| tt ff := q^2 • (function.update 0 ff 1) ⊗ₜ[K] (function.update 0 tt 1)
| tt tt := q • (function.update 0 tt 1) ⊗ₜ[K] (function.update 0 tt 1)

def jones_R_aux': bool × bool → (bool → K) ⊗[K] (bool → K) := λ ⟨i, j⟩, jones_R_aux q i j 
def jones_R_inv_aux': bool × bool → (bool → K) ⊗[K] (bool → K) := λ ⟨i, j⟩, jones_R_inv_aux q i j 

noncomputable def jones_R: (bool → K) ⊗[K] (bool → K) →ₗ[K] (bool → K) ⊗[K] (bool → K) :=
  ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).constr K (jones_R_aux' q)

noncomputable def jones_R_inv: (bool → K) ⊗[K] (bool → K) →ₗ[K] (bool → K) ⊗[K] (bool → K) :=
  ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).constr K (jones_R_inv_aux' q)

lemma aaa (x): (jones_R_inv q) x = x := begin
  rw jones_R_inv,
  rw basis.constr_apply,
  rw jones_R_inv_aux', simp, 
end

lemma jones_R_hom_inv_id: jones_R q ∘ₗ jones_R_inv q = linear_map.id := begin
  have h := @basis.constr_eq _ _ _ _ _ _ _ _ _
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    K _ _ _
    (jones_R q ∘ jones_R_inv_aux' q)
    linear_map.id 
    (_),
    {

      sorry,
    },
    {
      rintro ⟨x, y⟩, simp,
      cases x, cases y,
      {
        simp [jones_R_inv_aux', jones_R],
        -- have h := @basis.constr_eq _ _ _ _ _ _ _ _ _
        sorry,
      },
    }
    
    
    --((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)) K,
  -- apply tensor_product.ext', intros x y, rw [jones_R, jones_R_inv], rw ←basis.constr_comp, rw basis.constr_comp,
end

/-
  have h' := @basis.constr_eq _ _ _ _ _ _ _ _ _
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    K _ _ _
    (jones_R q ∘ jones_R_inv_aux' q)
    _
    (_),
-/

noncomputable def jones_enhanced_R_matrix: @enhanced_R_matrix (FinVect K) _ _ _ _ _ V₂ := {
  c := {
    hom := jones_R q,
    inv := jones_R_inv q,
    hom_inv_id' := begin
      simp [jones_R, jones_R_inv, jones_R_aux, jones_R_inv_aux],
      sorry,
    end,
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