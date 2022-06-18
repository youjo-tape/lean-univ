import kassel.Tangle
import kassel.rigid_appendix
import category_theory.monoidal.braided

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

def trace {V: C} (f: V ⟶ V) :=
  η_ _ _ ≫ (f ⊗ 𝟙 Vᘁ) ≫ τ_ _ _ ≫ ε_ _ _

def trace_2 {V: C} (f: V ⊗ V ⟶ V ⊗ V)
  :=                  (ρ_ _).inv
  ≫ (𝟙 V ⊗ η_ _ _) ≫ (α_ _ _ _).inv
  ≫ (f ⊗ 𝟙 Vᘁ)     ≫ (α_ _ _ _).hom
  ≫ (𝟙 V ⊗ τ_ _ _)
  ≫ (𝟙 V ⊗ ε_ _ _) ≫ (ρ_ _).hom

def partial_transpose_1 {V₁ V₂ W₁ W₂: C} (f: V₁ ⊗ V₂ ⟶ W₁ ⊗ W₂)
  :=                            (𝟙 W₁ᘁ ⊗ (λ_ _).inv)
  ≫ (𝟙 W₁ᘁ ⊗ η_ _ _ ⊗ 𝟙 V₂)  ≫ (𝟙 W₁ᘁ ⊗ τ_ _ _ ⊗ 𝟙 V₂) ≫ (𝟙 W₁ᘁ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv
  ≫ (τ_ _ _ ⊗ f)            ≫ (α_ _ _ _).hom ≫ (𝟙 V₁ᘁ ⊗ (α_ _ _ _).inv)
  ≫ (𝟙 V₁ᘁ ⊗ ε_ _ _ ⊗ 𝟙 W₂) ≫ (𝟙 V₁ᘁ ⊗ (λ_ _).hom)

postfix `⁺`:1025 := partial_transpose_1

structure enhanced_R_matrix (V: C) :=
  (c: V ⊗ V ≅ V ⊗ V)
  (μ: V ≅ V)
  (relation_1:
       (𝟙 V ⊗ c.hom) ≫ (α_ _ _ _).inv
    ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom
    ≫ (𝟙 V ⊗ c.hom)
  =                    (α_ _ _ _).inv
    ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom
    ≫ (𝟙 V ⊗ c.hom) ≫ (α_ _ _ _).inv
    ≫ (c.hom ⊗ 𝟙 V) ≫ (α_ _ _ _).hom
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
  | _ _ η⁺ := by simp; exact η_ _ _
  | _ _ η⁻ := by simp; exact η_ _ _ ≫ (𝟙 Vᘁ ⊗ ((φ_ _).hom ≫ R.μ.inv))
  | _ _ ε⁺ := by simp; exact ε_ _ _
  | _ _ ε⁻ := by simp; exact ((R.μ.hom ≫ (φ_ _).inv) ⊗ 𝟙 Vᘁ) ≫ ε_ Vᘁ Vᘁᘁ
  | _ _ β := R.c.hom
  | _ _ β⁻¹ := R.c.inv

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
  { simp only [functor_map],  }
end 

def functor (R: enhanced_R_matrix V): Tangle ⥤ C := {
  obj := functor_obj V,
  map := λ X Y f, quotient.lift_on' f (functor_map V R) (functor_map_well_defined V R)
}

end kassel