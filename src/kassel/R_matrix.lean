import algebra.category.FinVect
import category_theory.monoidal.braided
import kassel.Tangle

open category_theory

namespace kassel

universes v u
variables
  {C: Type u}
  [category.{v} C]
  [monoidal_category C]
  [right_rigid_category C]
  [symmetric_category C]

def swap (V W: C) := (β_ V W).hom
notation `τ_` := swap

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

end kassel