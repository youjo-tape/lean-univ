import algebra.category.Module.basic
import linear_algebra.tensor_product
import linear_algebra.dual
import Tangle

variables (K: Type) [field K]

namespace Tangle

@[simp] def to_module: Tangle → Module K
  | id := Module.of K K
  | (of x) := if x then Module.of K (fin 2 → K) else Module.of K (module.dual K (fin 2 → K))
  | (tensor a b) := Module.of K (tensor_product K a.to_module b.to_module)

end Tangle

@[simp] def functor_map: Π {X Y: Tangle}, (X ⟶ᵐ Y) → (X.to_module K ⟶ Y.to_module K)
  | _ _ (𝟙 a) := linear_map.id
  | _ _ (f ≫ g) := functor_map g ∘ₗ functor_map f
  | _ _ (f ⊗ᵐ g) := tensor_product.map (functor_map f) (functor_map g)
  | _ _ (α a b c) := begin
    have f := tensor_product.assoc K (a.to_module K) (b.to_module K) (c.to_module K),
    exact Module.of_hom f.to_linear_map,
  end
  | _ _ (α⁻¹ a b c) := begin
    have f := tensor_product.assoc K (a.to_module K) (b.to_module K) (c.to_module K),
    exact Module.of_hom f.symm.to_linear_map,
  end
  | _ _ (ℓ a) := begin
    have f := tensor_product.lid K (a.to_module K),
    exact Module.of_hom f.to_linear_map,
  end
  | _ _ (ℓ⁻¹ a) := begin
    have f := tensor_product.lid K (a.to_module K),
    exact Module.of_hom f.symm.to_linear_map,
  end
  | _ _ (ρ a) := begin
    have f := tensor_product.rid K (a.to_module K),
    exact Module.of_hom f.to_linear_map,
  end
  | _ _ (ρ⁻¹ a) := begin
    have f := tensor_product.rid K (a.to_module K),
    exact Module.of_hom f.symm.to_linear_map,
  end
  | _ _ (ε a) := sorry  -- FinVect じゃないので無理
  | _ _ (η a) := sorry
  | _ _ (β a b) := sorry
  | _ _ (β⁻¹ a b) := sorry

def functor_tangle: Tangle ⥤ Module K := {
  obj := Tangle.to_module K,
  map := begin rintro X Y ⟨f⟩, exact ⟦functor_map K f⟧, end,
}
