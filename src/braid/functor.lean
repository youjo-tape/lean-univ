import braid.Braid
import algebra.category.FinVect

variables (K: Type) [field K]

def K_2: Module K := Module.of K (fin 2 → K)
noncomputable def std_basis_K_2 := pi.basis_fun K (fin 2)

def FinVect_K_2: FinVect K := ⟨
  K_2 K,
  by change finite_dimensional K (fin 2 → K); apply_instance
⟩
def FinVect_tensor (X Y: FinVect K): FinVect K := ⟨
  Module.of K (tensor_product K X Y),
  by change finite_dimensional K (tensor_product K X Y); apply_instance
⟩
local infix ` ⊗ᶠ `: 50 := FinVect_tensor K

namespace Braid
  @[simp] def toFinVect: Braid → FinVect K
    | ↓ := FinVect_K_2 K
    | (X ⊗ᵗ Y) := X.toFinVect ⊗ᶠ Y.toFinVect
end Braid

def matrix_braiding (q: units K): matrix (fin 4) (fin 4) K := ![
  ![q^(1/2), 0, 0, 0],
  ![0, 0, q, 0],
  ![0, q, q^(1/2)-q^(3/2), 0],
  ![0, 0, 0, q^(1/2)]
]
def mat_braiding_aux: fin 2 × fin 2 → fin 4 := λ ⟨x, y⟩, 2*x+y

noncomputable def map_braiding (q: units K): FinVect_K_2 K ⊗ᶠ FinVect_K_2 K ⟶ FinVect_K_2 K ⊗ᶠ FinVect_K_2 K := begin
    have b := pi.basis_fun K (fin 2),
    have b2 := basis.tensor_product b b,
    have m := λ x y, matrix_braiding K q (mat_braiding_aux x) (mat_braiding_aux y),
    exact matrix.to_lin b2 b2 m,
end

noncomputable def functor_map (q: units K): Π {X Y: Braid}, (X ⟶ᵐ Y) → (X.toFinVect K ⟶ Y.toFinVect K)
  | _ _ 𝟙 := linear_map.id
  | _ _ (f ≫ g) := functor_map g ∘ₗ functor_map f
  | _ _ (f ⊗ᵐ g) := tensor_product.map (functor_map f) (functor_map g)
  | _ _ (α a b c) := begin
    have f := tensor_product.assoc K (a.toFinVect K) (b.toFinVect K) (c.toFinVect K),
    exact Module.of_hom f.to_linear_map,
  end
  | _ _ (α⁻¹ a b c) := begin
    have f := tensor_product.assoc K (a.toFinVect K) (b.toFinVect K) (c.toFinVect K),
    exact Module.of_hom f.symm.to_linear_map,
  end
  | _ _ β := map_braiding K q
  | _ _ β⁻¹ := map_braiding K q -- uso

def functor (q: units K): Braid ⥤ FinVect K := {
  obj := Braid.toFinVect K,
  map := begin
    rintro X Y f,
    refine functor_map K q _, induction f with _ f g hfg, assumption,
    
  end
}