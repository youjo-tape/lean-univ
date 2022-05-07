import algebra.category.FinVect
import algebra.group.units
import linear_algebra.dual
import data.matrix.notation
import linear_algebra.matrix.determinant
import group_theory.perm.fin
import tactic.norm_swap
import Tangle

variables (K: Type) [field K]

@[simp] def K_2: Module K := Module.of K (fin 2 → K)

def FinVect_K_2: FinVect K := ⟨
  K_2 K,
  by change finite_dimensional K (fin 2 → K); apply_instance,
⟩

@[simp] def FinVect_dual (V: FinVect K): FinVect K := ⟨
  Module.of K (module.dual K V),
  by change finite_dimensional K (module.dual K V); apply_instance
⟩

@[simp] def FinVect_tensor (X Y: FinVect K): FinVect K := ⟨
  Module.of K (tensor_product K X Y),
  by change finite_dimensional K (tensor_product K X Y); apply_instance
⟩

namespace Tangle

@[simp] def toFinVect: Tangle → FinVect K
  | id := ⟨Module.of K K, finite_dimensional.finite_dimensional_self K⟩
  | (of tt) := FinVect_K_2 K
  | (of ff) := FinVect_dual K (FinVect_K_2 K)
  | (tensor x y) := FinVect_tensor K x.toFinVect y.toFinVect

@[simp] def rotate_to_dual (a: Tangle): a.rotate.toFinVect K = FinVect_dual K (a.toFinVect K) := begin
  dsimp [Tangle.rotate], sorry
end

end Tangle

def functor_map (q: units K): Π {X Y: Tangle}, (X ⟶ᵐ Y) → (X.toFinVect K ⟶ Y.toFinVect K)
  | _ _ (𝟙 a) := linear_map.id
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
  | _ _ (ℓ a) := begin
    have f := tensor_product.lid K (a.toFinVect K),
    exact Module.of_hom f.to_linear_map,
  end
  | _ _ (ℓ⁻¹ a) := begin
    have f := tensor_product.lid K (a.toFinVect K),
    exact Module.of_hom f.symm.to_linear_map,
  end
  | _ _ (ρ a) := begin
    have f := tensor_product.rid K (a.toFinVect K),
    exact Module.of_hom f.to_linear_map,
  end
  | _ _ (ρ⁻¹ a) := begin
    have f := tensor_product.rid K (a.toFinVect K),
    exact Module.of_hom f.symm.to_linear_map,
  end
  | _ _ (hom.evaluation_1 tt) := begin
    have f := module.dual.eval K ((Tangle.of tt).toFinVect K),
    have g := tensor_product.uncurry K _ _ _ f,
    simp, dsimp [Tangle.rotate_to_dual K (Tangle.of tt)],
    exact Module.of_hom g,
  end
  | _ _ (hom.evaluation_1 ff) := begin
    have f := module.dual.eval K ((Tangle.of ff).toFinVect K),
    have g := tensor_product.uncurry K _ _ _ f,
    rw Tangle.toFinVect at g,
    simp, dsimp [Tangle.rotate_to_dual K (Tangle.of ff)],
    have h := Module.of_hom g,
    exact h,
  end
  | _ _ (hom.coevaluation_1 a) := begin
    have f := coevaluation K (a.toFinVect K),
    have g := (tensor_product.comm K _ _).to_linear_map ∘ₗ f,
    simp, dsimp [a.rotate_to_dual K],
    exact Module.of_hom g,
  end
  | _ _ hom.braiding_dd_hom := begin
    have mat: matrix (fin 4) (fin 4) K := ![
      ![q^(1/2), 0, 0, 0],
      ![0, 0, q, 0],
      ![0, q, q^(1/2)-q^(3/2), 0],
      ![0, 0, 0, q^(1/2)]
    ],
    have X := (↓ ⊗ᵗ ↓).toFinVect K,
    have b: basis _ _ _ := sorry,
    have f := matrix.to_lin b b mat,
    exact f,
  end
  | _ _ hom.braiding_dd_inv := sorry

def functor_tangle: Tangle ⥤ FinVect K := {
  obj := Tangle.toFinVect K,
  map := begin
    rintro X Y f, 
  end --by rintro X Y ⟨f⟩; exact functor_map K f,
}

namespace test

open_locale matrix

def f: fin 3 → rat := λ i, i + 2 -- (2, 3, 4)

@[simp] def iota (n: ℕ): fin n → ℤ := λ i, i

/-
iota 3 = (0, 1, 2)
iota 4 = (0, 1, 2, 3)
-/

example: iota 3 = ![0, 1, 2] := begin
  ext i, apply @fin.cons_induction i ![0, 1, 2], simp, cases i, induction i_val,
    simp,
    
end

example (i: fin 3): ![0, 1, 2] i = i := begin
  cases i,
  induction i_val,
    simp,
    have h' : i_val_n < 3 := by
      calc i_val_n < i_val_n.succ : sorry
      ...          < 3 : i_property,
    have h := matrix.cons_val_succ _ _ ⟨i_val_n, h'⟩, 
end

@[simp] def mat_id (n: nat): matrix (fin n) (fin n) rat
  := λ i j, if (i = j) then 1 else 0

example: mat_id 2 = ![![1, 0], ![0, 1]] := begin
  funext, simp,
end

example: ![![1, 0], ![0, 1]] ⬝ ![![1, 0], ![0, 1]] = ![![1, 0], ![0, 1]] := begin
  simp,
end

example (n: nat): mat_id n ⬝ mat_id n = mat_id n := begin
  funext, rw matrix.mul, dsimp [matrix.dot_product], simp,
end

end test
