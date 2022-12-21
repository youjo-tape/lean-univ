import kassel.lemma.right_pivotal_category

open category_theory
open category_theory.monoidal_category

namespace kassel
open right_pivotal_category

namespace FinVect

variables {K: Type*} [field K]

noncomputable instance finite_dimensional.decidable_eq (V) [add_comm_group V] [module K V] [finite_dimensional K V]:
  decidable_eq (basis.of_vector_space_index K V) :=
  equiv.decidable_eq (fintype.equiv_fin (basis.of_vector_space_index K V))

lemma dual_mul {V} [add_comm_monoid V] [module K V] (f: module.dual K V) (x: V) (t: K):
  f x * t = f (t • x) :=
by rw [map_smul, smul_eq_mul, mul_comm]

lemma right_adjoint_mate_eq_dual_linear_map {X Y: FinVect K} (f: X.obj →ₗ[K] Y.obj):
  left_unitor.hom K (module.dual K X.obj) ∘ₗ
  tensor_product.map (evaluation.hom K Y.obj) linear_map.id ∘ₗ
  associator.inv K _ _ _ ∘ₗ
  tensor_product.map linear_map.id (tensor_product.map f linear_map.id) ∘ₗ
  tensor_product.map linear_map.id (coevaluation.hom K X.obj) ∘ₗ
  right_unitor.inv K (module.dual K Y.obj) =
  f.dual_map :=
begin
  ext g x,
  have b := basis.of_vector_space K X.obj,
  simp [
    map_sum, tensor_product.tmul_sum, tensor_product.map_tmul,
    coevaluation_apply_one' b, linear_map.id_apply
  ],
  simp_rw [dual_mul, ←map_sum], congr,
  simp_rw [←map_smul, ←map_sum], congr,
  rw basis.sum_repr,
end

lemma right_adjoint_mate_eq_dual {X Y: FinVect K} (f: X ⟶ Y):
  fᘁ = f.dual_map :=
by apply right_adjoint_mate_eq_dual_linear_map

lemma module.eval_equiv_to_linear_map' (V) [add_comm_group V] [module K V] [finite_dimensional K V]:
  ⇑(module.eval_equiv K V) = module.dual.eval K V :=
by rw [←module.eval_equiv_to_linear_map, linear_equiv.coe_to_linear_map]

noncomputable def right_pivotor (X: FinVect K): X ≅ Xᘁᘁ := {
  hom := right_pivotor.hom K X.obj,
  inv := right_pivotor.inv K X.obj,
  hom_inv_id' := by ext; simp [←module.eval_equiv_to_linear_map],
  inv_hom_id' := by ext; simp [←module.eval_equiv_to_linear_map]
}

lemma right_pivotor_naturality (X Y: FinVect K) (f: X ⟶ Y):
  f ≫ (right_pivotor Y).hom = (right_pivotor X).hom ≫ fᘁᘁ :=
begin
  unfold_projs at *, dsimp [right_pivotor],
  ext x g, simp [right_adjoint_mate_eq_dual, module.eval_equiv_to_linear_map'],
end

lemma right_pivotor_tensor_naturality (X Y: FinVect K):
  (right_pivotor (X ⊗ Y)).hom = ((right_pivotor X).hom ⊗ (right_pivotor Y).hom) ≫ (δ_ _ _).inv ≫ ((δ_ _ _).hom)ᘁ :=
begin
  ext x y f, unfold_projs, dsimp [right_pivotor],
  simp_rw module.eval_equiv_to_linear_map',
  rw module.dual.eval_apply,
  
end

noncomputable instance right_pivotal_category: right_pivotal_category (FinVect K) := {
  right_pivotor := right_pivotor,
  right_pivotor_naturality' := right_pivotor_naturality,
  right_pivotor_tensor_naturality' := right_pivotor_tensor_naturality
}

end FinVect
end kassel
