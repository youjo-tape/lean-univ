import kassel.jones

noncomputable theory

namespace kassel

open jones
open_locale matrix kronecker

variables
  (K: Type*) [field K]
  (q: Kˣ)

lemma linear_map.smul_to_matrix
  {M N} [add_comm_monoid M] [add_comm_monoid N] [module K M] [module K N]
  {m n} [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
  (bM: basis m K M) (bN: basis n K N) (a: K) (f: M →ₗ[K] N):
  linear_map.to_matrix bM bN (a • f) = a • linear_map.to_matrix bM bN f :=
by rw [←linear_equiv.to_linear_map_to_fun_eq_to_fun, linear_map.map_smul]

def jones_polynomial {X Y} (f: X ⟶ᵐ Y) :=
  ((jones_R_matrix K q).functor (V₂ K)).map ⟦f⟧

lemma jones_polynomial_apply {X Y} (f: X ⟶ᵐ Y):
  jones_polynomial K q f = (jones_R_matrix K q).functor_map (V₂ K) f :=
by dsimp; refl

def trivial_knot := η⁺ ≫ᵐ ε⁻

namespace trivial_knot

@[simp] def jones_polynomial': K := q⁻¹ + q

lemma jones_polynomial_matrix:
  evaluation.matrix K bool ⬝
  μ_matrix q ⊗ₖ 1 ⬝
  coevaluation.matrix K bool =
  jones_polynomial' K q • 1 :=
begin
  apply matrix.ext',
  intro v,
  simp [←matrix.mul_vec_mul_vec],

  nth_rewrite 3 matrix.mul_vec_apply,
  simp_rw fintype.sum_unit,

  nth_rewrite 2 matrix.mul_vec_apply,
  simp_rw fintype.sum_unit,

  nth_rewrite 1 matrix.mul_vec_apply,
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [matrix.kronecker_apply', matrix.one_apply, coevaluation.matrix],
  simp_rw [eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 0 matrix.mul_vec_apply,
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [evaluation.matrix, μ_matrix],
  simp_rw [eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  ext u, cases u,
  simp, ring,
end

lemma jones_polynomial_linear_map:
  evaluation.rev K _ ∘ₗ
  (tensor_product.map (μ_hom q) linear_map.id) ∘ₗ
  coevaluation.hom K _ =
  jones_polynomial' K q • linear_map.id :=
begin
  apply (equiv_like.apply_eq_iff_eq (linear_map.to_matrix
    (basis.singleton unit K)
    (basis.singleton unit K)
  )).mp,
  simp only [
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool).dual_basis) _,
    tensor_product.to_matrix
  ],
  simp_rw [
    μ_hom, linear_map.to_matrix_to_lin,
    linear_map.smul_to_matrix,
    linear_map.to_matrix_id,
    coevaluation.to_matrix,
    evaluation.rev_to_matrix,
    ←matrix.mul_assoc
  ],
  rw jones_polynomial_matrix,
end

lemma jones_polynomial:
  jones_polynomial K q trivial_knot = jones_polynomial' K q • linear_map.id :=
begin
  rw [trivial_knot, jones_polynomial_apply],
  simp_rw enhanced_R_matrix.functor_map,
  apply jones_polynomial_linear_map K q,
end

end trivial_knot

def trefoil_knot := ρ⁻¹ _ ≫ᵐ
  η⁻ ⊗ᵐ η⁺          ≫ᵐ α _ _ _ ≫ᵐ 𝟙ᵐ _ ⊗ᵐ α⁻¹ _ _ _ ≫ᵐ
  𝟙ᵐ _ ⊗ᵐ β ⊗ᵐ 𝟙ᵐ _ ≫ᵐ
  𝟙ᵐ _ ⊗ᵐ β ⊗ᵐ 𝟙ᵐ _ ≫ᵐ
  𝟙ᵐ _ ⊗ᵐ β ⊗ᵐ 𝟙ᵐ _ ≫ᵐ 𝟙ᵐ _ ⊗ᵐ α _ _ _ ≫ᵐ α⁻¹ _ _ _ ≫ᵐ
  ε⁺ ⊗ᵐ ε⁻          ≫ᵐ ρ _

namespace trefoil_knot

-- (q⁻¹ + q) で割って q ↦ t ^ (-1/2) と置き換えれば（ちゃんとした）Jones 多項式になる

@[simp] def jones_polynomial': K := (q⁻¹ + q) * (q⁻¹ ^ 2 + q⁻¹ ^ 6 - q⁻¹ ^ 8)

lemma jones_polynomial_matrix:
  right_unitor.hom_matrix K unit ⬝
  evaluation.matrix K bool ⊗ₖ (evaluation.matrix K bool ⬝ μ_matrix q ⊗ₖ 1) ⬝
  associator.inv_matrix K ⬝
  (1: matrix bool bool K) ⊗ₖ associator.hom_matrix K ⬝
  (1: matrix bool bool K) ⊗ₖ (R_matrix q ⊗ₖ (1: matrix bool bool K)) ⬝
  (1: matrix bool bool K) ⊗ₖ (R_matrix q ⊗ₖ (1: matrix bool bool K)) ⬝
  (1: matrix bool bool K) ⊗ₖ (R_matrix q ⊗ₖ (1: matrix bool bool K)) ⬝
  (1: matrix bool bool K) ⊗ₖ associator.inv_matrix K ⬝
  associator.hom_matrix K ⬝
  (1 ⊗ₖ μ_matrix_inv q ⬝ coevaluation.matrix K bool) ⊗ₖ coevaluation.matrix K bool ⬝
  right_unitor.inv_matrix K unit =
  jones_polynomial' K q • 1 :=
begin
  apply matrix.ext',
  intro v,
  iterate 10 {
    rw ←matrix.mul_vec_mul_vec,
    nth_rewrite 1 matrix.mul_vec_apply,
    simp [←finset.univ_product_univ, finset.sum_product, matrix.mul_apply],
  },
  rw matrix.mul_vec_apply,
  simp [←finset.univ_product_univ, finset.sum_product, matrix.smul_mul_vec_assoc],
  ext x, cases x,
  ring_nf, field_simp, ring,
end

lemma jones_polynomial_linear_map:
  right_unitor.hom K _ ∘ₗ
  tensor_product.map (evaluation.hom K _) (
    evaluation.rev K _ ∘ₗ tensor_product.map (μ_hom q) linear_map.id
  ) ∘ₗ
  associator.inv K _ _ _ ∘ₗ
  tensor_product.map linear_map.id (associator.hom K _ _ _) ∘ₗ
  tensor_product.map linear_map.id (tensor_product.map (R_hom q) linear_map.id) ∘ₗ
  tensor_product.map linear_map.id (tensor_product.map (R_hom q) linear_map.id) ∘ₗ
  tensor_product.map linear_map.id (tensor_product.map (R_hom q) linear_map.id) ∘ₗ
  tensor_product.map linear_map.id (associator.inv K _ _ _) ∘ₗ
  associator.hom K _ _ _ ∘ₗ
  tensor_product.map (
    tensor_product.map linear_map.id (μ_inv q) ∘ₗ coevaluation.rev K (bool → K)
  ) (coevaluation.hom K (bool → K)) ∘ₗ
  right_unitor.inv K _ =
  jones_polynomial' K q • linear_map.id :=
begin
  apply (equiv_like.apply_eq_iff_eq (linear_map.to_matrix
    (basis.singleton unit K)
    (basis.singleton unit K)
  )).mp,
  simp only [
    linear_map.to_matrix_comp _ ((basis.singleton unit K).tensor_product (basis.singleton unit K)) _,
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool).dual_basis) _,
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).dual_basis.tensor_product (pi.basis_fun K bool)) _,
    linear_map.to_matrix_comp _ (((pi.basis_fun K bool).dual_basis.tensor_product (pi.basis_fun K bool)).tensor_product ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool).dual_basis)) _,
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).dual_basis.tensor_product ((pi.basis_fun K bool).tensor_product ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool).dual_basis))) _,
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).dual_basis.tensor_product (((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).tensor_product (pi.basis_fun K bool).dual_basis)) _,
    tensor_product.to_matrix
  ],
  simp_rw [
    R_hom, μ_hom, μ_inv, linear_map.to_matrix_to_lin,
    linear_map.smul_to_matrix,
    linear_map.to_matrix_id,
    associator.hom_to_matrix,
    associator.inv_to_matrix,
    right_unitor.hom_to_matrix,
    right_unitor.inv_to_matrix,
    coevaluation.to_matrix,
    coevaluation.rev_to_matrix,
    evaluation.to_matrix,
    evaluation.rev_to_matrix,
    ←matrix.mul_assoc
  ],
  rw jones_polynomial_matrix,
end

lemma jones_polynomial:
  jones_polynomial K q trefoil_knot = jones_polynomial' K q • linear_map.id :=
begin
  rw [trefoil_knot, jones_polynomial_apply],
  simp_rw enhanced_R_matrix.functor_map,
  apply jones_polynomial_linear_map K q,
end

end trefoil_knot

end kassel
