import kassel.enhanced_R_matrix
import tactic.field_simp
import kassel.to_matrix_appendix

namespace kassel
namespace jones

variables {K: Type*} [field K]

lemma pow_mul_single (a: K) (n: ℕ): a ^ n * a = a ^ (n + 1) := by nth_rewrite 1 ←pow_one a; rw pow_add
lemma single_mul_pow (a: K) (n: ℕ): a * a ^ n = a ^ (1 + n) := by nth_rewrite 0 ←pow_one a; rw pow_add

@[simp] def V₂: FinVect K := ⟨⟨bool → K⟩, begin
  change finite_dimensional K (bool → K),
  exact finite_dimensional.finite_dimensional_pi K,
end⟩

section

variables (q: Kˣ)

@[simp] def R_matrix: matrix (bool × bool) (bool × bool) K 
  | (ff, ff) (ff, ff) := q⁻¹
  | (ff, tt) (tt, ff) := (q⁻¹)^2
  | (tt, ff) (ff, tt) := (q⁻¹)^2
  | (tt, ff) (tt, ff) := q⁻¹ + -(q⁻¹)^3
  | (tt, tt) (tt, tt) := q⁻¹
  | _ _ := 0

@[simp] def R_matrix_inv: matrix (bool × bool) (bool × bool) K
  | (ff, ff) (ff, ff) := q
  | (ff, tt) (ff, tt) := q + -q^3
  | (ff, tt) (tt, ff) := q^2
  | (tt, ff) (ff, tt) := q^2
  | (tt, tt) (tt, tt) := q
  | _ _ := 0

noncomputable def R_hom :=
  matrix.to_lin
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    (R_matrix q)

noncomputable def R_inv :=
  matrix.to_lin
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    (R_matrix_inv q)

def μ_hom: (bool → K) →ₗ[K] (bool → K) := ((q⁻¹)^2: K) • linear_map.id
def μ_inv: (bool → K) →ₗ[K] (bool → K) := (q^2: K) • linear_map.id

end

variables {q: Kˣ}

lemma matrix_to_μ_hom:
  matrix.to_lin (pi.basis_fun K bool) (pi.basis_fun K bool) (((q⁻¹)^2: K) • 1) = μ_hom q
:=
  by rw [μ_hom, linear_equiv.map_smul, matrix.to_lin_one]

lemma matrix_to_μ_inv:
  matrix.to_lin (pi.basis_fun K bool) (pi.basis_fun K bool) ((q^2: K) • 1) = μ_inv q
:=
  by rw [μ_inv, linear_equiv.map_smul, matrix.to_lin_one]

lemma R_hom_inv_id: R_inv q ∘ₗ R_hom q = linear_map.id := begin
  rw [R_hom, R_inv, ←matrix.to_lin_mul],
  rw ←matrix.to_lin_one ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)),
  congr,
  ext ⟨i₁, i₂⟩ ⟨k₁, k₂⟩,
  simp_rw matrix.mul_apply,
  dsimp,
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  cases i₁; cases i₂; cases k₁; cases k₂; simp,
  field_simp,
  simp [left_distrib, right_distrib, ←pow_add, neg_mul, pow_mul_single, single_mul_pow],
  have: 5 + 0 = 5 := rfl, rw this,
  have: 7 + 0 = 7 := rfl, rw this,
  rw ←add_assoc, rw add_assoc ((q: K)^7) _ _,
  simp,
end

lemma R_inv_hom_id: R_hom q ∘ₗ R_inv q = linear_map.id := begin
  rw [R_hom, R_inv, ←matrix.to_lin_mul],
  rw ←matrix.to_lin_one ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)),
  congr,
  ext ⟨i₁, i₂⟩ ⟨k₁, k₂⟩,
  simp_rw matrix.mul_apply,
  dsimp,
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  cases i₁; cases i₂; cases k₁; cases k₂; simp,
  field_simp,
  simp [right_distrib, ←pow_add, neg_mul, pow_mul_single, single_mul_pow],
  have: 5 + 0 = 5 := rfl, rw this,
  have: 7 + 0 = 7 := rfl, rw this,
  rw ←add_assoc, rw add_assoc ((q: K)^7) _ _,
  simp,
end

lemma μ_hom_inv_id: μ_inv q ∘ₗ μ_hom q = linear_map.id :=
  by simp [μ_hom, μ_inv, linear_map.smul_comp, linear_map.comp_smul]

lemma μ_inv_hom_id: μ_hom q ∘ₗ μ_inv q = linear_map.id :=
  by simp [μ_hom, μ_inv, linear_map.smul_comp, linear_map.comp_smul]

open_locale matrix kronecker

lemma R_relation_1_matrix:
  (associator_inv_matrix K) ⬝
  ((1: matrix _ _ K).kronecker (R_matrix q)) ⬝
  (associator_hom_matrix K) ⬝
  ((R_matrix q).kronecker (1: matrix _ _ K)) ⬝
  (associator_inv_matrix K) ⬝
  ((1: matrix _ _ K).kronecker (R_matrix q)) =
  ((R_matrix q).kronecker (1: matrix _ _ K)) ⬝
  (associator_inv_matrix K) ⬝
  ((1: matrix _ _ K).kronecker (R_matrix q)) ⬝
  (associator_hom_matrix K) ⬝
  ((R_matrix q).kronecker (1: matrix _ _ K)) ⬝
  (associator_inv_matrix K) :=
begin
  simp only [
    associator_hom_matrix_reindex,
    associator_inv_matrix_reindex,
    associator_hom_matrix_reindex_assoc,
    associator_inv_matrix_reindex_assoc
  ],
  ext ⟨⟨i₁, i₂⟩, i₃⟩ ⟨j₁, j₂, j₃⟩,
  simp only [matrix.mul_apply],
  dsimp,
  simp_rw [←finset.univ_product_univ],
  simp_rw [finset.sum_product],
  simp_rw [fintype.sum_bool],
  simp only [associator_inv_matrix, matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul, add_zero, zero_add, R_matrix],
  cases i₁; simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul, add_zero, zero_add, R_matrix];
  cases j₁; simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul, add_zero, zero_add, R_matrix];
  cases i₃; simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul, add_zero, zero_add, R_matrix];
  cases i₂; simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul, add_zero, zero_add, R_matrix];
  cases j₂; cases j₃; simp; ring_nf; field_simp; ring,
end

lemma R_relation_1:
  (tensor_product.assoc K _ _ _).symm.to_linear_map ∘ₗ
  (tensor_product.map 1 (R_hom q)) ∘ₗ
  (tensor_product.assoc K _ _ _).to_linear_map ∘ₗ
  (tensor_product.map (R_hom q) 1) ∘ₗ
  (tensor_product.assoc K _ _ _).symm.to_linear_map ∘ₗ
  (tensor_product.map 1 (R_hom q))
= 
  (tensor_product.map (R_hom q) 1) ∘ₗ
  (tensor_product.assoc K _ _ _).symm.to_linear_map ∘ₗ
  (tensor_product.map 1 (R_hom q)) ∘ₗ
  (tensor_product.assoc K _ _ _).to_linear_map ∘ₗ
  (tensor_product.map (R_hom q) 1) ∘ₗ
  (tensor_product.assoc K _ _ _).symm.to_linear_map
:= begin
  apply (equiv_like.apply_eq_iff_eq (linear_map.to_matrix
    ((pi.basis_fun K bool).tensor_product ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)))
    (((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).tensor_product (pi.basis_fun K bool))
  )).mp,
  simp only [
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))) _,
    linear_map.to_matrix_comp _ (((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).tensor_product (pi.basis_fun K bool)) _
  ],
  simp only [
    linear_map.to_matrix_associator_hom,
    linear_map.to_matrix_associator_inv,
    linear_map.to_matrix_tensor,
    linear_map.to_matrix_one,
    linear_map.to_matrix_to_lin, R_hom,
    ←matrix.mul_assoc
  ],
  rw R_relation_1_matrix,
end

/-
lemma my_assoc_reindex (A: matrix ((bool × bool) × bool) ((bool × bool) × bool) K):
  matrix.reindex
    (equiv.prod_assoc bool bool bool)
    (equiv.prod_assoc bool bool bool)
    A
  = my_assoc_matrix K ⬝ A ⬝ my_assoc_matrix_inv K :=
begin
  ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩,
  simp_rw matrix.mul_apply,
  dsimp,
  simp_rw [←finset.univ_product_univ],
  simp_rw [finset.sum_product],
  simp_rw [fintype.sum_bool],
  cases j₁; cases j₂; cases j₃,
  {
    cases i₁; cases i₂; cases i₃; simp [my_assoc_matrix, my_assoc_matrix_inv],
  },
  {
    cases i₁; cases i₂; cases i₃; simp [my_assoc_matrix, my_assoc_matrix_inv],
  },
  {
    cases i₁; cases i₂; cases i₃; simp [my_assoc_matrix, my_assoc_matrix_inv],
  },
  {
    cases i₁; cases i₂; cases i₃; simp [my_assoc_matrix, my_assoc_matrix_inv],
  },
  {
    cases i₁; cases i₂; cases i₃; simp [my_assoc_matrix, my_assoc_matrix_inv],
  },
  {
    cases i₁; cases i₂; cases i₃; simp [my_assoc_matrix, my_assoc_matrix_inv],
  },
  {
    cases i₁; cases i₂; cases i₃; simp [my_assoc_matrix, my_assoc_matrix_inv],
  },
  {
    cases i₁; cases i₂; cases i₃; simp [my_assoc_matrix, my_assoc_matrix_inv],
  },

end
-/

lemma jones_R_relation_1':
  ((1: matrix bool bool K) ⊗ₖ R_matrix q)
  ⬝ (matrix.reindex
  (equiv.prod_assoc bool bool bool)
  (equiv.prod_assoc bool bool bool)
  ((R_matrix q) ⊗ₖ (1 : matrix bool bool K)))
  ⬝ ((1: matrix bool bool K) ⊗ₖ R_matrix q)
= 
  (matrix.reindex
  (equiv.prod_assoc bool bool bool)
  (equiv.prod_assoc bool bool bool)
  ((R_matrix q) ⊗ₖ (1 : matrix bool bool K)))
  ⬝ ((1: matrix bool bool K) ⊗ₖ R_matrix q)
  ⬝ (matrix.reindex
  (equiv.prod_assoc bool bool bool)
  (equiv.prod_assoc bool bool bool)
  ((R_matrix q) ⊗ₖ (1 : matrix bool bool K))) :=
begin
  ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩,
  simp_rw matrix.mul_apply,
  dsimp,
  simp_rw [←finset.univ_product_univ],
  simp_rw [finset.sum_product],
  simp_rw [fintype.sum_bool],

  simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul,
    add_zero, zero_add, R_matrix],
  cases j₃;
  simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul,
    add_zero, zero_add, R_matrix];
  cases i₁;
  simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul,
    add_zero, zero_add, R_matrix];
  cases j₁;
  simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul,
    add_zero, zero_add, R_matrix];
  cases i₂;
  simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul,
    add_zero, zero_add, R_matrix];
  cases i₃;
  simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul,
    add_zero, zero_add, R_matrix];
  cases j₂;
  simp only [matrix.one_apply_eq, mul_one, one_mul, matrix.one_apply_ne, ne.def, not_false_iff, mul_zero, zero_mul,
    add_zero, zero_add, R_matrix];
  ring,
end


lemma R_relation_2:
  tensor_product.map (μ_hom q) (μ_hom q) ∘ₗ R_hom q
  = R_hom q ∘ₗ tensor_product.map (μ_hom q) (μ_hom q)
:= begin
  sorry,
end

lemma R_relaton_3_1:

:= begin
  sorry,
end

-- trace_2 (c.hom ≫ (𝟙 V ⊗ μ.hom)) = 𝟙 V

-- coevaluation の計算はできる？

noncomputable def enhanced_R_matrix:
  @enhanced_R_matrix (FinVect K) _ _ _ _ _ V₂
:= {
  c := {
    hom := R_hom q,
    inv := R_inv q,
    hom_inv_id' := R_hom_inv_id,
    inv_hom_id' := R_inv_hom_id
  },
  μ := {
    hom := μ_hom q,
    inv := μ_inv q,
    hom_inv_id' := μ_hom_inv_id,
    inv_hom_id' := μ_inv_hom_id
  },
  relation_1 := by apply R_relation_1,
  relation_2 := by apply R_relation_2,
  relation_3_1 := sorry,
  relation_3_2 := sorry,
  relation_4_1 := sorry,
  relation_4_2 := sorry
}

end jones
end kassel
