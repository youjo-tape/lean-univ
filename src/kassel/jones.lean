import kassel.enhanced_R_matrix
import kassel.lemma.to_matrix
import tactic.field_simp

namespace kassel

namespace jones

variables {K: Type*} [field K]

open_locale big_operators matrix kronecker

section lemmas

lemma matrix.ext' {m n} [fintype n] [decidable_eq n] (A B: matrix m n K)
  (h: ∀ (v: n → K), A.mul_vec v = B.mul_vec v): A = B :=
begin
  ext i j,
  have h' := h (pi.single j (1: K)),
  simp [matrix.mul_vec_single] at h',
  change (λ i, A i j) i = (λ i, B i j) i,
  rw h',
end

lemma matrix.smul_apply {m n} (A: matrix m n K) (s: K) (x y):
  (s • A) x y = s * (A x y) :=
by simp

lemma matrix.mul_vec_apply {m n} [fintype n] (A: matrix m n K) (v: n → K):
  A.mul_vec v = λ i, ∑ j, A i j * v j :=
by ext j; rw [matrix.mul_vec, matrix.dot_product]

lemma matrix.kronecker_apply' {l m n o} (A: matrix l m K) (B: matrix n o K) (x y):
  (A ⊗ₖ B) x y = A x.1 y.1 * B x.2 y.2 :=
by simp

@[simp] lemma fintype.sum_unit (f: unit → K): ∑ (x : unit), f x = f unit.star :=
by rw [fintype.univ_punit, finset.sum_singleton]

lemma equiv.prod_punit_symm_apply {n x}: (equiv.prod_punit n).symm x = (x, punit.star) := by simp

end lemmas

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

@[simp] def μ_matrix: matrix bool bool K
  | ff ff := q
  | tt tt := q⁻¹
  | _ _ := 0

@[simp] def μ_matrix_inv: matrix bool bool K
  | ff ff := q⁻¹
  | tt tt := q
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

noncomputable def μ_hom :=
  matrix.to_lin (pi.basis_fun K bool) (pi.basis_fun K bool) (μ_matrix q)

noncomputable def μ_inv :=
  matrix.to_lin (pi.basis_fun K bool) (pi.basis_fun K bool) (μ_matrix_inv q)

end

variables (q: Kˣ) (K)

lemma R_hom_inv_id: R_inv q ∘ₗ R_hom q = linear_map.id := begin
  rw [R_hom, R_inv, ←matrix.to_lin_mul],
  rw ←matrix.to_lin_one ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)),
  congr,
  ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
  rw matrix.mul_apply,
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  cases x₁; cases x₂; cases y₁; cases y₂; simp,
  field_simp, ring,
end

lemma R_inv_hom_id: R_hom q ∘ₗ R_inv q = linear_map.id := begin
  rw [R_hom, R_inv, ←matrix.to_lin_mul],
  rw ←matrix.to_lin_one ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)),
  congr,
  ext ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
  rw matrix.mul_apply,
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  cases x₁; cases x₂; cases y₁; cases y₂; simp,
  field_simp, ring,
end

lemma μ_hom_inv_id: μ_inv q ∘ₗ μ_hom q = linear_map.id :=
begin
  rw [μ_hom, μ_inv, ←matrix.to_lin_mul],
  rw ←matrix.to_lin_one (pi.basis_fun K bool),
  congr,
  ext x y,
  rw matrix.mul_apply,
  rw fintype.sum_bool,
  cases x; cases y; simp,
end

lemma μ_inv_hom_id: μ_hom q ∘ₗ μ_inv q = linear_map.id :=
begin
  rw [μ_hom, μ_inv, ←matrix.to_lin_mul],
  rw ←matrix.to_lin_one (pi.basis_fun K bool),
  congr,
  ext x y,
  rw matrix.mul_apply,
  rw fintype.sum_bool,
  cases x; cases y; simp,
end

lemma R_relation_1_matrix:
  associator.inv_matrix K ⬝
  1 ⊗ₖ R_matrix q ⬝
  associator.hom_matrix K ⬝
  R_matrix q ⊗ₖ 1 ⬝
  associator.inv_matrix K ⬝
  1 ⊗ₖ R_matrix q =
  R_matrix q ⊗ₖ 1 ⬝
  associator.inv_matrix K ⬝
  1 ⊗ₖ R_matrix q ⬝
  associator.hom_matrix K ⬝
  R_matrix q ⊗ₖ 1 ⬝
  associator.inv_matrix K :=
begin
  simp_rw [
    associator.inv_matrix_reindex,
    associator.hom_matrix_reindex_assoc,
    associator.inv_matrix_reindex_assoc
  ],
  apply matrix.ext',
  intro v,
  simp [←matrix.mul_vec_mul_vec],

  nth_rewrite 6 matrix.mul_vec_apply,
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],

  nth_rewrite 5 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_symm_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [associator.inv_matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 4 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [R_matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 3 matrix.mul_vec_apply,
  simp_rw [matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [R_matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 2 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],

  nth_rewrite 1 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_symm_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [R_matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 0 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [R_matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  ext ⟨⟨x, y⟩, z⟩,
  cases x; cases y; cases z;
  simp_rw [R_matrix, eq_self_iff_true, if_true, if_false];
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one];
  ring,
end

lemma R_relation_1:
  associator.inv K _ _ _ ∘ₗ
  (tensor_product.map linear_map.id (R_hom q)) ∘ₗ
  associator.hom K _ _ _ ∘ₗ
  (tensor_product.map (R_hom q) linear_map.id) ∘ₗ
  associator.inv K _ _ _ ∘ₗ
  (tensor_product.map linear_map.id (R_hom q))
= 
  (tensor_product.map (R_hom q) linear_map.id) ∘ₗ
  associator.inv K _ _ _ ∘ₗ
  (tensor_product.map linear_map.id (R_hom q)) ∘ₗ
  associator.hom K _ _ _ ∘ₗ
  (tensor_product.map (R_hom q) linear_map.id) ∘ₗ
  associator.inv K _ _ _
:= begin
  apply (equiv_like.apply_eq_iff_eq (linear_map.to_matrix
    ((pi.basis_fun K bool).tensor_product ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)))
    (((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).tensor_product (pi.basis_fun K bool))
  )).mp,
  simp only [
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))) _,
    linear_map.to_matrix_comp _ (((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).tensor_product (pi.basis_fun K bool)) _,
    tensor_product.to_matrix
  ],
  simp_rw [
    linear_map.to_matrix_id,
    R_hom, linear_map.to_matrix_to_lin,
    associator.hom_to_matrix,
    associator.inv_to_matrix,
    ←matrix.mul_assoc
  ],
  rw R_relation_1_matrix,
end

lemma R_relation_2_matrix:
  μ_matrix q ⊗ₖ μ_matrix q ⬝ R_matrix q = R_matrix q ⬝ μ_matrix q ⊗ₖ μ_matrix q :=
begin
  apply matrix.ext',
  intro v,
  simp [←matrix.mul_vec_mul_vec],

  nth_rewrite 3 matrix.mul_vec_apply,
  simp_rw matrix.kronecker_apply',
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],

  nth_rewrite 2 matrix.mul_vec_apply,
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw μ_matrix,
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 1 matrix.mul_vec_apply,
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],

  nth_rewrite 0 matrix.mul_vec_apply,
  simp_rw matrix.kronecker_apply',
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw R_matrix,
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  ext ⟨x, y⟩,
  cases x; cases y;
  simp_rw [R_matrix, μ_matrix];
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one];
  ring,
end

lemma R_relation_2:
  tensor_product.map (μ_hom q) (μ_hom q) ∘ₗ R_hom q
  = R_hom q ∘ₗ tensor_product.map (μ_hom q) (μ_hom q)
:= begin
  apply (equiv_like.apply_eq_iff_eq (linear_map.to_matrix
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
    ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool))
  )).mp,
  simp only [
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)) _,
    tensor_product.to_matrix
  ],
  simp_rw [R_hom, μ_hom, linear_map.to_matrix_to_lin],
  rw R_relation_2_matrix,
end

lemma R_relation_3_1_matrix:
  right_unitor.hom_matrix K bool ⬝
  (1: matrix bool bool K) ⊗ₖ evaluation.matrix K bool ⬝
  associator.hom_matrix K ⬝
  (1 ⊗ₖ μ_matrix q ⬝ R_matrix q) ⊗ₖ 1 ⬝
  associator.inv_matrix K ⬝
  1 ⊗ₖ coevaluation.matrix K bool ⬝
  right_unitor.inv_matrix K bool =
  1 :=
begin
  simp_rw [
    associator.hom_matrix_reindex_assoc,
    associator.inv_matrix_reindex_assoc,
    right_unitor.hom_matrix_reindex
  ],
  apply matrix.ext',
  intro v,
  simp [←matrix.mul_vec_mul_vec],

  nth_rewrite 3 matrix.mul_vec_apply,
  simp_rw fintype.sum_bool,

  nth_rewrite 2 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool, fintype.sum_unit],
  simp_rw [right_unitor.inv_matrix, coevaluation.matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 1 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_symm_apply, id],
  simp only [matrix.kronecker_apply', matrix.one_apply, matrix.mul_apply, matrix.smul_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [R_matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 0 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_punit_symm_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [evaluation.matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  ext x,
  cases x;
  simp_rw [eq_self_iff_true, if_true, if_false];
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one];
  ring_nf; field_simp; ring,
end

lemma R_relation_3_1:
  right_unitor.hom K _ ∘ₗ
  tensor_product.map linear_map.id (evaluation.rev K _) ∘ₗ
  associator.hom K _ _ _ ∘ₗ
  tensor_product.map (
    tensor_product.map linear_map.id (μ_hom q) ∘ₗ R_hom q
  ) linear_map.id ∘ₗ
  associator.inv K _ _ _ ∘ₗ
  (tensor_product.map linear_map.id (coevaluation.hom K (bool → K))) ∘ₗ
  right_unitor.inv K _ =
  linear_map.id :=
begin
  apply (equiv_like.apply_eq_iff_eq (linear_map.to_matrix
    (pi.basis_fun K bool)
    (pi.basis_fun K bool)
  )).mp,
  simp only [
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product (basis.singleton unit K)) _,
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool).dual_basis)) _,
    linear_map.to_matrix_comp _ (((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).tensor_product (pi.basis_fun K bool).dual_basis) _,
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)) _,
    tensor_product.to_matrix
  ],
  simp_rw [
    R_hom, μ_hom, linear_map.to_matrix_to_lin,
    linear_map.to_matrix_id,
    associator.hom_to_matrix,
    associator.inv_to_matrix,
    right_unitor.hom_to_matrix,
    right_unitor.inv_to_matrix,
    coevaluation.to_matrix,
    evaluation.rev_to_matrix,
    ←matrix.mul_assoc
  ],
  rw R_relation_3_1_matrix,
end

lemma R_relation_3_2_matrix:
  right_unitor.hom_matrix K bool ⬝
  (1: matrix bool bool K) ⊗ₖ evaluation.matrix K bool ⬝
  associator.hom_matrix K ⬝
  (1 ⊗ₖ μ_matrix q ⬝ R_matrix_inv q) ⊗ₖ 1 ⬝
  associator.inv_matrix K ⬝
  1 ⊗ₖ coevaluation.matrix K bool ⬝
  right_unitor.inv_matrix K bool =
  1 :=
begin
  simp_rw [
    associator.hom_matrix_reindex_assoc,
    associator.inv_matrix_reindex_assoc,
    right_unitor.hom_matrix_reindex
  ],
  apply matrix.ext',
  intro v,
  simp [←matrix.mul_vec_mul_vec],

  nth_rewrite 3 matrix.mul_vec_apply,
  simp_rw fintype.sum_bool,

  nth_rewrite 2 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool, fintype.sum_unit],
  simp_rw [right_unitor.inv_matrix, coevaluation.matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 1 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_symm_apply, id],
  simp only [matrix.kronecker_apply', matrix.one_apply, matrix.mul_apply, matrix.smul_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [R_matrix_inv, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  nth_rewrite 0 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_punit_symm_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [evaluation.matrix, eq_self_iff_true, if_true, if_false],
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one],

  ext x,
  cases x;
  simp_rw [eq_self_iff_true, if_true, if_false];
  simp only [add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one];
  ring_nf; field_simp; ring,
end

lemma R_relation_3_2:
  right_unitor.hom K _ ∘ₗ
  tensor_product.map linear_map.id (evaluation.rev K _) ∘ₗ
  associator.hom K _ _ _ ∘ₗ
  tensor_product.map (
    tensor_product.map linear_map.id (μ_hom q) ∘ₗ R_inv q
  ) linear_map.id ∘ₗ
  associator.inv K _ _ _ ∘ₗ
  (tensor_product.map linear_map.id (coevaluation.hom K (bool → K))) ∘ₗ
  right_unitor.inv K _ =
  linear_map.id :=
begin
  apply (equiv_like.apply_eq_iff_eq (linear_map.to_matrix
    (pi.basis_fun K bool)
    (pi.basis_fun K bool)
  )).mp,
  simp only [
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product (basis.singleton unit K)) _,
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool).dual_basis)) _,
    linear_map.to_matrix_comp _ (((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).tensor_product (pi.basis_fun K bool).dual_basis) _,
    linear_map.to_matrix_comp _ ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)) _,
    tensor_product.to_matrix
  ],
  simp_rw [
    R_inv, μ_hom, linear_map.to_matrix_to_lin,
    linear_map.to_matrix_id,
    associator.hom_to_matrix,
    associator.inv_to_matrix,
    right_unitor.hom_to_matrix,
    right_unitor.inv_to_matrix,
    coevaluation.to_matrix,
    evaluation.rev_to_matrix,
    ←matrix.mul_assoc
  ],
  rw R_relation_3_2_matrix,
end

-- lemma R_relation_4_1:
#check
  tensor_product.map linear_map.id (associator.inv K (bool → K) (bool → K) (module.dual K (bool → K))) ∘ₗ
  associator.hom K (module.dual K (bool → K)) _ _ ∘ₗ
#check
  tensor_product.map
    ((tensor_product.map linear_map.id (μ_inv q)) ∘ₗ coevaluation.rev K (bool → K))
    (tensor_product.map linear_map.id linear_map.id)
#check
  left_unitor.inv K _


/-
  (η_⁻ (V₂ K) ≫ (𝟙 (V₂ K)ᘁ ⊗ (μ' K q).inv) ⊗ 𝟙 (V₂ K) ⊗ 𝟙 (V₂ K)ᘁ) ≫ (α_ (V₂ K)ᘁ (V₂ K) (V₂ K ⊗ (V₂ K)ᘁ)).hom ≫ (𝟙 (V₂ K)ᘁ ⊗ (α_ (V₂ K) (V₂ K) (V₂ K)ᘁ).inv) ≫ (𝟙 (V₂ K)ᘁ ⊗ (c' K q).inv ⊗ 𝟙 (V₂ K)ᘁ) ≫ (𝟙 (V₂ K)ᘁ ⊗ (α_ (V₂ K) (V₂ K) (V₂ K)ᘁ).hom) ≫ (α_ (V₂ K)ᘁ (V₂ K) (V₂ K ⊗ (V₂ K)ᘁ)).inv ≫ ((𝟙 (V₂ K)ᘁ ⊗ 𝟙 (V₂ K)) ⊗ ((μ' K q).hom ⊗ 𝟙 (V₂ K)ᘁ) ≫ ε_⁻ (V₂ K)) ≫ ((𝟙 (V₂ K)ᘁ ⊗ 𝟙 (V₂ K)) ⊗ η_⁺ (V₂ K)) ≫ (α_ (V₂ K)ᘁ (V₂ K) (V₂ K ⊗ (V₂ K)ᘁ)).hom ≫ (𝟙 (V₂ K)ᘁ ⊗ (α_ (V₂ K) (V₂ K) (V₂ K)ᘁ).inv) ≫ (𝟙 (V₂ K)ᘁ ⊗ (c' K q).hom ⊗ 𝟙 (V₂ K)ᘁ) ≫ (𝟙 (V₂ K)ᘁ ⊗ (α_ (V₂ K) (V₂ K) (V₂ K)ᘁ).hom) ≫ (α_ (V₂ K)ᘁ (V₂ K) (V₂ K ⊗ (V₂ K)ᘁ)).inv ≫ (ε_⁺ (V₂ K) ⊗ 𝟙 (V₂ K) ⊗ 𝟙 (V₂ K)ᘁ) ≫ (λ_ (V₂ K ⊗ (V₂ K)ᘁ)).hom = 𝟙 (V₂ K) ⊗ 𝟙 (V₂ K)
-/

@[simp] def V₂: FinVect K := ⟨⟨bool → K⟩, begin
  change finite_dimensional K (bool → K),
  exact finite_dimensional.finite_dimensional_pi K,
end⟩

noncomputable def c': (V₂ K) ⊗ (V₂ K) ≅ (V₂ K) ⊗ (V₂ K) := {
  hom := R_hom q,
  inv := R_inv q,
  hom_inv_id' := by apply R_hom_inv_id K q,
  inv_hom_id' := by apply R_inv_hom_id K q
}

noncomputable def μ': (V₂ K) ≅ (V₂ K) := {
  hom := μ_hom q,
  inv := μ_inv q,
  hom_inv_id' := by apply μ_hom_inv_id K q,
  inv_hom_id' := by apply μ_inv_hom_id K q
}

noncomputable def jones_R_matrix: enhanced_R_matrix (FinVect K) (V₂ K) := {
  c := c' K q,
  μ := μ' K q,
  relation_1 := by apply R_relation_1 K q,
  relation_2 := by apply R_relation_2 K q,
  relation_3_1 := by rw trace_2; apply R_relation_3_1 K q,
  relation_3_2 := by rw trace_2; apply R_relation_3_2 K q,
  relation_4_1 := begin
    unfold_projs, dsimp,
    sorry,
  end,
  relation_4_2 := sorry,
  relation_4_3 := sorry,
  relation_4_4 := sorry
}

end jones

end kassel

/-

# done
- coevaluation が基底によらないことの証明

# todo
- R_relation_4_* の記述および証明
  - enhanced_R_matrix に Tangle の 7_*, 8_* に相当する 4 式をそのまま仮定する方針で
- right_pivotal_category.lean の sorry 埋め

-/