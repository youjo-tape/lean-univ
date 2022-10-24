import kassel.enhanced_R_matrix
import tactic.field_simp
import kassel.to_matrix_appendix

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

lemma fintype.sum_unit (f: unit → K): ∑ (x : unit), f x = f unit.star :=
by rw [fintype.univ_punit, finset.sum_singleton]

lemma equiv.prod_punit_symm_apply {n x}: (equiv.prod_punit n).symm x = (x, punit.star) := by simp

end lemmas

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
  simp_rw [associator.inv_matrix_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],

  nth_rewrite 5 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_symm_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool],
  simp_rw [eq_self_iff_true, if_true, if_false],
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
  (tensor_product.assoc K _ _ _).symm.to_linear_map ∘ₗ
  (tensor_product.map linear_map.id (R_hom q)) ∘ₗ
  (tensor_product.assoc K _ _ _).to_linear_map ∘ₗ
  (tensor_product.map (R_hom q) linear_map.id) ∘ₗ
  (tensor_product.assoc K _ _ _).symm.to_linear_map ∘ₗ
  (tensor_product.map linear_map.id (R_hom q))
= 
  (tensor_product.map (R_hom q) linear_map.id) ∘ₗ
  (tensor_product.assoc K _ _ _).symm.to_linear_map ∘ₗ
  (tensor_product.map linear_map.id (R_hom q)) ∘ₗ
  (tensor_product.assoc K _ _ _).to_linear_map ∘ₗ
  (tensor_product.map (R_hom q) linear_map.id) ∘ₗ
  (tensor_product.assoc K _ _ _).symm.to_linear_map
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
  simp only [
    associator.hom_to_matrix,
    associator.inv_to_matrix,
    linear_map.to_matrix_one, ←linear_map.one_eq_id,
    linear_map.to_matrix_to_lin, R_hom,
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
  simp only [
    linear_map.to_matrix_to_lin, R_hom, μ_hom,
    ←matrix.mul_assoc
  ],
  rw R_relation_2_matrix,
end

lemma R_relaton_3_1_matrix:
  right_unitor.hom_matrix K ⬝
  (1: matrix bool bool K) ⊗ₖ evaluation.matrix K ⬝
  associator.hom_matrix K ⬝
  (1 ⊗ₖ μ_matrix q ⬝ R_matrix q) ⊗ₖ 1 ⬝
  associator.inv_matrix K ⬝
  1 ⊗ₖ coevaluation.matrix K ⬝
  right_unitor.inv_matrix K =
  (1: matrix bool bool K) :=
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
  simp_rw [right_unitor.inv_matrix_apply],
  simp_rw [fintype.sum_bool],

  nth_rewrite 2 matrix.mul_vec_apply,
  simp_rw [matrix.submatrix_apply, equiv.prod_assoc_apply, id, matrix.kronecker_apply', matrix.one_apply],
  simp_rw [←finset.univ_product_univ, finset.sum_product, fintype.sum_bool, fintype.sum_unit],
  simp_rw [coevaluation.matrix, eq_self_iff_true, if_true, if_false],
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

section aux

noncomputable def c': (@V₂ K _) ⊗ V₂ ≅ V₂ ⊗ V₂ := {
  hom := R_hom q,
  inv := R_inv q,
  hom_inv_id' := R_hom_inv_id K q,
  inv_hom_id' := R_inv_hom_id K q
}

noncomputable def μ': (@V₂ K _) ≅ V₂ := {
  hom := μ_hom q,
  inv := μ_inv q,
  hom_inv_id' := μ_hom_inv_id K q,
  inv_hom_id' := μ_inv_hom_id K q
}

end aux

noncomputable def enhanced_R_matrix:
  @enhanced_R_matrix (FinVect K) _ _ _ _ _ V₂ := {
  c := c' K q,
  μ := μ' K q,
  relation_1 := by apply R_relation_1 K q,
  relation_2 := by apply R_relation_2 K q,
  relation_3_1 := begin
    rw trace_2,
    unfold_projs, dsimp,
    simp only [
      coevaluation,
      evaluation,
      evaluation_rev
    ],
    simp only [
      Module.monoidal_category.associator,
      Module.monoidal_category.right_unitor,
      Module.monoidal_category.left_unitor,
      right_pivotal_category.right_pivotor
    ],
    sorry,
  end,
  relation_3_2 := sorry,
  relation_4_1 := sorry,
  relation_4_2 := sorry
}

end jones

end kassel

/-

# done
- R_relation_3_1_matrix を証明
  - 補題 matrix.ext' による、行列の等式証明の高速化
  - kassel p.311 における μₘ と λₘ を取り違えていて、μ_matrix などの定義が間違っていたのを修正
- to_matrix_appendix の内容を整理

# todo
- FinVect.right_pivotal_category の実装（relation_3_1 を書くのに必要）
- R_relation_3_1 の記述および証明
  - これができれば R_relation_3_2 も同様にできる

-/