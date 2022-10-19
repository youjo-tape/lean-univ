import linear_algebra.matrix.to_lin
import data.matrix.kronecker

namespace kassel

variables
  {K: Type*} [field K]

section lemmas
variables
  {α: Type*} [fintype α] [decidable_eq α]
  {s : finset α}

lemma separate_sum {e: α} {f: α → K} (h: e ∈ s):
  s.sum f = (s \ {e}).sum f + f e :=
begin
  have h1: s = s \ {e} ∪ {e} :=
    by rwa [finset.sdiff_union_self_eq_union, finset.left_eq_union_iff_subset, finset.singleton_subset_iff],
  nth_rewrite_lhs 0 h1,
  have h2: disjoint (s \ {e}) {e} := by simp,
  rw finset.sum_union h2,
  simp,
end

end lemmas

section associator

variables (K)
  {l m n: Type*}
  [fintype l] [fintype m] [fintype n]
  [decidable_eq l] [decidable_eq m] [decidable_eq n]

@[simp] def associator_hom_matrix: matrix (l × (m × n)) ((l × m) × n) K
| (a₁, (b₁, c₁)) ((a₂, b₂), c₂) :=
  if (a₁ = a₂) ∧ (b₁ = b₂) ∧ (c₁ = c₂) then 1 else 0

lemma matrix.to_lin_associator_hom_matrix:
  matrix.to_lin
    (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n))
    ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n)))
    (associator_hom_matrix K) =
  (tensor_product.assoc K _ _ _).to_linear_map :=
begin
  apply (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n)).ext,
  rintro ⟨⟨x, y⟩, z⟩,
  rw [matrix.to_lin_self, finset.univ],
  have h_union: fintype.elems (l × m × n) = (fintype.elems (l × m × n) \ {(x, y, z)}) ∪ {(x, y, z)} := by simp [fintype.complete],
  have h_disjoint: disjoint (fintype.elems (l × m × n) \ {(x, y, z)}) {(x, y, z)} := by simp,
  rw [h_union, finset.sum_union h_disjoint],
  simp,
  apply finset.sum_eq_zero,
  rintro ⟨x1, y1, z1⟩ h,
  simp at *,
  left,
  exact h.2,
end

lemma linear_map.to_matrix_associator_hom:
  linear_map.to_matrix
    (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n))
    ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n)))
    (tensor_product.assoc K _ _ _).to_linear_map =
  associator_hom_matrix K :=
begin
  apply (equiv_like.apply_eq_iff_eq (
    matrix.to_lin
      (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n))
      ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n)))
  )).mp,
  simp [matrix.to_lin_associator_hom_matrix],
end

@[simp] def associator_inv_matrix: matrix ((l × m) × n) (l × (m × n)) K
| ((a₁, b₁), c₁) (a₂, (b₂, c₂)) :=
  if (a₁ = a₂) ∧ (b₁ = b₂) ∧ (c₁ = c₂) then 1 else 0

lemma matrix.to_lin_associator_inv_matrix:
  matrix.to_lin
    ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n)))
    (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n))
    (associator_inv_matrix K) =
  (tensor_product.assoc K _ _ _).symm.to_linear_map :=
begin
  apply ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n))).ext,
  rintro ⟨x, ⟨y, z⟩⟩,
  rw [matrix.to_lin_self, finset.univ],
  have h_union: fintype.elems ((l × m) × n) = (fintype.elems ((l × m) × n) \ {((x, y), z)}) ∪ {((x, y), z)} := by simp [fintype.complete],
  have h_disjoint: disjoint (fintype.elems ((l × m) × n) \ {((x, y), z)}) {((x, y), z)} := by simp,
  rw [h_union, finset.sum_union h_disjoint],
  simp,
  apply finset.sum_eq_zero,
  rintro ⟨⟨x1, y1⟩, z1⟩ h,
  simp at *,
  left,
  exact h.2,
end

lemma linear_map.to_matrix_associator_inv:
  linear_map.to_matrix
    ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n)))
    (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n))
    (tensor_product.assoc K _ _ _).symm.to_linear_map =
  associator_inv_matrix K :=
begin
  apply (equiv_like.apply_eq_iff_eq (
    matrix.to_lin
      ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n)))
      (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n))
  )).mp,
  simp [matrix.to_lin_associator_inv_matrix],
end

open_locale matrix

lemma associator_hom_matrix_reindex {o}
  (A: matrix ((l × m) × n) o K):
  associator_hom_matrix K ⬝ A = matrix.reindex (equiv.prod_assoc l m n) (equiv.refl o) A :=
begin
  ext ⟨x, ⟨y, z⟩⟩ w,
  simp_rw matrix.mul_apply,
  dsimp,
  rw separate_sum (finset.mem_univ ((x, y), z)),
  rw associator_hom_matrix,
  have: ite (x = x ∧ y = y ∧ z = z) 1 0 * A ((x, y), z) w = A ((x, y), z) w := by simp,
  rw [this, add_left_eq_self],
  apply finset.sum_eq_zero,
  rintro ⟨⟨x', y'⟩, z'⟩ h,
  simp at *,
  tauto,
end

lemma associator_inv_matrix_reindex {o}
  (A: matrix (l × (m × n)) o K):
  associator_inv_matrix K ⬝ A = matrix.reindex (equiv.prod_assoc l m n).symm (equiv.refl o) A :=
begin
  ext ⟨⟨x, y⟩, z⟩ w,
  simp_rw matrix.mul_apply,
  dsimp,
  rw separate_sum (finset.mem_univ (x, (y, z))),
  rw associator_inv_matrix,
  have: ite (x = x ∧ y = y ∧ z = z) 1 0 * A (x, (y, z)) w = A (x, (y, z)) w := by simp,
  rw [this, add_left_eq_self],
  apply finset.sum_eq_zero,
  rintro ⟨x', ⟨y', z'⟩⟩ h,
  simp at *,
  tauto,
end

lemma associator_hom_matrix_reindex_assoc {o p}
  (A: matrix ((l × m) × n) o K) (B: matrix p (l × (m × n)) K):
  (B ⬝ associator_hom_matrix K) ⬝ A = B ⬝ matrix.reindex (equiv.prod_assoc l m n) (equiv.refl o) A :=
begin
  rw [matrix.mul_assoc, associator_hom_matrix_reindex],
end

lemma associator_inv_matrix_reindex_assoc {o p}
  (A: matrix (l × (m × n)) o K) (B: matrix p ((l × m) × n) K):
  (B ⬝ associator_inv_matrix K) ⬝ A = B ⬝ matrix.reindex (equiv.prod_assoc l m n).symm (equiv.refl o) A :=
begin
  rw [matrix.mul_assoc, associator_inv_matrix_reindex],
end

lemma reindex_associator_hom_matrix {o}
  (A: matrix o (l × (m × n)) K):
  A ⬝ associator_hom_matrix K = matrix.reindex (equiv.refl o) (equiv.prod_assoc l m n).symm A :=
begin
  ext w ⟨⟨x, y⟩, z⟩,
  simp_rw matrix.mul_apply,
  dsimp,
  rw separate_sum (finset.mem_univ (x, (y, z))),
  rw associator_hom_matrix,
  have: A w (x, (y, z)) * ite (x = x ∧ y = y ∧ z = z) 1 0 = A w (x, (y, z)) := by simp,
  rw [this, add_left_eq_self],
  apply finset.sum_eq_zero,
  rintro ⟨x', ⟨y', z'⟩⟩ h,
  simp at *,
  tauto,
end

lemma reindex_associator_inv_matrix {o}
  (A: matrix o ((l × m) × n) K):
  A ⬝ associator_inv_matrix K = matrix.reindex (equiv.refl o) (equiv.prod_assoc l m n) A :=
begin
  ext w ⟨x, ⟨y, z⟩⟩,
  simp_rw matrix.mul_apply,
  dsimp,
  rw separate_sum (finset.mem_univ ((x, y), z)),
  rw associator_inv_matrix,
  have: A w ((x, y), z) * ite (x = x ∧ y = y ∧ z = z) 1 0 = A w ((x, y), z) := by simp,
  rw [this, add_left_eq_self],
  apply finset.sum_eq_zero,
  rintro ⟨⟨x', y'⟩, z'⟩ h,
  simp at *,
  tauto,
end

end associator

section tensor_product

lemma linear_map.to_matrix_tensor
  {m₁ m₂ n₁ n₂: Type*}
  [fintype m₁] [fintype m₂] [fintype n₁] [fintype n₂]
  [decidable_eq m₁] [decidable_eq m₂] [decidable_eq n₁] [decidable_eq n₂]
  {M₁ M₂ N₁ N₂: Type*}
  [add_comm_group M₁] [module K M₁] (a₁: basis m₁ K M₁)
  [add_comm_group M₂] [module K M₂] (a₂: basis m₂ K M₂)
  [add_comm_group N₁] [module K N₁] (b₁: basis n₁ K N₁)
  [add_comm_group N₂] [module K N₂] (b₂: basis n₂ K N₂)
  (f₁: M₁ →ₗ[K] N₁)
  (f₂: M₂ →ₗ[K] N₂):
  linear_map.to_matrix
    (basis.tensor_product a₁ a₂)
    (basis.tensor_product b₁ b₂)
    (tensor_product.map f₁ f₂) =
  matrix.kronecker
    (linear_map.to_matrix a₁ b₁ f₁)
    (linear_map.to_matrix a₂ b₂ f₂)
  :=
begin
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩,
  rw [matrix.kronecker, matrix.kronecker_apply],
  simp_rw linear_map.to_matrix_apply,
  rw basis.tensor_product_apply,
  rw tensor_product.map_tmul,
  rw basis.tensor_product,
  simp,
end

end tensor_product

end kassel
