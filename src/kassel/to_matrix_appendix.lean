import linear_algebra.matrix.to_lin
import data.matrix.kronecker
import algebra.category.FinVect

namespace kassel

variables
  {K: Type*} [field K]

open_locale matrix big_operators

section lemmas

variables
  {α: Type*} [fintype α] [decidable_eq α]
  {s t: finset α}

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

lemma sum_nonzero
  (h1: t ⊆ s) (f: α → K) (h2: ∀ x ∈ s \ t, f x = 0):
  s.sum f = t.sum f :=
begin
  simp [←(finset.sum_filter_add_sum_filter_not s (λ x, x ∈ t) f)],
  rw [finset.filter_not, finset.filter_mem_eq_inter],
  simp only [(finset.inter_eq_right_iff_subset t s).mpr h1],
  have := finset.sum_eq_zero h2,
  simp at *,
  assumption,
end

lemma linear_equiv.to_linear_map_to_fun_eq_to_fun {X Y}
  [add_comm_monoid X] [module K X]
  [add_comm_monoid Y] [module K Y]
  (e: X ≃ₗ[K] Y): (e.to_linear_map: X → Y) = (e: X → Y) :=
by simp

variables
  {M N: Type*}
  [add_comm_group M] [module K M]
  [add_comm_group N] [module K N]
  {m n: Type*}
  [fintype m] (bM: basis m K M)
  [fintype n] (bN: basis n K N)

lemma basis.tensor_product_repr_apply
  (x y x' y'):
  (bM.tensor_product bN).repr (x ⊗ₜ y) (x', y') = ((bM.repr) x) x' * ((bN.repr) y) y' :=
by simp [basis.tensor_product]

lemma pi.basis_fun_apply' {l} [fintype l] [decidable_eq l] (x y: l):
  (pi.basis_fun K l) x y = if (y = x) then 1 else 0 :=
by simp [linear_map.std_basis_apply, function.update_apply]

variables
  {B: Type*} [fintype B] [decidable_eq B]
  (V: Type*) [add_comm_group V] [module K V] [finite_dimensional K V]
  (bV: basis B K V)

lemma coevaluation_apply_one':
  (coevaluation K V) (1: K) = ∑ (i: B), bV i ⊗ₜ[K] bV.coord i := sorry

end lemmas

variable (K)

namespace tensor_product

open_locale kronecker

lemma to_matrix
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
  linear_map.to_matrix a₁ b₁ f₁ ⊗ₖ linear_map.to_matrix a₂ b₂ f₂ :=
begin
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩,
  rw matrix.kronecker_apply,
  simp_rw linear_map.to_matrix_apply,
  rw basis.tensor_product_apply,
  rw tensor_product.map_tmul,
  rw basis.tensor_product_repr_apply,
end

end tensor_product

namespace associator

variables
  {l m n: Type*}
  [fintype l] [fintype m] [fintype n]
  [decidable_eq l] [decidable_eq m] [decidable_eq n]

@[simp] def hom_matrix: matrix (l × (m × n)) ((l × m) × n) K
| (a₁, (b₁, c₁)) ((a₂, b₂), c₂) :=
  (ite (a₁ = a₂) 1 0) * (ite (b₁ = b₂) 1 0) * (ite (c₁ = c₂) 1 0)

@[simp] def inv_matrix: matrix ((l × m) × n) (l × (m × n)) K
| ((a₁, b₁), c₁) (a₂, (b₂, c₂)) :=
  (ite (a₁ = a₂) 1 0) * (ite (b₁ = b₂) 1 0) * (ite (c₁ = c₂) 1 0)

lemma hom_matrix_apply (x: l × (m × n)) (y: (l × m) × n):
  hom_matrix K x y = (ite (x.1 = y.1.1) 1 0) * (ite (x.2.1 = y.1.2) 1 0) * (ite (x.2.2 = y.2) 1 0) :=
by tidy

lemma inv_matrix_apply (x: (l × m) × n) (y: l × (m × n)):
  inv_matrix K x y = (ite (x.1.1 = y.1) 1 0) * (ite (x.1.2 = y.2.1) 1 0) * (ite (x.2 = y.2.2) 1 0) :=
by tidy

lemma hom_to_matrix:
  linear_map.to_matrix
    (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n))
    ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n)))
    (tensor_product.assoc K _ _ _).to_linear_map =
  hom_matrix K :=
begin
  ext ⟨i₁, ⟨j₁, k₁⟩⟩ ⟨⟨i₂, j₂⟩, k₂⟩,
  rw linear_map.to_matrix_apply,
  simp_rw basis.tensor_product_apply,
  rw [linear_equiv.to_linear_map_to_fun_eq_to_fun, tensor_product.assoc_tmul, hom_matrix],
  simp_rw basis.tensor_product_repr_apply,
  simp_rw [pi.basis_fun_repr, pi.basis_fun_apply', mul_assoc],
end

lemma inv_to_matrix:
  linear_map.to_matrix
    ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n)))
    (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n))
    (tensor_product.assoc K _ _ _).symm.to_linear_map =
  inv_matrix K :=
begin
  ext ⟨⟨i₁, j₁⟩, k₁⟩ ⟨i₂, ⟨j₂, k₂⟩⟩,
  rw linear_map.to_matrix_apply,
  simp_rw basis.tensor_product_apply,
  rw [linear_equiv.to_linear_map_to_fun_eq_to_fun, tensor_product.assoc_symm_tmul, inv_matrix],
  simp_rw basis.tensor_product_repr_apply,
  simp_rw [pi.basis_fun_repr, pi.basis_fun_apply'],
end

lemma hom_matrix_reindex {o}
  (A: matrix ((l × m) × n) o K):
  hom_matrix K ⬝ A = matrix.reindex (equiv.prod_assoc l m n) (equiv.refl o) A :=
begin
  ext ⟨x, ⟨y, z⟩⟩ w,
  rw matrix.mul_apply,
  rw sum_nonzero (finset.subset_univ {((x, y), z)}) (λ (j : (l × m) × n), _),
  rw finset.sum_singleton, simp,
  rintro ⟨⟨x', y'⟩, z'⟩, simp, tauto,
end

lemma inv_matrix_reindex {o}
  (A: matrix (l × (m × n)) o K):
  inv_matrix K ⬝ A = matrix.reindex (equiv.prod_assoc l m n).symm (equiv.refl o) A :=
begin
  ext ⟨⟨x, y⟩, z⟩ w,
  rw matrix.mul_apply,
  rw sum_nonzero (finset.subset_univ {(x, (y, z))}) (λ (j : l × (m × n)), _),
  rw finset.sum_singleton, simp,
  rintro ⟨x', ⟨y', z'⟩⟩, simp, tauto,
end

lemma hom_matrix_reindex_assoc {o p}
  (A: matrix ((l × m) × n) o K) (B: matrix p (l × (m × n)) K):
  (B ⬝ hom_matrix K) ⬝ A = B ⬝ matrix.reindex (equiv.prod_assoc l m n) (equiv.refl o) A :=
begin
  rw [matrix.mul_assoc, hom_matrix_reindex],
end

lemma inv_matrix_reindex_assoc {o p}
  (A: matrix (l × (m × n)) o K) (B: matrix p ((l × m) × n) K):
  (B ⬝ inv_matrix K) ⬝ A = B ⬝ matrix.reindex (equiv.prod_assoc l m n).symm (equiv.refl o) A :=
begin
  rw [matrix.mul_assoc, inv_matrix_reindex],
end

end associator

namespace right_unitor

variables
  {n: Type*} [fintype n] [decidable_eq n]

@[simp] def hom_matrix: matrix n (n × unit) K
  | x (y, star) := ite (x = y) 1 0

@[simp] def inv_matrix: matrix (n × unit) n K
  | (x, star) y := ite (x = y) 1 0

lemma hom_matrix_apply (x: n) (y: n × unit):
  hom_matrix K x y = ite (x = y.1) 1 0 := by tidy

lemma inv_matrix_apply (x: n × unit) (y: n):
  inv_matrix K x y = ite (x.1 = y) 1 0 := by tidy

lemma hom_to_matrix:
  linear_map.to_matrix
    ((pi.basis_fun K bool).tensor_product (basis.singleton unit K))
    (pi.basis_fun K bool)
    (tensor_product.rid K (bool → K)).to_linear_map =
  hom_matrix K :=
begin
  ext i ⟨j, star⟩,
  rw linear_map.to_matrix_apply,
  rw basis.tensor_product_apply,
  rw [linear_equiv.to_linear_map_to_fun_eq_to_fun, tensor_product.rid_tmul, hom_matrix],
  rw [pi.basis_fun_repr, basis.singleton_apply, one_smul, pi.basis_fun_apply'],
end

lemma inv_to_matrix:
  linear_map.to_matrix
    (pi.basis_fun K n)
    ((pi.basis_fun K n).tensor_product (basis.singleton unit K))
    (tensor_product.rid K (n → K)).symm.to_linear_map =
  inv_matrix K :=
begin
  ext ⟨i, star⟩ j,
  rw linear_map.to_matrix_apply,
  rw [linear_equiv.to_linear_map_to_fun_eq_to_fun, tensor_product.rid_symm_apply, inv_matrix],
  rw [basis.tensor_product_repr_apply],
  rw [pi.basis_fun_repr, pi.basis_fun_apply', basis.singleton_repr, mul_one],
end

lemma hom_matrix_reindex {o}
  (A: matrix (n × unit) o K):
  hom_matrix K ⬝ A = matrix.reindex (equiv.prod_punit n) (equiv.refl o) A :=
begin
  ext x y,
  rw matrix.mul_apply,
  rw sum_nonzero (finset.subset_univ {(x, unit.star)}) (λ (j : n × unit), _),
  rw finset.sum_singleton, simp,
  rintro ⟨x', star⟩, simp, tauto,
end

lemma inv_matrix_reindex {o}
  (A: matrix n o K):
  inv_matrix K ⬝ A = matrix.reindex (equiv.prod_punit n).symm (equiv.refl o) A :=
begin
  ext ⟨x, star⟩ y,
  rw matrix.mul_apply,
  rw sum_nonzero (finset.subset_univ {x}) (λ (j : n), _),
  rw finset.sum_singleton, simp,
  rintro x', simp, tauto,
end

end right_unitor

namespace left_unitor

variables
  {n: Type*} [fintype n] [decidable_eq n]

@[simp] def hom_matrix: matrix n (unit × n) K
  | x (star, y) := ite (x = y) 1 0

@[simp] def inv_matrix: matrix (unit × n) n K
  | (star, x) y := ite (x = y) 1 0

lemma hom_matrix_apply (x: n) (y: unit × n):
  hom_matrix K x y = ite (x = y.2) 1 0 := by tidy

lemma inv_matrix_apply (x: unit × n) (y: n):
  inv_matrix K x y = ite (x.2 = y) 1 0 := by tidy

lemma hom_to_matrix:
  linear_map.to_matrix
    ((basis.singleton unit K).tensor_product (pi.basis_fun K bool))
    (pi.basis_fun K bool)
    (tensor_product.lid K (bool → K)).to_linear_map =
  hom_matrix K :=
begin
  ext i ⟨star, j⟩,
  rw linear_map.to_matrix_apply,
  rw basis.tensor_product_apply,
  rw [linear_equiv.to_linear_map_to_fun_eq_to_fun, tensor_product.lid_tmul, hom_matrix],
  rw [pi.basis_fun_repr, basis.singleton_apply, one_smul, pi.basis_fun_apply'],
end

lemma inv_to_matrix:
  linear_map.to_matrix
    (pi.basis_fun K n)
    ((basis.singleton unit K).tensor_product (pi.basis_fun K n))
    (tensor_product.lid K (n → K)).symm.to_linear_map =
  inv_matrix K :=
begin
  ext ⟨i, star⟩ j,
  rw linear_map.to_matrix_apply,
  rw [linear_equiv.to_linear_map_to_fun_eq_to_fun, tensor_product.lid_symm_apply, inv_matrix],
  rw [basis.tensor_product_repr_apply],
  rw [pi.basis_fun_repr, pi.basis_fun_apply', basis.singleton_repr, one_mul],
end

lemma hom_matrix_reindex {o}
  (A: matrix (unit × n) o K):
  hom_matrix K ⬝ A = matrix.reindex (equiv.punit_prod n) (equiv.refl o) A :=
begin
  ext x y,
  rw matrix.mul_apply,
  rw sum_nonzero (finset.subset_univ {(unit.star, x)}) (λ (j : unit × n), _),
  rw finset.sum_singleton, simp,
  rintro ⟨star, x'⟩, simp, tauto,
end

lemma inv_matrix_reindex {o}
  (A: matrix n o K):
  inv_matrix K ⬝ A = matrix.reindex (equiv.punit_prod n).symm (equiv.refl o) A :=
begin
  ext ⟨star, x⟩ y,
  rw matrix.mul_apply,
  rw sum_nonzero (finset.subset_univ {x}) (λ (j : n), _),
  rw finset.sum_singleton, simp,
  rintro x', simp, tauto,
end

end left_unitor

namespace coevaluation

@[simp] def matrix: matrix (bool × bool) unit K
  | (x, y) star := if (x = y) then 1 else 0

lemma to_matrix:
  linear_map.to_matrix
    (basis.singleton unit K)
    ((pi.basis_fun K bool).tensor_product ((pi.basis_fun K bool).dual_basis))
    (coevaluation K (bool → K)) =
  matrix K :=
begin
  ext ⟨x, y⟩ star,
  rw linear_map.to_matrix_apply,
  rw basis.singleton_apply,
  rw [coevaluation_apply_one' (bool → K) (pi.basis_fun K bool), matrix],
  rw [fintype.sum_bool, map_add, finsupp.coe_add, pi.add_apply],
  simp_rw [basis.tensor_product_repr_apply, pi.basis_fun_repr],
  simp_rw [basis.dual_basis_repr, pi.basis_fun_apply', basis.coord_apply, pi.basis_fun_repr, pi.basis_fun_apply'],
  cases x; cases y; simp,
end

end coevaluation

namespace evaluation

@[simp] def matrix: matrix unit (bool × bool) K
  | star (x, y) := if (x = y) then 1 else 0

-- FinVect.evaluation -> contract_left

lemma to_matrix:
  linear_map.to_matrix
    (((pi.basis_fun K bool).dual_basis).tensor_product (pi.basis_fun K bool))
    (basis.singleton unit K)
    (contract_left K (bool → K)) =
  matrix K :=
begin
  ext star ⟨x, y⟩,
  rw linear_map.to_matrix_apply,
  rw basis.tensor_product_apply,
  rw [contract_left_apply, matrix],
  rw [basis.singleton_repr, basis.dual_basis_apply, pi.basis_fun_repr, pi.basis_fun_apply'],
end

end evaluation

end kassel
