import algebra.category.FinVect

namespace kassel

noncomputable theory

open_locale matrix big_operators

variables
  {K: Type*} [field K]
  {V: Type*} [add_comm_group V] [module K V] [finite_dimensional K V]
  {ι: Type*} [fintype ι] (bV: basis ι K V)
  {ι': Type*} [fintype ι'] [decidable_eq ι'] (bV': basis ι' K V)
  
section lemmas

lemma basis_change (i: ι):
  bV i = ∑ (j: ι'), (bV'.to_matrix bV j i) • (bV' j) :=
by simp

lemma basis_change_dual (i: ι):
  bV.coord i = ∑ (j: ι'), (bV.to_matrix bV' i j) • (bV'.coord j) :=
begin
  ext,
  simp only [
    algebra.id.smul_eq_mul, linear_map.smul_apply, fintype.sum_apply, linear_map.coe_fn_sum, basis.coe_dual_basis, finset.sum_congr, finsupp.lapply_apply, linear_equiv.coe_coe, function.comp_app, linear_map.coe_comp,
    basis.to_matrix_apply, basis.dual_basis_apply, basis.coord, basis.sum_repr_mul_repr
  ],
end

lemma basis_change_relation (i j: ι'):
  ∑ (k: ι), bV'.to_matrix ⇑bV i k * bV.to_matrix ⇑bV' k j = (finsupp.single j 1) i :=
begin
  simp_rw basis.to_matrix_apply,
  rw [basis.sum_repr_mul_repr, basis.repr_self],
end

variables
  {α β γ: Type*} [fintype α] [fintype β] [fintype γ]
  {s t: finset α}
  {M: Type*} [add_comm_monoid M]

lemma sum_nonzero [decidable_eq α]
  (h1: t ⊆ s) (f: α → M) (h2: ∀ x ∈ s \ t, f x = 0):
  s.sum f = t.sum f :=
begin
  simp [←(finset.sum_filter_add_sum_filter_not s (λ x, x ∈ t) f)],
  rw [finset.filter_not, finset.filter_mem_eq_inter],
  simp only [(finset.inter_eq_right_iff_subset t s).mpr h1],
  simp [finset.sum_eq_zero h2],
end

lemma finset.sum_sum_comm (f: α → β → γ → M):
  ∑ (x: α) (y: β) (z: γ), f x y z = ∑ (y: β) (z: γ) (x: α), f x y z :=
begin
  rw finset.sum_comm,
  have h: ∀ y, ∑ (x: α) (z: γ), f x y z = ∑ (z: γ) (x: α), f x y z := (λ y, finset.sum_comm),
  simp_rw h,
end

end lemmas

lemma coevaluation_well_defined:
  ∑ (i: ι), bV i ⊗ₜ[K] bV.coord i = ∑ (i: ι'), bV' i ⊗ₜ[K] bV'.coord i :=
begin
  simp_rw [basis_change bV bV', basis_change_dual bV bV'],
  simp_rw [tensor_product.sum_tmul, tensor_product.tmul_sum, tensor_product.smul_tmul_smul],
  rw finset.sum_sum_comm,
  simp_rw ←finset.sum_smul,
  simp_rw basis_change_relation bV bV',
  have h := (λ x, sum_nonzero (finset.subset_univ {x}) (λ x_1, tensor_product.has_smul.smul (ite (x = x_1) 1 0) (bV' x ⊗ₜ[K] bV'.coord x_1)) _),
  simp [h],
  intro y, simp, tauto,
end

lemma coevaluation_apply_one':
  coevaluation K V 1 = ∑ (i: ι'), bV' i ⊗ₜ[K] bV'.coord i :=
begin
  rw coevaluation_apply_one,
  have h := coevaluation_well_defined (basis.of_vector_space K V) bV',
  rw ←h,
end

end kassel
