import linear_algebra.matrix.to_lin
import data.matrix.kronecker

variables
  (K: Type*) [field K]
  {l m n: Type*}
  [fintype l] [fintype m] [fintype n]
  [decidable_eq l] [decidable_eq m] [decidable_eq n]

def associator_matrix: matrix (l × (m × n)) ((l × m) × n) K
 | (a₁, (b₁, c₁)) ((a₂, b₂), c₂) := 
   if (a₁ = a₂) ∧ (b₁ = b₂) ∧ (c₁ = c₂) then 1 else 0

/- def associator_matrix_to_lin:
  matrix.to_lin
    (((pi.basis_fun K l).tensor_product (pi.basis_fun K m)).tensor_product (pi.basis_fun K n))
    ((pi.basis_fun K l).tensor_product ((pi.basis_fun K m).tensor_product (pi.basis_fun K n)))
    (associator_matrix K) -/

def my_assoc_matrix: matrix (bool × (bool × bool)) ((bool × bool) × bool) K
  | (a1, (b1, c1)) ((a2, b2), c2) := 
  if (a1=a2) ∧ (b1=b2) ∧ (c1=c2) then 1 else 0

def my_assoc_matrix_inv: matrix ((bool × bool) × bool) (bool × (bool × bool)) K
  | ((a1, b1), c1) (a2, (b2, c2)) := 
  if (a1 = a2) ∧ (b1 = b2) ∧ (c1 = c2) then 1 else 0

noncomputable def my_assoc :=
 matrix.to_lin
    (((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).tensor_product (pi.basis_fun K bool))
    ((pi.basis_fun K bool).tensor_product ((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)))
    (my_assoc_matrix K)

lemma assoc_assoc: my_assoc K = (tensor_product.assoc K _ _ _).to_linear_map :=
begin
  apply (((pi.basis_fun K bool).tensor_product (pi.basis_fun K bool)).tensor_product (pi.basis_fun K bool)).ext,
  rintro ⟨⟨x, y⟩, z⟩,
  rw my_assoc,
  rw matrix.to_lin_self,
  rw finset.univ,
  have A: disjoint (fintype.elems (bool × bool × bool) \ {(x, (y, z))}) {(x, (y,z))} := 
  begin
    simp,
  end,
  have B: (fintype.elems (bool × bool × bool) \ {(x, (y, z))}) ∪ {(x, (y,z))} = fintype.elems (bool × bool × bool) := 
  begin
    simp,
    apply fintype.complete,
  end,
  rw B.symm,
  rw (finset.sum_union A),
  simp,
  rw my_assoc_matrix,
  simp,
  rw (finset.sum_congr rfl),
  apply finset.sum_const_zero,
  rintro ⟨x1, y1, z1⟩,
  rw my_assoc_matrix,
  simp,
  intros,
  apply or.intro_left,
  tauto,
end

open_locale tensor_product kronecker

lemma x
  {a₁ a₂ b₁ b₂: Type*}
  [fintype a₁] [fintype a₂] [decidable_eq a₂]
  [fintype b₁] [fintype b₂] [decidable_eq b₂]
  (A: matrix a₁ a₂ K) (B: matrix b₁ b₂ K)
  {A₁ A₂ B₁ B₂}
  [add_comm_monoid A₁] [module K A₁] {α₁: basis a₁ K A₁}
  [add_comm_monoid A₂] [module K A₂] {α₂: basis a₂ K A₂}
  [add_comm_monoid B₁] [module K B₁] {β₁: basis b₁ K B₁}
  [add_comm_monoid B₂] [module K B₂] {β₂: basis b₂ K B₂}
:
  matrix.to_lin (basis.tensor_product α₂ β₂) (basis.tensor_product α₁ β₁) (A ⊗ₖ B)
  = (matrix.to_lin α₂ α₁ A) ⊗[K] (matrix.to_lin β₂ β₁ B) :=
begin
  simp,
end