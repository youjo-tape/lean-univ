import linear_algebra.matrix.to_lin
import data.matrix.kronecker

variables
  (R: Type*) [field R]

open_locale tensor_product kronecker

lemma x
  {a₁ a₂ b₁ b₂: Type*}
  [fintype a₁] [fintype a₂] [decidable_eq a₂]
  [fintype b₁] [fintype b₂] [decidable_eq b₂]
  (A: matrix a₁ a₂ R) (B: matrix b₁ b₂ R)
  {A₁ A₂ B₁ B₂}
  [add_comm_monoid A₁] [module R A₁] {α₁: basis a₁ R A₁}
  [add_comm_monoid A₂] [module R A₂] {α₂: basis a₂ R A₂}
  [add_comm_monoid B₁] [module R B₁] {β₁: basis b₁ R B₁}
  [add_comm_monoid B₂] [module R B₂] {β₂: basis b₂ R B₂}
:
  matrix.to_lin (basis.tensor_product α₂ β₂) (basis.tensor_product α₁ β₁) (A ⊗ₖ B)
  = (matrix.to_lin α₂ α₁ A) ⊗[R] (matrix.to_lin β₂ β₁ B) :=
begin
  simp,
end