import algebra.category.FinVect
import data.complex.basic
import data.matrix.basic
import ring_theory.matrix_algebra
open tensor_product
open_locale tensor_product

variables (K: Type) [field K]

structure rmatrix (C: Type) [category C] (x: C) := -- x 上の R 行列
  (hom: x ⊗ x → x ⊗ x)
  () -- ここに関係式

/- C -> FinVect, x -> (fin 2 -> K) -/

abbreviation mat (r c: nat) (K) := matrix (fin r) (fin c) K

def matrix_tensor {r₁ c₁ r₂ c₂} (M₁: mat r₁ c₁ K) (M₂: mat r₂ c₂ K)
  := tensor_product.map (matrix.to_lin' M₁) (matrix.to_lin' M₂)
#check matrix_tensor K

noncomputable def equiv_2_2_to_4 {m n}: ((fin m → K) ⊗[K] (fin n → K)) ≃ₗ[K] (fin (m * n) → K) := begin
  refine fin_dim_vectorspace_equiv _ _, tidy,
end

def mat1 := (1: matrix (fin 2) (fin 2) K)
def matrix_example := matrix_tensor K (mat1 K) (mat1 K)
#check (matrix_tensor ℚ (mat1 ℚ) (mat1 ℚ)) -- ((fin 2 → K) ⊗ (fin 2 → K))