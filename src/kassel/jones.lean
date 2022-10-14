import kassel.enhanced_R_matrix
import tactic.field_simp
import kassel.kronecker_appendix

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
  rw matrix.mul,
  ext ⟨i₁, i₂⟩ ⟨k₁, k₂⟩,
  rw [matrix.dot_product, finset.univ],
  erw [finset.sum_product, fintype.sum_bool],
  simp,
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
  rw matrix.mul,
  ext ⟨i₁, i₂⟩ ⟨k₁, k₂⟩,
  rw [matrix.dot_product, finset.univ],
  erw [finset.sum_product, fintype.sum_bool],
  simp,
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

lemma R_relation_1:
  (tensor_product.assoc K _ _ _).symm.to_linear_map
  ∘ₗ ((R_hom q).ltensor _)
  ∘ₗ (tensor_product.assoc K _ _ _).to_linear_map
  ∘ₗ ((R_hom q).rtensor _)
  ∘ₗ (tensor_product.assoc K _ _ _).symm.to_linear_map
  ∘ₗ ((R_hom q).ltensor _)
= 
  ((R_hom q).rtensor _)
  ∘ₗ (tensor_product.assoc K _ _ _).symm.to_linear_map
  ∘ₗ ((R_hom q).ltensor _)
  ∘ₗ (tensor_product.assoc K _ _ _).to_linear_map
  ∘ₗ ((R_hom q).rtensor _)
  ∘ₗ (tensor_product.assoc K _ _ _).symm.to_linear_map
:= begin
  ext,
  sorry,  
end

/-
open_locale kronecker

#check
  (jones_R_matrix q ⊗ₖ (1: matrix bool bool K))
#check
  ((1: matrix bool bool K) ⊗ₖ jones_R_matrix q)

-- lemma jones_R_relation_1':
-- kronecker
-/

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
