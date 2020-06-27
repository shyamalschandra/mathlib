/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.matrix_algebra
import ring_theory.polynomial_algebra
import data.polynomial_cayley_hamilton
import linear_algebra.nonsingular_inverse

/-!
The Cayley-Hamilton theorem, over a commutative ring.
-/

noncomputable theory

universes u v w

open polynomial matrix
open_locale big_operators

variables {R : Type u} [comm_ring R]
variables {n : Type w} [fintype n] [decidable_eq n] [inhabited n]

noncomputable def baz : matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R) :=
(((matrix_equiv_tensor R (polynomial R) n)).trans (algebra.tensor_product.comm R _ _)).trans (polynomial_equiv_tensor R (matrix n n R)).symm

-- maybe we don't need this?
-- lemma matrix_eq {X : Type*} [add_comm_monoid X] (m : matrix n n X) :
--   m = ∑ (x : n × n), (λ i j, if (i, j) = x then m i j else 0) := by { ext, simp }



open finset


@[elab_as_eliminator] protected lemma matrix.induction_on {X : Type*} [semiring X] {M : matrix n n X → Prop} (m : matrix n n X)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_elementary : ∀ i j x, M (λ i' j', if i' = i ∧ j' = j then x else 0)) :
  M m :=
begin
  rw matrix_eq_sum_elementary m,
  conv {congr, congr, skip, funext, },
  rw ← sum_product',
  apply sum_induction _ M h_add,
  { have := h_elementary (arbitrary n) (arbitrary n) 0,
    simp at this; exact this },
  intros, cases x with i j, dsimp,
  have := h_elementary i j (m i j),
  unfold elementary_matrix,
  convert this,
  ext, dsimp, simp [mul_ite],
end


-- instance is_ring_hom_of_alg_hom
--   {R : Type u} [comm_ring R] {A : Type v} [ring A] [algebra R A] {B : Type w} [ring B] [algebra R B]
--   (f : A →ₐ[R] B) :
-- is_ring_hom f :=
-- {map_one := by simp, map_mul := by simp, map_add := by simp}

lemma baz_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
  baz (λ i' j', if i' = i ∧ j' = j then monomial k x else 0) =
    monomial k (λ i' j', if i' = i ∧ j' = j then x else 0) :=
begin
  dsimp only [baz, alg_equiv.trans_apply],
  simp only [matrix_equiv_tensor_apply_elementary],
  apply (polynomial_equiv_tensor R (matrix n n R)).injective,
  simp only [alg_equiv.apply_symm_apply],
  convert algebra.tensor_product.comm_tmul _ _ _ _ _,
  simp only [polynomial_equiv_tensor_apply],
  convert eval₂_monomial _ _,
  { simp only [algebra.tensor_product.tmul_mul_tmul, one_pow, one_mul, matrix.mul_one, algebra.tensor_product.tmul_pow,
     algebra.tensor_product.include_left_apply, mul_eq_mul],
    rw monomial_eq_smul_X,
    rw ← tensor_product.smul_tmul,
    congr, ext, simp },
  { apply_instance },
end

lemma baz_coeff_apply_aux_2 (i j : n) (p : polynomial R) (k : ℕ) :
  coeff (baz (λ i' j', if i' = i ∧ j' = j then p else 0)) k =
    (λ i' j', if i' = i ∧ j' = j then coeff p k else 0) :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq,
    rw coeff_add,
    sorry, },
  { intros k x,
    rw baz_coeff_apply_aux_1,
    simp [coeff_single],
    split_ifs; { funext, simp, }, }
end

@[simp] lemma baz_coeff_apply (m : matrix n n (polynomial R)) (k : ℕ) (i j : n) :
  coeff (baz m) k i j = coeff (m i j) k :=
begin
  apply matrix.induction_on m,
  { intros p q hp hq, simp [hp, hq], },
  { intros i' j' x,
    rw baz_coeff_apply_aux_2,
    dsimp,
    split_ifs; simp },
end

/--
The "characteristic matrix" of `M : matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def characteristic_matrix (M : matrix n n R) : matrix n n (polynomial R) :=
matrix.scalar n (X : polynomial R) - (λ i j, C (M i j))

@[simp] lemma characteristic_matrix_apply_eq (M : matrix n n R) (i : n) :
  characteristic_matrix M i i = (X : polynomial R) - C (M i i) :=
by simp only [characteristic_matrix, sub_left_inj, pi.sub_apply, scalar_apply_eq]

@[simp] lemma characteristic_matrix_apply_ne (M : matrix n n R) (i j : n) (h : i ≠ j) :
  characteristic_matrix M i j = - C (M i j) :=
by simp only [characteristic_matrix, pi.sub_apply, scalar_apply_ne _ _ _ h, zero_sub]

lemma matrix_polynomial_equiv_polynomial_matrix_characteristic_matrix (M : matrix n n R) :
  matrix_polynomial_equiv_polynomial_matrix (characteristic_matrix M) = X - C M :=
begin
  ext k i j,
  simp only [matrix_polynomial_equiv_polynomial_matrix_coeff_apply, coeff_sub, pi.sub_apply],
  by_cases h : i = j,
  { subst h, rw [characteristic_matrix_apply_eq, coeff_sub],
    simp only [coeff_X, coeff_C],
    split_ifs; simp, },
  { rw [characteristic_matrix_apply_ne _ _ _ h, coeff_X, coeff_neg, coeff_C, coeff_C],
    split_ifs; simp [h], }
end

/--
The characteristic polynomial of a matrix `M` is given by $det (t I - M)$.
-/
def characteristic_polynomial (M : matrix n n R) : polynomial R :=
(characteristic_matrix M).det

/--
The Cayley-Hamilton theorem, that the characteristic polynomial of a matrix,
applied to the matrix itself, is zero.

This holds over any commutative ring.
-/
-- This proof follows http://drorbn.net/AcademicPensieve/2015-12/CayleyHamilton.pdf
theorem cayley_hamilton (M : matrix n n R) :
  (characteristic_polynomial M).eval₂ (algebra_map R (matrix n n R)) M = 0 :=
begin
  -- We begin with the fact $χ_M(t) I = adjugate (t I - M) * (t I - M)$,
  -- as an identity in `matrix n n (polynomial R)`.
  have := calc
    (characteristic_polynomial M) • (1 : matrix n n (polynomial R))
         = (characteristic_matrix M).det • (1 : matrix n n (polynomial R)) : rfl
     ... = adjugate (characteristic_matrix M) * (characteristic_matrix M)  : (adjugate_mul _).symm,
  -- Using the algebra isomorphism `matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R)`,
  -- we have the same identity in `polynomial (matrix n n R)`.
  apply_fun matrix_polynomial_equiv_polynomial_matrix at this,
  change _ = matrix_polynomial_equiv_polynomial_matrix (_ * _) at this,
  simp only [matrix_polynomial_equiv_polynomial_matrix.map_mul] at this,
  rw matrix_polynomial_equiv_polynomial_matrix_characteristic_matrix at this,
  -- Because the coefficient ring `matrix n n R` is non-commutative,
  -- evaluation at `M` is not multiplicative.
  -- However, any polynomial which is a product of the form $N * (t I - M)$
  -- is sent to zero, because the evaluation function puts the polynomial variable
  -- to the right of any coefficients.
  apply_fun (λ p, p.eval₂ (ring_hom.id _) M) at this,
  rw eval₂_mul_X_sub_C at this,
  -- Now $χ_M (t) I$, when thought of as a polynomial of matrices
  -- and evaluated at some `N` is exactly $χ_M (N)$.
  -- Thus we have $χ_M(M) = 0$, which is the desired result.
  rw matrix_polynomial_equiv_polynomial_matrix_smul_one at this,
  rw eval₂_eq_eval_map at this ⊢,
  simp at this,
  exact this,
end
