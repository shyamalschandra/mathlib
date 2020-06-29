import data.polynomial

open polynomial
open finset
open_locale big_operators

-- TODO everything here should move up to cayley_hamilton.lean or down to polynomial.lean/...

variables {R S : Type*}

section ring

variables [ring R]

@[simp]
theorem coeff_mul_monomial (p : polynomial R) (n d : ℕ) (r : R) :
  coeff (p * monomial n r) (d + n) = coeff p d * r :=
by rw [single_eq_C_mul_X, ←X_pow_mul, ←mul_assoc, coeff_mul_C, coeff_mul_X_pow]

@[simp]
theorem coeff_mul_monomial_zero (p : polynomial R) (d : ℕ) (r : R) :
  coeff (p * monomial 0 r) d = coeff p d * r :=
coeff_mul_monomial p 0 d r

lemma coeff_mul_X_sub_monomial {p : polynomial R} {r : R} {a : ℕ} :
  coeff (p * (X - monomial 0 r)) (a + 1) = coeff p a - coeff p (a + 1) * r :=
by simp [mul_sub]

variables [ring S]

variables (f : R →+* S) (x : S)

lemma eval₂_mul_X_sub_monomial {p : polynomial R} {r : R} :
  (p * (X - monomial 0 r)).eval₂ f (f r) = 0 :=
begin
  simp [eval₂],
  have bound := calc
    (p * (X - monomial 0 r)).nat_degree
         ≤ p.nat_degree + (X - monomial 0 r).nat_degree : nat_degree_mul_le
     ... ≤ p.nat_degree + 1 : add_le_add_left nat_degree_X_sub_monomial_zero_le _
     ... < p.nat_degree + 2 : lt_add_one _,
  rw sum_over_range' _ _ (p.nat_degree + 2) bound,
  swap,
  { simp, },
  rw sum_range_succ',
  conv_lhs {
    congr, apply_congr, skip,
    rw [coeff_mul_X_sub_monomial, f.map_sub, f.map_mul, sub_mul, mul_assoc, ←pow_succ],
  },
  simp [sum_range_sub', coeff_single],
end

/--
The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
lemma eval_mul_X_sub_C {p : polynomial R} (r : R) :
  (p * (X - C r)).eval r = 0 :=
eval₂_mul_X_sub_monomial _

end ring
