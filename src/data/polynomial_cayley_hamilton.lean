import data.polynomial

open polynomial
open finset
open_locale big_operators

-- TODO everything here should move up to cayley_hamilton.lean or down to polynomial.lean/...


variables {R S : Type*}

section ring
variables [ring R]

variables [ring S]
variables (f : R →+* S) (x : S)

lemma coeff_mul_X_sub_monomial {p : polynomial R} {r : R} {a : ℕ} :
  coeff (p * (X - monomial 0 r)) (a + 1) = coeff p a - coeff p (a + 1) * r :=
begin
  simp [coeff_mul],
  transitivity ∑ (x : ℕ × ℕ) in {(a+1, 0), (a, 1)}, coeff p x.1 * (coeff X x.2 - (monomial 0 r).coeff x.2),
  apply finset.sum_bij_ne_zero (λ n _ _, n),
  { intros x h₁ h₂, simp, rw finset.nat.mem_antidiagonal at h₁,
    have h₃ := ne_zero_of_mul_ne_zero_left h₂,
    simp [single_eq_C_mul_X, coeff_C] at h₃,
    by_cases x.snd = 0, left, rw h at h₁, ext, simp [← h₁], rw ← h, rw if_neg h at h₃,
    by_cases 1 = x.snd, right, rw ← h at h₁, ext, apply nat.add_right_cancel h₁, rw h,
    exfalso, apply h₃, rw [coeff_X, if_neg h], simp, },
  { tauto, },
  { intros b mem ne, use b,
    simp only [exists_prop, and_true, eq_self_iff_true, ne.def, nat.mem_antidiagonal],
    split; simp only [mem_insert, mem_singleton] at mem,
    { rcases mem with rfl|rfl; simp, },
    { exact ne, }, },
  { intros, simp, },
  { intros, rw sub_eq_add_neg, conv_rhs {rw add_comm}, simp [single_eq_C_mul_X, coeff_C], },
end

/--
We can reexpress a sum over the `p.support` as a sum over `range n`,
for any `n` satisfying `p.nat_degree < n`.
-/
lemma sum_over_range' (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0)
  (n : ℕ) (w : p.nat_degree < n) :
  p.sum f = ∑ (a : ℕ) in range n, f a (coeff p a) :=
begin
  rw finsupp.sum,
  apply finset.sum_bij_ne_zero (λ n _ _, n),
  { intros k h₁ h₂, simp only [mem_range],
    calc k ≤ p.nat_degree : _
       ... < n : w,
    rw finsupp.mem_support_iff at h₁,
    exact le_nat_degree_of_ne_zero h₁, },
  { intros, assumption },
  { intros b hb hb',
    refine ⟨b, _, hb', rfl⟩,
    rw finsupp.mem_support_iff,
    contrapose! hb',
    convert h b, },
  { intros, refl }
end

/--
We can reexpress a sum over the `p.support` as a sum over `range (p.nat_degree + 1)`.
-/
lemma sum_over_range (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
  p.sum f = ∑ (a : ℕ) in range (p.nat_degree + 1), f a (coeff p a) :=
sum_over_range' p h (p.nat_degree + 1) (lt_add_one _)

@[simp] lemma coeff_monomial (n : ℕ) (r : R) : coeff (monomial n r) n = r :=
by simp [coeff_single]

@[simp] lemma mul_coeff_zero (p q : polynomial R) : coeff (p * q) 0 = coeff p 0 * coeff q 0 :=
by simp [coeff_mul]


/--
The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
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
  simp [sum_range_sub', is_ring_hom.map_zero f],
end

lemma eval₂_mul_X_sub_monomial' {p : polynomial R} (r : R) :
  (p * (X - monomial 0 r)).eval₂ (ring_hom.id _) r = 0 :=
eval₂_mul_X_sub_monomial _

lemma eval_mul_X_sub_C {p : polynomial R} (r : R) :
  (p * (X - C r)).eval r = 0 :=
eval₂_mul_X_sub_monomial _

end ring
