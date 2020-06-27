import data.polynomial

open polynomial
open finset
open_locale big_operators

-- TODO everything here should move up to cayley_hamilton.lean or down to polynomial.lean/...


variables {R S : Type*}

section ring
variables [ring R]

variables [ring S]
variables (f : R → S) (x : S)
variables [is_ring_hom f]

lemma foo {p : polynomial R} {r : R} {a : ℕ} :
  coeff (p * (X - monomial 0 r)) (a + 1) = coeff p a - coeff p (a + 1) * r :=
begin
  -- Yuck... This will get there, but it is very painful.
  -- Surely there's a better way?
  simp [coeff_mul],
  transitivity ∑ (x : ℕ × ℕ) in {(a+1, 0), (a, 1)}, coeff p x.1 * (coeff X x.2 - (monomial 0 r).coeff x.2),
  apply finset.sum_bij_ne_zero (λ n _ _, n),
  { intros x h₁ h₂, simp, rw finset.nat.mem_antidiagonal at h₁,
    have h₃ := ne_zero_of_mul_ne_zero_left h₂,
    simp [single_eq_C_mul_X, coeff_C] at h₃,
    --rw coeff_X at h,
    by_cases x.snd = 0, left, rw h at h₁, ext, simp [← h₁], rw ← h, rw if_neg h at h₃,
    by_cases 1 = x.snd, right, rw ← h at h₁, ext, apply nat.add_right_cancel h₁, rw h,
    exfalso, apply h₃, rw [coeff_X, if_neg h], simp },
  { tauto },
  { intros, existsi b,
    simp only [exists_prop, and_true, eq_self_iff_true, ne.def, nat.mem_antidiagonal],
    split; simp only [mem_insert, mem_singleton] at H, cases H; rw H; simp, apply a_1 },
  { intros, simp },
  { intros, rw sub_eq_add_neg, conv_rhs {rw add_comm}, simp [single_eq_C_mul_X, coeff_C] },
end

@[simp] lemma coeff_nat_degree_succ_eq_zero {p : polynomial R} : p.coeff (p.nat_degree + 1) = 0 :=
coeff_eq_zero_of_nat_degree_lt (lt_add_one _)

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

lemma sum_over_range (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
  p.sum f = ∑ (a : ℕ) in range (p.nat_degree + 1), f a (coeff p a) :=
sum_over_range' p h (p.nat_degree + 1) (lt_add_one _)

@[simp] lemma coeff_monomial (n : ℕ) (r : R) : coeff (monomial n r) n = r :=
by rw [monomial_eq_smul_X, coeff_smul, coeff_X_pow, if_pos rfl, mul_one]

@[simp] lemma mul_coeff_zero (p q : polynomial R) : coeff (p * q) 0 = coeff p 0 * coeff q 0 :=
by simp [coeff_mul]

lemma nat_degree_mul_le {p q : polynomial R} : nat_degree (p * q) ≤ nat_degree p + nat_degree q :=
begin
  apply nat_degree_le_of_degree_le, apply le_trans (degree_mul_le p q),
  rw with_bot.coe_add, refine add_le_add _ _; apply degree_le_nat_degree
end

variable [nonzero R] --otherwise this nat_degree is 0
lemma nat_degree_X_sub_monomial_zero {r : R} : (X - monomial 0 r).nat_degree = 1 :=
by { rw single_eq_C_mul_X, apply nat_degree_eq_of_degree_eq_some, simp }

/--
The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.
-/
lemma eval₂_mul_X_sub_monomial {p : polynomial R} {r : R} :
  (p * (X - monomial 0 r)).eval₂ f (f r) = 0 :=
begin
  simp [eval₂],
  have bound := calc
    (p * (X - monomial 0 r)).nat_degree
         ≤ p.nat_degree + (X - monomial 0 r).nat_degree : nat_degree_mul_le
     ... = p.nat_degree + 1 : by rw nat_degree_X_sub_monomial_zero
     ... < p.nat_degree + 2 : lt_add_one _,
  rw sum_over_range' _ _ (p.nat_degree + 2) bound,
  swap,
  { simp [is_ring_hom.map_zero f], },
  rw sum_range_succ',
  conv_lhs {
    congr, apply_congr, skip,
    rw [foo, is_ring_hom.map_sub f, is_ring_hom.map_mul f, sub_mul, mul_assoc, ←pow_succ],
  },
  conv_lhs {
    congr, skip,
    simp [is_ring_hom.map_neg f, is_ring_hom.map_mul f],
  },
  simp [sum_range_sub', is_ring_hom.map_zero f],
end

lemma eval₂_mul_X_sub_monomial' {p : polynomial R} (r : R) :
  (p * (X - monomial 0 r)).eval₂ (ring_hom.id _) r = 0 :=
eval₂_mul_X_sub_monomial id

lemma eval₂_mul_X_sub_C {p : polynomial R} (r : R) :
  (p * (X - C r)).eval₂ (ring_hom.id _) r = 0 :=
eval₂_mul_X_sub_monomial id

end ring
