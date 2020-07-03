/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Paul van Wamelen.
-/
import algebra.field
import algebra.gcd_domain
import algebra.group_with_zero_power
import tactic


-- move this
lemma nat.prime.dvd_nat_abs_of_coe_dvd_pow_two {p : ℕ} (hp : p.prime) (k : ℤ) (h : ↑p ∣ k ^ 2) :
  p ∣ k.nat_abs :=
begin
  apply hp.dvd_of_dvd_pow,
  show p ∣ k.nat_abs ^ 2,
  rwa [nat.pow_two, ← int.nat_abs_mul, ← int.coe_nat_dvd_left, ← pow_two],
end

-- move this
lemma pow_two_sub_pow_two {R : Type*} [comm_ring R] (a b : R) :
  a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by ring

-- move this
lemma int.eq_or_eq_neg_of_pow_two_eq_pow_two (a b : ℤ) (h : a ^ 2 = b ^ 2) :
  a = b ∨ a = -b :=
by rwa [← add_eq_zero_iff_eq_neg, ← sub_eq_zero, or_comm, ← mul_eq_zero,
        ← pow_two_sub_pow_two, sub_eq_zero]

/-!
# Pythagorean Triples
The main result is the classification of pythagorean triples. The final result is for general
pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof.
-/

noncomputable theory
open_locale classical

/-- Three integers `x`, `y`, and `z` form a Pythagorean triple if `x * x + y * y = z * z`. -/
def pythagorean_triple (x y z : ℤ) : Prop := x * x + y * y = z * z

lemma pythagorean_triple_comm {x y z : ℤ} :
 (pythagorean_triple x y z) ↔ (pythagorean_triple y x z) :=
by { delta pythagorean_triple, rw add_comm }

lemma pythagorean_triple.zero : pythagorean_triple 0 0 0 :=
by simp only [pythagorean_triple, zero_mul, zero_add]

namespace pythagorean_triple

variables {x y z : ℤ} (h : pythagorean_triple x y z)

include h

lemma eq : x * x + y * y = z * z := h

@[symm]
lemma symm :
  pythagorean_triple y x z :=
by rwa [pythagorean_triple_comm]

lemma mul (k : ℤ) : pythagorean_triple (k * x) (k * y) (k * z) :=
begin
  by_cases hk : k = 0,
  { simp only [pythagorean_triple, hk, zero_mul, zero_add], },
  { calc (k * x) * (k * x) + (k * y) * (k * y)
        = k ^ 2 * (x * x + y * y) : by ring
    ... = k ^ 2 * (z * z)         : by rw h.eq
    ... = (k * z) * (k * z)       : by ring }
end

omit h

lemma mul_iff (k : ℤ) (hk : k ≠ 0) :
  pythagorean_triple (k * x) (k * y) (k * z) ↔ pythagorean_triple x y z :=
begin
  refine ⟨_, λ h, h.mul k⟩,
  simp only [pythagorean_triple],
  intro h,
  rw ← domain.mul_left_inj (mul_ne_zero hk hk),
  convert h using 1; ring,
end

include h

/-- A pythogorean triple `x, y, z` is “classified” if there exist integers `k, m, n` such that either
 * `x = k * (m ^ 2 - n ^ 2)` and `y = k * (2 * m * n)`, or
 * `(x = k * (2 * m * n)` and `y = k * (m ^ 2 - n ^ 2)`. -/
def is_classified := ∃ (k m n : ℤ),
  ((x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n)) ∨ (x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)))

lemma mul_is_classified (k : ℤ) (hc : h.is_classified) : (h.mul k).is_classified :=
begin
  obtain ⟨l, m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hc,
  { use [k * l, m, n], left, split; ring },
  { use [k * l, m, n], right, split; ring },
end

lemma even_odd_of_coprime (hc : int.gcd x y = 1) :
  (x % 2 = 0 ∧ y % 2 = 1) ∨ (x % 2 = 1 ∧ y % 2 = 0) :=
begin
  cases int.mod_two_eq_zero_or_one x with hx hx;
    cases int.mod_two_eq_zero_or_one y with hy hy,
  { -- x even, y even
    exfalso,
    apply nat.not_coprime_of_dvd_of_dvd (dec_trivial : 1 < 2) _ _ hc,
    { apply int.dvd_nat_abs_of_of_nat_dvd, apply int.dvd_of_mod_eq_zero hx },
    { apply int.dvd_nat_abs_of_of_nat_dvd, apply int.dvd_of_mod_eq_zero hy } },
  { left, exact ⟨hx, hy⟩ },  -- x even, y odd
  { right, exact ⟨hx, hy⟩ }, -- x odd, y even
  { -- x odd, y odd
    exfalso,
    obtain ⟨x0, y0, rfl, rfl⟩ : ∃ x0 y0, x = x0* 2 + 1 ∧ y = y0 * 2 + 1,
    { cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hx) with x0 hx2,
      cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hy) with y0 hy2,
      rw sub_eq_iff_eq_add at hx2 hy2, exact ⟨x0, y0, hx2, hy2⟩ },
    have hz : (z * z) % 4 = 2,
    { rw show z * z = 4 * (x0 * x0 + x0 + y0 * y0 + y0) + 2, by { rw ← h.eq, ring },
      simp only [int.add_mod, int.mul_mod_right, int.mod_mod, zero_add], refl },
    have : ∀ (k : ℤ), 0 ≤ k → k < 4 → k * k % 4 ≠ 2 := dec_trivial,
    have h4 : (4 : ℤ) ≠ 0 := dec_trivial,
    apply this (z % 4) (int.mod_nonneg z h4) (int.mod_lt z h4),
    rwa [← int.mul_mod] },
end

lemma gcd_dvd : (int.gcd x y : ℤ) ∣ z :=
begin
  by_cases h0 : int.gcd x y = 0,
  { have hx : x = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_left h0 },
    have hy : y = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_right h0 },
    have hz : z = 0,
    { simpa only [pythagorean_triple, hx, hy, add_zero, zero_eq_mul, mul_zero, or_self] using h },
    simp only [hz, dvd_zero], },
  obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ :
    ∃ (k : ℕ) x0 y0, 0 < k ∧ int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    int.exists_gcd_one' (nat.pos_of_ne_zero h0),
  rw [int.gcd_mul_right, h2, int.nat_abs_of_nat, one_mul],
  rw [← int.pow_dvd_pow_iff (dec_trivial : 0 < 2), pow_two z, ← h.eq],
  rw (by ring : x0 * k * (x0 * k) + y0 * k * (y0 * k) = k ^ 2 * (x0 * x0 + y0 * y0)),
  exact dvd_mul_right _ _
end

lemma normalize : pythagorean_triple (x / int.gcd x y) (y / int.gcd x y) (z / int.gcd x y) :=
begin
  by_cases h0 : int.gcd x y = 0,
  { have hx : x = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_left h0 },
    have hy : y = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_right h0 },
    have hz : z = 0,
    { simpa only [pythagorean_triple, hx, hy, add_zero, zero_eq_mul, mul_zero, or_self] using h },
    simp only [hx, hy, hz, int.zero_div], exact zero },
  rcases h.gcd_dvd with ⟨z0, rfl⟩,
  obtain ⟨k, x0, y0, k0, h2, rfl, rfl⟩ :
    ∃ (k : ℕ) x0 y0, 0 < k ∧ int.gcd x0 y0 = 1 ∧ x = x0 * k ∧ y = y0 * k :=
    int.exists_gcd_one' (nat.pos_of_ne_zero h0),
  have hk : (k : ℤ) ≠ 0, { norm_cast, rwa nat.pos_iff_ne_zero at k0 },
  rw [int.gcd_mul_right, h2, int.nat_abs_of_nat, one_mul] at h ⊢,
  rw [mul_comm x0, mul_comm y0, mul_iff k hk] at h,
  rwa [int.mul_div_cancel _ hk, int.mul_div_cancel _ hk, int.mul_div_cancel_left _ hk],
end

lemma is_classified_of_normalize_is_classified (hc : h.normalize.is_classified) :
  h.is_classified :=
begin
  convert h.normalize.mul_is_classified (int.gcd x y) hc; rw int.mul_div_cancel',
  { exact int.gcd_dvd_left x y },
  { exact int.gcd_dvd_right x y },
  { exact h.gcd_dvd }
end

-- move this
theorem pow_two_pos_of_ne_zero {R : Type*} [linear_ordered_ring R] (a : R) (h : a ≠ 0) : 0 < a ^ 2 :=
lt_of_le_of_ne (pow_two_nonneg a) (pow_ne_zero 2 h).symm

lemma ne_zero_of_coprime (hc : int.gcd x y = 1) : z ≠ 0 :=
begin
  suffices : 0 < z * z, { rintro rfl, simpa only [] },
  rw [← h.eq, ← pow_two, ← pow_two],
  have hc' : int.gcd x y ≠ 0, { rw hc, exact one_ne_zero },
  cases int.ne_zero_of_gcd hc' with hxz hyz,
  { apply lt_add_of_pos_of_le (pow_two_pos_of_ne_zero x hxz) (pow_two_nonneg y) },
  { apply lt_add_of_le_of_pos (pow_two_nonneg x) (pow_two_pos_of_ne_zero y hyz) }
end

lemma is_classified_of_coprime_of_zero_left (hc : int.gcd x y = 1) (hx : x = 0) :
  h.is_classified :=
begin
  subst x,
  change nat.gcd 0 (int.nat_abs y) = 1 at hc,
  rw [nat.gcd_zero_left (int.nat_abs y)] at hc,
  cases int.nat_abs_eq y with hy hy,
  { use [1, 1, 0], rw [hy, hc], norm_num },
  { use [1, 0, 1], rw [hy, hc], norm_num }
end

lemma coprime_of_coprime (hc : int.gcd x y = 1) : int.gcd y z = 1 :=
begin
  by_contradiction H,
  obtain ⟨p, hp, hpy, hpz⟩ := nat.prime.not_coprime_iff_dvd.mp H,
  apply hp.not_dvd_one,
  rw [← hc],
  apply nat.dvd_gcd (hp.dvd_nat_abs_of_coe_dvd_pow_two _ _) hpy,
  rw [pow_two, eq_sub_of_add_eq h],
  rw [← int.coe_nat_dvd_left] at hpy hpz,
  exact dvd_sub (dvd_mul_of_dvd_left (hpz) _) (dvd_mul_of_dvd_left (hpy) _),
end

end pythagorean_triple

section circle_equiv_gen
/-!
### A parametrization of the unit circle

For the classification of pythogorean triples, we will use a parametrization of the unit circle.
-/

variables {K : Type*} [field K]

/--  A parameterization of the unit circle that is useful for classifying Pythagorean triples.
 (To be applied in the case where `K = ℚ`.) -/
def circle_equiv_gen (hk : ∀ x : K, 1 + x^2 ≠ 0) :
  K ≃ {p : K × K // p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1} :=
{ to_fun := λ x, ⟨⟨2 * x / (1 + x^2), (1 - x^2) / (1 + x^2)⟩,
    by { field_simp [hk x, div_pow], ring },
    begin
      simp only [ne.def, div_eq_iff (hk x), ←neg_mul_eq_neg_mul, one_mul, neg_add,
        sub_eq_add_neg, add_left_inj],
      simpa only [eq_neg_iff_add_eq_zero, one_pow] using hk 1,
    end⟩,
  inv_fun := λ p, (p : K × K).1 / ((p : K × K).2 + 1),
  left_inv := λ x,
  begin
    have h2 : (1 + 1 : K) = 2 := rfl,
    have h3 : (2 : K) ≠ 0, { convert hk 1, rw [one_pow 2, h2] },
    field_simp [hk x, h2, h3, add_assoc, add_comm, add_sub_cancel'_right, mul_comm],
  end,
  right_inv := λ ⟨⟨x, y⟩, hxy, hy⟩,
  begin
    change x ^ 2 + y ^ 2 = 1 at hxy,
    have h2 : y + 1 ≠ 0, { apply mt eq_neg_of_add_eq_zero, exact hy },
    have h3 : (y + 1) ^ 2 + x ^ 2 = 2 * (y + 1),
    { rw [(add_neg_eq_iff_eq_add.mpr hxy.symm).symm], ring },
    have h4 : (2 : K) ≠ 0, { convert hk 1, rw one_pow 2, refl },
    simp only [prod.mk.inj_iff, subtype.mk_eq_mk],
    split,
    { field_simp [h2, h3, h4], ring },
    { field_simp [h2, h3, h4], rw [← add_neg_eq_iff_eq_add.mpr hxy.symm], ring }
  end }

@[simp] lemma circle_equiv_apply (hk : ∀ x : K, 1 + x^2 ≠ 0) (x : K) :
  (circle_equiv_gen hk x : K × K) = ⟨2 * x / (1 + x^2), (1 - x^2) / (1 + x^2)⟩ := rfl

@[simp] lemma circle_equiv_symm_apply (hk : ∀ x : K, 1 + x^2 ≠ 0)
  (v : {p : K × K // p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1}) :
  (circle_equiv_gen hk).symm v = (v : K × K).1 / ((v : K × K).2 + 1) := rfl

end circle_equiv_gen

private lemma coprime_pow_two_sub_pow_two_add_of_even_odd {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 0) (hn : n % 2 = 1) :
  int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 :=
begin
  by_contradiction H,
  obtain ⟨p, hp, hp1, hp2⟩ := nat.prime.not_coprime_iff_dvd.mp H,
  rw ← int.coe_nat_dvd_left at hp1 hp2,
  have h2m : (p : ℤ) ∣ 2 * m ^ 2, { convert dvd_add hp2 hp1, ring },
  have h2n : (p : ℤ) ∣ 2 * n ^ 2, { convert dvd_sub hp2 hp1, ring },
  have hmc : p = 2 ∨ p ∣ int.nat_abs m, { exact prime_two_or_dvd_of_dvd_two_mul_mul_self hp h2m },
  have hnc : p = 2 ∨ p ∣ int.nat_abs n, { exact prime_two_or_dvd_of_dvd_two_mul_mul_self hp h2n },
  by_cases h2 : p = 2,
  { have h3 : (m ^ 2 + n ^ 2) % 2 = 1, { norm_num [pow_two, int.add_mod, int.mul_mod, hm, hn], },
    have h4 : (m ^ 2 + n ^ 2) % 2 = 0, { apply int.mod_eq_zero_of_dvd, rwa h2 at hp2, },
    rw h4 at h3, exact zero_ne_one h3 },
  { apply hp.not_dvd_one,
    rw ← h,
    exact nat.dvd_gcd (or.resolve_left hmc h2) (or.resolve_left hnc h2), }
end

private lemma coprime_pow_two_sub_pow_two_add_of_odd_even {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 1) (hn : n % 2 = 0):
  int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 :=
begin
  rw [int.gcd, ← int.nat_abs_neg (m ^ 2 - n ^ 2)],
  rw [(by ring : -(m ^ 2 - n ^ 2) = n ^ 2 - m ^ 2), add_comm],
  apply coprime_pow_two_sub_pow_two_add_of_even_odd _ hn hm, rwa [int.gcd_comm],
end

private lemma coprime_pow_two_sub_pow_two_sum_of_odd_odd {m n : ℤ} (h : int.gcd m n = 1)
  (hm : m % 2 = 1) (hn : n % 2 = 1) :
  2 ∣ m ^ 2 + n ^ 2
  ∧ 2 ∣ m ^ 2 - n ^ 2
  ∧ ((m ^ 2 - n ^ 2) / 2) % 2 = 0
  ∧ int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1 :=
begin
  cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hm) with m0 hm2,
  cases exists_eq_mul_left_of_dvd (int.dvd_sub_of_mod_eq hn) with n0 hn2,
  rw sub_eq_iff_eq_add at hm2 hn2, subst m, subst n,
  have h1 : (m0 * 2 + 1) ^ 2 + (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 + n0 ^ 2 + m0 + n0) + 1),
  by ring_exp,
  have h2 : (m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2 = 2 * (2 * (m0 ^ 2 - n0 ^ 2 + m0 - n0)),
  by ring_exp,
  have h3 : ((m0 * 2 + 1) ^ 2 - (n0 * 2 + 1) ^ 2) / 2 % 2 = 0,
  { rw [h2, int.mul_div_cancel_left, int.mul_mod_right], exact dec_trivial },
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, h3, _⟩,
  have h20 : (2:ℤ) ≠ 0 := dec_trivial,
  rw [h1, h2, int.mul_div_cancel_left _ h20, int.mul_div_cancel_left _ h20],
  by_contra h4,
  obtain ⟨p, hp, hp1, hp2⟩ := nat.prime.not_coprime_iff_dvd.mp h4,
  apply hp.not_dvd_one,
  rw ← h,
  rw ← int.coe_nat_dvd_left at hp1 hp2,
  apply nat.dvd_gcd,
  { apply hp.dvd_nat_abs_of_coe_dvd_pow_two,
    convert dvd_add hp1 hp2, ring_exp },
  { apply hp.dvd_nat_abs_of_coe_dvd_pow_two,
    convert dvd_sub hp2 hp1, ring_exp },
end

namespace pythagorean_triple

variables {x y z : ℤ} (h : pythagorean_triple x y z)

include h

lemma is_classified_aux (hc : x.gcd y = 1) (hzpos : 0 < z)
  {m n : ℤ} (hm2n2 : 0 < m ^ 2 + n ^ 2)
  (hv2 : (x : ℚ) / z = 2 * m * n / (m ^ 2 + n ^ 2))
  (hw2 : (y : ℚ) / z = (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))
  (H : int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1) :
  h.is_classified :=
begin
  have hz : z ≠ 0, apply ne_of_gt hzpos,
  have h2 : y = m ^ 2 - n ^ 2 ∧ z = m ^ 2 + n ^ 2,
    { apply rat.div_int_inj hzpos hm2n2 (h.coprime_of_coprime hc) H, rw [hw2], norm_cast },
    use [1, m, n], right,
    rw [one_mul, one_mul],
    refine ⟨_, h2.left⟩,
    rw [← rat.coe_int_inj _ _, ← div_left_inj' ((mt (rat.coe_int_inj z 0).mp) hz), hv2, h2.right],
    norm_cast
end

theorem is_classified_of_coprime_of_odd_of_pos
  (hc : int.gcd x y = 1) (hyo : y % 2 = 1) (hzpos : 0 < z) :
  h.is_classified :=
begin
  by_cases h0 : x = 0, { exact h.is_classified_of_coprime_of_zero_left hc h0 },
  let v := (x : ℚ) / z,
  let w := (y : ℚ) / z,
  have hz : z ≠ 0, apply ne_of_gt hzpos,
  have hq : v ^ 2 + w ^ 2 = 1,
  { field_simp [hz, pow_two], norm_cast, exact h },
  have hvz : v ≠ 0, { field_simp [hz], exact h0 },
  have hw1 : w ≠ -1,
  { contrapose! hvz with hw1, rw [hw1, neg_square, one_pow, add_left_eq_self] at hq, exact pow_eq_zero hq, },
  have hQ : ∀ x : ℚ, 1 + x^2 ≠ 0,
  { intro q, apply ne_of_gt, exact lt_add_of_pos_of_le zero_lt_one (pow_two_nonneg q) },
  have hp : (⟨v, w⟩ : ℚ × ℚ) ∈ {p : ℚ × ℚ | p.1^2 + p.2^2 = 1 ∧ p.2 ≠ -1} := ⟨hq, hw1⟩,
  let q := (circle_equiv_gen hQ).symm ⟨⟨v, w⟩, hp⟩,
  have ht4 : v = 2 * q / (1 + q ^ 2) ∧ w = (1 - q ^ 2) / (1 + q ^ 2),
  { apply prod.mk.inj,
    have := ((circle_equiv_gen hQ).apply_symm_apply ⟨⟨v, w⟩, hp⟩).symm,
    exact congr_arg subtype.val this, },
  let m := (q.denom : ℤ),
  let n := q.num,
  have hm0 : m ≠ 0, { norm_cast, apply rat.denom_ne_zero q },
  have hq2 : q = n / m, { rw [int.cast_coe_nat], exact (rat.cast_id q).symm },
  have hm2n2 : 0 < m ^ 2 + n ^ 2,
  { apply lt_add_of_pos_of_le _ (pow_two_nonneg n),
    exact lt_of_le_of_ne (pow_two_nonneg m) (ne.symm (pow_ne_zero 2 hm0)) },
  have hw2 : w = (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2),
  { rw [ht4.2, hq2], field_simp [hm2n2, (rat.denom_ne_zero q)] },
  have hm2n20 : (m : ℚ) ^ 2 + (n : ℚ) ^ 2 ≠ 0,
  { norm_cast, simpa only [int.coe_nat_pow] using ne_of_gt hm2n2 },
  have hv2 : v = 2 * m * n / (m ^ 2 + n ^ 2),
  { apply eq.symm, apply (div_eq_iff hm2n20).mpr, rw [ht4.1], field_simp [hQ q],
    rw [hq2] {occs := occurrences.pos [2, 3]}, field_simp [rat.denom_ne_zero q], ring },
  have hnmcp : int.gcd n m = 1 := q.cop,
  have hmncp : int.gcd m n = 1, { rw int.gcd_comm, exact hnmcp },
  cases int.mod_two_eq_zero_or_one m with hm2 hm2;
    cases int.mod_two_eq_zero_or_one n with hn2 hn2,
  { -- m even, n even
    exfalso,
    have h1 : 2 ∣ (int.gcd n m : ℤ),
    { exact int.dvd_gcd (int.dvd_of_mod_eq_zero hn2) (int.dvd_of_mod_eq_zero hm2) },
    rw hnmcp at h1, revert h1, norm_num },
  { -- m even, n odd
    apply h.is_classified_aux hc hzpos hm2n2 hv2 hw2,
    apply coprime_pow_two_sub_pow_two_add_of_even_odd hmncp hm2 hn2, },
  { -- m odd, n even
    apply h.is_classified_aux hc hzpos hm2n2 hv2 hw2,
    apply coprime_pow_two_sub_pow_two_add_of_odd_even hmncp hm2 hn2, },
  { -- m odd, n odd
    exfalso,
    have h1 : 2 ∣ m ^ 2 + n ^ 2 ∧ 2 ∣ m ^ 2 - n ^ 2
      ∧ ((m ^ 2 - n ^ 2) / 2) % 2 = 0 ∧ int.gcd ((m ^ 2 - n ^ 2) / 2) ((m ^ 2 + n ^ 2) / 2) = 1,
    { exact coprime_pow_two_sub_pow_two_sum_of_odd_odd hmncp hm2 hn2 },
    have h2 : y = (m ^ 2 - n ^ 2) / 2 ∧ z = (m ^ 2 + n ^ 2) / 2,
    { apply rat.div_int_inj hzpos _ (h.coprime_of_coprime hc) h1.2.2.2,
      { show w = _, rw [←rat.mk_eq_div, ←(rat.div_mk_div_cancel_left (by norm_num : (2 : ℤ) ≠ 0))],
        rw [int.div_mul_cancel h1.1, int.div_mul_cancel h1.2.1, hw2], norm_cast },
      { apply (mul_lt_mul_right (by norm_num : 0 < (2 : ℤ))).mp,
        rw [int.div_mul_cancel h1.1, zero_mul], exact hm2n2 } },
    rw [h2.1, h1.2.2.1] at hyo,
    revert hyo,
    norm_num }
end

theorem is_classified_of_coprime_of_pos (hc : int.gcd x y = 1) (hzpos : 0 < z):
  h.is_classified :=
begin
  cases h.even_odd_of_coprime hc with h1 h2,
  { exact (h.is_classified_of_coprime_of_odd_of_pos hc h1.right hzpos) },
  rw int.gcd_comm at hc,
  obtain ⟨k, m, n, H⟩ := (h.symm.is_classified_of_coprime_of_odd_of_pos hc h2.left hzpos),
  use [k, m, n], tauto
end

theorem is_classified_of_coprime (hc : int.gcd x y = 1) : h.is_classified :=
begin
  by_cases hz : 0 < z,
  { exact h.is_classified_of_coprime_of_pos hc hz },
  have h' : pythagorean_triple x y (-z),
  { simpa [pythagorean_triple, neg_mul_neg] using h.eq, },
  apply h'.is_classified_of_coprime_of_pos hc,
  apply lt_of_le_of_ne _ (h'.ne_zero_of_coprime hc).symm,
  exact le_neg.mp (not_lt.mp hz)
end

theorem classified : h.is_classified :=
begin
  by_cases h0 : int.gcd x y = 0,
  { have hx : x = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_left h0 },
    have hy : y = 0, { apply int.nat_abs_eq_zero.mp, apply nat.eq_zero_of_gcd_eq_zero_right h0 },
    use [0, 0, 0], norm_num [hx, hy], },
  apply h.is_classified_of_normalize_is_classified,
  apply h.normalize.is_classified_of_coprime,
  apply int.gcd_div_gcd_div_gcd (nat.pos_of_ne_zero h0),
end

omit h

theorem classification :
  pythagorean_triple x y z ↔
  ∃ k m n, ((x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n)) ∨
            (x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)))
          ∧ (z = k * (m ^ 2 + n ^ 2) ∨ z = - k * (m ^ 2 + n ^ 2)) :=
begin
  split,
  { intro h,
    obtain ⟨k, m, n, H⟩ := h.classified,
    use [k, m, n],
    rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
    { refine ⟨or.inl ⟨rfl, rfl⟩, _⟩,
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2,
      { rw [pow_two, ← h.eq], ring },
      simpa using int.eq_or_eq_neg_of_pow_two_eq_pow_two _ _ this, },
    { refine ⟨or.inr ⟨rfl, rfl⟩, _⟩,
      have : z ^ 2 = (k * (m ^ 2 + n ^ 2)) ^ 2,
      { rw [pow_two, ← h.eq], ring },
      simpa using int.eq_or_eq_neg_of_pow_two_eq_pow_two _ _ this, }, },
  { rintro ⟨k, m, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, rfl | rfl⟩;
    delta pythagorean_triple; ring, }
end

end pythagorean_triple