/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import combinatorics.composition
import data.nat.parity
import tactic.apply_fun

/-!
# Partitions

A partition of an integer `n` is a way of writing `n` as a sum of positive integers, where the order
does not matter: two sums that differ only in the order of their summands are considered the same
partition. This notion is closely related to that of a composition of `n`, but in a composition of
`n` the order does matter.

## Main functions

* `p : partition n` is a structure, made of a multiset of integers which are all positive and
  add up to `n`.

## Implementation details

The main motivation for this structure and its API is to show Euler's partition theorem, and
related results.

The representation of a partition as a multiset is very handy as multisets are very flexible and
already have a well-developed API.

## Tags

Partition

## References

<https://en.wikipedia.org/wiki/Partition_(number_theory)>
-/


variables {α : Type*}

open multiset nat
open_locale big_operators

/-- A partition of `n` is a multiset of positive integers summing to `n`. -/
@[ext, derive decidable_eq] structure partition (n : ℕ) :=
(parts : multiset ℕ)
(parts_pos : ∀ {i}, i ∈ parts → 0 < i)
(parts_sum : parts.sum = n)

namespace partition

/-- A composition induces a partition (just convert the list to a multiset). -/
def of_composition (n : ℕ) (c : composition n) : partition n :=
{ parts := c.blocks,
  parts_pos := λ i hi, c.blocks_pos hi,
  parts_sum := by rw [multiset.coe_sum, c.blocks_sum] }

lemma of_composition_surj {n : ℕ} : function.surjective (of_composition n) :=
begin
  rintro ⟨b, hb₁, hb₂⟩,
  rcases quotient.exists_rep b with ⟨b, rfl⟩,
  refine ⟨⟨b, λ i hi, hb₁ hi, _⟩, partition.ext _ _ rfl⟩,
  simpa using hb₂
end

lemma multiset.sum_eq_zero_iff (l : multiset ℕ) : l.sum = 0 ↔ ∀ x ∈ l, x = 0 :=
begin
  apply multiset.induction_on l,
  { simp },
  intros x l ih,
  simp only [mem_cons, sum_cons, add_eq_zero_iff, ih],
  split,
  { rintro ⟨rfl, t⟩ y (rfl | b),
    { refl },
    { apply t _ ‹y ∈ l› } },
  { intro t,
    exact ⟨t _ (or.inl rfl), λ _ h, t _ (or.inr h)⟩ },
end

def of_sums (n : ℕ) (l : multiset ℕ) (hl : l.sum = n) : partition n :=
{ parts := l.filter (≠ 0),
  parts_pos := λ i hi, nat.pos_of_ne_zero $ by apply of_mem_filter hi,
  parts_sum :=
  begin
    have lt : l.filter (= 0) + l.filter (≠ 0) = l := filter_add_not l,
    apply_fun multiset.sum at lt,
    have lz : (l.filter (= 0)).sum = 0,
    { rw multiset.sum_eq_zero_iff,
      simp },
    simpa [lz, hl] using lt,
  end }

@[simp] theorem count_filter_of_neg {p} [decidable_pred p] [decidable_eq α]
  {a} {s : multiset α} (h : ¬ p a) : count a (filter p s) = 0 :=
multiset.induction_on s (by simp)
begin
  intros b s' ih,
  by_cases h₁ : p b,
  { rw [filter_cons_of_pos _ h₁, count_cons_of_ne, ih],
    rintro t, apply h (t.symm ▸ h₁) },
  { rw [filter_cons_of_neg _ h₁, ih] }
end

lemma count_of_sums_of_ne_zero {n : ℕ} {l : multiset ℕ} (hl : l.sum = n) {i : ℕ} (hi : i ≠ 0) :
  (of_sums n l hl).parts.count i = l.count i :=
count_filter hi

lemma count_of_sums_zero {n : ℕ} {l : multiset ℕ} (hl : l.sum = n) :
  (of_sums n l hl).parts.count 0 = 0 :=
begin
  apply count_filter_of_neg,
  simp,
end

/--
Show there are finitely many partitions by considering the surjection from compositions to
partitions.
-/
instance (n : ℕ) : fintype (partition n) :=
fintype.of_surjective (of_composition n) of_composition_surj

def test : partition 10 := ⟨⟦[5,4,1]⟧, by tidy, by simp⟩

structure diagram :=
(vals : finset (ℕ × ℕ))
(lc : ∀ i j, (i+1,j) ∈ vals → (i,j) ∈ vals)
(uc : ∀ i j, (i,j+1) ∈ vals → (i,j) ∈ vals)

def conj (d : diagram) : diagram :=
{ vals := d.vals.image (prod.swap),

}

example {n : ℕ} (m : multiset ℕ)
  (hm₁ : ∀ i, i ∈ m → 0 < i)
  (hm₂ : m.sum = n) :
  (map (λ i, countp (λ j, i < j) m) (range n)).sum = n :=
begin

end

def conjugate {n : ℕ} (p : partition n) : partition n :=
of_sums n ((range n).map (λ i, p.parts.countp (λ j, i < j)))
begin
  rcases p with ⟨m, hm₁, hm₂⟩,
  change multiset.sum ((range n).map (λ i, countp (λ j, i < j) m)) = n,
  extract_goal,
end
-- { parts := ((range n).map (λ i, p.parts.countp (λ j, i < j))).filter (λ q, 0 < q),
--   parts_pos := λ i, multiset.of_mem_filter,
--   parts_sum :=
--   begin
--     suffices : (((range n).map (λ i, p.parts.countp (λ j, i < j)))).sum = n,
--     have := multiset.filter_add_not,
--   end
-- }

/-- The finset of those partitions in which every part is odd. -/
def odd_partition (n : ℕ) : finset (partition n) :=
finset.univ.filter (λ c, ∀ i ∈ c.parts, ¬ even i)

/-- The finset of those partitions in which each part is used at most once. -/
def distinct_partition (n : ℕ) : finset (partition n) :=
finset.univ.filter (λ c, c.parts.nodup)

/-- The finset of those partitions in which every part is odd and used at most once. -/
def odd_distinct_partition (n : ℕ) : finset (partition n) := odd_partition n ∩ distinct_partition n

end partition
