/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.list.range

open list function nat

namespace list
namespace nat

/-- The antidiagonal of a natural number `n` is the list of pairs `(i,j)` such that `i+j = n`. -/
def antidiagonal (n : ℕ) : list (ℕ × ℕ) :=
(range (n+1)).map (λ i, (i, n - i))

/-- A pair (i,j) is contained in the antidiagonal of `n` if and only if `i+j=n`. -/
@[simp] lemma mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
  x ∈ antidiagonal n ↔ x.1 + x.2 = n :=
begin
  rw [antidiagonal, mem_map], split,
  { rintros ⟨i, hi, rfl⟩, rw [mem_range, lt_succ_iff] at hi, exact add_sub_of_le hi },
  { rintro rfl, refine ⟨x.fst, _, _⟩,
    { rw [mem_range, add_assoc, lt_add_iff_pos_right], exact zero_lt_succ _ },
    { exact prod.ext rfl (nat.add_sub_cancel_left _ _) } }
end

/-- The length of the antidiagonal of `n` is `n+1`. -/
@[simp] lemma length_antidiagonal (n : ℕ) : (antidiagonal n).length = n+1 :=
by rw [antidiagonal, length_map, length_range]

/-- The antidiagonal of `0` is the list `[(0,0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = [(0, 0)] :=
rfl

/-- The antidiagonal of `n` does not contain duplicate entries. -/
lemma nodup_antidiagonal (n : ℕ) : nodup (antidiagonal n) :=
nodup_map (@left_inverse.injective ℕ (ℕ × ℕ) prod.fst (λ i, (i, n-i)) $ λ i, rfl) (nodup_range _)

@[simp] lemma antidiagonal_succ {n : ℕ} :
  antidiagonal (n + 1) = (0, n + 1) :: ((antidiagonal n).map (prod.map nat.succ id)) :=
begin
  simp only [antidiagonal, range_succ_eq_map, map_cons, true_and, nat.add_succ_sub_one, add_zero,
    id.def, eq_self_iff_true, nat.sub_zero, map_map, prod.map_mk],
  apply congr (congr rfl _) rfl,
  ext; simp,
end

-- TODO: PICK A BETTER NAME.
/--
`big_diag n l` is the list of functions supported on a subset of `l` which sum to `n`.
If `l` is a two-element set, this is essentially the same as `antidiagonal n`.
-/
def big_diag {ι : Sort*} : ℕ → list ι → list (ι → ℕ)
| 0 l := [λ _, 0]
| (n+1) [] := []
| (n+1) (x :: xs) := (antidiagonal (n+1)).bind (λ p, (big_diag p.2 xs).map (λ f x, f x + p.1))

lemma sum_eq_zero : ∀ (l : list ℕ), l.sum = 0 ↔ ∀ x ∈ l, x = 0
| [] := by simp
| (x :: xs) := by simp [sum_eq_zero xs]

lemma mem_big_diag {ι : Sort*} (n : ℕ) (l : list ι) (f : ι → ℕ) :
  f ∈ big_diag n l ↔ (l.map f).sum = n ∧ ∀ x ∉ l, f x = 0 :=
begin
  cases n,
  { change f ∈ [λ (i : ι), 0] ↔ _,
    simp only [mem_singleton, sum_eq_zero, forall_mem_map_iff],
    split,
    { tidy },
    { rintro ⟨hxl, hxr⟩, ext x, apply (em (x ∈ l)).elim (hxl x) (hxr x) } },
  { induction l,
    { simp [(nat.succ_ne_zero n).symm, big_diag] },
    { simp [big_diag, l_ih],

    }


  }

    -- split,
    -- { tidy },
    -- { rintros ⟨_, _⟩,
    --   ext x,
    --   by_cases x ∈ l,
    --     have := a_left (f x),

    -- }
end

end nat
end list
