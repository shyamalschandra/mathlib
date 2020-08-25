/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.giry_monad

/-!
# The product measure space

TODO:

Define finite (and countably infinite) product measure
Fubini's theorem

-/
noncomputable theory
open_locale classical big_operators
open function set measure_theory.outer_measure measurable_space topological_space (hiding generate_from)

namespace replace
lemma measurable.ennreal_add {α : Type*} [measurable_space α] {f g : α → ennreal}
  (hf : measurable f) (hg : measurable g) : measurable (λa, f a + g a) :=
hf.add hg

end replace


namespace function
/-- Evaluation a function to an argument. Useful if you want to talk about the partially applied
  `function.eval i : (Π i, α i) → α i`. -/
@[reducible] def eval {ι} {α : ι → Type*} (i : ι) (f : Π i, α i) : α i := f i

@[simp] lemma eval_apply {ι} {α : ι → Type*} (i : ι) (f : Π i, α i) : eval i f = f i := rfl

example {ι : Type*} {α : ι → Type*} (i : ι) (g : (Π i, α i) → α i) (s : set (Π i, α i)) :
  eval i '' s = g '' s :=
begin
  success_if_fail { simp only [eval_apply] },
  simp, -- why does this simplify?
  sorry
end

end function
open function


namespace set

section

variables {α β : Type*}

lemma univ_prod {t : set β} : set.prod (univ : set α) t = prod.snd ⁻¹' t :=
by simp [prod_eq]

lemma prod_univ {s : set α} : set.prod s (univ : set β) = prod.fst ⁻¹' s :=
by simp [prod_eq]

@[simp] lemma mk_preimage_prod_left_eq_empty {s : set α} {t : set β} {y : β} (hy : y ∉ t) :
  (λ x, (x, y)) ⁻¹' s.prod t = ∅ :=
by { ext z, simp [hy] }

@[simp] lemma mk_preimage_prod_right_eq_empty {s : set α} {t : set β} {x : α} (hx : x ∉ s) :
  prod.mk x ⁻¹' s.prod t = ∅ :=
by { ext z, simp [hx] }

lemma mk_preimage_prod_left_eq_if {s : set α} {t : set β} {y : β} :
  (λ x, (x, y)) ⁻¹' s.prod t = if y ∈ t then s else ∅ :=
by { split_ifs; simp [h] }

lemma mk_preimage_prod_right_eq_if {s : set α} {t : set β} {x : α} :
  prod.mk x ⁻¹' s.prod t = if x ∈ s then t else ∅ :=
by { split_ifs; simp [h] }

end

section

variables {α β γ : Type*} (s : α → set β) {t : α → set γ}

/-- The union of `s y` for `y ≤ x`. -/
def accumulate [has_le α] (x : α) : set β := ⋃ y ≤ x, s y

variable {s}
lemma accumulate_def [has_le α] {x : α} : accumulate s x = ⋃ y ≤ x, s y := rfl
@[simp] lemma mem_accumulate [has_le α] {x : α} {z : β} : z ∈ accumulate s x ↔ ∃ y ≤ x, z ∈ s y :=
mem_bUnion_iff

lemma subset_accumulate [preorder α] {x : α} : s x ⊆ accumulate s x :=
λ z, mem_bUnion le_rfl

lemma monotone_accumulate [preorder α] : monotone (accumulate s) :=
λ x y hxy, bUnion_subset_bUnion_left $ λ z hz, le_trans hz hxy

lemma bUnion_accumulate [preorder α] (y : α) : (⋃ x ≤ y, accumulate s x) = ⋃ x ≤ y, s x :=
begin
  apply subset.antisymm,
  { simp only [subset_def, mem_Union, exists_imp_distrib, mem_accumulate],
    intros z x hxy x' hx'x hz, exact ⟨x', hx'x.trans hxy, hz⟩ },
  { exact bUnion_subset_bUnion (λ x hx, ⟨x, hx, subset_accumulate⟩) }
end

lemma Union_accumulate [preorder α] : (⋃ x, accumulate s x) = ⋃ x, s x :=
begin
  apply subset.antisymm,
  { simp only [subset_def, mem_Union, exists_imp_distrib, mem_accumulate],
    intros z x x' hx'x hz, exact ⟨x', hz⟩ },
  { exact Union_subset_Union (λ i, subset_accumulate),  }
end

lemma accumulate_nat (s : ℕ → set β) {n : ℕ} : accumulate s n = ⋃ y ∈ finset.range (n+1), s y :=
by { ext, simp [nat.lt_succ_iff] }

lemma Union_prod_of_monotone [semilattice_sup α] (hs : monotone s) (ht : monotone t) :
  (⋃ x, (s x).prod (t x)) = (⋃ x, (s x)).prod (⋃ x, (t x)) :=
begin
  ext ⟨z, w⟩, simp only [mem_prod, mem_Union, exists_imp_distrib, and_imp, iff_def], split,
  { intros x hz hw, exact ⟨⟨x, hz⟩, ⟨x, hw⟩⟩ },
  { intros x hz x' hw, exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩ }
end

end

section
variables {ι : Type*} {α : ι → Type*} {s : set ι} {t : Π i, set (α i)}
@[simp] lemma mem_pi {f : Π i, α i} : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i :=
by refl

@[simp] lemma mem_univ_pi {f : Π i, α i} : f ∈ pi univ t ↔ ∀ i, f i ∈ t i :=
by simp

lemma pi_eq_empty {i : ι} (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ :=
by { ext f, simp only [mem_empty_eq, not_forall, iff_false, mem_pi, not_imp],
     exact ⟨i, hs, by simp [ht]⟩ }

lemma univ_pi_eq_empty {i : ι} (ht : t i = ∅) : pi univ t = ∅ :=
pi_eq_empty (mem_univ i) ht

lemma pi_nonempty_iff : (s.pi t).nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i :=
by simp [classical.skolem, set.nonempty]

lemma univ_pi_nonempty_iff : (pi univ t).nonempty ↔ ∀ i, (t i).nonempty :=
by simp [classical.skolem, set.nonempty]

lemma pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, (α i → false) ∨ (i ∈ s ∧ t i = ∅) :=
begin
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff], push_neg, apply exists_congr, intro i,
  split,
  { intro h, by_cases hα : nonempty (α i),
    { cases hα with x, refine or.inr ⟨(h x).1, by simp [eq_empty_iff_forall_not_mem, h]⟩ },
    { exact or.inl (λ x, hα ⟨x⟩) }},
  { rintro (h|h) x, exfalso, exact h x, simp [h] }
end

lemma univ_pi_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ :=
by simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]

lemma eval_image_pi {i : ι} (hs : i ∈ s) (ht : (s.pi t).nonempty) : eval i '' s.pi t = t i :=
begin
  ext x, rcases ht with ⟨f, hf⟩, split,
  { rintro ⟨g, hg, rfl⟩, exact hg i hs },
  { intro hg, refine ⟨function.update f i x, _, by simp⟩,
    intros j hj, by_cases hji : j = i,
    { subst hji, simp [hg] },
    { rw [mem_pi] at hf, simp [hji, hf, hj] }},
end

@[simp] lemma eval_image_univ_pi {i : ι} (ht : (pi univ t).nonempty) :
  (λ f : Π i, α i, f i) '' pi univ t = t i :=
eval_image_pi (mem_univ i) ht

lemma update_preimage_pi {i : ι} {f : Π i, α i} (hi : i ∈ s)
  (hf : ∀ j ∈ s, j ≠ i → f j ∈ t j) : (update f i) ⁻¹' s.pi t = t i :=
begin
  ext x, split,
  { intro h, convert h i hi, simp },
  { intros hx j hj, by_cases h : j = i,
    { cases h, simpa },
    { rw [update_noteq h], exact hf j hj h }}
end

lemma update_preimage_univ_pi {i : ι} {f : Π i, α i} (hf : ∀ j ≠ i, f j ∈ t j) :
  (update f i) ⁻¹' pi univ t = t i :=
update_preimage_pi (mem_univ i) (λ j _, hf j)

lemma subset_pi_eval_image (s : set ι) (u : set (Π i, α i)) : u ⊆ pi s (λ i, eval i '' u) :=
λ f hf i hi, ⟨f, hf, rfl⟩

end

section
variables {α β : Type*}
lemma image_inter_preimage {f : α → β} {s : set α} {t : set β} : f '' (s ∩ f ⁻¹' t) = f '' s ∩ t :=
set.push_pull f s t

lemma image_compl_preimage {f : α → β} {s : set α} {t : set β} : f '' (s \ f ⁻¹' t) = f '' s \ t :=
by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]

end
end set
open set

namespace canonically_ordered_semiring
variables {α : Type*} [canonically_ordered_comm_semiring α]

lemma mul_le_mul_left' {b c : α} (h : b ≤ c) (a : α) : a * b ≤ a * c :=
mul_le_mul (le_refl a) h

lemma mul_le_mul_right' {b c : α} (h : b ≤ c) (a : α) : b * a ≤ c * a :=
mul_le_mul h (le_refl a)

end canonically_ordered_semiring

section monoid_with_zero

@[simp] lemma zero_pow_eq_zero {α} [monoid_with_zero α] [nontrivial α] {n : ℕ} :
  (0 : α) ^ n = 0 ↔ 0 < n :=
begin
  split; intro h,
  { rw [nat.pos_iff_ne_zero], rintro rfl, simpa using h },
  { exact zero_pow' n h.ne.symm }
end


end monoid_with_zero

namespace finset
@[to_additive]
lemma prod_split {α β} [decidable_eq α] [comm_monoid β] (s t : finset α) (f : α → β) :
  (∏ x in s, f x) = (∏ x in s ∩ t, f x) * (∏ x in s \ t, f x) :=
by { convert s.prod_piecewise t f f, simp [finset.piecewise] }

@[to_additive]
lemma prod_split_single {α β} [decidable_eq α] [comm_monoid β] {s : finset α} {i : α} (h : i ∈ s)
  (f : α → β) : (∏ x in s, f x) = f i * (∏ x in s \ {i}, f x) :=
by { convert s.prod_split {i} f, simp [h] }

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
lemma prod_add_prod_eq {α β} [comm_semiring β] {s : finset α} {i : α} {f g h : α → β}
  (hi : i ∈ s) (h1 : g i + h i = f i) (h2 : ∀ j ∈ s, j ≠ i → g j = f j)
  (h3 : ∀ j ∈ s, j ≠ i → h j = f j) : ∏ i in s, g i + ∏ i in s, h i = ∏ i in s, f i :=
by { simp_rw [prod_split_single hi, ← h1, right_distrib], congr' 2; apply prod_congr rfl; simpa }

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` is the
  sum of the products of `g` and `h`. -/
lemma prod_univ_add_prod_univ_eq {α β} [fintype α] [comm_semiring β] (i : α) {f g h : α → β}
  (h1 : g i + h i = f i) (h2 : ∀ j ≠ i, g j = f j) (h3 : ∀ j ≠ i, h j = f j) :
  ∏ i, g i + ∏ i, h i = ∏ i, f i :=
prod_add_prod_eq (mem_univ i) h1 (λ j _, h2 j) (λ j _, h3 j)

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `linear_ordered_comm_ring`. -/
lemma prod_add_prod_le {α β} [linear_ordered_comm_ring β] {s : finset α} {i : α} {f g h : α → β}
  (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
  (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i) :
  ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  simp_rw [prod_split_single hi],
  refine le_trans _ (mul_le_mul_of_nonneg_right h2i _),
  { rw [right_distrib],
    apply add_le_add; apply mul_le_mul_of_nonneg_left; try { apply prod_le_prod };
    simp only [and_imp, mem_sdiff, mem_singleton]; intros; apply_assumption; assumption },
  { apply prod_nonneg, simp only [and_imp, mem_sdiff, mem_singleton],
    intros j h1j h2j, refine le_trans (hg j h1j) (hgf j h1j h2j) }
end

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` is at least the sum of the
  products of `g` and `h`. This is the version for `linear_ordered_comm_ring`. -/
lemma prod_univ_add_prod_univ_le {α β} [fintype α] [linear_ordered_comm_ring β] (i : α)
  {f g h : α → β} (h2i : g i + h i ≤ f i) (hgf : ∀ j ≠ i, g j ≤ f j)
  (hhf : ∀ j ≠ i, h j ≤ f j) (hg : ∀ i, 0 ≤ g i) (hh : ∀ i, 0 ≤ h i) :
  ∏ i, g i + ∏ i, h i ≤ ∏ i, f i :=
prod_add_prod_le (mem_univ i) h2i (λ j _, hgf j) (λ j _, hhf j) (λ j _, hg j) (λ j _, hh j)

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`.
-/
lemma prod_add_prod_le' {α β} [canonically_ordered_comm_semiring β] {s : finset α} {i : α}
  {f g h : α → β} (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
  (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) : ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  simp_rw [prod_split_single hi],
  refine le_trans _ (canonically_ordered_semiring.mul_le_mul_right' h2i _),
  rw [right_distrib],
  apply add_le_add; apply canonically_ordered_semiring.mul_le_mul_left'; apply prod_le_prod';
  simp only [and_imp, mem_sdiff, mem_singleton]; intros; apply_assumption; assumption
end

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` is at least the sum of the
  products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`. -/
lemma prod_univ_add_prod_univ_le' {α β} [fintype α] [canonically_ordered_comm_semiring β] (i : α)
  {f g h : α → β} (h2i : g i + h i ≤ f i) (hgf : ∀ j ≠ i, g j ≤ f j)
  (hhf : ∀ j ≠ i, h j ≤ f j) : ∏ i, g i + ∏ i, h i ≤ ∏ i, f i :=
prod_add_prod_le' (mem_univ i) h2i (λ j _, hgf j) (λ j _, hhf j)

end finset

section tsum

open filter
variables {ι α : Type*} {β : α → Type*} [∀ x, add_comm_monoid (β x)]
  [∀ x, topological_space (β x)] {f : ι → ∀ x, β x}

lemma pi.has_sum  {g : ∀ x, β x} : has_sum f g ↔ ∀ x, has_sum (λ i, f i x) (g x) :=
begin
  simp_rw [has_sum, nhds_pi, filter.tendsto_infi, filter.tendsto_comap_iff],
  apply forall_congr, intro a, congr', ext s, simp
end

lemma pi.summable : summable f ↔ ∀ x, summable (λ i, f i x) :=
by simp [summable, pi.has_sum, classical.skolem]

lemma tsum_apply [∀ x, t2_space (β x)] {x : α} (hf : summable f) : (∑' i, f i) x = ∑' i, f i x :=
(pi.has_sum.mp hf.has_sum x).tsum_eq.symm

protected lemma ennreal.tsum_apply {ι α : Type*} {f : ι → α → ennreal} {x : α} :
  (∑' i, f i) x = ∑' i, f i x :=
tsum_apply $ pi.summable.mpr $ λ _, ennreal.summable

end tsum

lemma measurable_space_ennreal_def :
  generate_from (range Iio) = (by apply_instance : measurable_space ennreal) :=
(borel_eq_generate_Iio _).symm

lemma measurable_of_Iio {ι α} [measurable_space ι]
  [topological_space α] [second_countable_topology α]
  [linear_order α] [order_topology α] [measurable_space α] [borel_space α] {f : ι → α}
  (hf : ∀ x, is_measurable (f ⁻¹' Iio x)) :
  measurable f :=
begin
  convert measurable_generate_from _,
  exact borel_space.measurable_eq.trans (borel_eq_generate_Iio _),
  rintro _ ⟨x, rfl⟩, exact hf x
end

lemma measurable_of_Ioi {ι α} [measurable_space ι]
  [topological_space α] [second_countable_topology α]
  [linear_order α] [order_topology α] [measurable_space α] [borel_space α] {f : ι → α}
  (hf : ∀ x, is_measurable (f ⁻¹' Ioi x)) :
  measurable f :=
begin
  convert measurable_generate_from _,
  exact borel_space.measurable_eq.trans (borel_eq_generate_Ioi _),
  rintro _ ⟨x, rfl⟩, exact hf x
end

lemma measurable_of_Iic {ι α} [measurable_space ι]
  [topological_space α] [second_countable_topology α]
  [linear_order α] [order_topology α] [measurable_space α] [borel_space α] {f : ι → α}
  (hf : ∀ x, is_measurable (f ⁻¹' Iic x)) : measurable f :=
begin
  apply measurable_of_Ioi,
  simp_rw [← compl_Iic, preimage_compl, is_measurable.compl_iff],
  assumption
end

lemma measurable_of_Ici {ι α} [measurable_space ι]
  [topological_space α] [second_countable_topology α]
  [linear_order α] [order_topology α] [measurable_space α] [borel_space α] {f : ι → α}
  (hf : ∀ x, is_measurable (f ⁻¹' Ici x)) : measurable f :=
begin
  apply measurable_of_Iio,
  simp_rw [← compl_Ici, preimage_compl, is_measurable.compl_iff],
  assumption
end

lemma Inter_set_of {ι α} (P : ι → α → Prop) :
  (⋂ (i : ι), {x : α | P i x }) = {x : α | ∀ (i : ι), P i x} :=
by { ext, simp }

lemma measurable.supr {ι α β : Type*} [encodable ι] [measurable_space α]
  [measurable_space β] [topological_space β] [second_countable_topology β] [complete_linear_order β]
  [borel_space β] [order_topology β]
  (f : ι → α → β) (h : ∀ i, measurable (f i)) : measurable (⨆ i, f i) :=
begin
  apply measurable_of_Iic, simp [preimage, _root_.supr_apply, ← Inter_set_of], intro y,
  apply is_measurable.Inter, intro i, exact h i is_measurable_Iic
end

#check ∀ {ι ι₂ : Sort*} {α : Type*} [_inst_2 : has_Sup α] {f : ι → α} {g : ι₂ → α}
  (h : ι → ι₂), surjective h → (∀ (x : ι), g (h x) = f x) → by exactI (⨆ (x : ι), f x) = ⨆ (y : ι₂), g y

#check @supr_congr
/-- todo: `ennreal` can probably be generalized to a
[measurable_space β] [topological_space β] [add_comm_monoid β] [has_continuous_add β]
  [borel_space β] -/
lemma measurable.ennreal_tsum {ι α} [encodable ι] [measurable_space α]
  {f : ι → α → ennreal} (h : ∀ i, measurable (f i)) : measurable (∑' i, f i) :=
begin
  convert measurable.supr (λ s x, ∑ (a : ι) in s, f a x) _,
  { ext1 x, simp [ennreal.tsum_apply, ennreal.tsum_eq_supr_sum, _root_.supr_apply] },
  intros s t ht,
end

lemma measurable.tsum {ι α β} [measurable_space α]
  [measurable_space β] [topological_space β] [add_comm_monoid β] [has_continuous_add β]
  [borel_space β]
  {f : ι → α → β} (h : ∀ i, measurable (f i)) : measurable (∑' i, f i) :=
begin
  intros s hs,
end

section complete_lattice

variables {ι : Sort*} {α : Type*} {x : α} [complete_lattice α]
lemma supr_const_le : (⨆ (h : ι), x) ≤ x :=
supr_le (λ _, le_rfl)

lemma le_infi_const : x ≤ (⨅ (h : ι), x) :=
le_infi (λ _, le_rfl)

end complete_lattice




namespace measure_theory

section

namespace outer_measure
section bounded_by

variables {α : Type*} (m : set α → ennreal)

/-- Given any function `m` assigning measures to sets, there is a unique maximal outer measure `μ`
  satisfying `μ s ≤ m s` for all `s : set α`. This is the same as `outer_measure.of_function`,
  except that it doesn't require `m ∅ = 0`. -/
def bounded_by : outer_measure α :=
outer_measure.of_function (λ s, ⨆ (h : s.nonempty), m s) (by simp [empty_not_nonempty])

variables {m}
theorem bounded_by_le (s : set α) : bounded_by m s ≤ m s :=
(of_function_le _).trans supr_const_le

local attribute [irreducible] outer_measure.of_function
theorem bounded_by_eq_of_function (m_empty : m ∅ = 0) (s : set α) :
  bounded_by m s = outer_measure.of_function m m_empty s :=
begin
  have : (λ s : set α, ⨆ (h : s.nonempty), m s) = m,
  { ext1 t, cases t.eq_empty_or_nonempty with h h; simp [h, empty_not_nonempty, m_empty] },
  simp [bounded_by, this]
end

theorem bounded_by_eq (s : set α) (m_empty : m ∅ = 0) (m_mono : ∀ ⦃t : set α⦄, s ⊆ t → m s ≤ m t)
  (m_subadd : ∀ (s : ℕ → set α), m (⋃i, s i) ≤ (∑'i, m (s i))) : bounded_by m s = m s :=
by rw [bounded_by_eq_of_function m_empty, of_function_eq s m_mono m_subadd]

theorem le_bounded_by {μ : outer_measure α} : μ ≤ bounded_by m ↔ ∀ s, μ s ≤ m s :=
begin
  rw [bounded_by, le_of_function, forall_congr], intro s,
  cases s.eq_empty_or_nonempty with h h; simp [h, empty_not_nonempty]
end

theorem le_bounded_by' {μ : outer_measure α} :
  μ ≤ bounded_by m ↔ ∀ s : set α, s.nonempty → μ s ≤ m s :=
by { rw [le_bounded_by, forall_congr], intro s, cases s.eq_empty_or_nonempty with h h; simp [h] }

lemma bounded_by_caratheodory {m : set α → ennreal} {s : set α}
  (hs : ∀t, m (t ∩ s) + m (t \ s) ≤ m t) : (bounded_by m).caratheodory.is_measurable' s :=
begin
  apply of_function_caratheodory, intro t,
  cases t.eq_empty_or_nonempty with h h,
  { simp [h, empty_not_nonempty] },
  { convert le_trans _ (hs t), simp [h], exact add_le_add supr_const_le supr_const_le }
end

/- TODO: also replace `Inf_eq_of_function_Inf_gen`. -/
end bounded_by
end outer_measure
open outer_measure measure

section measurable_pi
variables {α : Type*} {β : α → Type*} [Πa, measurable_space (β a)]

lemma is_measurable.pi [encodable α] {t : Π i, set (β i)} (hs : ∀ i, is_measurable (t i)) :
  is_measurable (pi univ t) :=
by { convert is_measurable.Inter (λ i, measurable_pi_apply _ (hs i) : _), simp [pi_def] }

lemma measurable_update (f : Π (a : α), β a) {i : α} : measurable (update f i) :=
begin
  apply measurable_pi_lambda,
  intro j, by_cases hj : j = i,
  { cases hj, convert measurable_id, ext, simp },
  simp_rw [update_noteq hj], apply measurable_const,
end

lemma is_measurable_pi_of_nonempty [encodable α] {t : Π i, set (β i)} (h : (pi univ t).nonempty) :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) :=
begin
  rcases h with ⟨f, hf⟩, refine ⟨λ hst i, _, is_measurable.pi⟩,
  convert measurable_update f hst, rw [update_preimage_univ_pi], exact λ j _, hf j (mem_univ j)
end

lemma is_measurable_pi [encodable α] {t : Π i, set (β i)} :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) ∨ ∃ i, t i = ∅ :=
begin
  cases (pi univ t).eq_empty_or_nonempty with h h,
  { have := univ_pi_eq_empty_iff.mp h, simp [h, univ_pi_eq_empty_iff.mp h] },
  { simp [←not_nonempty_iff_eq_empty, univ_pi_nonempty_iff.mp h, is_measurable_pi_of_nonempty h] }
end

lemma measurable_pi {γ} [measurable_space γ] {f : γ → Π i, β i} :
  measurable f ↔ ∀ x, measurable (λ c, f c x) :=
⟨λ hf x, (measurable_pi_apply _).comp hf, measurable_pi_lambda f⟩

end measurable_pi

section measurable

variables {α β γ: Type*} [measurable_space α] [measurable_space β] [measurable_space γ]

lemma measurable_measure {μ : α → measure β} :
  measurable μ ↔ ∀(s : set β) (hs : is_measurable s), measurable (λb, μ b s) :=
⟨λ hμ s hs, (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

lemma measurable_prod_mk_left {x : α} : measurable (@prod.mk _ β x) :=
measurable_const.prod_mk measurable_id

lemma measurable_prod_mk_right {y : β} : measurable (λ x : α, (x, y)) :=
measurable_id.prod_mk measurable_const

lemma measurable.prod_mk : measurable (@prod.mk α β) :=
measurable_pi_lambda _ $ λ x, measurable_prod_mk_right

lemma measurable_prod {f : α → β × γ} : measurable f ↔
  measurable (λa, (f a).1) ∧ measurable (λa, (f a).2) :=
⟨λ hf, ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, λ h, measurable.prod h.1 h.2⟩

end measurable

section measure_pi

variables {ι : Type*} [fintype ι] {α : ι → Type*} {m : Π i, outer_measure (α i)}

/-- An upper bound for the measure in a product space.
  It is defined to be the product of the measures of all its projections.
  For boxes it should be equal to the correct measure. -/
def pi_premeasure (m : Π i, outer_measure (α i)) (s : set (Π i, α i)) : ennreal :=
∏ i, m i (eval i '' s)

@[simp] lemma pi_premeasure_def {s : set (Π i, α i)} :
  pi_premeasure m s = ∏ i, m i (eval i '' s) := rfl

lemma pi_premeasure_pi {s : Π i, set (α i)} (hs : (pi univ s).nonempty) :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
by simp [hs]

lemma pi_premeasure_pi' [nonempty ι] {s : Π i, set (α i)} :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
begin
  cases (pi univ s).eq_empty_or_nonempty with h h,
  { rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩,
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩,
    simpa [h, finset.card_univ, zero_pow (fintype.card_pos_iff.mpr _inst_2),
      @eq_comm _ (0 : ennreal), finset.prod_eq_zero_iff] },
  { simp [h] }
end

lemma pi_premeasure_pi_mono {s t : set (Π i, α i)} (h : s ⊆ t) :
  pi_premeasure m s ≤ pi_premeasure m t :=
finset.prod_le_prod' (λ i _, (m i).mono' (image_subset _ h))

lemma pi_premeasure_pi_eval [nonempty ι] {s : set (Π i, α i)} :
  pi_premeasure m (pi univ (λ i, eval i '' s)) = pi_premeasure m s :=
by simp [pi_premeasure_pi']

namespace outer_measure
/-- `outer_measure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{ s i | i : ι }`. -/
protected def pi (m : Π i, outer_measure (α i)) : outer_measure (Π i, α i) :=
bounded_by (pi_premeasure m)

lemma pi_pi_le (s : Π i, set (α i)) :
  outer_measure.pi m (pi univ s) ≤ ∏ i, m i (s i) :=
by { cases (pi univ s).eq_empty_or_nonempty with h h, simp [h],
     exact (bounded_by_le _).trans_eq (pi_premeasure_pi h) }


lemma le_pi {m : Π i, outer_measure (α i)} {n : outer_measure (Π i, α i)} :
  n ≤ outer_measure.pi m ↔ ∀ (s : Π i, set (α i)), (pi univ s).nonempty →
    n (pi univ s) ≤ ∏ i, m i (s i) :=
begin
  rw [outer_measure.pi, le_bounded_by'], split,
  { intros h s hs, refine (h _ hs).trans_eq (pi_premeasure_pi hs)  },
  { intros h s hs, refine le_trans (n.mono $ subset_pi_eval_image univ s) (h _ _),
    simp [univ_pi_nonempty_iff, hs] }
end

lemma pi_pi_false [encodable ι] (s : Π i, set (α i))
  (h2s : (pi univ s).nonempty) : outer_measure.pi m (pi univ s) = ∏ i, m i (s i) :=
begin
  simp_rw [← pi_premeasure_pi h2s],
  refine le_antisymm (bounded_by_le _) _,
  refine le_binfi _, dsimp only, intros t ht,
  sorry
  -- refine le_trans _ (ennreal.tsum_le_tsum $ λ i, _),
end
end outer_measure

namespace measure

variables [Π i, measurable_space (α i)] (μ : Π i, measure (α i))

protected lemma caratheodory {α} [measurable_space α] (μ : measure α) {s t : set α}
  (hs : is_measurable s) : μ (t ∩ s) + μ (t \ s) = μ t :=
(le_to_outer_measure_caratheodory μ s hs t).symm

lemma pi_caratheodory :
  measurable_space.pi ≤ (outer_measure.pi (λ i, (μ i).to_outer_measure)).caratheodory :=
begin
  refine supr_le _, intros i s hs,
  simp [measurable_space.comap] at hs, rcases hs with ⟨s, hs, rfl⟩,
  apply bounded_by_caratheodory, intro t,
  simp_rw [pi_premeasure_def],
  refine finset.prod_univ_add_prod_univ_le' i _ _ _,
  { simp [image_inter_preimage, image_compl_preimage, (μ i).caratheodory hs, le_refl] },
  { intros j hj, apply mono', apply image_subset, apply inter_subset_left },
  { intros j hj, apply mono', apply image_subset, apply diff_subset }
end

/-- `measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be the maximal product measure, i.e.
  the maximal measure `n` with the property that `ν (pi univ s) = ∏ i, μ i (s i)`,
  where `pi univ s` is the product of the sets `{ s i | i : ι }`. -/
protected def pi : measure (Π i, α i) :=
to_measure (outer_measure.pi (λ i, (μ i).to_outer_measure)) (pi_caratheodory μ)

lemma pi_pi [encodable ι] (s : Π i, set (α i)) (h1s : ∀ i, is_measurable (s i))
  (h2s : (pi univ s).nonempty) : measure.pi μ (pi univ s) = ∏ i, μ i (s i) :=
begin
  rw [measure.pi, to_measure_apply _ _ (is_measurable.pi h1s)],
  simp_rw [← to_outer_measure_apply, ← pi_premeasure_pi h2s],
  refine le_antisymm (bounded_by_le _) _,
  refine le_binfi _, dsimp only, intros t ht,
  sorry
end

end measure

end measure_pi


/-! ### Prod -/

variables {α β γ : Type*} [measurable_space α] [measurable_space β] [measurable_space γ]

def is_pi_system {α} (C : set (set α)) : Prop :=
∀ ⦃s t : set α⦄, s ∈ C → t ∈ C → (s ∩ t).nonempty → s ∩ t ∈ C

lemma generate_from_prod : generate_from
    (image2 set.prod { s | is_measurable s } { t | is_measurable t } : set (set (α × β))) =
  prod.measurable_space :=
begin
  apply le_antisymm,
  { apply generate_from_le, rintro _ ⟨s, t, hs, ht, rfl⟩, rw [prod_eq],
    exact (measurable_fst hs).inter (measurable_snd ht) },
  { refine sup_le _ _; rintro _ ⟨s, hs, rfl⟩; apply is_measurable_generate_from,
    exact ⟨s, univ, hs, is_measurable.univ, prod_univ⟩,
    exact ⟨univ, s, is_measurable.univ, hs, univ_prod⟩ }
end

lemma is_pi_system_prod :
  is_pi_system (image2 set.prod { s : set α | is_measurable s } { t : set β | is_measurable t }) :=
by { rintro _ _ ⟨s₁, t₁, hs₁, ht₁, rfl⟩ ⟨s₂, t₂, hs₂, ht₂, rfl⟩ _, rw [prod_inter_prod],
     exact mem_image2_of_mem (hs₁.inter hs₂) (ht₁.inter ht₂) }


/-
Use `sigma_finite_mk` to create an instance without the requirement that `spanning_sets` is
  monotone.
-/

def sigma_finite_mk {μ : measure α} {s : set α} (sets : ℕ → set α)
  (h1 : ∀ i, is_measurable (sets i)) (h2 : ∀ i, μ (sets i) < ⊤) (h3 : (⋃ i, sets i) = s) :
  sigma_finite μ s :=
{ spanning_sets := accumulate sets,
  monotone_spanning_sets := monotone_accumulate,
  is_measurable_spanning_sets :=
    λ i, is_measurable.Union $ λ j, is_measurable.Union_Prop $ λ hij, h1 j,
  measure_spanning_sets_lt_top :=
    by { intro i, rw [accumulate_nat],
      apply (measure_bUnion_le _ _).trans_lt,
      refine (finset.tsum_subtype _ (λ i, μ (sets i))).le.trans_lt _,
      rw ennreal.sum_lt_top_iff, exact λ j _, h2 j,
      exact (finset.range (i+1)).countable_to_set },
  Union_spanning_sets := by { rw [Union_accumulate, h3] } }

namespace measure

variables (μ : measure α) (ν : measure β)

lemma measure_if {x : β} {t : set β} {s : set α} {μ : measure α} :
  μ (if x ∈ t then s else ∅) = indicator t (λ _, μ s) x :=
begin
  split_ifs; simp [h],
end


/-- The product of two measures. -/
protected def prod : measure (α × β) :=
bind μ $ λ x : α, map (prod.mk x) ν

/-- The symmetric version of the product of two measures. -/
protected def prod_symm : measure (α × β) :=
bind ν $ λ y : β, map (λ x, (x, y)) μ

variables {μ ν}

-- instance Prop.measurable_space : measurable_space Prop := ⊤
-- instance set.measurable_space : measurable_space (set α) := measurable_space.pi

-- lemma measurable.measure_apply {ι} [measurable_space ι] {s : ι → set α}
--   (hf : ∀ i, is_measurable (s i)) : measurable (λi, μ (s i)) :=
-- begin
--   refine measurable.comp _ _,
-- end

--measurable_supr

def directed_supr {ι} [nonempty ι] [partial_order ι] {μ : ι → measure α} (hμ : monotone μ) :
  measure α :=
begin
  apply measure.of_measurable (λ s _, ⨆ i, μ i s) (by simp),

end


/-- A directed supremum of measures applied is evaluated as a supremum on `ennreal`. -/
lemma supr_apply_of_monotone {ι} [partial_order ι] {μ : ι → measure α} (hμ : monotone μ)
  {s : set α} (hs : is_measurable s) : (⨆ i, μ i) s = ⨆ i, μ i s :=
begin
  refine le_antisymm _ _,
  {  },
  { refine supr_le _, intro i, exact (le_supr μ i : _) s hs },
end

lemma supr_restrict {ι} {μ : measure α} {t : ι → set α} :
  (⨆ i, μ.restrict (t i)) = μ.restrict (⋃ i, t i) :=
begin
  ext1 s hs, simp [hs, outer_measure.supr_apply],
end

lemma supr_restrict_spanning_sets {μ : measure α} [sigma_finite μ univ] {s : set α} :
  ⨆ i, μ.restrict (spanning_sets μ univ i) s = μ s :=
begin

end

/- Proposition 5.1.3 -/
lemma measurable.map_prod_mk {μ : measure β} [sigma_finite μ univ] :
  measurable (λx, map (prod.mk x : β → α × β) μ) :=
begin
  apply measurable_of_measurable_coe, intros s hs,
  simp_rw [map_apply measurable_prod_mk_left hs],
  refine induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ hs,
  { simp [measurable_const] },
  { rintro _ ⟨s, t, hs, ht, rfl⟩, simp only [mk_preimage_prod_right_eq_if, measure_if],
    exact measurable_const.indicator hs },
  { intros t ht h2t, simp_rw [preimage_compl], sorry },
  { intros f h1f h2f h3f, simp_rw [preimage_Union], sorry },
end

@[simp] lemma prod_apply {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ x, ν (prod.mk x ⁻¹' s) ∂μ :=
begin
  rw [measure.prod, bind_apply hs],
  congr, ext x : 1, rw [map_apply _ hs],
  apply measurable_prod_mk_left,
  refine measurable.map_prod_mk
end

@[simp] lemma prod_prod {s : set α} {t : set β} (hs : is_measurable s) (ht : is_measurable t) :
  μ.prod ν (s.prod t) = μ s * ν t :=
by simp_rw [prod_apply (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
  lintegral_indicator _ hs, lintegral_const, restrict_apply is_measurable.univ,
  univ_inter, mul_comm]

@[simp] lemma prod_symm_apply {s : set (α × β)} (hs : is_measurable s) :
  μ.prod_symm ν s = ∫⁻ y, μ ((λ x, (x, y)) ⁻¹' s) ∂ν :=
begin
  rw [measure.prod_symm, bind_apply hs],
  congr, ext x : 1, rw [map_apply _ hs],
  apply measurable_prod_mk_right,
  sorry
end

@[simp] lemma prod_symm_prod {s : set α} {t : set β} (hs : is_measurable s) (ht : is_measurable t) :
  μ.prod_symm ν (s.prod t) = μ s * ν t :=
by simp_rw [prod_symm_apply (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
  lintegral_indicator _ ht, lintegral_const, restrict_apply is_measurable.univ, univ_inter]

variables  [sigma_finite μ univ] [sigma_finite ν univ]

lemma prod_unique {μν₁ μν₂ : measure (α × β)}
  (h₁ : ∀ s t, is_measurable s → is_measurable t → μν₁ (s.prod t) = μ s * ν t)
  (h₂ : ∀ s t, is_measurable s → is_measurable t → μν₂ (s.prod t) = μ s * ν t) : μν₁ = μν₂ :=
begin
  refine ext_sigma_finite _ generate_from_prod.symm is_pi_system_prod
    (λ i, (spanning_sets μ univ i).prod (spanning_sets ν univ i)) _ _ _ _ _ _,
  { rw [Union_prod_of_monotone (monotone_spanning_sets μ _) (monotone_spanning_sets ν _)],
    simp_rw [Union_spanning_sets, univ_prod_univ] },
  { intro i, apply mem_image2_of_mem; apply is_measurable_spanning_sets },
  { intros i j hij, apply prod_mono; refine monotone_spanning_sets _ _ hij },
  { intro i, rw [h₁], apply ennreal.mul_lt_top; apply measure_spanning_sets_lt_top,
    all_goals { apply is_measurable_spanning_sets } },
  { intro i, rw [h₂], apply ennreal.mul_lt_top; apply measure_spanning_sets_lt_top,
    all_goals { apply is_measurable_spanning_sets } },
  { rintro _ ⟨s, t, hs, ht, rfl⟩, simp * at * }
end

lemma prod_eq_prod_symm : μ.prod ν = μ.prod_symm ν :=
prod_unique (λ _ _, prod_prod) (λ _ _, prod_symm_prod)

lemma prod_apply_symm {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ y, μ ((λ x, (x, y)) ⁻¹' s) ∂ν :=
by rw [prod_eq_prod_symm, prod_symm_apply hs]

/-- The Lebesgue intergral is measurable -/
lemma measurable_lintegral_prod_right (f : α × β → ennreal) :
  measurable (λ x, ∫⁻ y, f (x, y) ∂ν) :=
begin
  sorry
end

lemma measurable_lintegral_prod_left (f : α × β → ennreal) :
  measurable (λ y, ∫⁻ x, f (x, y) ∂μ) :=
begin
  sorry
end

/-- Tonelli's Theorem -/
lemma lintegral_prod (f : α × β → ennreal) :
  ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
begin

end

/-- symmetric version of Tonelli's Theorem -/
lemma lintegral_prod_symm (f : α × β → ennreal) :
  ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
begin

end

end measure

end

end measure_theory

-- #lint

#print nat.has_Inf
