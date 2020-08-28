/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.giry_monad
import measure_theory.bochner_integration
import measure_theory.set_integral

/-!
# The product measure space

TODO:

Define finite (and countably infinite) product measure
Fubini's theorem

-/
noncomputable theory
open_locale classical big_operators
open function set measure_theory.outer_measure measurable_space topological_space (hiding generate_from)

namespace function

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

lemma Inter_set_of {ι α} (P : ι → α → Prop) :
  (⋂ (i : ι), {x : α | P i x }) = {x : α | ∀ (i : ι), P i x} :=
by { ext, simp }

lemma range_subset_singleton {ι α} {f : ι → α} {x : α} : range f ⊆ {x} ↔ f = λ _, x :=
by simp [range_subset_iff, funext_iff, mem_singleton]

lemma subset_of_eq {α} {s t : set α} : s = t → s ⊆ t :=
by { rintro rfl, exact subset.rfl }


lemma diff_diff_comm {α} {s t u : set α} : s \ t \ u = s \ u \ t :=
by simp_rw [diff_diff, union_comm]

-- rename: image_compl_preimage -> image_diff_preimage

lemma image_preimage_eq_iff {α β} {f : α → β} {s : set β} : f '' (f ⁻¹' s) = s ↔ s ⊆ range f :=
⟨by { rintro h, rw [← h], apply image_subset_range }, image_preimage_eq_of_subset⟩

-- todo: rename
lemma image_compl_preimage' {α β} {f : α → β} {s : set β} : f '' ((f ⁻¹' s)ᶜ) = range f \ s :=
by rw [compl_eq_univ_diff, image_compl_preimage, image_univ]

-- function
variables {α β γ : Type*}
lemma comp_piecewise (h : β → γ) {f g : α → β} {s : set α} {x : α} :
  h (s.piecewise f g x) = s.piecewise (h ∘ f) (h ∘ g) x :=
by by_cases hx : x ∈ s; simp [hx]

@[simp] lemma piecewise_same {f : α → β} {s : set α} : s.piecewise f f = f :=
by { ext x, by_cases hx : x ∈ s; simp [hx] }

lemma range_piecewise {α : Type*} {β : Sort*} (s : set α) (f g : α → β) [∀j, decidable (j ∈ s)] :
  range (s.piecewise f g) = f '' s ∪ g '' sᶜ :=
begin
  ext y, split,
  { rintro ⟨x, rfl⟩, by_cases h : x ∈ s;[left, right]; use x; simp [h] },
  { rintro (⟨x, hx, rfl⟩|⟨x, hx, rfl⟩); use x; simp * at * }
end

-- indicator
@[simp] lemma piecewise_eq_indicator [has_zero β] {f : α → β} {s : set α} :
  s.piecewise f 0 = s.indicator f :=
rfl

@[simp] lemma indicator_zero' [has_zero β] {s : set α} : s.indicator (0 : α → β) = 0 :=
indicator_zero β s

lemma comp_indicator [has_zero β] (h : β → γ) {f : α → β} {s : set α} {x : α} :
  h (s.indicator f x) = s.piecewise (h ∘ f) (const α (h 0)) x :=
comp_piecewise h

lemma indicator_add_eq_left [add_monoid β] {f g : α → β} (h : univ ⊆ f ⁻¹' {0} ∪ g ⁻¹' {0}) :
  (f ⁻¹' {0})ᶜ.indicator (f + g) = f :=
begin
  ext x, by_cases hx : x ∈ (f ⁻¹' 0)ᶜ,
  { have : g x = 0, { simp at hx, specialize h (mem_univ x), simpa [hx] using h },
    simp [hx, this] },
  { simp * at * }
end

lemma indicator_add_eq_right [add_monoid β] {f g : α → β} (h : univ ⊆ f ⁻¹' {0} ∪ g ⁻¹' {0}) :
  (g ⁻¹' {0})ᶜ.indicator (f + g) = g :=
begin
  ext x, by_cases hx : x ∈ (g ⁻¹' 0)ᶜ,
  { have : f x = 0, { simp at hx, specialize h (mem_univ x), simpa [hx] using h },
    simp [hx, this] },
  { simp * at * }
end

end set
open set

section
variables {α β γ : Type*}


@[simp, to_additive] lemma const_one [has_one β] : const α (1 : β) = 1 :=
rfl


@[simp] lemma const_def {y : β} : (λ x : α, y) = const α y := rfl

@[simp] lemma const_apply {y : β} {x : α} : const α y x = y := rfl

@[simp] lemma comp_zero [has_zero β] {f : β → γ} : f ∘ 0 = const α (f 0) := rfl

@[simp] lemma zero_comp [has_zero γ] {f : α → β} : (0 : β → γ) ∘ f = 0 := rfl

@[simp] lemma const_comp {f : α → β} {c : γ} : const β c ∘ f = const α c := rfl

@[simp] lemma comp_const {f : β → γ} {b : β} : f ∘ const α b = const α (f b) := rfl

end

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

namespace ennreal

lemma ne_top_of_mul_ne_top_left {a b : ennreal} (h : a * b ≠ ⊤) (hb : b ≠ 0) : a ≠ ⊤ :=
by { simp [mul_eq_top, hb, not_or_distrib] at h ⊢, exact h.2 }

lemma ne_top_of_mul_ne_top_right {a b : ennreal} (h : a * b ≠ ⊤) (ha : a ≠ 0) : b ≠ ⊤ :=
ne_top_of_mul_ne_top_left (by rwa [mul_comm]) ha

lemma lt_top_of_mul_lt_top_left {a b : ennreal} (h : a * b < ⊤) (hb : b ≠ 0) : a < ⊤ :=
by { rw [ennreal.lt_top_iff_ne_top] at h ⊢, exact ne_top_of_mul_ne_top_left h hb }

lemma lt_top_of_mul_lt_top_right {a b : ennreal} (h : a * b < ⊤) (ha : a ≠ 0) : b < ⊤ :=
lt_top_of_mul_lt_top_left (by rwa [mul_comm]) ha

lemma not_lt_top {x : ennreal} : ¬ x < ⊤ ↔ x = ⊤ :=
by rw [lt_top_iff_ne_top, not_not]

end ennreal

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

lemma measurable.supr {ι α β : Type*} [encodable ι] [measurable_space α]
  [measurable_space β] [topological_space β] [second_countable_topology β] [complete_linear_order β]
  [borel_space β] [order_topology β]
  (f : ι → α → β) (h : ∀ i, measurable (f i)) : measurable (λ x, ⨆ i, f i x) :=
begin
  apply measurable_of_Iic, simp only [preimage, ←Inter_set_of, supr_le_iff, mem_Iic], intro y,
  apply is_measurable.Inter, intro i, exact h i is_measurable_Iic
end

lemma measurable.sum {ι α β} [measurable_space α] [measurable_space β] [add_comm_monoid β]
  [topological_space β] [has_continuous_add β] [borel_space β] [second_countable_topology β]
  (f : ι → α → β) (h : ∀ i, measurable (f i)) (s : finset ι) : measurable (λ x, ∑ i in s, f i x) :=
begin
  refine s.induction_on (by simp [measurable_zero]) _,
  intros i t hi hf, have := (h i).add hf, simpa [finset.sum_insert, hi]
end

/-- todo: `ennreal` can probably be generalized to a
[measurable_space β] [topological_space β] [add_comm_monoid β] [has_continuous_add β]
  [borel_space β] -/
lemma measurable.ennreal_tsum {ι α} [encodable ι] [measurable_space α]
  {f : ι → α → ennreal} (h : ∀ i, measurable (f i)) : measurable (λ x, ∑' i, f i x) :=
by { simp_rw [ennreal.tsum_eq_supr_sum], apply measurable.supr, exact measurable.sum f h }

section complete_lattice

variables {ι : Sort*} {α : Type*} {x : α} [complete_lattice α]
lemma supr_const_le : (⨆ (h : ι), x) ≤ x :=
supr_le (λ _, le_rfl)

lemma le_infi_const : x ≤ (⨅ (h : ι), x) :=
le_infi (λ _, le_rfl)

end complete_lattice




namespace measure_theory

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
  { convert le_trans _ (hs t), { simp [h] }, exact add_le_add supr_const_le supr_const_le }
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

-- lemma pi_pi_false [encodable ι] (s : Π i, set (α i))
--   (h2s : (pi univ s).nonempty) : outer_measure.pi m (pi univ s) = ∏ i, m i (s i) :=
-- begin
--   simp_rw [← pi_premeasure_pi h2s],
--   refine le_antisymm (bounded_by_le _) _,
--   refine le_binfi _, dsimp only, intros t ht,
--   sorry
--   -- refine le_trans _ (ennreal.tsum_le_tsum $ λ i, _),
-- end
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
  rw [measurable_space.comap] at hs, rcases hs with ⟨s, hs, rfl⟩,
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

-- lemma pi_pi [encodable ι] (s : Π i, set (α i)) (h1s : ∀ i, is_measurable (s i))
--   (h2s : (pi univ s).nonempty) : measure.pi μ (pi univ s) = ∏ i, μ i (s i) :=
-- begin
--   rw [measure.pi, to_measure_apply _ _ (is_measurable.pi h1s)],
--   simp_rw [← to_outer_measure_apply, ← pi_premeasure_pi h2s],
--   refine le_antisymm (bounded_by_le _) _,
--   refine le_binfi _, dsimp only, intros t ht,
--   sorry
-- end

end measure

end measure_pi

lemma indicator_comp_right {α β γ} [has_zero γ] {s : set β} (f : α → β) {g : β → γ} {x : α} :
  indicator (f ⁻¹' s) (g ∘ f) x = indicator s g (f x) :=
by { simp only [indicator], split_ifs; refl }


lemma measure_if {α β} [measurable_space α] {x : β} {t : set β} {s : set α} {μ : measure α} :
  μ (if x ∈ t then s else ∅) = indicator t (λ _, μ s) x :=
begin
  split_ifs; simp [h],
end

/-! ### Prod -/

variables {α β : Type*} [measurable_space α] [measurable_space β]

/-- x -/
def is_pi_system {α} (C : set (set α)) : Prop :=
∀ s t ∈ C, (s ∩ t : set α).nonempty → s ∩ t ∈ C

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


/--
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
lemma supr_restrict_spanning_sets {μ : measure α} [sigma_finite μ univ] {s : set α}
  (hs : is_measurable s) :
  (⨆ i, μ.restrict (spanning_sets μ univ i) s) = μ s :=
begin
  convert (restrict_Union_apply_eq_supr (is_measurable_spanning_sets μ univ) _ hs).symm,
  { simp [Union_spanning_sets] },
  { exact directed_of_sup (monotone_spanning_sets μ univ) }
end

end measure
end measure_theory

variables {α β : Type*} [measurable_space α] [measurable_space β]
  {μ : measure_theory.measure α} {ν : measure_theory.measure β}
open measure_theory measure_theory.measure

lemma is_measurable.measure_prod_mk_left_finite [finite_measure ν] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ x, ν (prod.mk x ⁻¹' s)) :=
begin
  refine induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ hs,
  { simp [measurable_zero] },
  { rintro _ ⟨s, t, hs, ht, rfl⟩, simp only [mk_preimage_prod_right_eq_if, measure_if],
    exact measurable_const.indicator hs },
  { intros t ht h2t,
    simp_rw [preimage_compl, measure_compl (measurable_prod_mk_left ht) (measure_lt_top ν _)],
    exact measurable_const.ennreal_sub h2t },
  { intros f h1f h2f h3f, simp_rw [preimage_Union],
    have : ∀ b, ν (⋃ i, prod.mk b ⁻¹' f i) = ∑' i, ν (prod.mk b ⁻¹' f i) :=
      λ b, measure_Union (λ i j hij, disjoint.preimage _ (h1f i j hij))
        (λ i, measurable_prod_mk_left (h2f i)),
    simp_rw [this], apply measurable.ennreal_tsum h3f },
end

lemma is_measurable.measure_prod_mk_left [sigma_finite ν univ] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ x, ν (prod.mk x ⁻¹' s)) :=
begin
  have : ∀ x, is_measurable (prod.mk x ⁻¹' s) := λ x, measurable_prod_mk_left hs,
  simp only [← supr_restrict_spanning_sets, this],
  apply measurable.supr, intro i,
  haveI : fact _ := measure_spanning_sets_lt_top ν univ i,
  exact hs.measure_prod_mk_left_finite
end

lemma measurable.map_prod_mk_left [sigma_finite ν univ] : measurable (λ x : α, map (prod.mk x) ν) :=
begin
  apply measurable_of_measurable_coe, intros s hs,
  simp_rw [map_apply measurable_prod_mk_left hs],
  exact hs.measure_prod_mk_left
end

/- Is there a way to do this without duplicating? -/
lemma is_measurable.measure_prod_mk_right_finite {μ : measure α} [finite_measure μ] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ y, μ ((λ x, (x, y)) ⁻¹' s)) :=
begin
  refine induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ hs,
  { simp [measurable_zero] },
  { rintro _ ⟨s, t, hs, ht, rfl⟩, simp only [mk_preimage_prod_left_eq_if, measure_if],
    exact measurable_const.indicator ht },
  { intros t ht h2t,
    simp_rw [preimage_compl, measure_compl (measurable_prod_mk_right ht) (measure_lt_top μ _)],
    exact measurable_const.ennreal_sub h2t },
  { intros f h1f h2f h3f, simp_rw [preimage_Union],
    have : ∀ y, μ (⋃ i, (λ x, (x, y)) ⁻¹' f i) = ∑' i, μ ((λ x, (x, y)) ⁻¹' f i) :=
      λ y, measure_Union (λ i j hij, disjoint.preimage _ (h1f i j hij))
        (λ i, measurable_prod_mk_right (h2f i)),
    simp_rw [this], apply measurable.ennreal_tsum h3f },
end

lemma is_measurable.measure_prod_mk_right {μ : measure α} [sigma_finite μ univ] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ y, μ ((λ x, (x, y)) ⁻¹' s)) :=
begin
  have : ∀ y, is_measurable ((λ x, (x, y)) ⁻¹' s) := λ y, measurable_prod_mk_right hs,
  simp only [← supr_restrict_spanning_sets, this],
  apply measurable.supr, intro i,
  haveI : fact _ := measure_spanning_sets_lt_top μ univ i,
  exact hs.measure_prod_mk_right_finite
end

lemma measurable.map_prod_mk_right {μ : measure α} [sigma_finite μ univ] :
  measurable (λ y : β, map (λ x : α, (x, y)) μ) :=
begin
  apply measurable_of_measurable_coe, intros s hs,
  simp_rw [map_apply measurable_prod_mk_right hs],
  exact hs.measure_prod_mk_right
end

namespace measure_theory
namespace measure

/-- The product of two measures. -/
protected def prod (μ : measure α) (ν : measure β) : measure (α × β) :=
bind μ $ λ x : α, map (prod.mk x) ν

/-- The symmetric version of the product of two measures. -/
protected def prod_symm (μ : measure α) (ν : measure β) : measure (α × β) :=
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

-- def directed_supr {ι} [nonempty ι] [partial_order ι] {μ : ι → measure α} (hμ : monotone μ) :
--   measure α :=
-- begin
--   apply measure.of_measurable (λ s _, ⨆ i, μ i s) (by simp),
--   sorry
-- end


/-- A directed supremum of measures applied is evaluated as a supremum on `ennreal`. -/
-- lemma supr_apply_of_monotone {ι} [partial_order ι] {μ : ι → measure α} (hμ : monotone μ)
--   {s : set α} (hs : is_measurable s) : (⨆ i, μ i) s = ⨆ i, μ i s :=
-- begin
--   refine le_antisymm _ _,
--   { sorry },
--   { refine supr_le _, intro i, exact (le_supr μ i : _) s hs },
-- end

-- lemma supr_restrict {ι} [encodable ι] {μ : measure α} {t : ι → set α} :
--   (⨆ i, μ.restrict (t i)) = μ.restrict (⋃ i, t i) :=
-- begin
--   ext s hs, rw [restrict_Union_apply_eq_supr],
-- end

/- todo: rename set.disjoint.preimage -> disjoint.preimage -/


lemma prod_apply [sigma_finite ν univ] {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ x, ν (prod.mk x ⁻¹' s) ∂μ :=
begin
  rw [measure.prod, bind_apply hs],
  congr, ext x : 1, rw [map_apply _ hs],
  apply measurable_prod_mk_left,
  exact measurable.map_prod_mk_left
end

@[simp] lemma prod_prod [sigma_finite ν univ] {s : set α} {t : set β}
  (hs : is_measurable s) (ht : is_measurable t) : μ.prod ν (s.prod t) = μ s * ν t :=
by simp_rw [prod_apply (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
  lintegral_indicator _ hs, lintegral_const, restrict_apply is_measurable.univ,
  univ_inter, mul_comm]

@[simp] lemma prod_symm_apply [sigma_finite μ univ] {s : set (α × β)} (hs : is_measurable s) :
  μ.prod_symm ν s = ∫⁻ y, μ ((λ x, (x, y)) ⁻¹' s) ∂ν :=
begin
  rw [measure.prod_symm, bind_apply hs],
  congr, ext x : 1, rw [map_apply _ hs],
  apply measurable_prod_mk_right,
  exact measurable.map_prod_mk_right
end

@[simp] lemma prod_symm_prod [sigma_finite μ univ] {s : set α} {t : set β}
  (hs : is_measurable s) (ht : is_measurable t) : μ.prod_symm ν (s.prod t) = μ s * ν t :=
by simp_rw [prod_symm_apply (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
  lintegral_indicator _ ht, lintegral_const, restrict_apply is_measurable.univ, univ_inter]

section both_sigma_finite

variables [sigma_finite μ univ] [sigma_finite ν univ]

lemma prod_unique {μν₁ μν₂ : measure (α × β)}
  (h₁ : ∀ s t, is_measurable s → is_measurable t → μν₁ (s.prod t) = μ s * ν t)
  (h₂ : ∀ s t, is_measurable s → is_measurable t → μν₂ (s.prod t) = μ s * ν t) : μν₁ = μν₂ :=
begin
  refine ext_of_generate_from_of_Union _
    (λ i, (spanning_sets μ univ i).prod (spanning_sets ν univ i))
    generate_from_prod.symm is_pi_system_prod _ _ _ _,
  { rw [Union_prod_of_monotone (monotone_spanning_sets μ _) (monotone_spanning_sets ν _)],
    simp_rw [Union_spanning_sets, univ_prod_univ] },
  { intro i, apply mem_image2_of_mem; apply is_measurable_spanning_sets },
  { intro i, rw [h₁], apply ennreal.mul_lt_top; apply measure_spanning_sets_lt_top,
    all_goals { apply is_measurable_spanning_sets } },
  { rintro _ ⟨s, t, hs, ht, rfl⟩, simp * at * }
end

lemma prod_eq_prod_symm : μ.prod ν = μ.prod_symm ν :=
prod_unique (λ _ _, prod_prod) (λ _ _, prod_symm_prod)

lemma prod_apply_symm {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ y, μ ((λ x, (x, y)) ⁻¹' s) ∂ν :=
by simp [prod_eq_prod_symm, prod_symm_apply, hs]

end both_sigma_finite

end measure
open measure
-- @[elab_as_eliminator]
-- theorem finset.induction_subsingleton {α : Type*} {p : finset α → Prop} [decidable_eq α]
--   (h₁ : ∀ s x, s ⊆ {x} → p s)
--   (h₂ : ∀ ⦃x a : α⦄ {s : finset α}, x ∈ s → a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
-- begin
--   refine finset.induction _ _,
--   { exact },
--   { }
-- end


section simple_func
open simple_func finset

@[elab_as_eliminator]
lemma simple_func.induction {γ} [add_monoid γ] {P : simple_func α γ → Prop}
  (h_ind : ∀ c {s} (hs : is_measurable s),
    P (simple_func.piecewise s hs (simple_func.const _ c) (simple_func.const _ 0)))
  (h_sum : ∀ ⦃f g : simple_func α γ⦄, set.univ ⊆ f ⁻¹' {0} ∪ g ⁻¹' {0} → P f → P g → P (f + g))
  (f : simple_func α γ) : P f :=
begin
  generalize' h : f.range \ {0} = s,
  rw [← finset.coe_inj, finset.coe_sdiff, finset.coe_singleton, simple_func.coe_range] at h,
  revert s f h, refine finset.induction _ _,
  { intros f hf, rw [finset.coe_empty, diff_eq_empty, range_subset_singleton] at hf,
    convert h_ind 0 is_measurable.univ, ext x, simp [hf] },
  { intros x s hxs ih f hf,
    have mx := f.is_measurable_preimage {x},
    let g := simple_func.piecewise (f ⁻¹' {x}) mx 0 f,
    have Pg : P g,
    { apply ih, simp only [g, simple_func.coe_piecewise, range_piecewise],
      rw [image_compl_preimage', union_diff_distrib, diff_diff_comm, hf, finset.coe_insert,
        insert_diff_self_of_not_mem, diff_eq_empty.mpr, set.empty_union],
      { rw [set.image_subset_iff], convert set.subset_univ _,
        exact preimage_const_of_mem (mem_singleton _) },
      { rwa [finset.mem_coe] }},
    convert h_sum _ Pg (h_ind x mx),
    { ext1 y, by_cases hy : y ∈ f ⁻¹' {x}; [simpa [hy], simp [hy]] },
    { rintro y -, by_cases hy : y ∈ f ⁻¹' {x}; simp [hy] }}
end

-- /- deprecated -/
-- @[elab_as_eliminator]
-- lemma simple_func.induction2 {γ} [add_monoid γ] (P : (α → γ) → Prop)
--   (h_ind : ∀ c {s}, is_measurable s → P (indicator s (λ _, c)))
--   (h_sum : ∀ ⦃f g⦄, P f → P g → P (f + g)) (f : simple_func α γ) : P f :=
-- simple_func.induction h_ind (λ f g hf hg, h_sum hf hg) f

-- /- deprecated -/
-- @[elab_as_eliminator]
-- lemma simple_func.induction3 {γ} [measurable_space γ] [add_monoid γ]
--   (P : (α → γ) → Prop) (h_ind : ∀ (c : γ) ⦃s⦄, is_measurable s → P (indicator s (λ _, c)))
--   (h_sum : ∀ ⦃f g⦄, measurable f → measurable g → P f → P g → P (f + g))
--   (f : simple_func α γ) : P f :=
-- simple_func.induction h_ind (λ f g hf hg, h_sum f.measurable g.measurable hf hg) f

end simple_func
end measure_theory
open measure_theory measure_theory.measure
section simple_func
open measure_theory.simple_func

lemma measurable.ennreal_induction {P : (α → ennreal) → Prop}
  (h_ind : ∀ (c : ennreal) ⦃s⦄, is_measurable s → P (indicator s (λ _, c)))
  (h_sum : ∀ ⦃f g⦄, measurable f → measurable g → P f → P g → P (f + g))
  (h_supr : ∀ ⦃f : ℕ → α → ennreal⦄ (hf : ∀n, measurable (f n)) (h_mono : monotone f)
    (hP : ∀ n, P (f n)), P (λ x, ⨆ n, f n x))
  ⦃f : α → ennreal⦄ (hf : measurable f) : P f :=
begin
  convert h_supr (λ n, (simple_func.eapprox f n).measurable) (simple_func.monotone_eapprox f) _,
  { ext1 x, rw [simple_func.supr_eapprox_apply f hf] },
  { exact λ n, simple_func.induction (λ c s hs, h_ind c hs)
      (λ f g _ hf hg, h_sum f.measurable g.measurable hf hg) (eapprox f n) }
end

end simple_func

lemma measurable.ennreal_induction' {P : (α → ennreal) → Prop}
  (h_ind : ∀ ⦃s⦄, is_measurable s → P (indicator s 1))
  (h_sum : ∀ ⦃f g⦄, measurable f → measurable g → P f → P g → P (f + g))
  (h_smul : ∀ (c : ennreal) ⦃f⦄, measurable f → P f → P (c • f))
  (h_supr : ∀ ⦃f : ℕ → α → ennreal⦄ (hf : ∀n, measurable (f n)) (h_mono : monotone f)
    (hP : ∀ n, P (f n)), P (λ x, ⨆ n, f n x))
  ⦃f : α → ennreal⦄ (hf : measurable f) : P f :=
begin
  refine hf.ennreal_induction _ h_sum h_supr,
  intros c s hs, convert h_smul c (measurable_one.indicator hs) (h_ind hs),
  ext1 x, simp [indicator]
end

/-- The Lebesgue intergral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable. -/
lemma measurable.lintegral_prod_right [sigma_finite ν univ] :
  ∀ {f : α × β → ennreal} (hf : measurable f), measurable (λ x, ∫⁻ y, f (x, y) ∂ν) :=
begin
  have m := @measurable_prod_mk_left,
  refine measurable.ennreal_induction _ _ _,
  { intros c s hs, simp only [← indicator_comp_right],
    suffices : measurable (λ x, c * ν (prod.mk x ⁻¹' s)),
    { simpa [lintegral_indicator _ (m hs)] },
    exact measurable_const.ennreal_mul hs.measure_prod_mk_left },
  { intros f g hf hg h2f h2g, simp [lintegral_add (hf.comp m) (hg.comp m)], exact h2f.add h2g },
  { intros f hf h2f h3f,
    have := measurable_supr h3f,
    have : ∀ x, monotone (λ n y, f n (x, y)) := λ x i j hij y, h2f hij (x, y),
    simpa [lintegral_supr (λ n, (hf n).comp m), this] }
end

/-- The Lebesgue intergral is measurable This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable. -/
lemma measurable.lintegral_prod_left [sigma_finite μ univ] :
  ∀ {f : α × β → ennreal} (hf : measurable f), measurable (λ y, ∫⁻ x, f (x, y) ∂μ) :=
begin
  have m := @measurable_prod_mk_right,
  refine measurable.ennreal_induction _ _ _,
  { intros c s hs, simp only [(show (_, _) = (λ x, (x, _)) _, from rfl), ← indicator_comp_right]
      {single_pass := tt, beta := ff},
    suffices : measurable (λ y, c * μ ((λ x, (x, y)) ⁻¹' s)),
    { simpa [function.comp, lintegral_indicator _ (m hs)] },
    exact measurable_const.ennreal_mul hs.measure_prod_mk_right },
  { intros f g hf hg h2f h2g, simp [lintegral_add (hf.comp m) (hg.comp m)], exact h2f.add h2g },
  { intros f hf h2f h3f,
    have := measurable_supr h3f,
    have : ∀ y, monotone (λ n x, f n (x, y)) := λ y i j hij x, h2f hij (x, y),
    simpa [lintegral_supr (λ n, (hf n).comp m), this] },
end

variables {E : Type*} [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [measurable_space E] [borel_space E]

namespace measure_theory
/-- Tonelli's Theorem: For `ennreal`-valued measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
lemma lintegral_prod [sigma_finite ν univ] :
  ∀ (f : α × β → ennreal) (hf : measurable f), ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
begin
  have m := @measurable_prod_mk_left,
  refine measurable.ennreal_induction _ _ _,
  { intros c s hs, simp only [← indicator_comp_right],
    simp [lintegral_indicator, m hs, hs, lintegral_const_mul, hs.measure_prod_mk_left,
      prod_apply] },
  { intros f g hf hg h2f h2g,
    simp [lintegral_add, hf.comp m, hg.comp m, h2f, h2g, measurable.lintegral_prod_right, hf, hg] },
  { intros f hf h2f h3f,
    have kf : ∀ x n, measurable (λ y, f n (x, y)) := λ x n, (hf n).comp m,
    have k2f : ∀ x, monotone (λ n y, f n (x, y)) := λ x i j hij y, h2f hij (x, y),
    have lf : ∀ n, measurable (λ x, ∫⁻ y, f n (x, y) ∂ν) :=
      λ n, measurable.lintegral_prod_right (hf n),
    have l2f : monotone (λ n x, ∫⁻ y, f n (x, y) ∂ν) := λ i j hij x, lintegral_mono (k2f x hij),
    simp only [lintegral_supr hf h2f, lintegral_supr (kf _), k2f, lintegral_supr lf l2f, h3f] },
end

/-- The symmetric verion of Tonelli's Theorem: For `ennreal`-valued measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral, in reverse order. -/
lemma lintegral_prod_symm [sigma_finite ν univ] [sigma_finite μ univ] :
  ∀ (f : α × β → ennreal) (hf : measurable f), ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
begin
  have m := @measurable_prod_mk_right,
  refine measurable.ennreal_induction _ _ _,
  { intros c s hs, simp only [(show (_, _) = (λ x, (x, _)) _, from rfl), ← indicator_comp_right]
      {single_pass := tt, beta := ff},
    simp [lintegral_indicator, m hs, hs, lintegral_const_mul, hs.measure_prod_mk_right,
      prod_apply_symm] },
  { intros f g hf hg h2f h2g,
    simp [lintegral_add, hf.comp m, hg.comp m, h2f, h2g, measurable.lintegral_prod_left, hf, hg] },
  { intros f hf h2f h3f,
    have kf : ∀ y n, measurable (λ x, f n (x, y)) := λ y n, (hf n).comp m,
    have k2f : ∀ y, monotone (λ n x, f n (x, y)) := λ y i j hij x, h2f hij (x, y),
    have lf : ∀ n, measurable (λ y, ∫⁻ x, f n (x, y) ∂μ) := λ n, (hf n).lintegral_prod_left,
    have l2f : monotone (λ n y, ∫⁻ x, f n (x, y) ∂μ) := λ i j hij y, lintegral_mono (k2f y hij),
    simp only [lintegral_supr hf h2f, lintegral_supr (kf _), k2f, lintegral_supr lf l2f, h3f] },
end

/-- The reversed version of Tonelli's Theorem. -/
lemma lintegral_lintegral [sigma_finite ν univ] ⦃f : α → β → ennreal⦄
  (hf : measurable (λ z : α × β, f z.1 z.2)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.1 z.2 ∂(μ.prod ν) :=
(lintegral_prod _ hf).symm

-- variables {G : Type*} [measurable_space β] [normed_group G]

lemma ae_lt_top {f : α → ennreal} (hf : measurable f)
  (h2f : ∫⁻ x, f x ∂μ < ⊤) : ∀ᵐ x ∂μ, f x < ⊤ :=
begin
  simp_rw [ae_iff, ennreal.not_lt_top], by_contra h, rw [← not_le] at h2f, apply h2f,
  have : (f ⁻¹' {⊤}).indicator ⊤ ≤ f,
  { intro x, by_cases hx : x ∈ f ⁻¹' {⊤}; [simpa [hx], simp [hx]] },
  convert lintegral_mono this,
  rw [lintegral_indicator _ (hf (is_measurable_singleton ⊤))], simp [ennreal.top_mul, preimage, h]
end

lemma integrable.prod_left [sigma_finite μ univ] [sigma_finite ν univ] ⦃f : α × β → E⦄
  (h1f : measurable f) (h2f : integrable f (μ.prod ν)) : ∀ᵐ y ∂ ν, integrable (λ x, f (x, y)) μ :=
begin
  refine ae_lt_top h1f.ennnorm.lintegral_prod_left _,
  simp_rw [← lintegral_prod_symm _ h1f.ennnorm], exact h2f,
end

lemma integrable.prod_right [sigma_finite ν univ] ⦃f : α × β → E⦄ (h1f : measurable f)
  (h2f : integrable f (μ.prod ν)) : ∀ᵐ x ∂ μ, integrable (λ y, f (x, y)) ν :=
begin
  refine ae_lt_top h1f.ennnorm.lintegral_prod_right _,
  simp_rw [← lintegral_prod _ h1f.ennnorm], exact h2f
end

end measure_theory

/- rename `to_fun_of_fun` to `coe_of_fun` (in `l1`) -/


lemma integrable_add {f g : α → E} (h : univ ⊆ f ⁻¹' {0} ∪ g ⁻¹' {0})
  (hf : measurable f) (hg : measurable g) :
  integrable (f + g) μ ↔ integrable f μ ∧ integrable g μ :=
begin
  refine ⟨λ hfg, _, λ h, h.1.add hf hg h.2⟩,
  rw [← indicator_add_eq_left h],
  conv { congr, skip, rw [← indicator_add_eq_right h] },
  rw [integrable_indicator_iff (hf (is_measurable_singleton 0)).compl],
  rw [integrable_indicator_iff (hg (is_measurable_singleton 0)).compl],
  exact ⟨hfg.integrable_on, hfg.integrable_on⟩
end

lemma integrable.induction {P : (α → E) → Prop}
  (h_ind : ∀ (c : E) ⦃s⦄, is_measurable s → μ s < ⊤ → P (s.indicator (λ _, c)))
  (h_sum : ∀ ⦃f g⦄, measurable f → measurable g → integrable f μ → integrable g μ → P f → P g → P (f + g))
  (h_closed : is_closed {f : α →₁[μ] E | P f} )
  (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → measurable f → measurable g → integrable f μ → P f → P g) :
  ∀ ⦃f : α → E⦄ (hf : measurable f) (h2f : integrable f μ), P f :=
begin
  have : ∀ (f : simple_func α E), integrable f μ → P f,
  { refine simple_func.induction _ _,
    { intros c s hs h, dsimp at h ⊢,
      by_cases hc : c = 0,
      { subst hc, convert h_ind 0 is_measurable.empty (by simp) using 1, simp },
      apply h_ind c hs,
      have := @comp_indicator _ _ _ _ (λ x : E, (nnnorm x : ennreal)) (const α c), dsimp at this,
      simp [integrable, this, lintegral_indicator, hs] at h,
      exact ennreal.lt_top_of_mul_lt_top_right h (by simp [hc]) },
    { intros f g hfg hf hg int_fg, dsimp at int_fg,
      rw [integrable_add hfg f.measurable g.measurable] at int_fg,
      refine h_sum f.measurable g.measurable int_fg.1 int_fg.2 (hf int_fg.1) (hg int_fg.2) } },
  have : ∀ (f : α →₁ₛ[μ] E), P f,
  { intro f, exact h_ae f.to_simple_func_eq_to_fun f.measurable (l1.measurable _) f.integrable
      (this f.to_simple_func f.integrable) },
  have : ∀ (f : α →₁[μ] E), P f :=
    λ f, l1.simple_func.dense_range.induction_on f h_closed this,
  exact λ f hf h2f, h_ae (l1.to_fun_of_fun f hf h2f) (l1.measurable _) hf (l1.integrable _)
    (this (l1.of_fun f hf h2f))
end


-- lemma integrable.induction {P : (α → E) → Prop}
--   (h_ind : ∀ (c : E) ⦃s⦄, is_measurable s → integrable (indicator s (λ _, c)) μ → P (indicator s (λ _, c)))
--   (h_sum : ∀ ⦃f g⦄, measurable f → integrable f μ → measurable g → integrable g μ → P f → P g →
--     P (f + g))
--   (h_closed : is_closed {f : α →₁[μ] E | P f} )
--   (h_ae : ∀ ⦃f g⦄, f =ᵐ[μ] g → P f → P g) :
--   ∀ ⦃f : α → E⦄ (hf : measurable f) (h2f : integrable f μ), P f :=
-- begin
--   have : ∀ (f : simple_func α E), integrable f μ → P f,
--   { refine simple_func.induction _ _,
--     { exact h_ind  },
--     { },
--     --
--       },
--   have : ∀ (f : α →₁ₛ[μ] E), P f,
--   { intro f, exact h_ae f.to_simple_func_eq_to_fun (this f.to_simple_func) },
--   have : ∀ (f : α →₁[μ] E), P f :=
--     λ f, l1.simple_func.dense_range.induction_on f h_closed this,
--   exact h_ae (l1.to_fun_of_fun f hf h2f) (this (l1.of_fun f hf h2f))
-- end

-- lemma integral_indicator (f : α → E) {s : set α} (hs : is_measurable s) :
--   ∫ x, s.indicator f x ∂μ = ∫ x in s, f x ∂μ :=
-- begin
--   sorry
-- end

lemma measurable.congr' {f g : α → β} {s : set α} {y : β} (hs : is_measurable s)
  (h : ∀ x ∈ s, f x = g x) (hg : measurable g) (hf : ∀ x ∉ s, f x = y)
  : measurable f :=
begin
  intros t ht,
  by_cases hy : y ∈ t,
  { convert (hg ht).union hs.compl, ext x, by_cases hx : x ∈ s; simp * },
  { convert (hg ht).inter hs, ext x, by_cases hx : x ∈ s; simp * }
end

-- lemma measurable_integral_congr_ae {f : α × β → E} {h : α → E}
--   (h : integrable)
--    (hg : measurable (λ x, ∫ y, g (x, y) ∂ν)) :
--     measurable (λ x, ∫ y, f (x, y) ∂ν) :=
-- begin

-- end
--

lemma measurable_to_real : measurable ennreal.to_real :=
begin
  sorry
end
/-- The Bochner intergral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable. -/
lemma measurable.integral_prod_left [sigma_finite ν univ] :
  ∀ ⦃f : α × β → E⦄ (h1f : measurable f) (h2f : integrable f (μ.prod ν)),
    measurable (λ x, ∫ y, f (x, y) ∂ν) :=
begin
  have m := @measurable_prod_mk_left,
  refine integrable.induction _ _ _ _,
  { intros c s hs h,
    have : measurable (λ (x : α), (ν (prod.mk x ⁻¹' s)).to_real • c) :=
      (measurable_to_real.comp hs.measure_prod_mk_left).smul measurable_const,
    simpa [← indicator_comp_right, integral_indicator measurable_const (m hs)] {eta := ff} },
    /-
α : Type u_1,
β : Type u_2,
_inst_1 : measurable_space α,
_inst_2 : measurable_space β,
μ : measure α,
ν : measure β,
E : Type u_3,
_inst_3 : normed_group E,
_inst_4 : second_countable_topology E,
_inst_5 : normed_space ℝ E,
_inst_6 : complete_space E,
_inst_7 : measurable_space E,
_inst_8 : borel_space E,
_inst_9 : sigma_finite ν univ,
m :
  ∀ {α : Type u_1} {β : Type u_2} [_inst_1 : measurable_space α] [_inst_2 : measurable_space β] {x : α},
    measurable (prod.mk x),
f g : α × β → E,
hf : measurable f,
hg : measurable g,
h2f : integrable f (μ.prod ν),
h2g : integrable g (μ.prod ν),
h3f : measurable (λ (x : α), ∫ (y : β), f (x, y) ∂ν),
h3g : measurable (λ (x : α), ∫ (y : β), g (x, y) ∂ν),
this : measurable (λ (a : α), ∫ (y : β), f (a, y) ∂ν + ∫ (y : β), g (a, y) ∂ν)
⊢ measurable (λ (x : α), ∫ (y : β), (f + g) (x, y) ∂ν)
-/

  { intros f g hf hg h2f h2g h3f h3g, have := h3f.add h3g, dsimp at this,
    -- refine (h3f.add h3g).congr' _ _ _,
    ext1 x, apply integral_add (hf.comp m) _ (hg.comp m) _, }
  -- { intros f hf h2f h3f,
  --   have : ∀ x, monotone (λ n y, f n (x, y)) := λ x i j hij y, h2f hij (x, y),
  --   simp [lintegral_supr (λ n, (hf n).comp m), this],
  --   exact measurable_supr h3f },
  -- { },
  -- { },
  -- { },
  -- { }
end

/-- Fubini's Theorem: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral. -/
lemma integrable_integral_prod_left [sigma_finite ν univ] :
  ∀ ⦃f : α × β → E⦄ (h1f : measurable f) (h2f : integrable f (μ.prod ν)),
    measurable (λ x, ∫ y, f (x, y) ∂ν) :=
begin
  sorry
end

/-- Fubini's Theorem: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral. -/
lemma integral_prod [sigma_finite ν univ] :
  ∀ ⦃f : α × β → E⦄ (h1f : measurable f) (h2f : integrable f (μ.prod ν)),
  ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
begin
  sorry
end

end measure

end

end measure_theory
