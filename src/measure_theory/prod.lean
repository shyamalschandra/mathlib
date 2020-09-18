/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.giry_monad
import measure_theory.set_integral

/-!
# The product measure space

TODO:

Define finite (and countably infinite) product measure
Fubini's theorem

-/
noncomputable theory
open_locale classical big_operators nnreal
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

-- lemma if_eq_piecewise {α : Type*} {β : α → Sort*} (p : α → Prop) (f g : Πi, β i) [decidable_pred p] :
--   (λ x, if p x then f x else g x) = {x | p x}.piecewise f g :=
-- rfl

end set
open set

section
variables {α β γ : Type*}

-- done
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

end canonically_ordered_semiring

namespace finset

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` is at least the sum of the
  products of `g` and `h`. This is the version for `linear_ordered_comm_ring`. -/
lemma prod_univ_add_prod_univ_le {α β} [fintype α] [linear_ordered_comm_ring β] (i : α)
  {f g h : α → β} (h2i : g i + h i ≤ f i) (hgf : ∀ j ≠ i, g j ≤ f j)
  (hhf : ∀ j ≠ i, h j ≤ f j) (hg : ∀ i, 0 ≤ g i) (hh : ∀ i, 0 ≤ h i) :
  ∏ i, g i + ∏ i, h i ≤ ∏ i, f i :=
prod_add_prod_le (mem_univ i) h2i (λ j _, hgf j) (λ j _, hhf j) (λ j _, hg j) (λ j _, hh j)

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` is at least the sum of the
  products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`. -/
lemma prod_univ_add_prod_univ_le' {α β} [fintype α] [canonically_ordered_comm_semiring β] (i : α)
  {f g h : α → β} (h2i : g i + h i ≤ f i) (hgf : ∀ j ≠ i, g j ≤ f j)
  (hhf : ∀ j ≠ i, h j ≤ f j) : ∏ i, g i + ∏ i, h i ≤ ∏ i, f i :=
prod_add_prod_le' (mem_univ i) h2i (λ j _, hgf j) (λ j _, hhf j)

end finset

namespace ennreal

end ennreal

section filter

open filter
variables {α β : Type*} [topological_space α] [conditionally_complete_linear_order α] [order_topology α]
open_locale topological_space

-- todo: replace
/-- If a function has a limit, then its limsup coincides with its limit. -/
theorem filter.tendsto.limsup_eq' {f : filter β} {u : β → α} {a : α} [ne_bot f]
  (h : tendsto u f (𝓝 a)) : limsup f u = a :=
Limsup_eq_of_le_nhds h

/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem filter.tendsto.liminf_eq' {f : filter β} {u : β → α} {a : α} [ne_bot f]
  (h : tendsto u f (𝓝 a)) : liminf f u = a :=
Liminf_eq_of_le_nhds h

end filter

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
#print is_measurable.bInter

-- #print is_rational

-- section
-- open filter
-- lemma has_countable_basis_at_top_ennreal :
--   has_countable_basis (at_top : filter ennreal) (λ x : ennreal, x.to_real ∈ range (coe : ℚ → ℝ)) Iic :=
-- _

-- lemma countable_basis_elim {ι ι' α β : Type*} [preorder ι] [preorder β] {p : ι' → Prop} {q : ι' → ι}
--   (h : has_countable_basis (at_top : filter ι) p (Iic ∘ q)) (f : ι → α → β) {y : β} :
--   (⋂ (i : ι), {x : α | f i x ≤ y}) = (⋂ (i' : ι') (h : p i'), {x : α | f (q i') x ≤ y}) :=
-- begin

-- end


-- lemma measurable_supr' {ι ι' α β : Type*} [preorder ι] {p : ι' → Prop} {q : ι' → set ι}
--   (h : has_countable_basis (at_top : filter ι) p q) [measurable_space α]
--   [measurable_space β] [topological_space β] [second_countable_topology β] [complete_linear_order β]
--   [borel_space β] [order_topology β]
--   (f : ι → α → β) (h : ∀ i, measurable (f i)) : measurable (λ x, ⨆ i, f i x) :=
-- begin
--   apply measurable_of_Iic, simp only [preimage, ←Inter_set_of, supr_le_iff, mem_Iic], intro y,
--   sorry
--   -- apply is_measurable.Inter, intro i, exact h i is_measurable_Iic
-- end

-- lemma measurable_infi' {ι α β : Type*} [encodable ι] [measurable_space α]
--   [measurable_space β] [topological_space β] [second_countable_topology β] [complete_linear_order β]
--   [borel_space β] [order_topology β]
--   (f : ι → α → β) (h : ∀ i, measurable (f i)) : measurable (λ x, ⨅ i, f i x) :=
-- begin
--   apply measurable_of_Ici, simp only [preimage, ←Inter_set_of, le_infi_iff, mem_Ici], intro y,
--   apply is_measurable.Inter, intro i, exact h i is_measurable_Ici
-- end

-- end

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
by { simp_rw [ennreal.tsum_eq_supr_sum], apply measurable_supr, exact measurable.sum f h }
















section complete_lattice

variables {ι : Sort*} {α : Type*} {x : α} [complete_lattice α]
lemma supr_const_le : (⨆ (h : ι), x) ≤ x :=
supr_le (λ _, le_rfl)

lemma le_infi_const : x ≤ (⨅ (h : ι), x) :=
le_infi (λ _, le_rfl)

end complete_lattice

section metric
open metric emetric
variables {α : Type*} [metric_space α] {x : α} {s : set α}

/-- The minimal distance of a point to a set as a `nnreal` -/
def inf_nndist (x : α) (s : set α) : ℝ≥0 := ennreal.to_nnreal (inf_edist x s)
@[simp] lemma coe_inf_nndist : (inf_nndist x s : ℝ) = inf_dist x s := rfl

@[simp] lemma inf_nndist_eq_zero : (inf_nndist x s : ℝ) = inf_dist x s := rfl

/-- The minimal distance to a set (as `nnreal`) is Lipschitz in point with constant 1 -/
lemma lipschitz_inf_nndist_pt (s : set α) : lipschitz_with 1 (λx, inf_nndist x s) :=
lipschitz_with.of_le_add $ λ x y, inf_dist_le_inf_dist_add_dist

/-- The minimal distance to a set (as `nnreal`) is uniformly continuous in point -/
lemma uniform_continuous_inf_nndist_pt (s : set α) :
  uniform_continuous (λx, inf_nndist x s) :=
(lipschitz_inf_nndist_pt s).uniform_continuous

/-- The minimal distance to a set (as `nnreal`) is continuous in point -/
lemma continuous_inf_nndist_pt (s : set α) : continuous (λx, inf_nndist x s) :=
(uniform_continuous_inf_nndist_pt s).continuous


end metric

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
  { simp [image_inter_preimage, image_diff_preimage, (μ i).caratheodory hs, le_refl] },
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
open measure_theory




section measurable


variables {α β γ: Type*} [measurable_space α] [measurable_space β] [measurable_space γ]

lemma measurable.of_uncurry_left {f : α → β → γ} (hf : measurable (uncurry f)) {x : α} :
  measurable (f x) :=
hf.comp measurable_prod_mk_left

lemma measurable.of_uncurry_right {f : α → β → γ} (hf : measurable (uncurry f)) {y : β} :
  measurable (λ x, f x y) :=
hf.comp measurable_prod_mk_right

end measurable







variables {α β : Type*} [measurable_space α] [measurable_space β]
  {μ : measure_theory.measure α} {ν : measure_theory.measure β}
open measure_theory.measure

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
  apply measurable_supr, intro i,
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
  apply measurable_supr, intro i,
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

end simple_func

lemma measurable.ennreal_induction' {P : (α → ennreal) → Prop}
  (h_ind : ∀ ⦃s⦄, is_measurable s → P (indicator s 1))
  (h_sum : ∀ ⦃f g : α → ennreal⦄, set.univ ⊆ f ⁻¹' {0} ∪ g ⁻¹' {0} → measurable f → measurable g →
    P f → P g → P (f + g))
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
  { rintro f g - hf hg h2f h2g, simp [lintegral_add (hf.comp m) (hg.comp m)], exact h2f.add h2g },
  { intros f hf h2f h3f,
    have := measurable_supr h3f,
    have : ∀ x, monotone (λ n y, f n (x, y)) := λ x i j hij y, h2f hij (x, y),
    simpa [lintegral_supr (λ n, (hf n).comp m), this] }
end

lemma measurable.lintegral_prod_right' [sigma_finite ν univ] {f : α → β → ennreal}
  (hf : measurable (uncurry f)) : measurable (λ x, ∫⁻ y, f x y ∂ν) :=
hf.lintegral_prod_right

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
  { rintro f g - hf hg h2f h2g, simp [lintegral_add (hf.comp m) (hg.comp m)], exact h2f.add h2g },
  { intros f hf h2f h3f,
    have := measurable_supr h3f,
    have : ∀ y, monotone (λ n x, f n (x, y)) := λ y i j hij x, h2f hij (x, y),
    simpa [lintegral_supr (λ n, (hf n).comp m), this] },
end

section

variables {δ : Type*} [measurable_space δ] [measurable_space α] [topological_space α] [borel_space α]

-- use in integrable_add
@[to_additive]
lemma measurable.mul' [has_mul α] [has_continuous_mul α] [second_countable_topology α]
  {f : δ → α} {g : δ → α} : measurable f → measurable g → measurable (f * g) :=
measurable.mul

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
  { rintro f g - hf hg h2f h2g,
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
  { rintro f g - hf hg h2f h2g,
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
  (hf : measurable (uncurry f)) :
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
  (hf : integrable f (μ.prod ν)) : ∀ᵐ y ∂ ν, integrable (λ x, f (x, y)) μ :=
begin
  simp [integrable, and_iff_right (hf.measurable.comp measurable_prod_mk_right)],
  refine ae_lt_top hf.measurable.ennnorm.lintegral_prod_left _,
  simp_rw [← lintegral_prod_symm _ hf.measurable.ennnorm], exact hf.has_finite_integral
end

lemma integrable.prod_right [sigma_finite ν univ] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : ∀ᵐ x ∂ μ, integrable (λ y, f (x, y)) ν :=
begin
  simp [integrable, and_iff_right (hf.measurable.comp measurable_prod_mk_left)],
  refine ae_lt_top hf.measurable.ennnorm.lintegral_prod_right _,
  simp_rw [← lintegral_prod _ hf.measurable.ennnorm], exact hf.has_finite_integral
end

end measure_theory

/- rename `to_fun_of_fun` to `coe_of_fun` (in `l1`) -/

-- lemma measurable_add_iff {f g : α → E} (h : univ ⊆ f ⁻¹' {0} ∪ g ⁻¹' {0}) :
--   measurable (f + g) ↔ measurable f ∧ measurable g :=
-- begin
--   refine ⟨λ hfg, _, λ h, h.1.add h.2⟩,
--   rw [← indicator_add_eq_left h],
--   conv { congr, skip, rw [← indicator_add_eq_right h] },
--   exact ⟨hfg.indicator $ hf $ is_measurable_singleton 0, _⟩,
--   rw [integrable_indicator_iff (hf (is_measurable_singleton 0)).compl],
--   rw [integrable_indicator_iff (hg (is_measurable_singleton 0)).compl],
--   exact ⟨hfg.integrable_on, hfg.integrable_on⟩
-- end

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

lemma measurable.to_real {f : α → ennreal} (hf : measurable f) : measurable (λ x, ennreal.to_real (f x)) :=
measurable_to_real.comp hf

lemma set_of_compl {p : α → Prop} : {x | p x}ᶜ = {x | ¬ p x } := rfl

lemma is_closed_le_prod [topological_space α] [partial_order α] [t : order_closed_topology α] [second_countable_topology α] : is_closed {p : α × α | p.1 ≤ p.2} :=
t.is_closed_le'

lemma is_open_lt_prod [topological_space α] [linear_order α] [t : order_closed_topology α] [second_countable_topology α] : is_open {p : α × α | p.1 < p.2} :=
by { simp_rw [← is_closed_compl_iff, set_of_compl, not_lt],
     exact is_closed_le continuous_snd continuous_fst }

lemma is_measurable_lt' [topological_space α] [opens_measurable_space α] [linear_order α] [order_closed_topology α] [second_countable_topology α] : is_measurable {p : α × α | p.1 < p.2} :=
is_open_lt_prod.is_measurable

lemma is_measurable_lt [topological_space α] [opens_measurable_space α] [linear_order α] [order_closed_topology α] [second_countable_topology α] {f g : β → α} (hf : measurable f) (hg : measurable g) :
  is_measurable {a | f a < g a} :=
hf.prod_mk hg is_measurable_lt'

lemma is_measurable.integrable [sigma_finite ν univ] ⦃f : α → β → E⦄ (hf : measurable (uncurry f)) :
  is_measurable { x | integrable (f x) ν } :=
begin
  simp [integrable, and_iff_right hf.of_uncurry_left],
  refine is_measurable_lt (measurable.lintegral_prod_right' _) measurable_const,
  exact hf.ennnorm
end

open filter
#print Pi.topological_space
#print metric.inf_dist

lemma measurable_of_is_open [topological_space β] [borel_space β] {f : α → β}
  (hf : ∀ s, is_open s → is_measurable (f ⁻¹' s)) : measurable f :=
by { rw [‹borel_space β›.measurable_eq], exact measurable_generate_from hf }

lemma measurable_of_is_closed [topological_space β] [borel_space β] {f : α → β}
  (hf : ∀ s, is_closed s → is_measurable (f ⁻¹' s)) : measurable f :=
begin
  apply measurable_of_is_open, intros s hs,
  rw [← is_measurable.compl_iff, ← preimage_compl], apply hf, rw [is_closed_compl_iff], exact hs
end

lemma measurable_of_is_closed' [topological_space β] [borel_space β] {f : α → β}
  (hf : ∀ s, is_closed s → s.nonempty → s ≠ univ → is_measurable (f ⁻¹' s)) : measurable f :=
begin
  apply measurable_of_is_closed, intros s hs,
  cases eq_empty_or_nonempty s with h1 h1, { simp [h1] },
  by_cases h2 : s = univ, { simp [h2] },
  exact hf s hs h1 h2
end
open metric emetric

lemma measurable_inf_edist [emetric_space α] [opens_measurable_space α] {A : set α} :
  measurable (λ x, inf_edist x A) :=
continuous_inf_edist.measurable

lemma measurable.inf_edist [emetric_space β] [opens_measurable_space β] {f : α → β}
  (hf : measurable f) {A : set β} : measurable (λ x, inf_edist (f x) A) :=
measurable_inf_edist.comp hf

lemma measurable_inf_dist [metric_space α] [opens_measurable_space α] {A : set α} :
  measurable (λ x, inf_dist x A) :=
(continuous_inf_dist_pt A).measurable

lemma measurable.inf_dist [metric_space β] [opens_measurable_space β] {f : α → β}
  (hf : measurable f) {A : set β} : measurable (λ x, inf_dist (f x) A) :=
measurable_inf_dist.comp hf

lemma measurable_inf_nndist [metric_space α] [opens_measurable_space α] {A : set α} :
  measurable (λ x, inf_nndist x A) :=
(continuous_inf_nndist_pt A).measurable

lemma measurable.inf_nndist [metric_space β] [opens_measurable_space β] {f : α → β}
  (hf : measurable f) {A : set β} : measurable (λ x, inf_nndist (f x) A) :=
measurable_inf_nndist.comp hf

section
variables {δ : Type*} [topological_space α] [borel_space α] [measurable_space δ]

lemma measurable_bsupr' [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} (s : set ι) (f : ι → δ → α) (hf : ∀ i, measurable (f i)) (hs : countable s) :
  measurable (λ b, ⨆ i ∈ s, f i b) :=
by { haveI : encodable s := hs.to_encodable, simp only [supr_subtype'],
     exact measurable_supr (λ i, hf i) }

lemma measurable_binfi' [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} (s : set ι) {f : ι → δ → α} (hf : ∀ i, measurable (f i)) (hs : countable s) :
  measurable (λ b, ⨅ i ∈ s, f i b) :=
by { haveI : encodable s := hs.to_encodable, simp only [infi_subtype'],
     exact measurable_infi (λ i, hf i) }

end

lemma measurable_liminf {ι} [complete_lattice β] {f : ι → α → β} {u : filter ι}
  (hf : ∀ i, measurable (f i)) :
  measurable (λ x, liminf u (λ i, f i x)) :=
by { simp_rw [liminf, Liminf, Sup_eq_supr], sorry } -- conditions needed?

instance foo {α} [conditionally_complete_linear_order_bot α] : conditionally_complete_linear_order α :=
{ .._inst_9 }

-- this can probably be used in `ennreal_equiv_sum`
lemma measurable_to_nnreal : measurable ennreal.to_nnreal :=
ennreal.measurable_of_measurable_nnreal measurable_id

lemma measurable.to_nnreal [measurable_space α] {f : α → ennreal} (hf : measurable f) :
  measurable (λ x, (f x).to_nnreal) :=
measurable_to_nnreal.comp hf

lemma measurable_ennreal_coe_iff [measurable_space α] {f : α → nnreal} :
  measurable (λ x, (f x : ennreal)) ↔ measurable f :=
⟨λ h, h.to_nnreal, λ h, h.ennreal_coe⟩

namespace ennreal
lemma coe_liminf {ι} {f : ι → nnreal} (u : filter ι) :
  (↑(liminf u f) : ennreal) = liminf u (λ x, (f x : ennreal)) :=
begin
  sorry
end
end ennreal

lemma tendsto_pi {ι α β : Type*} [topological_space β] {f : ι → α → β} {g : α → β} {u : filter ι} :
  tendsto f u (nhds g) ↔ ∀ x, tendsto (λ i, f i x) u (nhds (g x)) :=
by simp [nhds_pi, filter.tendsto_comap_iff]

lemma measurable_of_tendsto_nnreal {f : ℕ → α → nnreal} {g : α → nnreal}
  (hf : ∀ i, measurable (f i)) (lim : tendsto f at_top (nhds g)) : measurable g :=
begin
  rw [tendsto_pi] at lim,
  have : (λ x, liminf at_top (λ n, f n x)) = g := funext (λ x, (lim x).liminf_eq'),
  subst this,
  have : measurable (λ x, liminf at_top (λ n, (f n x : ennreal))) := measurable_liminf (λ i, (hf i).ennreal_coe),
  simp_rw [← measurable_ennreal_coe_iff, ennreal.coe_liminf], exact this
end

lemma measurable_of_tendsto_metric [metric_space β] [borel_space β] {f : ℕ → α → β} {g : α → β}
  (hf : ∀ i, measurable (f i)) (lim : tendsto f at_top (nhds g)) : measurable g :=
begin
  apply measurable_of_is_closed', intros s h1s h2s h3s,
  have : measurable (λx, inf_nndist (g x) s),
  { apply measurable_of_tendsto_nnreal (λ i, (hf i).inf_nndist),
    rw [tendsto_pi], rw [tendsto_pi] at lim, intro x,
    exact ((continuous_inf_nndist_pt s).tendsto (g x)).comp (lim x) },
    have h4s : g ⁻¹' s = (λ x, inf_nndist (g x) s) ⁻¹' {0},
    { ext x, simp [h1s, ← mem_iff_inf_dist_zero_of_closed h1s h2s, ← nnreal.coe_eq_zero] },
    rw [h4s], exact this (is_measurable_singleton 0),
end


#print measurable_of_tendsto_metric

/-- The Bochner intergral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable. -/
lemma measurable.integral_prod_left [sigma_finite ν univ] ⦃f : α → β → E⦄
  (hf : measurable (uncurry f)) : measurable (λ x, ∫ y, f x y ∂ν) :=
begin
  have : ∀ x, measurable (f x) := λ x, hf.of_uncurry_left,
  have := λ x, simple_func_sequence_tendsto (this x),
  choose s h1s h2s using this,
  let f' : ℕ → α → E := λ n, {x | integrable (f x) ν}.indicator (λ x, (s x n).integral ν),
  have hf' : ∀ n, measurable (f' n),
  { intro n, refine measurable.indicator _ (is_measurable.integrable hf),  },
  have h2f' : tendsto f' at_top (nhds (λ (x : α), ∫ (y : β), f x y ∂ν)),
  { rw [tendsto_pi], intro x,  },
  exact measurable_of_tendsto_metric hf' h2f'
end

/-
proof -



  have "⋀i. s i ∈ measurable (N ⨂⇩M M) (count_space UNIV)"
    by (rule measurable_simple_function) fact

  { fix i x assume "x ∈ space N"
    then have "simple_bochner_integral M (λy. s i (x, y)) =
      (∑z∈s i ` (space N × space M). measure M {y ∈ space M. s i (x, y) = z} *⇩R z)"
      using s(1)[THEN simple_functionD(1)]
      unfolding simple_bochner_integral_def
      by (intro sum.mono_neutral_cong_left)
         (auto simp: eq_commute space_pair_measure image_iff cong: conj_cong) }
  note eq = this

  show ?thesis
  proof (rule borel_measurable_LIMSEQ_metric)
    fix i show "f' i ∈ borel_measurable N"
      unfolding f'_def by (simp_all add: eq cong: measurable_cong if_cong)
  next
    fix x assume x: "x ∈ space N"
    { assume int_f: "integrable M (f x)"
      have int_2f: "integrable M (λy. 2 * norm (f x y))"
        by (intro integrable_norm integrable_mult_right int_f)
      have "(λi. integral⇧L M (λy. s i (x, y))) ⇢ integral⇧L M (f x)"
      proof (rule integral_dominated_convergence)
        from int_f show "f x ∈ borel_measurable M" by auto
        show "⋀i. (λy. s i (x, y)) ∈ borel_measurable M"
          using x by simp
        show "AE xa in M. (λi. s i (x, xa)) ⇢ f x xa"
          using x s(2) by auto
        show "⋀i. AE xa in M. norm (s i (x, xa)) ≤ 2 * norm (f x xa)"
          using x s(3) by auto
      qed fact
      moreover
      { fix i
        have "simple_bochner_integrable M (λy. s i (x, y))"
        proof (rule simple_bochner_integrableI_bounded)
          have "(λy. s i (x, y)) ` space M ⊆ s i ` (space N × space M)"
            using x by auto
          then show "simple_function M (λy. s i (x, y))"
            using simple_functionD(1)[OF s(1), of i] x
            by (intro simple_function_borel_measurable)
               (auto simp: space_pair_measure dest: finite_subset)
          have "(∫⇧+ y. ennreal (norm (s i (x, y))) ∂M) ≤ (∫⇧+ y. 2 * norm (f x y) ∂M)"
            using x s by (intro nn_integral_mono) auto
          also have "(∫⇧+ y. 2 * norm (f x y) ∂M) < ∞"
            using int_2f unfolding integrable_iff_bounded by simp
          finally show "(∫⇧+ xa. ennreal (norm (s i (x, xa))) ∂M) < ∞" .
        qed
        then have "integral⇧L M (λy. s i (x, y)) = simple_bochner_integral M (λy. s i (x, y))"
          by (rule simple_bochner_integrable_eq_integral[symmetric]) }
      ultimately have "(λi. simple_bochner_integral M (λy. s i (x, y))) ⇢ integral⇧L M (f x)"
        by simp }
    then
    show "(λi. f' i x) ⇢ integral⇧L M (f x)"
      unfolding f'_def
      by (cases "integrable M (f x)") (simp_all add: not_integrable_integral_eq)
  qed
qed
-/


lemma integrable_prod_iff [sigma_finite ν univ] ⦃f : α × β → E⦄ (h1f : measurable f) :
  (∀ᵐ x ∂ μ, integrable (λ y, f (x, y)) ν) ∧ integrable (λ x, ∫ y, f (x, y) ∂ν) μ ↔ integrable f (μ.prod ν) :=
sorry

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
