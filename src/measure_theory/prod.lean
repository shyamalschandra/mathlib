/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.giry_monad
import measure_theory.set_integral
import topology.list

/-!
# The product measure space

TODO:

variants of Fubini
finitary products

-/
noncomputable theory
open_locale classical big_operators nnreal topological_space filter
open function set measure_theory.outer_measure measurable_space topological_space (hiding generate_from)
  filter (hiding prod_eq map)

namespace function

-- example {ι : Type*} {α : ι → Type*} (i : ι) (g : (Π i, α i) → α i) (s : set (Π i, α i)) :
--   eval i '' s = g '' s :=
-- begin
--   success_if_fail { simp only [eval_apply] },
--   simp, -- why does this simplify?
--   sorry
-- end

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

variables {α β : Type*} {f : α → β} {s : set α}

theorem forall_image_iff {p : β → Prop} : (∀ y ∈ f '' s, p y) ↔ (∀ x ∈ s, p (f x)) :=
by { simp only [mem_image, exists_imp_distrib, @forall_swap β, and_imp, imp.swap],
  apply forall_congr, intro x, simp only [forall_eq'] }

lemma set_of_compl {p : α → Prop} : {x | p x}ᶜ = {x | ¬ p x } := rfl

@[simp] lemma univ_disjoint : disjoint univ s ↔ s = ∅ :=
by simp [set.disjoint_iff_inter_eq_empty]

@[simp] lemma disjoint_univ : disjoint s univ ↔ s = ∅ :=
by simp [set.disjoint_iff_inter_eq_empty]

-- fix: disjoint_singleton_left simp
-- fix: rename disjoint.preimage [remove set.]
lemma preimage_eq_empty {f : α → β} {s : set β} (h : disjoint s (range f)) :
  f ⁻¹' s = ∅ :=
by simpa using disjoint.preimage f h

lemma preimage_eq_empty_iff {f : α → β} {s : set β} : disjoint s (range f) ↔ f ⁻¹' s = ∅ :=
⟨preimage_eq_empty, λ h, by { simp [eq_empty_iff_forall_not_mem, set.disjoint_iff_inter_eq_empty] at h ⊢, finish }⟩

theorem preimage_swap_prod {s : set α} {t : set β} : prod.swap ⁻¹' t.prod s = s.prod t :=
by { ext ⟨x, y⟩, simp [and_comm] }


end set
open set
section
variables {α β γ : Type*}

namespace pi
lemma const_def {y : β} : (λ x : α, y) = const α y := rfl

end pi

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

lemma of_real_le_of_le_to_real {a : ℝ} {b : ennreal} (h : a ≤ ennreal.to_real b) :
  ennreal.of_real a ≤ b :=
(of_real_le_of_real h).trans of_real_to_real_le

lemma mul_lt_top_iff {a b : ennreal} : a * b < ⊤ ↔ (a < ⊤ ∧ b < ⊤) ∨ a = 0 ∨ b = 0 :=
begin
  split,
  { intro h, rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right], intros hb ha,
    exact ⟨lt_top_of_mul_lt_top_left h hb, lt_top_of_mul_lt_top_right h ha⟩ },
  { rintro (⟨ha, hb⟩|rfl|rfl); [exact mul_lt_top ha hb, simp, simp] }
end

-- fix: rename, and let other one be continuous_coe_iff (also use this once)
lemma continuous_coe' : continuous (coe : nnreal → ennreal) :=
embedding_coe.continuous

end ennreal

section norm

lemma norm_eq_self {x : ℝ} (hx : 0 ≤ x) : ∥ x ∥ = x :=
by { rw [real.norm_eq_abs, abs_of_nonneg hx] }

lemma nnnorm_coe_eq_self {x : nnreal} : nnnorm (x : ℝ) = x :=
by { ext, exact norm_eq_self (zero_le x) }

lemma nnnorm_eq_self {x : ℝ} (hx : 0 ≤ x) : nnnorm x = ⟨x, hx⟩ :=
@nnnorm_coe_eq_self ⟨x, hx⟩

lemma ennnorm_eq_of_real {x : ℝ} (hx : 0 ≤ x) : (nnnorm x : ennreal) = ennreal.of_real x :=
by { rw [← of_real_norm_eq_coe_nnnorm, norm_eq_self hx] }

end norm

namespace filter

open filter

section
variables {α β ι : Type*} [complete_lattice α]

theorem has_basis.Liminf_eq_supr_Inf {p : ι → Prop} {s : ι → set α} {f : filter α}
  (h : f.has_basis p s) : f.Liminf = ⨆ i (hi : p i), Inf (s i) :=
@has_basis.Limsup_eq_infi_Sup (order_dual α) _ _ _ _ _ h

theorem has_basis.limsup_eq_infi_supr {p : ι → Prop} {s : ι → set β} {f : filter β} {u : β → α}
  (h : f.has_basis p s) : f.limsup u = ⨅ i (hi : p i), ⨆ a ∈ s i, u a :=
(h.map u).Limsup_eq_infi_Sup.trans $ by simp only [Sup_image, id]

theorem has_basis.liminf_eq_supr_infi {p : ι → Prop} {s : ι → set β} {f : filter β} {u : β → α}
  (h : f.has_basis p s) : f.liminf u = ⨆ i (hi : p i), ⨅ a ∈ s i, u a :=
@has_basis.limsup_eq_infi_supr (order_dual α) _ _ _ _ _ _ _ h

end

end filter

-- section filter
-- open filter

-- variables {α β : Type*} [topological_space α] [conditionally_complete_linear_order α] [order_topology α]
-- open_locale topological_space

-- -- already moved
-- /-- If a function has a limit, then its limsup coincides with its limit. -/
-- theorem filter.tendsto.limsup_eq' {f : filter β} {u : β → α} {a : α} [ne_bot f]
--   (h : tendsto u f (𝓝 a)) : limsup f u = a :=
-- Limsup_eq_of_le_nhds h

-- /-- If a function has a limit, then its liminf coincides with its limit. -/
-- theorem filter.tendsto.liminf_eq' {f : filter β} {u : β → α} {a : α} [ne_bot f]
--   (h : tendsto u f (𝓝 a)) : liminf f u = a :=
-- Liminf_eq_of_le_nhds h

-- end filter

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

-- lemma measurable.sum {ι α β} [measurable_space α] [measurable_space β] [add_comm_monoid β]
--   [topological_space β] [has_continuous_add β] [borel_space β] [second_countable_topology β]
--   (f : ι → α → β) (h : ∀ i, measurable (f i)) (s : finset ι) : measurable (λ x, ∑ i in s, f i x) :=
-- begin
--   refine s.induction_on (by simp [measurable_zero]) _,
--   intros i t hi hf, have := (h i).add hf, simpa [finset.sum_insert, hi]
-- end

/-- todo: `ennreal` can probably be generalized to a
[measurable_space β] [topological_space β] [add_comm_monoid β] [has_continuous_add β]
  [borel_space β] -/
lemma measurable.ennreal_tsum {ι α} [encodable ι] [measurable_space α]
  {f : ι → α → ennreal} (h : ∀ i, measurable (f i)) : measurable (λ x, ∑' i, f i x) :=
by { simp_rw [ennreal.tsum_eq_supr_sum], apply measurable_supr, exact λ s, s.measurable_sum h }
















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

-- @[simp] lemma inf_nndist_eq_zero : (inf_nndist x s : ℝ) = inf_dist x s := rfl

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

section topological_space
open topological_space filter

variables {α : Type*} [topological_space α]

lemma is_closed_le_prod [partial_order α] [t : order_closed_topology α] :
  is_closed {p : α × α | p.1 ≤ p.2} :=
t.is_closed_le'

lemma is_open_lt_prod [linear_order α] [t : order_closed_topology α] :
  is_open {p : α × α | p.1 < p.2} :=
by { simp_rw [← is_closed_compl_iff, set_of_compl, not_lt],
     exact is_closed_le continuous_snd continuous_fst }

lemma tendsto_pi {ι α β : Type*} [topological_space β] {f : ι → α → β} {g : α → β} {u : filter ι} :
  tendsto f u (𝓝 g) ↔ ∀ x, tendsto (λ i, f i x) u (𝓝 (g x)) :=
by simp [nhds_pi, filter.tendsto_comap_iff]


open list
@[to_additive]
lemma tendsto_prod {α} [topological_space α] [monoid α] [has_continuous_mul α] {l : list α} :
  tendsto list.prod (𝓝 l) (𝓝 l.prod) :=
begin
  induction l with x l ih, { simp [nhds_nil, mem_of_nhds, tendsto_pure_left] {contextual := tt} },
  simp_rw [tendsto_cons_iff, prod_cons],
  have := continuous_iff_continuous_at.mp continuous_mul (x, l.prod),
  rw [continuous_at, nhds_prod_eq] at this,
  exact this.comp (tendsto_id.prod_map ih)
end

@[to_additive]
lemma continuous_prod {α} [topological_space α] [monoid α] [has_continuous_mul α] :
  continuous (prod : list α → α) :=
continuous_iff_continuous_at.mpr $ λ l, tendsto_prod

lemma tendsto_fst' {α β} [topological_space α] [topological_space β] {x : α × β} :
  tendsto prod.fst (𝓝 x) (𝓝 x.fst) :=
continuous_iff_continuous_at.mp continuous_fst x

lemma tendsto_snd' {α β} [topological_space α] [topological_space β] {x : α × β} :
  tendsto prod.snd (𝓝 x) (𝓝 x.snd) :=
continuous_iff_continuous_at.mp continuous_snd x

-- rename tendsto_cons tendsto_cons'
lemma continuous_cons {α} [topological_space α] : continuous (λ x : α × list α, (x.1 :: x.2 : list α)) :=
continuous_iff_continuous_at.mpr $ λ x, tendsto_cons tendsto_fst' tendsto_snd'

-- lemma tendsto_list_map {α β} [topological_space α] [topological_space β]
--   {f : α → β} {l : list α} :
--   tendsto (λ p : (α → β) × list α, p.2.map p.1) (𝓝 f ×ᶠ 𝓝 l) (𝓝 (l.map f)) :=
-- begin
--   induction l with x l ih,
--   { simp only [nhds_nil, list.map, tendsto_pure, list.map_eq_nil],
--     refine eventually.filter_mono inf_le_right _, simp },
--   { have : 𝓝 f ×ᶠ 𝓝 (x :: l : list α) =
--       (𝓝 f ×ᶠ (𝓝 x ×ᶠ 𝓝 l)).map (λp : _ × α × list α, (p.1, p.2.1 :: p.2.2)),
--     { sorry },
--     simp_rw [this, tendsto_map'_iff, function.comp],
--     refine tendsto_cons _ (ih.comp $ tendsto_fst.prod_mk $ tendsto_snd.comp tendsto_snd),
--     refine tendsto_eval.comp (tendsto_fst.prod_mk $ tendsto_fst.comp tendsto_snd) }
-- end

-- @[to_additive]
-- lemma tendsto.list_prod {α β γ} [topological_space α] [monoid α] [has_continuous_mul α]
--   [topological_space β] [topological_space γ] {f : γ → β → α} {u : filter β} {g : γ → α}
--   (hf : ∀c, tendsto (f c) u (nhds (g c))) {l : β → list γ} {l' : list γ}
--   (hl : tendsto l u (𝓝 l')) :
--   tendsto (λ b, ((l b).map (λc, f c b)).prod) u (𝓝 ((l'.map g).prod)) :=
-- tendsto_prod.comp $ tendsto_list_map.comp $ (tendsto_pi.mpr hf).prod_mk hl

-- @[to_additive]
-- lemma prod_congr {α} [comm_monoid α] ⦃l1 l2 : list α⦄ (hl : l1 ≈ l2) :
--   l1.prod = l2.prod :=
-- by { rw [← multiset.coe_prod, ← multiset.coe_prod], apply congr_arg, exact @quotient.sound (list α) _ _ _ hl }


-- @[to_additive]
-- def multiset.prod_def {α} [comm_monoid α] (s : multiset α) : s.prod = quotient.lift list.prod prod_congr s :=
-- by { rcases s with ⟨l⟩, simp, refl }

end topological_space


section measurable
open measure_theory

variables {α β γ : Type*} [measurable_space α] [measurable_space β] [measurable_space γ]
  {μ : measure α}

/- fix: rename `to_fun_of_fun` to `coe_of_fun` (in `l1`) -/
-- fix: integral_map_measure vs lintegral_map is inconsistent

lemma measurable.congr' {f g : α → β} {s : set α} {y : β} (hs : is_measurable s)
  (h : ∀ x ∈ s, f x = g x) (hg : measurable g) (hf : ∀ x ∉ s, f x = y)
  : measurable f :=
begin
  intros t ht,
  by_cases hy : y ∈ t,
  { convert (hg ht).union hs.compl, ext x, by_cases hx : x ∈ s; simp * },
  { convert (hg ht).inter hs, ext x, by_cases hx : x ∈ s; simp * }
end

lemma nnreal.measurable_coe : measurable (coe : nnreal → ℝ) :=
nnreal.continuous_coe.measurable

lemma measurable_ennreal_to_real : measurable ennreal.to_real :=
ennreal.measurable_of_measurable_nnreal nnreal.measurable_coe

section
variables [normed_group α] [opens_measurable_space α]
lemma measurable_ennnorm : measurable (λ x : α, (nnnorm x : ennreal)) :=
measurable_nnnorm.ennreal_coe
end

lemma measurable.to_real {f : α → ennreal} (hf : measurable f) : measurable (λ x, ennreal.to_real (f x)) :=
measurable_ennreal_to_real.comp hf

open filter

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
  {ι} (s : set ι) (f : ι → δ → α) (hs : countable s) (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨆ i ∈ s, f i b) :=
by { haveI : encodable s := hs.to_encodable, simp only [supr_subtype'],
     exact measurable_supr (λ i, hf i) }

lemma measurable_binfi' [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} (s : set ι) (f : ι → δ → α) (hs : countable s) (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨅ i ∈ s, f i b) :=
by { haveI : encodable s := hs.to_encodable, simp only [infi_subtype'],
     exact measurable_infi (λ i, hf i) }

end

lemma measurable_of_is_measurable_lt [linear_order β] [topological_space β] [second_countable_topology β]
  [order_topology β] [borel_space β] {f : α → β} (hf : ∀ y, is_measurable {x | f x < y}) : measurable f :=
begin
  rw [‹borel_space β›.measurable_eq, borel_eq_generate_Iio],
  apply measurable_generate_from, rintro _ ⟨y, rfl⟩, exact hf y
end

lemma measurable_of_is_measurable_le [linear_order β] [topological_space β] [second_countable_topology β]
  [order_topology β] [borel_space β] {f : α → β} (hf : ∀ y, is_measurable {x | f x ≤ y}) : measurable f :=
begin
  rw [‹borel_space β›.measurable_eq, borel_eq_generate_Ioi],
  apply measurable_generate_from, rintro _ ⟨y, rfl⟩, convert (hf y).compl, simp [set_of_compl, Ioi]
end

lemma measurable_cSup {ι} [conditionally_complete_linear_order β] [topological_space β]
  [second_countable_topology β] [order_topology β] [borel_space β]
  {f : ι → α → β} {s : set ι} (hs : s.countable)
  (hf : ∀ i, measurable (f i)) (bdd : ∀ x, bdd_above ((λ i, f i x) '' s)) :
  measurable (λ x, Sup ((λ i, f i x) '' s)) :=
begin
  cases eq_empty_or_nonempty s with h2s h2s,
  { simp [h2s, measurable_const] },
  { apply measurable_of_is_measurable_le, intro y,
    have : is_measurable {x : α | ∀ (i : ι), i ∈ s → f i x ≤ y},
    { simp_rw set_of_forall,
      exact is_measurable.bInter hs (λ i hi, is_measurable_le (hf i) measurable_const) },
    convert this, ext x, simp_rw [cSup_le_iff (bdd x) (h2s.image _), forall_image_iff] }
end

lemma measurable_liminf' {ι ι'} [complete_linear_order β] [topological_space β] [second_countable_topology β]
  [order_topology β] [borel_space β] {f : ι → α → β} {u : filter ι} (hf : ∀ i, measurable (f i))
  {p : ι' → Prop} {s : ι' → set ι} (hu : u.has_countable_basis p s) (hs : ∀ i, (s i).countable) :
  measurable (λ x, liminf u (λ i, f i x)) :=
begin
  simp_rw [hu.to_has_basis.liminf_eq_supr_infi],
  refine measurable_bsupr' _ _ hu.countable _,
  exact λ i, measurable_binfi' _ _ (hs i) hf
end

lemma measurable_limsup' {ι ι'} [complete_linear_order β] [topological_space β] [second_countable_topology β]
  [order_topology β] [borel_space β] {f : ι → α → β} {u : filter ι} (hf : ∀ i, measurable (f i))
  {p : ι' → Prop} {s : ι' → set ι} (hu : u.has_countable_basis p s) (hs : ∀ i, (s i).countable) :
  measurable (λ x, limsup u (λ i, f i x)) :=
begin
  simp_rw [hu.to_has_basis.limsup_eq_infi_supr],
  refine measurable_binfi' _ _ hu.countable _,
  exact λ i, measurable_bsupr' _ _ (hs i) hf
end

lemma measurable_liminf [complete_linear_order β] [topological_space β] [second_countable_topology β]
  [order_topology β] [borel_space β] {f : ℕ → α → β} (hf : ∀ i, measurable (f i)) :
  measurable (λ x, liminf at_top (λ i, f i x)) :=
measurable_liminf' hf at_top_countable_basis (λ i, countable_encodable _)

lemma measurable_limsup [complete_linear_order β] [topological_space β] [second_countable_topology β]
  [order_topology β] [borel_space β] {f : ℕ → α → β} (hf : ∀ i, measurable (f i)) :
  measurable (λ x, limsup at_top (λ i, f i x)) :=
measurable_limsup' hf at_top_countable_basis (λ i, countable_encodable _)

-- @[priority 100]
-- instance foo {α} [h : conditionally_complete_linear_order_bot α] : conditionally_complete_linear_order α :=
-- { ..h }

-- this can probably be used in `ennreal_equiv_sum`
lemma measurable_to_nnreal : measurable ennreal.to_nnreal :=
ennreal.measurable_of_measurable_nnreal measurable_id

lemma measurable.to_nnreal {f : α → ennreal} (hf : measurable f) : measurable (λ x, (f x).to_nnreal) :=
measurable_to_nnreal.comp hf

lemma measurable_ennreal_coe_iff {f : α → nnreal} :
  measurable (λ x, (f x : ennreal)) ↔ measurable f :=
⟨λ h, h.to_nnreal, λ h, h.ennreal_coe⟩

lemma measurable_of_tendsto_nnreal' {ι ι'} {f : ι → α → nnreal} {g : α → nnreal} (u : filter ι)
  [ne_bot u] (hf : ∀ i, measurable (f i)) (lim : tendsto f u (𝓝 g)) {p : ι' → Prop}
  {s : ι' → set ι} (hu : u.has_countable_basis p s) (hs : ∀ i, (s i).countable) : measurable g :=
begin
  rw [tendsto_pi] at lim, rw [← measurable_ennreal_coe_iff],
  have : (λ x, liminf u (λ n, (f n x : ennreal))) = λ x, (g x : ennreal) :=
  funext (λ x, ((ennreal.continuous_coe'.tendsto (g x)).comp (lim x)).liminf_eq),
  rw [← this],
  show measurable (λ x, liminf u (λ n, (f n x : ennreal))),
  exact measurable_liminf' (λ i, (hf i).ennreal_coe) hu hs,
end

lemma measurable_of_tendsto_nnreal {f : ℕ → α → nnreal} {g : α → nnreal}
  (hf : ∀ i, measurable (f i)) (lim : tendsto f at_top (𝓝 g)) : measurable g :=
measurable_of_tendsto_nnreal' at_top hf lim at_top_countable_basis (λ i, countable_encodable _)

lemma measurable_of_tendsto_metric' {ι ι'} [metric_space β] [borel_space β] {f : ι → α → β} {g : α → β}
  (u : filter ι) [ne_bot u] (hf : ∀ i, measurable (f i)) (lim : tendsto f u (𝓝 g)) {p : ι' → Prop}
  {s : ι' → set ι} (hu : u.has_countable_basis p s) (hs : ∀ i, (s i).countable) :
  measurable g :=
begin
  apply measurable_of_is_closed', intros s h1s h2s h3s,
  have : measurable (λx, inf_nndist (g x) s),
  { refine measurable_of_tendsto_nnreal' u (λ i, (hf i).inf_nndist) _ hu hs, swap,
    rw [tendsto_pi], rw [tendsto_pi] at lim, intro x,
    exact ((continuous_inf_nndist_pt s).tendsto (g x)).comp (lim x) },
    have h4s : g ⁻¹' s = (λ x, inf_nndist (g x) s) ⁻¹' {0},
    { ext x, simp [h1s, ← mem_iff_inf_dist_zero_of_closed h1s h2s, ← nnreal.coe_eq_zero] },
    rw [h4s], exact this (is_measurable_singleton 0),
end

lemma measurable_of_tendsto_metric [metric_space β] [borel_space β] {f : ℕ → α → β} {g : α → β}
  (hf : ∀ i, measurable (f i)) (lim : tendsto f at_top (𝓝 g)) :
  measurable g :=
measurable_of_tendsto_metric' at_top hf lim at_top_countable_basis (λ i, countable_encodable _)

section

variables {δ : Type*} [measurable_space δ] [topological_space α] [borel_space α]

-- use in integrable_add
@[to_additive]
lemma measurable.mul' [has_mul α] [has_continuous_mul α] [second_countable_topology α]
  {f : δ → α} {g : δ → α} : measurable f → measurable g → measurable (f * g) :=
measurable.mul

end

open measure_theory measure_theory.measure

lemma measurable_measure {μ : α → measure β} :
  measurable μ ↔ ∀(s : set β) (hs : is_measurable s), measurable (λb, μ b s) :=
⟨λ hμ s hs, (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

lemma measurable_prod_mk_left {x : α} : measurable (@prod.mk _ β x) :=
measurable_const.prod_mk measurable_id

lemma measurable_prod_mk_right {y : β} : measurable (λ x : α, (x, y)) :=
measurable_id.prod_mk measurable_const

-- #print measurable.prod_mk
-- lemma measurable.prod_mk : measurable (@prod.mk α β) :=
-- measurable_pi_lambda _ $ λ x, measurable_prod_mk_right

lemma measurable_prod {f : α → β × γ} : measurable f ↔
  measurable (λa, (f a).1) ∧ measurable (λa, (f a).2) :=
⟨λ hf, ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, λ h, measurable.prod h.1 h.2⟩

lemma measurable_swap : measurable (prod.swap : α × β → β × α) :=
measurable.prod measurable_snd measurable_fst

lemma measurable_swap_iff {f : α × β → γ} : measurable (f ∘ prod.swap) ↔ measurable f :=
⟨λ hf, by { convert hf.comp measurable_swap, ext ⟨x, y⟩, refl }, λ hf, hf.comp measurable_swap⟩

lemma is_measurable_swap_iff {s : set (α × β)} : is_measurable (prod.swap ⁻¹' s) ↔ is_measurable s :=
⟨λ hs, by { convert measurable_swap hs, ext ⟨x, y⟩, refl }, λ hs, measurable_swap hs⟩

lemma measurable.of_uncurry_left {f : α → β → γ} (hf : measurable (uncurry f)) {x : α} :
  measurable (f x) :=
hf.comp measurable_prod_mk_left

lemma measurable.of_uncurry_right {f : α → β → γ} (hf : measurable (uncurry f)) {y : β} :
  measurable (λ x, f x y) :=
hf.comp measurable_prod_mk_right

variables {E : Type*} [measurable_space E] [normed_group E] [second_countable_topology E] [normed_space ℝ E] [complete_space E] [borel_space E]
lemma measurable_smul_const {f : α → ℝ} {c : E} (hc : c ≠ 0) :
  measurable (λ x, f x • c) ↔ measurable f :=
begin
  refine ⟨λ hf, _, λ hf, hf.smul measurable_const⟩,
  intros s hs,
  have : is_measurable ((λ x, x • c) '' s) := sorry,
  convert hf this, rw [@preimage_comp _ _ _ f (• c), preimage_image_eq],
  sorry
end

end measurable

namespace measure_theory

section

variables {α : Type*} [measurable_space α] {μ : measure α}

lemma ae_lt_top {f : α → ennreal} (hf : measurable f)
  (h2f : ∫⁻ x, f x ∂μ < ⊤) : ∀ᵐ x ∂μ, f x < ⊤ :=
begin
  simp_rw [ae_iff, ennreal.not_lt_top], by_contra h, rw [← not_le] at h2f, apply h2f,
  have : (f ⁻¹' {⊤}).indicator ⊤ ≤ f,
  { intro x, by_cases hx : x ∈ f ⁻¹' {⊤}; [simpa [hx], simp [hx]] },
  convert lintegral_mono this,
  rw [lintegral_indicator _ (hf (is_measurable_singleton ⊤))], simp [ennreal.top_mul, preimage, h]
end

lemma measure_Union_null_iff {ι} [encodable ι] {s : ι → set α} :
  μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 :=
⟨λ h i, measure_mono_null (subset_Union _ _) h, measure_Union_null⟩

end


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

/- fix: also replace `Inf_eq_of_function_Inf_gen`. -/
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

variables {α β E : Type*} [measurable_space α] [measurable_space β] {μ : measure α}


namespace simple_func

section
variables [normed_group E] [normed_space ℝ E]

lemma integral_eq_sum_of_subset {f : simple_func α E} {μ : measure α} {s : finset E}
  (hs : f.range.filter (λ x, x ≠ 0) ⊆ s) : f.integral μ = ∑ x in s, (μ (f ⁻¹' {x})).to_real • x :=
begin
  rw [simple_func.integral_eq_sum_filter, finset.sum_subset hs],
  rintro x - hx, rw [finset.mem_filter, not_and_distrib, ne.def, not_not] at hx,
  rcases hx with hx|rfl; [skip, simp],
  rw [simple_func.mem_range] at hx, rw [preimage_eq_empty]; simp [disjoint_singleton_left, hx]
end

variables [normed_group α] [opens_measurable_space α] {γ : Type*} [measurable_space γ]
open simple_func

lemma norm_approx_on_zero_le {f : β → α} (hf : measurable f) {s : set α} (h₀ : (0 : α) ∈ s)
  [separable_space s] (x : β) (n : ℕ) :
  ∥ approx_on f hf s 0 h₀ n x ∥ ≤ ∥ f x ∥ + ∥ f x ∥ :=
begin
  have := edist_approx_on_y0_le hf h₀ x n,
  simp [edist_comm (0 : α), edist_eq_coe_nnnorm] at this,
  exact_mod_cast this,
end
end



end simple_func

section integrals

lemma lintegral_mul_const (r : ennreal) {f : α → ennreal} (hf : measurable f) :
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul r hf]

lemma lintegral_mul_const_le (r : ennreal) (f : α → ennreal) :
  ∫⁻ a, f a ∂μ * r ≤ ∫⁻ a, f a * r ∂μ :=
by simp_rw [mul_comm, lintegral_const_mul_le r f]

lemma lintegral_mul_const' (r : ennreal) (f : α → ennreal) (hr : r ≠ ⊤):
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul' r f hr]

lemma integral_to_real {f : α → ennreal} (hfm : measurable f) (hf : ∀ᵐ x ∂μ, f x < ⊤) :
  ∫ a, (f a).to_real ∂μ = (∫⁻ a, f a ∂μ).to_real :=
begin
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.to_real],
  { rw lintegral_congr_ae, refine hf.mp (eventually_of_forall _),
    intros x hx, rw [lt_top_iff_ne_top] at hx, simp [hx] },
  { exact (eventually_of_forall $ λ x, ennreal.to_real_nonneg) }
end

lemma lintegral_coe_eq_integral (f : α → nnreal) (hfi : integrable (λ x, (f x : real)) μ) :
  ∫⁻ a, f a ∂μ = ennreal.of_real ∫ a, f a ∂μ :=
begin
  rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall (λ x, (f x).coe_nonneg))
    hfi.measurable],
  simp_rw [← ennreal.coe_nnreal_eq], rw [ennreal.of_real_to_real],
  rw [← lt_top_iff_ne_top], convert hfi.has_finite_integral, ext1 x,
  rw [nnnorm_coe_eq_self]
end


namespace l1

variables [normed_group β] [second_countable_topology β] [borel_space β]

lemma norm_eq_lintegral {f : α →₁[μ] β} : ∥ f ∥ = (∫⁻ x, (nnnorm (f x) : ennreal) ∂μ).to_real :=
by simp [l1.norm_eq, ae_eq_fun.edist_zero_eq_coe, ← edist_eq_coe_nnnorm]

lemma norm_sub_eq_lintegral {f g : α →₁[μ] β} :
  ∥ f - g ∥ = (∫⁻ x, (nnnorm (f x - g x) : ennreal) ∂μ).to_real :=
begin
  simp_rw [l1.norm_eq, ae_eq_fun.edist_zero_eq_coe, ← edist_eq_coe_nnnorm],
  rw lintegral_congr_ae,
  refine (ae_eq_fun.coe_fn_sub (f : α →ₘ[μ] β) g).mp _,
  apply eventually_of_forall, intros x hx, simp [hx]
end

lemma of_real_norm_eq_lintegral {f : α →₁[μ] β} :
  ennreal.of_real ∥ f ∥ = ∫⁻ x, (nnnorm (f x) : ennreal) ∂μ :=
by { rw [norm_eq_lintegral, ennreal.of_real_to_real], rw [← ennreal.lt_top_iff_ne_top],
  exact f.has_finite_integral }

lemma of_real_norm_sub_eq_lintegral {f g : α →₁[μ] β} :
  ennreal.of_real ∥ f - g ∥ = ∫⁻ x, (nnnorm (f x - g x) : ennreal) ∂μ :=
begin
  simp_rw [of_real_norm_eq_lintegral, ← edist_eq_coe_nnnorm],
  apply lintegral_congr_ae,
  refine (ae_eq_fun.coe_fn_sub (f : α →ₘ[μ] β) g).mp _,
  apply eventually_of_forall, intros x hx, simp only [l1.coe_coe, pi.sub_apply] at hx,
  simp_rw [← hx, ← l1.coe_sub, l1.coe_coe]
end

end l1

variables [measurable_space E] [normed_group E] [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [borel_space E] {f g : α → E}

lemma integral_add' (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
integral_add hf hg

lemma integral_zero' : integral μ (0 : α → E) = 0 :=
integral_zero α E

lemma integral_sub' (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
integral_sub hf hg

-- todo: this can probably be generalized to `f` without the assumption `hf`.
lemma integral_smul_const {f : α → ℝ} (hf : integrable f μ) (c : E) :
  ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c :=
((continuous_linear_map.id ℝ ℝ).smul_right c).integral_comp_comm hf

lemma integrable_smul_const {f : α → ℝ} {c : E} (hc : c ≠ 0) :
  integrable (λ x, f x • c) μ ↔ integrable f μ :=
begin
  simp_rw [integrable, measurable_smul_const hc, and.congr_right_iff, has_finite_integral,
    nnnorm_smul, ennreal.coe_mul],
  intro hf, rw [lintegral_mul_const' _ _ ennreal.coe_ne_top, ennreal.mul_lt_top_iff],
  have : ∀ x : ennreal, x = 0 → x < ⊤ := by simp,
  simp [hc, or_iff_left_of_imp (this _)]
end

lemma integral_smul_const' (f : α → ℝ) (c : E) :
  ∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c :=
begin
  by_cases hf : integrable f μ,
  { exact ((continuous_linear_map.id ℝ ℝ).smul_right c).integral_comp_comm hf },
  { by_cases hc : c = 0,
    { simp only [hc, integral_zero, smul_zero] },
    rw [integral_undef hf, integral_undef, zero_smul],
    rwa [integrable_smul_const hc] }
end


/- fix: replace all notation with

notation `∫` binders `, ` r:(scoped:0 f, f) ` ∂` μ:70 := integral μ r

The following code snippet should succeed:
```
import measure_theory.bochner_integration

open measure_theory

example {α} [measurable_space α] {f : α → ℝ} {μ : measure α} :
  ∫ x, abs ∥ f x ∥ ∂μ = ∫ x, abs ∥ f x ∥ ∂μ :=
rfl
```

-/

lemma ennnorm_integral_le_lintegral_norm (f : α → E) :
  (nnnorm (∫ a, f a ∂μ) : ennreal) ≤ ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ :=
by { rw [← of_real_norm_eq_coe_nnnorm], apply ennreal.of_real_le_of_le_to_real,
  exact norm_integral_le_lintegral_norm f }

end integrals

/-! ### Prod -/


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

lemma lintegral_comp {μ : measure α} {f : β → ennreal} {g : α → β} (hf : measurable f) (hg : measurable g) :
  lintegral μ (f ∘ g) = ∫⁻ a, f a ∂(map g μ) :=
(lintegral_map hf hg).symm

-- def sigma_finite_mk {μ : measure α} {s : set α} (sets : ℕ → set α)
--   (h1 : ∀ i, is_measurable (sets i)) (h2 : ∀ i, μ (sets i) < ⊤) (h3 : (⋃ i, sets i) = s) :
--   sigma_finite μ s :=
-- { spanning_sets := accumulate sets,
--   monotone_spanning_sets := monotone_accumulate,
--   is_measurable_spanning_sets :=
--     λ i, is_measurable.Union $ λ j, is_measurable.Union_Prop $ λ hij, h1 j,
--   measure_spanning_sets_lt_top :=
--     by { intro i, rw [accumulate_nat],
--       apply (measure_bUnion_le _ _).trans_lt,
--       refine (finset.tsum_subtype _ (λ i, μ (sets i))).le.trans_lt _,
--       rw ennreal.sum_lt_top_iff, exact λ j _, h2 j,
--       exact (finset.range (i+1)).countable_to_set },
--   Union_spanning_sets := by { rw [Union_accumulate, h3] } }

/-- A measure `μ` is called σ-finite if there is a countable collection of sets
  `{ A i | i ∈ ℕ }` such that `μ (A i) < ⊤` and `⋃ i, A i = s`. -/
class sigma_finite (μ : measure α) : Prop :=
(exists_finite_spanning_sets :
  ∃ s : ℕ → set α,
  (∀ i, is_measurable (s i)) ∧
  (∀ i, μ (s i) < ⊤) ∧
  (⋃ i, s i) = univ)

lemma exists_finite_spanning_sets (μ : measure α) [sigma_finite μ] :
  ∃ s : ℕ → set α,
  (∀ i, is_measurable (s i)) ∧
  (∀ i, μ (s i) < ⊤) ∧
  (⋃ i, s i) = univ :=
sigma_finite.exists_finite_spanning_sets

/-- A noncomputable way to get a monotone collection of sets that span `univ` and have finite
  measure using `classical.some`. This definition satisfies monotonicity in addition to all other
  properties in `sigma_finite`. -/
def spanning_sets (μ : measure α) [sigma_finite μ] (i : ℕ) : set α :=
accumulate (classical.some (exists_finite_spanning_sets μ)) i

lemma monotone_spanning_sets (μ : measure α) [sigma_finite μ] :
  monotone (spanning_sets μ) :=
monotone_accumulate

lemma is_measurable_spanning_sets (μ : measure α) [sigma_finite μ] (i : ℕ) :
  is_measurable (spanning_sets μ i) :=
is_measurable.Union $ λ j, is_measurable.Union_Prop $
  λ hij, (classical.some_spec (exists_finite_spanning_sets μ)).1 j

lemma measure_spanning_sets_lt_top (μ : measure α) [sigma_finite μ] (i : ℕ) :
  μ (spanning_sets μ i) < ⊤ :=
begin
  rw [spanning_sets, accumulate_nat],
  apply (measure_bUnion_le _ _).trans_lt,
  refine (finset.tsum_subtype _ (λ i, μ _)).le.trans_lt _,
  rw ennreal.sum_lt_top_iff,
  exact λ j _, (classical.some_spec (exists_finite_spanning_sets μ)).2.1 j,
  exact (finset.range (i+1)).countable_to_set
end

lemma Union_spanning_sets (μ : measure α) [sigma_finite μ] :
  (⋃ i : ℕ, spanning_sets μ i) = univ :=
by simp_rw [spanning_sets, Union_accumulate,
  (classical.some_spec (exists_finite_spanning_sets μ)).2.2]

namespace measure
lemma supr_restrict_spanning_sets {μ : measure α} [sigma_finite μ] {s : set α}
  (hs : is_measurable s) :
  (⨆ i, μ.restrict (spanning_sets μ i) s) = μ s :=
begin
  convert (restrict_Union_apply_eq_supr (is_measurable_spanning_sets μ) _ hs).symm,
  { simp [Union_spanning_sets] },
  { exact directed_of_sup (monotone_spanning_sets μ) }
end

end measure
end measure_theory
open measure_theory








variables {α β : Type*} [measurable_space α] [measurable_space β]
  {μ : measure_theory.measure α} {ν : measure_theory.measure β}
open measure_theory.measure





lemma is_measurable.measure_prod_mk_left_finite [finite_measure ν] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ x, ν (prod.mk x ⁻¹' s)) :=
begin
  refine induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ hs,
  { simp [measurable_zero, pi.const_def] },
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

lemma is_measurable.measure_prod_mk_left [sigma_finite ν] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ x, ν (prod.mk x ⁻¹' s)) :=
begin
  have : ∀ x, is_measurable (prod.mk x ⁻¹' s) := λ x, measurable_prod_mk_left hs,
  simp only [← supr_restrict_spanning_sets, this],
  apply measurable_supr, intro i,
  haveI : fact _ := measure_spanning_sets_lt_top ν i,
  exact hs.measure_prod_mk_left_finite
end

lemma measurable.map_prod_mk_left [sigma_finite ν] : measurable (λ x : α, map (prod.mk x) ν) :=
begin
  apply measurable_of_measurable_coe, intros s hs,
  simp_rw [map_apply measurable_prod_mk_left hs],
  exact hs.measure_prod_mk_left
end

lemma is_measurable.measure_prod_mk_right_finite {μ : measure α} [finite_measure μ] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ y, μ ((λ x, (x, y)) ⁻¹' s)) :=
by { convert (is_measurable_swap_iff.mpr hs).measure_prod_mk_left_finite, apply_instance }

lemma is_measurable.measure_prod_mk_right {μ : measure α} [sigma_finite μ] {s : set (α × β)}
  (hs : is_measurable s) : measurable (λ y, μ ((λ x, (x, y)) ⁻¹' s)) :=
by { convert (is_measurable_swap_iff.mpr hs).measure_prod_mk_left, apply_instance }

/- Is there a way to do this without duplicating? -/
lemma measurable.map_prod_mk_right {μ : measure α} [sigma_finite μ] :
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

variables {μ ν}

/- todo: rename set.disjoint.preimage -> disjoint.preimage -/


lemma prod_apply [sigma_finite ν] {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ x, ν (prod.mk x ⁻¹' s) ∂μ :=
begin
  rw [measure.prod, bind_apply hs],
  congr, ext x : 1, rw [map_apply _ hs],
  apply measurable_prod_mk_left,
  exact measurable.map_prod_mk_left
end

@[simp] lemma prod_prod [sigma_finite ν] {s : set α} {t : set β}
  (hs : is_measurable s) (ht : is_measurable t) : μ.prod ν (s.prod t) = μ s * ν t :=
by simp_rw [prod_apply (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
  lintegral_indicator _ hs, lintegral_const, restrict_apply is_measurable.univ,
  univ_inter, mul_comm]

lemma ae_measure_lt_top [sigma_finite ν] {s : set (α × β)} (hs : is_measurable s)
  (h2s : (μ.prod ν) s < ⊤) : ∀ᵐ x ∂μ, ν (prod.mk x ⁻¹' s) < ⊤ :=
by { simp_rw [prod_apply hs] at h2s, refine ae_lt_top hs.measure_prod_mk_left h2s }

lemma integrable_measure_prod_mk_left [sigma_finite ν] {s : set (α × β)}
  (hs : is_measurable s) (h2s : (μ.prod ν) s < ⊤) : integrable (λ x, (ν (prod.mk x ⁻¹' s)).to_real) μ :=
begin
  refine ⟨hs.measure_prod_mk_left.to_real, _⟩,
  simp_rw [has_finite_integral, ennnorm_eq_of_real ennreal.to_real_nonneg],
  convert h2s using 1, simp_rw [prod_apply hs], apply lintegral_congr_ae,
  refine (ae_measure_lt_top hs h2s).mp _, apply eventually_of_forall, intros x hx,
  rw [lt_top_iff_ne_top] at hx, simp [ennreal.of_real_to_real, hx],
end

section both_sigma_finite

variables [sigma_finite μ] [sigma_finite ν]

lemma prod_unique {μν₁ μν₂ : measure (α × β)}
  (h₁ : ∀ s t, is_measurable s → is_measurable t → μν₁ (s.prod t) = μ s * ν t)
  (h₂ : ∀ s t, is_measurable s → is_measurable t → μν₂ (s.prod t) = μ s * ν t) : μν₁ = μν₂ :=
begin
  refine ext_of_generate_from_of_Union _
    (λ i, (spanning_sets μ i).prod (spanning_sets ν i))
    generate_from_prod.symm is_pi_system_prod _ _ _ _,
  { rw [Union_prod_of_monotone (monotone_spanning_sets μ) (monotone_spanning_sets ν)],
    simp_rw [Union_spanning_sets, univ_prod_univ] },
  { intro i, apply mem_image2_of_mem; apply is_measurable_spanning_sets },
  { intro i, rw [h₁], apply ennreal.mul_lt_top; apply measure_spanning_sets_lt_top,
    all_goals { apply is_measurable_spanning_sets } },
  { rintro _ ⟨s, t, hs, ht, rfl⟩, simp * at * }
end

lemma prod_swap : map prod.swap (μ.prod ν) = ν.prod μ :=
begin
  refine prod_unique _ (λ _ _, prod_prod),
  intros s t hs ht,
  simp_rw [map_apply measurable_swap (hs.prod ht), preimage_swap_prod, prod_prod ht hs, mul_comm]
end

lemma prod_apply_symm {s : set (α × β)} (hs : is_measurable s) :
  μ.prod ν s = ∫⁻ y, μ ((λ x, (x, y)) ⁻¹' s) ∂ν :=
by { rw [← prod_swap, map_apply measurable_swap hs],
     simp only [prod_apply (measurable_swap hs)], refl }

instance prod.sigma_finite : sigma_finite (μ.prod ν) :=
⟨⟨λ n, (spanning_sets μ n).prod (spanning_sets ν n),
  λ n, (is_measurable_spanning_sets μ n).prod (is_measurable_spanning_sets ν n),
  λ n, by { simp_rw [prod_prod (is_measurable_spanning_sets μ n) (is_measurable_spanning_sets ν n)],
    apply ennreal.mul_lt_top (measure_spanning_sets_lt_top μ n) (measure_spanning_sets_lt_top ν n) },
  by { simp_rw [Union_prod_of_monotone (monotone_spanning_sets μ) (monotone_spanning_sets ν),
    Union_spanning_sets, univ_prod_univ] }⟩⟩

end both_sigma_finite

end measure

end measure_theory
open measure_theory measure_theory.measure

/-- The Lebesgue intergral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable. -/
lemma measurable.lintegral_prod_right' [sigma_finite ν] :
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

lemma measurable.lintegral_prod_right [sigma_finite ν] {f : α → β → ennreal}
  (hf : measurable (uncurry f)) : measurable (λ x, ∫⁻ y, f x y ∂ν) :=
hf.lintegral_prod_right'

/-- The Lebesgue intergral is measurable This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable. -/
lemma measurable.lintegral_prod_left' [sigma_finite μ] {f : α × β → ennreal}
  (hf : measurable f) : measurable (λ y, ∫⁻ x, f (x, y) ∂μ) :=
(measurable_swap_iff.mpr hf).lintegral_prod_right'

lemma measurable.lintegral_prod_left [sigma_finite μ] {f : α → β → ennreal}
  (hf : measurable (uncurry f)) : measurable (λ y, ∫⁻ x, f x y ∂μ) :=
hf.lintegral_prod_left'

namespace measure_theory

lemma lintegral_prod_swap [sigma_finite μ] [sigma_finite ν] (f : α × β → ennreal)
  (hf : measurable f) : ∫⁻ z, f z.swap ∂(ν.prod μ) = ∫⁻ z, f z ∂(μ.prod ν) :=
by rw [← lintegral_map hf measurable_swap, prod_swap]

/-- Tonelli's Theorem: For `ennreal`-valued measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
lemma lintegral_prod [sigma_finite ν] :
  ∀ (f : α × β → ennreal) (hf : measurable f), ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
begin
  have m := @measurable_prod_mk_left,
  refine measurable.ennreal_induction _ _ _,
  { intros c s hs, simp only [← indicator_comp_right],
    simp [lintegral_indicator, m hs, hs, lintegral_const_mul, hs.measure_prod_mk_left,
      prod_apply] },
  { rintro f g - hf hg h2f h2g,
    simp [lintegral_add, hf.comp m, hg.comp m, h2f, h2g, measurable.lintegral_prod_right', hf, hg] },
  { intros f hf h2f h3f,
    have kf : ∀ x n, measurable (λ y, f n (x, y)) := λ x n, (hf n).comp m,
    have k2f : ∀ x, monotone (λ n y, f n (x, y)) := λ x i j hij y, h2f hij (x, y),
    have lf : ∀ n, measurable (λ x, ∫⁻ y, f n (x, y) ∂ν) := λ n, (hf n).lintegral_prod_right',
    have l2f : monotone (λ n x, ∫⁻ y, f n (x, y) ∂ν) := λ i j hij x, lintegral_mono (k2f x hij),
    simp only [lintegral_supr hf h2f, lintegral_supr (kf _), k2f, lintegral_supr lf l2f, h3f] },
end

/-- The symmetric verion of Tonelli's Theorem: For `ennreal`-valued measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral, in reverse order. -/
lemma lintegral_prod_symm [sigma_finite μ] [sigma_finite ν] (f : α × β → ennreal)
  (hf : measurable f) : ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
by { simp_rw [← lintegral_prod_swap f hf], exact lintegral_prod _ (hf.comp measurable_swap) }

/-- The reversed version of Tonelli's Theorem. -/
lemma lintegral_lintegral [sigma_finite ν] ⦃f : α → β → ennreal⦄
  (hf : measurable (uncurry f)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.1 z.2 ∂(μ.prod ν) :=
(lintegral_prod _ hf).symm

/-- The reversed version of Tonelli's Theorem (symmetric version). -/
lemma lintegral_lintegral_symm [sigma_finite μ] [sigma_finite ν] ⦃f : α → β → ennreal⦄
  (hf : measurable (uncurry f)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.2 z.1 ∂(ν.prod μ) :=
(lintegral_prod_symm _ (hf.comp measurable_swap)).symm

/-- You can change the order of integration. -/
lemma lintegral_lintegral_swap [sigma_finite μ] [sigma_finite ν] ⦃f : α → β → ennreal⦄
  (hf : measurable (uncurry f)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν :=
(lintegral_lintegral hf).trans (lintegral_prod_symm _ hf)

end measure_theory
open measure_theory

variables {E : Type*} [normed_group E] [measurable_space E]

namespace measure_theory
variables [opens_measurable_space E]

lemma integrable.swap [sigma_finite μ] [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (f ∘ prod.swap) (ν.prod μ) :=
begin
  refine ⟨hf.measurable.comp measurable_swap, lt_of_le_of_lt (eq.le _) hf.has_finite_integral⟩,
  convert lintegral_prod_swap _ hf.measurable.ennnorm; apply_instance
end

lemma integrable_swap_iff [sigma_finite μ] [sigma_finite ν] ⦃f : α × β → E⦄ :
  integrable (f ∘ prod.swap) (ν.prod μ) ↔ integrable f (μ.prod ν) :=
⟨λ hf, by { convert hf.swap, ext ⟨x, y⟩, refl }, λ hf, hf.swap⟩

lemma has_finite_integral_prod_iff [sigma_finite ν] ⦃f : α × β → E⦄ (h1f : measurable f) :
  (∀ᵐ x ∂ μ, has_finite_integral (λ y, f (x, y)) ν) ∧
    has_finite_integral (λ x, ∫ y, ∥ f (x, y) ∥ ∂ν) μ ↔ has_finite_integral f (μ.prod ν) :=
begin
  simp only [has_finite_integral, lintegral_prod _ h1f.ennnorm],
  have : ∀ x, ∀ᵐ y ∂ν, 0 ≤ ∥ f (x, y) ∥ := λ x, eventually_of_forall (λ y, norm_nonneg _),
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _) (h1f.norm.comp measurable_prod_mk_left),
    ennnorm_eq_of_real (ennreal.to_real_nonneg), of_real_norm_eq_coe_nnnorm],
  -- this fact looks to specialized to be its own lemma
  have : ∀ {p q r : Prop} (h1 : r → p), (p ∧ q ↔ r) ↔ (p → (q ↔ r)) :=
  λ p q r h1, by rw [← and.congr_right_iff, and_iff_right_of_imp h1],
  rw [this],
  { intro h2f, rw lintegral_congr_ae,
    refine h2f.mp _, apply eventually_of_forall, intros x hx, dsimp,
    rw [ennreal.of_real_to_real], rw [← ennreal.lt_top_iff_ne_top], exact hx },
  { intro h2f, refine ae_lt_top _ h2f, exact h1f.ennnorm.lintegral_prod_right' },
end

end measure_theory
open measure_theory

lemma is_measurable_integrable [opens_measurable_space E] [sigma_finite ν] ⦃f : α → β → E⦄
  (hf : measurable (uncurry f)) : is_measurable { x | integrable (f x) ν } :=
begin
  simp [integrable, hf.of_uncurry_left],
  refine is_measurable_lt (measurable.lintegral_prod_right _) measurable_const,
  exact hf.ennnorm
end

section
variables [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [borel_space E]

lemma integral_prod_swap [sigma_finite μ] [sigma_finite ν] (f : α × β → E)
  (hf : measurable f) : ∫ z, f z.swap ∂(ν.prod μ) = ∫ z, f z ∂(μ.prod ν) :=
by rw [← integral_map_measure measurable_swap hf, prod_swap]

/-- The Bochner intergral is measurable. This shows that the integrand of (the right-hand-side of)
  Fubini's theorem is measurable. -/
lemma measurable.integral_prod_right [sigma_finite ν] ⦃f : α → β → E⦄
  (hf : measurable (uncurry f)) : measurable (λ x, ∫ y, f x y ∂ν) :=
begin
  let s : ℕ → simple_func (α × β) E := simple_func.approx_on _ hf univ _ (mem_univ 0),
  let s' : ℕ → α → simple_func β E := λ n x, (s n).comp (prod.mk x) measurable_prod_mk_left,
  let f' : ℕ → α → E := λ n, {x | integrable (f x) ν}.indicator
    (λ x, (s' n x).integral ν),
  have hf' : ∀ n, measurable (f' n),
  { intro n, refine measurable.indicator _ (is_measurable_integrable hf),
    have : ∀ x, (s' n x).range.filter (λ x, x ≠ 0) ⊆
      (s n).range,
    { intros x, refine finset.subset.trans (finset.filter_subset _) _, intro y,
      simp_rw [simple_func.mem_range], rintro ⟨z, rfl⟩, exact ⟨(x, z), rfl⟩ },
    simp only [simple_func.integral_eq_sum_of_subset (this _)],
    refine finset.measurable_sum _ _, intro x,
    refine (measurable.to_real _).smul measurable_const,
    simp only [simple_func.coe_comp, preimage_comp] {single_pass := tt},
    apply is_measurable.measure_prod_mk_left,
    exact (s n).is_measurable_fiber x },
  have h2f' : tendsto f' at_top (𝓝 (λ (x : α), ∫ (y : β), f x y ∂ν)),
  { rw [tendsto_pi], intro x,
    by_cases hfx : integrable (f x) ν,
    { have : ∀ n, integrable (s' n x) ν := λ n, (hfx.norm.add hfx.norm).mono' (s' n x).measurable
        (eventually_of_forall $
          λ y, by { dsimp [s'], exact simple_func.norm_approx_on_zero_le _ _ (x, y) n }),
      simp only [f', hfx, simple_func.integral_eq_integral _ (this _), indicator_of_mem,
        mem_set_of_eq],
      refine tendsto_integral_of_dominated_convergence (λ y, ∥f x y∥ + ∥f x y∥)
        (λ n, (s' n x).measurable) hf.of_uncurry_left (hfx.norm.add hfx.norm) _ _,
      { exact λ n, eventually_of_forall (λ y, simple_func.norm_approx_on_zero_le _ _ (x, y) n) },
      { exact eventually_of_forall (λ y, simple_func.tendsto_approx_on _ _ (by simp)) } },
    { simpa [f', hfx, integral_undef] using @tendsto_const_nhds _ _ _ (0 : E) _, }
     },
  exact measurable_of_tendsto_metric hf' h2f'
end

lemma measurable.integral_prod_right' [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : measurable f) : measurable (λ x, ∫ y, f (x, y) ∂ν) :=
by { rw [← uncurry_curry f] at hf, exact hf.integral_prod_right }

end

namespace measure_theory

section
variables [opens_measurable_space E]

lemma integrable_prod_iff [sigma_finite ν] ⦃f : α × β → E⦄ (h1f : measurable f) :
  (∀ᵐ x ∂ μ, integrable (λ y, f (x, y)) ν) ∧ integrable (λ x, ∫ y, ∥ f (x, y) ∥ ∂ν) μ ↔
  integrable f (μ.prod ν) :=
by simp only [integrable, h1f, h1f.comp measurable_prod_mk_left, h1f.norm.integral_prod_right',
  true_and, has_finite_integral_prod_iff]

lemma integrable_prod_iff' [sigma_finite μ] [sigma_finite ν] ⦃f : α × β → E⦄ (h1f : measurable f) :
  (∀ᵐ y ∂ ν, integrable (λ x, f (x, y)) μ) ∧ integrable (λ y, ∫ x, ∥ f (x, y) ∥ ∂μ) ν ↔
  integrable f (μ.prod ν) :=
by { convert integrable_prod_iff (h1f.comp measurable_swap) using 1, rw [integrable_swap_iff],
  apply_instance }

lemma integrable.prod_left_ae [sigma_finite μ] [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : ∀ᵐ y ∂ ν, integrable (λ x, f (x, y)) μ :=
((integrable_prod_iff' hf.measurable).mpr hf).1

lemma integrable.prod_right_ae [sigma_finite μ] [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : ∀ᵐ x ∂ μ, integrable (λ y, f (x, y)) ν :=
hf.swap.prod_left_ae

lemma integrable.integral_norm_prod_left [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ x, ∫ y, ∥ f (x, y) ∥ ∂ν) μ :=
((integrable_prod_iff hf.measurable).mpr hf).2

lemma integrable.integral_norm_prod_right [sigma_finite μ] [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ y, ∫ x, ∥ f (x, y) ∥ ∂μ) ν :=
hf.swap.integral_norm_prod_left

end

variables [second_countable_topology E] [normed_space ℝ E]
  [complete_space E] [borel_space E]

lemma integrable.integral_prod_left [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ x, ∫ y, f (x, y) ∂ν) μ :=
integrable.mono hf.integral_norm_prod_left hf.measurable.integral_prod_right' $
  eventually_of_forall $ λ x, (norm_integral_le_integral_norm _).trans_eq $
  (norm_eq_self $ integral_nonneg_of_ae $ eventually_of_forall $ λ y, (norm_nonneg _ : _)).symm

lemma integrable.integral_prod_right [sigma_finite μ] [sigma_finite ν] ⦃f : α × β → E⦄
  (hf : integrable f (μ.prod ν)) : integrable (λ y, ∫ x, f (x, y) ∂μ) ν :=
hf.swap.integral_prod_left

lemma measure_prod_null_of_is_measurable [sigma_finite ν] {s : set (α × β)}
  (hs : is_measurable s) : μ.prod ν s = 0 ↔ (λ x, ν (prod.mk x ⁻¹' s)) =ᵐ[μ] 0 :=
by simp_rw [prod_apply hs, lintegral_eq_zero_iff hs.measure_prod_mk_left]

-- todo: rename or prove iff
lemma measure_prod_null [sigma_finite ν] {s : set (α × β)}
  (h : μ.prod ν s = 0) : (λ x, ν (prod.mk x ⁻¹' s)) =ᵐ[μ] 0 :=
begin
  obtain ⟨t, hst, mt, ht⟩ := exists_is_measurable_superset_of_measure_eq_zero h,
  simp_rw [measure_prod_null_of_is_measurable mt] at ht,
  rw [eventually_le_antisymm_iff],
  exact ⟨eventually_le.trans_eq
    (eventually_of_forall $ λ x, (measure_mono (preimage_mono hst) : _)) ht,
    eventually_of_forall $ λ x, zero_le _⟩
end

lemma ae_prod [sigma_finite ν] {p : α × β → Prop} (h : ∀ᵐ z ∂μ.prod ν, p z) :
  ∀ᵐ x ∂ μ, ∀ᵐ y ∂ ν, p (x, y) :=
measure_prod_null h

-- lemma measure_prod_null [sigma_finite μ] [sigma_finite ν] {s : set (α × β)} :
--   μ.prod ν s = 0 ↔ (λ x, ν (prod.mk x ⁻¹' s)) =ᵐ[μ] 0 :=
-- begin
--   split,
--   { intro h, obtain ⟨t, hst, mt, ht⟩ := exists_is_measurable_superset_of_measure_eq_zero h,
--     simp_rw [measure_prod_null_of_is_measurable mt] at ht,
--     rw [eventually_le_antisymm_iff],
--     exact ⟨eventually_le.trans_eq
--       (eventually_of_forall $ λ x, (measure_mono (preimage_mono hst) : _)) ht,
--       eventually_of_forall $ λ x, zero_le _⟩ },
--   { intro h, obtain ⟨t, hst, mt, ht⟩ := exists_is_measurable_superset_of_measure_eq_zero h,
--     dsimp [set_of_compl, ← ne.def] at hst,
--     have : (μ.prod ν) (t.prod univ) = 0,
--     { simp_rw [prod_prod mt is_measurable.univ, ht, zero_mul] },
--     refine measure_mono_null _ this, rintro ⟨x, y⟩ hxy, refine ⟨hst _, mem_univ y⟩, sorry
--      }
-- end

-- lemma ae_prod [sigma_finite μ] [sigma_finite ν] {p : α × β → Prop} :
--   (∀ᵐ z ∂μ.prod ν, p z) ↔ ∀ᵐ x ∂ μ, ∀ᵐ y ∂ ν, p (x, y) :=
-- begin
--   exact measure_prod_null,
-- end

variables {E' : Type*} [measurable_space E'] [normed_group E'] [borel_space E'] [complete_space E']
  [normed_space ℝ E'] [second_countable_topology E']

lemma integral_fn_integral_add [sigma_finite μ] [sigma_finite ν] ⦃f g : α × β → E⦄
  {F : E → E'} (hF : measurable F)
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, F (∫ y, f (x, y) + g (x, y) ∂ν) ∂μ = ∫ x, F (∫ y, f (x, y) ∂ν + ∫ y, g (x, y) ∂ν) ∂μ :=
begin
  refine integral_congr_ae
    (hF.comp (hf.add hg).measurable.integral_prod_right')
    (hF.comp (hf.measurable.integral_prod_right'.add hg.measurable.integral_prod_right')) _,
  refine hg.prod_right_ae.mp _, refine hf.prod_right_ae.mp _,
  apply eventually_of_forall, intros x h2f h2g, simp [integral_add h2f h2g]
end

lemma integral_fn_integral_sub [sigma_finite μ] [sigma_finite ν] ⦃f g : α × β → E⦄
  {F : E → E'} (hF : measurable F)
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ = ∫ x, F (∫ y, f (x, y) ∂ν - ∫ y, g (x, y) ∂ν) ∂μ :=
begin
  refine integral_congr_ae
    (hF.comp (hf.sub hg).measurable.integral_prod_right')
    (hF.comp (hf.measurable.integral_prod_right'.sub hg.measurable.integral_prod_right')) _,
  refine hg.prod_right_ae.mp _, refine hf.prod_right_ae.mp _,
  apply eventually_of_forall, intros x h2f h2g, simp [integral_sub h2f h2g]
end

lemma lintegral_fn_integral_sub [sigma_finite μ] [sigma_finite ν] ⦃f g : α × β → E⦄
  (F : E → ennreal) (hf : integrable f (μ.prod ν)) (hg : integrable g (μ.prod ν)) :
  ∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂ν) ∂μ = ∫⁻ x, F (∫ y, f (x, y) ∂ν - ∫ y, g (x, y) ∂ν) ∂μ :=
begin
  refine lintegral_congr_ae _,
  refine hg.prod_right_ae.mp _, refine hf.prod_right_ae.mp _,
  apply eventually_of_forall, intros x h2f h2g, simp [integral_sub h2f h2g]
end

lemma integral_integral_add [sigma_finite μ] [sigma_finite ν] ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, f (x, y) + g (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν + ∫ y, g (x, y) ∂ν ∂μ :=
integral_fn_integral_add measurable_id hf hg

lemma integral_integral_add' [sigma_finite μ] [sigma_finite ν] ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, (f + g) (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν + ∫ y, g (x, y) ∂ν ∂μ :=
integral_integral_add hf hg

lemma integral_integral_sub [sigma_finite μ] [sigma_finite ν] ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, f (x, y) - g (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν - ∫ y, g (x, y) ∂ν ∂μ :=
integral_fn_integral_sub measurable_id hf hg

lemma integral_integral_sub' [sigma_finite μ] [sigma_finite ν] ⦃f g : α × β → E⦄
  (hf : integrable f (μ.prod ν))
  (hg : integrable g (μ.prod ν)) :
  ∫ x, ∫ y, (f - g) (x, y) ∂ν ∂μ = ∫ x, ∫ y, f (x, y) ∂ν - ∫ y, g (x, y) ∂ν ∂μ :=
integral_integral_sub hf hg

lemma continuous_integral_integral [sigma_finite μ] [sigma_finite ν] :
  continuous (λ (f : α × β →₁[μ.prod ν] E), ∫ x, ∫ y, f (x, y) ∂ν ∂μ) :=
begin
  rw [continuous_iff_continuous_at], intro g,
  refine tendsto_integral_of_l1 _ g.integrable.integral_prod_left
    (eventually_of_forall $ λ h, h.integrable.integral_prod_left) _,
  simp_rw [edist_eq_coe_nnnorm_sub,
    ← lintegral_fn_integral_sub (λ x, (nnnorm x : ennreal)) (l1.integrable _) g.integrable],
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (λ i, zero_le _) _,
  { exact λ i, ∫⁻ x, ∫⁻ y, ennreal.of_real (∥i (x, y) - g (x, y)∥) ∂ν ∂μ },
  swap, { exact λ i, lintegral_mono (λ x, ennnorm_integral_le_lintegral_norm _) },
  simp_rw [of_real_norm_eq_coe_nnnorm],
  show tendsto (λ (i : α × β →₁[μ.prod ν] E),
    ∫⁻ x, ∫⁻ (y : β), nnnorm (i (x, y) - g (x, y)) ∂ν ∂μ) (𝓝 g) (𝓝 0),
  have : ∀ (i : α × β →₁[μ.prod ν] E), measurable (λ z, (nnnorm (i z - g z) : ennreal)) :=
  λ i, (i.measurable.sub g.measurable).ennnorm,
  simp_rw [← lintegral_prod _ (this _), ← l1.of_real_norm_sub_eq_lintegral,
    ← ennreal.of_real_zero],
  refine (ennreal.continuous_of_real.tendsto 0).comp _,
  rw [← tendsto_iff_norm_tendsto_zero], exact tendsto_id
end

/-- Fubini's Theorem: For integrable functions on `α × β`,
  the Bochner integral of `f` is equal to the iterated Bochner integral. -/
lemma integral_prod [t2_space E] [sigma_finite μ] [sigma_finite ν] :
  ∀ ⦃f : α × β → E⦄ (hf : integrable f (μ.prod ν)),
  ∫ z, f z ∂(μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
begin
  apply integrable.induction,
  { intros c s hs h2s, simp_rw [integral_indicator measurable_const hs, ← indicator_comp_right,
      function.comp, integral_indicator measurable_const (measurable_prod_mk_left hs),
      set_integral_const], rw [integral_smul_const (integrable_measure_prod_mk_left hs h2s)],
      simp_rw [integral_to_real hs.measure_prod_mk_left (ae_measure_lt_top hs h2s), prod_apply hs] },
  { intros f g hfg i_f i_g hf hg,
    simp_rw [integral_add' i_f i_g, hf, hg,
      ← integral_add i_f.integral_prod_left i_g.integral_prod_left,
      integral_integral_add' i_f i_g] },
  { exact is_closed_eq continuous_integral continuous_integral_integral },
  { intros f g hfg i_f m_g hf, convert hf using 1,
    { exact integral_congr_ae m_g i_f.measurable hfg.symm },
    { refine integral_congr_ae m_g.integral_prod_right' i_f.measurable.integral_prod_right' _,
      rw [eventually_eq] at hfg, refine (ae_prod hfg).mp _,
      apply eventually_of_forall, intros x hfgx,
      refine integral_congr_ae (m_g.comp measurable_prod_mk_left)
        (i_f.measurable.comp measurable_prod_mk_left) (ae_eq_symm hfgx) } }
end

end measure_theory
