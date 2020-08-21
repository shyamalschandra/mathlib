import order.order_iso_nat

open_locale classical

variable {α : Type*}

variables (α) [preorder α]

abbreviation DCC : Prop := well_founded ((<) : α → α → Prop)

abbreviation ACC : Prop := well_founded ((>) : α → α → Prop)

variable {α}

section extrema

lemma exists_min_of_DCC : DCC α → ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, ¬ x < m :=
λ wf a ha, ⟨well_founded.min wf a ha, well_founded.min_mem _ _ _,
  λ x hx, well_founded.not_lt_min wf a ha hx⟩

lemma DCC_of_exists_min
  (exists_min : ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, ¬ x < m) :
  DCC α :=
⟨begin
  set counterexamples := {x : α | ¬ acc has_lt.lt x},
  intro x,
  by_contra hx,
  obtain ⟨m, m_mem, hm⟩ := exists_min counterexamples ⟨x, hx⟩,
  refine m_mem (acc.intro _ (λ y y_gt_m, _)),
  by_contra hy,
  apply (hm y hy) y_gt_m,
end⟩

theorem DCC_iff_exists_min : DCC α ↔ ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, ¬ x < m :=
⟨exists_min_of_DCC, DCC_of_exists_min⟩

lemma exists_max_of_ACC : ACC α → ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, ¬ m < x :=
λ wf a ha, ⟨well_founded.min wf a ha, well_founded.min_mem _ _ _,
  λ x hx, well_founded.not_lt_min wf a ha hx⟩

lemma ACC_of_exists_max
  (exists_max : ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, ¬ m < x) :
  ACC α :=
⟨begin
  set counterexamples := {x : α | ¬ acc gt x},
  intro x,
  by_contra hx,
  obtain ⟨m, m_mem, hm⟩ := exists_max counterexamples ⟨x, hx⟩,
  refine m_mem (acc.intro _ (λ y y_gt_m, _)),
  by_contra hy,
  apply (hm y hy) y_gt_m,
end⟩

theorem ACC_iff_exists_max : ACC α ↔ ∀ (p : set α), p.nonempty → ∃ m ∈ p, ∀ x ∈ p, ¬ m < x :=
⟨exists_max_of_ACC, ACC_of_exists_max⟩

end extrema

theorem ACC_dual_iff_DCC : ACC (order_dual α) ↔ DCC α := iff.refl _

theorem DCC_dual_iff_ACC : DCC (order_dual α) ↔ ACC α := iff.refl _

theorem nat.DCC : DCC ℕ := nat.lt_wf

theorem nat.not_ACC : ¬ ACC ℕ := by {
  intro con, apply rel_embedding.well_founded_iff_no_descending_seq.1 con,
  have f : gt ↪r gt := rel_embedding.nat_gt (id) (λ n, by apply nat.lt_succ_self),
  apply nonempty_of_exists, swap, {intro _, apply true},
  existsi f, exact trivial, }

namespace rel_embedding
variables {β : Type*} [preorder β] (f : α ↪o β)
include f

protected theorem DCC : DCC β → DCC α := f.well_founded

theorem not_DCC : ¬ DCC α → ¬ DCC β := by { contrapose!, exact f.DCC }

protected theorem ACC : ACC β → ACC α := f.osymm.well_founded

theorem not_ACC : ¬ ACC α → ¬ ACC β := by { contrapose!, exact f.ACC }

end rel_embedding

namespace order_iso
variables {β : Type*} [preorder β] (f : α ≃o β)
include f

theorem ACC_iff : ACC α ↔ ACC β := ⟨f.symm.to_rel_embedding.ACC, f.to_rel_embedding.ACC⟩

theorem DCC_iff : DCC α ↔ DCC β := ⟨f.symm.to_rel_embedding.DCC, f.to_rel_embedding.DCC⟩

end order_iso

namespace subtype

variables (p : α → Prop)

def order_embedding [preorder α] : {x // p x} ↪o α :=
{ to_fun := subtype.val,
  inj' := subtype.val_injective,
  map_rel_iff' := λ a b, iff.refl _, }

protected theorem DCC : DCC α → DCC {x // p x} := (order_embedding p).DCC

protected theorem ACC : ACC α → ACC {x // p x} := (order_embedding p).ACC

theorem not_DCC : ¬ DCC {x // p x} → ¬ DCC α := (order_embedding p).not_DCC

theorem not_ACC : ¬ ACC {x // p x} → ¬ ACC α := (order_embedding p).not_ACC

end subtype

theorem boolean_algebra.ACC_iff_DCC {β : Type*} [boolean_algebra β] : ACC β ↔ DCC β :=
iff.trans (compl_order_iso β).ACC_iff ACC_dual_iff_DCC
