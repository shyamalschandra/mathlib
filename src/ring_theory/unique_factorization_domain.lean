/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

Theory of unique factorization domains.

@TODO: setup the complete lattice structure on `factor_set`.
-/
import algebra.gcd_monoid
import ring_theory.integral_domain
import ring_theory.noetherian

variables {α : Type*}
local infix ` ~ᵤ ` : 50 := associated

/-- This class refers to `comm_cancel_monoid_with_zero`s whose divisibility relation
satisfies the descending chain condition. -/
class DCC_dvd (α : Type*) [comm_cancel_monoid_with_zero α] : Prop :=
(well_founded_dvd_not_unit : well_founded (λ a b : α, a ≠ 0 ∧ ∃ x, ¬is_unit x ∧ b = a * x))

instance is_noetherian_ring.DCC_dvd [integral_domain α] [is_noetherian_ring α] :
  DCC_dvd α :=
⟨is_noetherian_ring.well_founded_dvd_not_unit⟩

instance polynomial.DCC_dvd [integral_domain α] [DCC_dvd α] : DCC_dvd (polynomial α) :=
{ well_founded_dvd_not_unit := begin
    classical,
    apply rel_hom.well_founded, swap,
    exact (prod.lex_wf (with_top.well_founded_lt $ with_bot.well_founded_lt nat.lt_wf)
      _inst_2.well_founded_dvd_not_unit),
    exact {
      to_fun := λ p, (if p = 0 then ⊤ else ↑p.degree, p.leading_coeff),
      map_rel' := λ a b ⟨ane0, ⟨c, ⟨not_unit_c, bac⟩⟩⟩, begin
        rw bac, rw polynomial.degree_mul, rw if_neg ane0, by_cases c = 0,
        { simp only [h, if_true, polynomial.leading_coeff_zero, eq_self_iff_true, ne.def, mul_zero],
          apply prod.lex.left _ _ (lt_of_le_of_ne le_top _), apply with_top.coe_ne_top, },
        { simp only [h, ane0, if_false, ne.def, polynomial.leading_coeff_mul, or_self, mul_eq_zero],
          rename h cne0, by_cases c.degree = 0,
        { simp only [h, add_zero, ne.def, polynomial.leading_coeff_mul],
          apply prod.lex.right, split, {rw polynomial.leading_coeff_eq_zero, apply ane0},
          use c.leading_coeff, split, swap, {refl},
          contrapose! not_unit_c, rw polynomial.is_unit_iff, use c.leading_coeff,
          split, {exact not_unit_c}, rw polynomial.leading_coeff,
          convert (polynomial.eq_C_of_degree_eq_zero h).symm,
          apply polynomial.nat_degree_eq_of_degree_eq_some h,},
        { apply prod.lex.left, rw polynomial.degree_eq_nat_degree cne0 at *,
          rw [with_top.coe_lt_coe, polynomial.degree_eq_nat_degree ane0,
            ← with_bot.coe_add, with_bot.coe_lt_coe],
          apply lt_add_of_pos_right, apply nat.pos_of_ne_zero, contrapose! h, rw h, refl, }, }
      end }
  end }

namespace DCC_dvd

variables [comm_cancel_monoid_with_zero α] [DCC_dvd α]

open associates nat

theorem well_founded_associates : well_founded ((<) : associates α → associates α → Prop) :=
begin
  sorry
end

local attribute [elab_as_eliminator] well_founded.fix

lemma exists_irreducible_factor {a : α} (ha : ¬ is_unit a) (ha0 : a ≠ 0) :
  ∃ i, irreducible i ∧ i ∣ a :=
(irreducible_or_factor a ha).elim (λ hai, ⟨a, hai, dvd_refl _⟩)
  (well_founded.fix
    DCC_dvd.well_founded_dvd_not_unit
    (λ a ih ha ha0 ⟨x, y, hx, hy, hxy⟩,
      have hx0 : x ≠ 0, from λ hx0, ha0 (by rw [← hxy, hx0, zero_mul]),
      (irreducible_or_factor x hx).elim
        (λ hxi, ⟨x, hxi, hxy ▸ by simp⟩)
        (λ hxf, let ⟨i, hi⟩ := ih x ⟨hx0, y, hy, hxy.symm⟩ hx hx0 hxf in
          ⟨i, hi.1, dvd.trans hi.2 (hxy ▸ by simp)⟩)) a ha ha0)

@[elab_as_eliminator] lemma induction_on_irreducible {P : α → Prop} (a : α)
  (h0 : P 0) (hu : ∀ u : α, is_unit u → P u)
  (hi : ∀ a i : α, a ≠ 0 → irreducible i → P a → P (i * a)) :
  P a :=
by haveI := classical.dec; exact
well_founded.fix DCC_dvd.well_founded_dvd_not_unit
  (λ a ih, if ha0 : a = 0 then ha0.symm ▸ h0
    else if hau : is_unit a then hu a hau
    else let ⟨i, hii, ⟨b, hb⟩⟩ := exists_irreducible_factor hau ha0 in
      have hb0 : b ≠ 0, from λ hb0, by simp * at *,
      hb.symm ▸ hi _ _ hb0 hii (ih _ ⟨hb0, i,
        hii.1, by rw [hb, mul_comm]⟩))
  a

lemma exists_factors (a : α) : a ≠ 0 →
  ∃f : multiset α, (∀b ∈ f, irreducible b) ∧ associated a f.prod :=
DCC_dvd.induction_on_irreducible a
  (λ h, (h rfl).elim)
  (λ u hu _, ⟨0, by simp [associated_one_iff_is_unit, hu]⟩)
  (λ a i ha0 hii ih hia0,
    let ⟨s, hs⟩ := ih ha0 in
    ⟨i::s, ⟨by clear _let_match; finish,
      by rw multiset.prod_cons;
        exact associated_mul_mul (by refl) hs.2⟩⟩)

end DCC_dvd

theorem DCC_dvd_of_well_founded_associates [comm_cancel_monoid_with_zero α]
  (h : well_founded ((<) : associates α → associates α → Prop)): DCC_dvd α :=
⟨by { refine rel_hom.well_founded _ h,
  exact { to_fun := associates.mk,
    map_rel' := λ a b ⟨ane0, ⟨c, ⟨hc, bac⟩⟩⟩,
      by { rw bac, apply lt_of_le_of_ne (associates.mk_le_mk_of_dvd (dvd.intro c rfl)),
        intro con, rw associates.mk_eq_mk_iff_associated at con, apply hc,
        rw ← associated_one_iff_is_unit, symmetry, apply associated_mul_left_cancel,
        convert con, apply mul_one, refl, exact ane0, }}}⟩

theorem DCC_dvd_iff_well_founded_associates [comm_cancel_monoid_with_zero α] :
  DCC_dvd α ↔ well_founded ((<) : associates α → associates α → Prop) :=
⟨by apply DCC_dvd.well_founded_associates, DCC_dvd_of_well_founded_associates⟩

/-- Unique factorization monoids.

These are defined as `comm_cancel_monoid_with_zero`s with the descending chain condition on
the divisibility relation, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_unique_irreducible_factorization`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factorization`

-/
class unique_factorization_monoid (α : Type*) [comm_cancel_monoid_with_zero α] extends DCC_dvd α :
  Prop :=
(irreducible_iff_prime : ∀ {a : α}, irreducible a ↔ prime a )

instance ufm_of_gcd_of_DCC_dvd [nontrivial α] [comm_cancel_monoid_with_zero α]
  [DCC_dvd α] [gcd_monoid α] : unique_factorization_monoid α :=
{ irreducible_iff_prime := λ _, gcd_monoid.irreducible_iff_prime
  .. ‹DCC_dvd α› }

namespace unique_factorization_monoid
variables [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α]

theorem exists_prime_factors (a : α) : a ≠ 0 →
  ∃ f : multiset α, (∀b ∈ f, prime b) ∧ a ~ᵤ f.prod :=
by { simp_rw ← unique_factorization_monoid.irreducible_iff_prime, apply DCC_dvd.exists_factors a, }

@[elab_as_eliminator] lemma induction_on_prime {P : α → Prop}
  (a : α) (h₁ : P 0) (h₂ : ∀ x : α, is_unit x → P x)
  (h₃ : ∀ a p : α, a ≠ 0 → prime p → P a → P (p * a)) : P a :=
begin
  simp_rw ← unique_factorization_monoid.irreducible_iff_prime at h₃,
  exact DCC_dvd.induction_on_irreducible a h₁ h₂ h₃,
end

lemma unique : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod →
  multiset.rel associated f g :=
by haveI := classical.dec_eq α; exact
λ f, multiset.induction_on f
  (λ g _ hg h,
    multiset.rel_zero_left.2 $
      multiset.eq_zero_of_forall_not_mem (λ x hx,
        have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
        (hg x hx).1 (is_unit_iff_dvd_one.2 (dvd.trans (multiset.dvd_prod hx)
          (is_unit_iff_dvd_one.1 this)))))
  (λ p f ih g hf hg hfg,
    let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
      (irreducible_iff_prime.1 (hf p (by simp)))
      (λ q hq, irreducible_iff_prime.1 (hg _ hq)) $
        (dvd_iff_dvd_of_rel_right hfg).1
          (show p ∣ (p :: f).prod, by simp) in
    begin
      rw ← multiset.cons_erase hbg,
      exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
        (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
        (associated_mul_left_cancel
          (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
        (hf p (by simp)).ne_zero))
    end)

end unique_factorization_monoid

lemma prime_factors_unique [comm_cancel_monoid_with_zero α] : ∀{f g : multiset α},
  (∀x∈f, prime x) → (∀x∈g, prime x) → f.prod ~ᵤ g.prod →
  multiset.rel associated f g :=
by haveI := classical.dec_eq α; exact
λ f, multiset.induction_on f
  (λ g _ hg h,
    multiset.rel_zero_left.2 $
      multiset.eq_zero_of_forall_not_mem (λ x hx,
        have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
        (irreducible_of_prime $ hg x hx).1 (is_unit_iff_dvd_one.2 (dvd.trans (multiset.dvd_prod hx)
          (is_unit_iff_dvd_one.1 this)))))
  (λ p f ih g hf hg hfg,
    let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
      (hf p (by simp)) (λ q hq, hg _ hq) $
        (dvd_iff_dvd_of_rel_right hfg).1
          (show p ∣ (p :: f).prod, by simp) in
    begin
      rw ← multiset.cons_erase hbg,
      exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
        (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
        (associated_mul_left_cancel
          (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
        (hf p (by simp)).ne_zero))
    end)

lemma prime_factors_irreducible [comm_cancel_monoid_with_zero α] {a : α} {f : multiset α}
  (ha : irreducible a) (pfa : (∀b ∈ f, prime b) ∧ a ~ᵤ f.prod) :
  ∃ p, a ~ᵤ p ∧ f = p :: 0 :=
by haveI := classical.dec_eq α; exact
multiset.induction_on f
  (λ h, (ha.1 (associated_one_iff_is_unit.1 h)).elim)
  (λ p s _ hp hs, let ⟨u, hu⟩ := hp in ⟨p,
    have hs0 : s = 0, from classical.by_contradiction
      (λ hs0, let ⟨q, hq⟩ := multiset.exists_mem_of_ne_zero hs0 in
       (hs q (by simp [hq])).2.1 $
        (ha.2 ((p * ↑(u⁻¹)) * (s.erase q).prod) _
          (by {rw [mul_right_comm _ _ q, mul_assoc, ← multiset.prod_cons, multiset.cons_erase hq,
            mul_comm p _, mul_assoc, ← multiset.prod_cons, hu.symm, mul_comm, mul_assoc],
            simp, })).resolve_left $
              mt is_unit_of_mul_is_unit_left $ mt is_unit_of_mul_is_unit_left
                (hs p (multiset.mem_cons_self _ _)).2.1),
    ⟨(by {clear _let_match; simp * at *}), hs0 ▸ rfl⟩⟩)
  (pfa.2) (pfa.1)

section exists_prime_factors

variables [comm_cancel_monoid_with_zero α]
  (pf : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, prime b) ∧ a ~ᵤ f.prod)

include pf

lemma DCC_dvd_of_exists_prime_factors : DCC_dvd α :=
⟨begin
    classical,
    apply rel_hom.well_founded (rel_hom.mk _ _) (with_top.well_founded_lt nat.lt_wf),
    { intro a, by_cases a = 0, exact ⊤, exact (classical.some (pf a h)).card, },
    { intros a b hab, rw dif_neg hab.1, by_cases b = 0, { simp [h, lt_top_iff_ne_top], },
      rw [dif_neg h, with_top.coe_lt_coe],
      cases hab.2 with c hc, have cne0 : c ≠ 0, { intro con, apply h, rw [hc.2, con, mul_zero], },
      rw hc.2 at hab, apply lt_of_lt_of_le,
      apply lt_add_of_pos_right, rw multiset.card_pos, swap, exact (classical.some (pf c cne0)),
      { intro con, apply hc.1, rw is_unit_iff_of_associated, apply is_unit_one,
        convert (classical.some_spec (pf c cne0)).2, simp [con], },
      rw ← multiset.card_add,
      apply le_of_eq (multiset.card_eq_card_of_rel (prime_factors_unique _ (classical.some_spec (pf _ h)).1 _)),
      { intros x hadd, rw multiset.mem_add at hadd,
        cases hadd; apply (classical.some_spec (pf _ _)).1 _ hadd, },
      { rw multiset.prod_add, transitivity a * c,
        { apply associated_mul_mul; apply (classical.some_spec (pf _ _)).2.symm, },
        { rw ← hc.2, apply (classical.some_spec (pf _ _)).2, } } },
end⟩

lemma irreducible_iff_prime_of_exists_prime_factors {p : α} : irreducible p ↔ prime p :=
by letI := classical.dec_eq α; exact
if hp0 : p = 0 then by simp [hp0]
else
  ⟨λ h, begin
    cases pf p hp0 with f hf, cases prime_factors_irreducible h hf with q hq,
    rw prime_iff_of_associated hq.1, apply hf.1 q, rw hq.2, simp,
  end,
    irreducible_of_prime⟩

theorem unique_factorization_monoid_of_exists_prime_factors :
  unique_factorization_monoid α :=
{ irreducible_iff_prime := λ _, irreducible_iff_prime_of_exists_prime_factors pf,
  .. DCC_dvd_of_exists_prime_factors pf }

end exists_prime_factors

theorem unique_factorization_monoid_iff_exists_prime_factors [comm_cancel_monoid_with_zero α] :
  unique_factorization_monoid α ↔
    (∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, prime b) ∧ a ~ᵤ f.prod) :=
⟨λ h, @unique_factorization_monoid.exists_prime_factors _ _ h,
  unique_factorization_monoid_of_exists_prime_factors⟩

theorem irreducible_iff_prime_of_exists_unique_irreducible_factors [comm_cancel_monoid_with_zero α]
  (eif : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, irreducible b) ∧ a ~ᵤ f.prod)
  (uif : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod → multiset.rel associated f g) :
  ∀ (p : α), irreducible p ↔ prime p :=
λ p, ⟨by letI := classical.dec_eq α; exact λ hpi,
    ⟨hpi.ne_zero, hpi.1,
      λ a b ⟨x, hx⟩,
      if hab0 : a * b = 0
      then (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim
        (λ ha0, by simp [ha0])
        (λ hb0, by simp [hb0])
      else
        have hx0 : x ≠ 0, from λ hx0, by simp * at *,
        have ha0 : a ≠ 0, from left_ne_zero_of_mul hab0,
        have hb0 : b ≠ 0, from right_ne_zero_of_mul hab0,
        begin
          cases eif x hx0 with fx hfx,
          cases eif a ha0 with fa hfa,
          cases eif b hb0 with fb hfb,
          have h : multiset.rel associated (p :: fx) (fa + fb),
          { apply uif,
            { exact λ i hi, (multiset.mem_cons.1 hi).elim (λ hip, hip.symm ▸ hpi) (hfx.1 _), },
            { exact λ i hi, (multiset.mem_add.1 hi).elim (hfa.1 _) (hfb.1 _), },
            calc multiset.prod (p :: fx)
                  ~ᵤ a * b : by rw [hx, multiset.prod_cons];
                    exact associated_mul_mul (by refl)
                      (hfx.2.symm)
              ... ~ᵤ (fa).prod * (fb).prod :
                associated_mul_mul hfa.2 hfb.2
              ... = _ : by rw multiset.prod_add, },
          exact let ⟨q, hqf, hq⟩ := multiset.exists_mem_of_rel_of_mem h
          (multiset.mem_cons_self p _) in
        (multiset.mem_add.1 hqf).elim
          (λ hqa, or.inl $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right hfa.2.symm).1
              (multiset.dvd_prod hqa))
          (λ hqb, or.inr $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right hfb.2.symm).1
              (multiset.dvd_prod hqb))
        end⟩, irreducible_of_prime⟩

namespace unique_factorization_monoid
variables [comm_cancel_monoid_with_zero α] [decidable_eq α] [nontrivial α] [normalization_monoid α]
  [unique_factorization_monoid α]

/-- Noncomputably determines the multiset of prime factors -/
noncomputable def factors (a : α) : multiset α := if h : a = 0 then 0 else
multiset.map normalize $ classical.some (unique_factorization_monoid.exists_prime_factors a h)

theorem factors_prod {a : α} (ane0 : a ≠ 0) : associated (factors a).prod a :=
begin
  rw [factors, dif_neg ane0],
  transitivity, swap,
  { exact (classical.some_spec (unique_factorization_monoid.exists_prime_factors a ane0)).2.symm },
  { rw [← associates.mk_eq_mk_iff_associated, ← associates.prod_mk, ← associates.prod_mk,
    multiset.map_map],
    refine congr rfl (congr (congr rfl _) rfl), ext,
    rw [function.comp_apply, associates.mk_eq_mk_iff_associated], apply normalize_associated },
end

theorem prime_factors {a : α} : ∀ (x : α), x ∈ factors a → prime x :=
begin
  rw [factors],
  by_cases a = 0, {simp [h]}, rw dif_neg h,
  intros x hx, rcases multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩,
  rw prime_iff_of_associated (normalize_associated),
  exact (classical.some_spec (unique_factorization_monoid.exists_prime_factors a h)).1 y hy,
end

theorem irreducible_factors {a : α} : ∀ (x : α), x ∈ factors a → irreducible x :=
λ x h, irreducible_of_prime (prime_factors x h)

theorem normalize_factors {a : α} : ∀ (x : α), x ∈ factors a → normalize x = x :=
begin
  rw [factors],
  by_cases a = 0, {simp [h]}, rw dif_neg h,
  intros x hx, rcases multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩,
  apply normalize_idem,
end

lemma factors_irreducible {a : α} (ha : irreducible a) :
  factors a = normalize a :: 0 :=
begin
  cases prime_factors_irreducible ha ⟨prime_factors,(factors_prod ha.ne_zero).symm⟩ with p hp,
  convert hp.2, rw [← normalize_factors p, normalize_eq_normalize_iff, dvd_dvd_iff_associated],
  {apply hp.1}, rw hp.2, simp,
end

lemma exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) : p ∣ a →
  ∃ q ∈ factors a, p ~ᵤ q :=
λ ⟨b, hb⟩,
have hb0 : b ≠ 0, from λ hb0, by simp * at *,
have multiset.rel associated (p :: factors b) (factors a),
  from unique
    (λ x hx, (multiset.mem_cons.1 hx).elim (λ h, h.symm ▸ hp)
      (irreducible_factors _))
    (irreducible_factors)
    (associated.symm $ calc multiset.prod (factors a) ~ᵤ a : factors_prod ha0
      ... = p * b : hb
      ... ~ᵤ multiset.prod (p :: factors b) :
        by rw multiset.prod_cons; exact associated_mul_mul
          (associated.refl _)
          (associated.symm (factors_prod hb0))),
multiset.exists_mem_of_rel_of_mem this (by simp)

end unique_factorization_monoid

namespace unique_factorization_monoid

variables {R : Type*} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R]

lemma no_factors_of_no_prime_factors {a b : R} (ha : a ≠ 0)
  (h : (∀ {d}, d ∣ a → d ∣ b → ¬ prime d)) : ∀ {d}, d ∣ a → d ∣ b → is_unit d :=
λ d, induction_on_prime d
  (by { simp only [zero_dvd_iff], intros, contradiction })
  (λ x hx _ _, hx)
  (λ d q hp hq ih dvd_a dvd_b,
    absurd hq (h (dvd_of_mul_right_dvd dvd_a) (dvd_of_mul_right_dvd dvd_b)))

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `is_coprime.dvd_of_dvd_mul_left`. -/
lemma dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0) :
  (∀ {d}, d ∣ a → d ∣ c → ¬ prime d) → a ∣ b * c → a ∣ b :=
begin
  refine induction_on_prime c _ _ _,
  { intro no_factors,
    simp only [dvd_zero, mul_zero, forall_prop_of_true],
    haveI := classical.prop_decidable,
    exact is_unit_iff_forall_dvd.mp
      (no_factors_of_no_prime_factors ha @no_factors (dvd_refl a) (dvd_zero a)) _ },
  { rintros _ ⟨x, rfl⟩ _ a_dvd_bx,
    apply units.dvd_mul_right.mp a_dvd_bx },
  { intros c p hc hp ih no_factors a_dvd_bpc,
    apply ih (λ q dvd_a dvd_c hq, no_factors dvd_a (dvd_mul_of_dvd_right dvd_c _) hq),
    rw mul_left_comm at a_dvd_bpc,
    refine or.resolve_left (left_dvd_or_dvd_right_of_dvd_prime_mul hp a_dvd_bpc) (λ h, _),
    exact no_factors h (dvd_mul_right p c) hp }
end

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `is_coprime.dvd_of_dvd_mul_right`. -/
lemma dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
  (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬ prime d) : a ∣ b * c → a ∣ c :=
by simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
lemma exists_reduced_factors : ∀ (a ≠ (0 : R)) b,
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
begin
  haveI := classical.prop_decidable,
  intros a,
  refine induction_on_prime a _ _ _,
  { intros, contradiction },
  { intros a a_unit a_ne_zero b,
    use [a, b, 1],
    split,
    { intros p p_dvd_a _,
      exact is_unit_of_dvd_unit p_dvd_a a_unit },
    { simp } },
  { intros a p a_ne_zero p_prime ih_a pa_ne_zero b,
    by_cases p ∣ b,
    { rcases h with ⟨b, rfl⟩,
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b,
      refine ⟨a', b', p * c', @no_factor, _, _⟩,
      { rw [mul_assoc, ha'] },
      { rw [mul_assoc, hb'] } },
    { obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b,
      refine ⟨p * a', b', c', _, mul_left_comm _ _ _, rfl⟩,
      intros q q_dvd_pa' q_dvd_b',
      cases left_dvd_or_dvd_right_of_dvd_prime_mul p_prime q_dvd_pa' with p_dvd_q q_dvd_a',
      { have : p ∣ c' * b' := dvd_mul_of_dvd_right (dvd_trans p_dvd_q q_dvd_b') _,
        contradiction },
      exact coprime q_dvd_a' q_dvd_b'  } }
end

lemma exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
in ⟨a', b', c', λ _ hpb hpa, no_factor hpa hpb, ha, hb⟩

end unique_factorization_monoid
