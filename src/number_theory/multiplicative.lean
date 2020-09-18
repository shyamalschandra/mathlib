import data.nat.totient
import number_theory.divisors

open nat finset
open_locale big_operators

variable (α : Type*)

structure arithmetic_function [has_zero α] :=
(to_fun : ℕ → α)
(map_zero' : to_fun 0 = 0)

variable {α}

namespace arithmetic_function

section has_zero
variable [has_zero α]

instance : has_coe_to_fun (arithmetic_function α) := ⟨λ _, ℕ → α, to_fun⟩

theorem coe_inj ⦃f g : arithmetic_function α⦄ (h : (f : ℕ → α) = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext] theorem ext ⦃f g : arithmetic_function α⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)

theorem ext_iff {f g : arithmetic_function α} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp]
lemma map_zero {f : arithmetic_function α} : f 0 = 0 := f.map_zero'

instance : has_zero (arithmetic_function α) := ⟨⟨λ _, 0, rfl⟩⟩

@[simp]
lemma zero_apply {x : ℕ} : (0 : arithmetic_function α) x = 0 := rfl

section has_one
variable [has_one α]

instance : has_one (arithmetic_function α) := ⟨⟨λ x, ite (x = 1) 1 0, rfl⟩⟩

@[simp]
lemma one_one : (1 : arithmetic_function α) 1 = 1 := rfl

@[simp]
lemma one_apply_of_ne_one {x : ℕ} (h : x ≠ 1) : (1 : arithmetic_function α) x = 0 := if_neg h

/-- `ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann ζ.  -/
def zeta [has_zero α] [has_one α] : arithmetic_function α := ⟨λ x, ite (x = 0) 0 1, rfl⟩

localized "notation `ζ` := zeta" in arithmetic_function

end has_one
end has_zero

open_locale arithmetic_function

section add_monoid

variable [add_monoid α]

instance : has_add (arithmetic_function α) := ⟨λ x y, ⟨λ n, x n + y n, by simp⟩⟩

@[simp]
lemma add_apply {f g : arithmetic_function α} {n : ℕ} : (f + g) n = f n + g n := rfl

instance : add_monoid (arithmetic_function α) :=
{ add_assoc := λ _ _ _, ext (λ _, add_assoc _ _ _),
  zero_add := λ _, ext (λ _, zero_add _),
  add_zero := λ _, ext (λ _, add_zero _),
  .. (infer_instance : has_zero (arithmetic_function α)),
  .. (infer_instance : has_add (arithmetic_function α)) }

end add_monoid

instance [add_comm_monoid α] : add_comm_monoid (arithmetic_function α) :=
{ add_comm := λ _ _, ext (λ _, add_comm _ _),
  .. (infer_instance : add_monoid (arithmetic_function α)) }

instance [add_group α] : add_group (arithmetic_function α) :=
{ neg := λ f, ⟨λ n, - f n, by simp⟩,
  add_left_neg := λ _, ext (λ _, add_left_neg _),
  .. (infer_instance : add_monoid (arithmetic_function α)) }

instance [add_comm_group α] : add_comm_group (arithmetic_function α) :=
{ .. (infer_instance : add_comm_monoid (arithmetic_function α)),
  .. (infer_instance : add_group (arithmetic_function α)) }

section dirichlet_ring
variable [comm_semiring α]

/-- Dirichlet convolution -/
def convolve (f g : arithmetic_function α) : arithmetic_function α :=
⟨λ n, ∑ x in divisors_antidiagonal n, f x.fst * g x.snd, by simp⟩

@[simp]
lemma convolve_apply {f g : arithmetic_function α} {n : ℕ} :
  (convolve f g) n = ∑ x in divisors_antidiagonal n, f x.fst * g x.snd := rfl

lemma convolve_comm (f g : arithmetic_function α) : convolve f g = convolve g f :=
begin
  ext,
  rw [convolve_apply, ← map_swap_divisors_antidiagonal, sum_map],
  simp [mul_comm],
end

@[simp]
lemma one_convolve (f : arithmetic_function α) : convolve 1 f = f :=
begin
  ext,
  rw convolve_apply,
  by_cases x0 : x = 0, {simp [x0]},
  have h : {(1,x)} ⊆ divisors_antidiagonal x := by simp [x0],
  rw ← sum_subset h, {simp},
  intros y ymem ynmem,
  have y1ne : y.fst ≠ 1,
  { intro con,
    simp only [con, mem_divisors_antidiagonal, one_mul, ne.def] at ymem,
    simp only [mem_singleton, prod.ext_iff] at ynmem,
    tauto },
  simp [y1ne],
end

@[simp]
lemma convolve_one (f : arithmetic_function α) : convolve f 1 = f :=
by rw [convolve_comm, one_convolve]

@[simp]
lemma zero_convolve (f : arithmetic_function α) : convolve 0 f = 0 :=
by { ext, simp }

@[simp]
lemma convolve_zero (f : arithmetic_function α) : convolve f 0 = 0 :=
by { ext, simp }

lemma convolve_assoc (f g h : arithmetic_function α) :
  convolve (convolve f g) h = convolve f (convolve g h) :=
begin
  ext,
  simp [sum_mul, mul_sum],
  sorry,
end

lemma convolve_add (a b c : arithmetic_function α) :
  convolve a (b + c) = convolve a b + convolve a c :=
by { ext, simp [← sum_add_distrib, mul_add] }

lemma add_convolve (a b c : arithmetic_function α) :
  convolve (a + b) c = convolve a c + convolve b c :=
begin
  rw [convolve_comm (a + b) _, convolve_comm a _, convolve_comm b _],
  apply convolve_add,
end

instance : has_mul (arithmetic_function α) := ⟨convolve⟩

@[simp]
lemma mul_apply {f g : arithmetic_function α} {n : ℕ} :
  (f * g) n = ∑ x in divisors_antidiagonal n, f x.fst * g x.snd := rfl

instance : comm_semiring (arithmetic_function α) :=
{ mul_comm := convolve_comm,
  one_mul := one_convolve,
  mul_one := convolve_one,
  zero_mul := zero_convolve,
  mul_zero := convolve_zero,
  mul_assoc := convolve_assoc,
  left_distrib := convolve_add,
  right_distrib := add_convolve,
  .. (infer_instance : has_one (arithmetic_function α)),
  .. (infer_instance : has_mul (arithmetic_function α)),
  .. (infer_instance : add_comm_monoid (arithmetic_function α)) }

variable (α)
/-- `nat.cast` as an `arithmetic_function`  -/
def nat_cast : arithmetic_function α := ⟨nat.cast, rfl⟩
variable {α}

end dirichlet_ring

instance [comm_ring α] : comm_ring (arithmetic_function α) :=
{ .. (infer_instance : add_comm_group (arithmetic_function α)),
  .. (infer_instance : comm_semiring (arithmetic_function α)) }

section pointwise_mul

def pointwise_mul [mul_zero_class α] (f g : arithmetic_function α) :
  arithmetic_function α :=
⟨λ x, f x * g x, by simp⟩

@[simp]
lemma pointwise_mul_apply [mul_zero_class α] {f g : arithmetic_function α} {x : ℕ} :
  (pointwise_mul f g) x = f x * g x := rfl

lemma pointwise_mul_comm [comm_monoid_with_zero α] (f g : arithmetic_function α) :
  pointwise_mul f g = pointwise_mul g f :=
by { ext, simp [mul_comm] }

variable [monoid_with_zero α]

def pointwise_pow (f : arithmetic_function α) (k : ℕ) (kpos : 0 < k) :
  arithmetic_function α :=
⟨λ x, (f x) ^ k, by { rw [map_zero], exact zero_pow kpos }⟩

@[simp]
lemma pointwise_pow_apply {f : arithmetic_function α} {k x : ℕ} {kpos : 0 < k} :
  (pointwise_pow f k kpos) x = (f x) ^ k := rfl

lemma pointwise_pow_succ {f : arithmetic_function α} {k : ℕ} {kpos : 0 < k} :
  pointwise_pow f (k + 1) (k.succ_pos) = pointwise_mul f (pointwise_pow f k kpos) :=
by { ext, simp [pow_succ] }

lemma pointwise_pow_succ' {f : arithmetic_function α} {k : ℕ} {kpos : 0 < k} :
  pointwise_pow f (k + 1) (k.succ_pos) = pointwise_mul (pointwise_pow f k kpos) f :=
by { ext, simp [pow_succ'] }

def pow (k : ℕ) : arithmetic_function α :=
if h : k = 0 then ζ else pointwise_pow (nat_cast α) k (nat.pos_of_ne_zero h)

end pointwise_mul

section multiplicative

variable [monoid_with_zero α]

/-- Multiplicative functions -/
class is_multiplicative (f : ℕ → α) : Prop :=
(map_zero : f 0 = 0)
(map_one : f 1 = 1)
(map_mul_of_coprime : ∀ {m n : ℕ}, m.coprime n → f (m * n) = f m * f n)

attribute [simp] is_multiplicative.map_zero is_multiplicative.map_one
  is_multiplicative.map_mul_of_coprime

export is_multiplicative (map_mul_of_coprime)


def sigma (k : ℕ) : arithmetic_function ℕ := ζ * 1


end multiplicative

end arithmetic_function
