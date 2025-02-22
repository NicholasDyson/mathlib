/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import tactic.abel
import tactic.linarith

/-!
# Floor and ceil

## Summary

We define the natural- and integer-valued floor and ceil functions on linearly ordered rings.

## Main Definitions

* `floor_semiring`: A linearly ordered semiring with natural-valued floor and ceil.
* `nat.floor a`: Greatest natural `n` such that `n ≤ a`. Equal to `0` if `a < 0`.
* `nat.ceil a`: Least natural `n` such that `a ≤ n`.

* `floor_ring`: A linearly ordered ring with integer-valued floor and ceil.
* `int.floor a`: Greatest integer `z` such that `z ≤ a`.
* `int.ceil a`: Least integer `z` such that `a ≤ z`.
* `int.fract a`: Fractional part of `a`, defined as `a - floor a`.

## Notations

* `⌊a⌋₊` is `nat.floor a`.
* `⌈a⌉₊` is `nat.ceil a`.
* `⌊a⌋` is `int.floor a`.
* `⌈a⌉` is `int.ceil a`.

The index `₊` in the notations for `nat.floor` and `nat.ceil` is used in analogy to the notation
for `nnnorm`.

## TODO

Some `nat.floor` and `nat.ceil` lemmas require `linear_ordered_ring α`.Is `has_ordered_sub` enough?

`linear_ordered_ring`/`linear_ordered_semiring` can be relaxed to `order_ring`/`order_semiring` in
many lemmas.

## Tags

rounding, floor, ceil
-/

variables {α : Type*}

/-! ### Floor semiring -/

/-- A `floor_semiring` is a linear ordered semiring over `α` with a function
`floor : α → ℕ` satisfying `∀ (n : ℕ) (x : α), n ≤ ⌊x⌋ ↔ (n : α) ≤ x)`. -/
class floor_semiring (α) [ordered_semiring α] :=
(floor : α → ℕ)
(ceil : α → ℕ)
(floor_of_neg {a : α} (ha : a < 0) : floor a = 0)
(gc_floor {a : α} {n : ℕ} (ha : 0 ≤ a) : n ≤ floor a ↔ (n : α) ≤ a)
(gc_ceil : galois_connection ceil coe)

instance : floor_semiring ℕ :=
{ floor := id,
  ceil := id,
  floor_of_neg := λ a ha, (a.not_lt_zero ha).elim,
  gc_floor := λ n a ha, by { rw nat.cast_id, refl },
  gc_ceil := λ n a, by { rw nat.cast_id, refl } }

namespace nat
section linear_ordered_semiring
variables [linear_ordered_semiring α] [floor_semiring α] {a : α} {n : ℕ}

/-- `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`. -/
def floor : α → ℕ := floor_semiring.floor

/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
def ceil : α → ℕ := floor_semiring.ceil

notation `⌊` a `⌋₊` := nat.floor a
notation `⌈` a `⌉₊` := nat.ceil a

lemma le_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a := floor_semiring.gc_floor ha

lemma le_floor (h : (n : α) ≤ a) : n ≤ ⌊a⌋₊ := (le_floor_iff $ n.cast_nonneg.trans h).2 h

lemma floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n := lt_iff_lt_of_le_iff_le $ le_floor_iff ha

lemma lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n := lt_of_not_ge' $ λ h', (le_floor h').not_lt h

lemma floor_le (ha : 0 ≤ a) : (⌊a⌋₊ : α) ≤ a := (le_floor_iff ha).1 le_rfl

lemma lt_succ_floor (a : α) : a < ⌊a⌋₊.succ := lt_of_floor_lt $ nat.lt_succ_self _

lemma lt_floor_add_one (a : α) : a < ⌊a⌋₊ + 1 := lt_succ_floor a

@[simp] lemma floor_coe (n : ℕ) : ⌊(n : α)⌋₊ = n :=
eq_of_forall_le_iff $ λ a, by { rw [le_floor_iff, nat.cast_le], exact n.cast_nonneg }

@[simp] lemma floor_zero : ⌊(0 : α)⌋₊ = 0 := floor_coe 0

@[simp] lemma floor_one : ⌊(1 : α)⌋₊ = 1 := by rw [←nat.cast_one, floor_coe]

lemma floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 :=
ha.lt_or_eq.elim floor_semiring.floor_of_neg $ by { rintro rfl, exact floor_zero }

lemma floor_mono : monotone (floor : α → ℕ) := λ a b h, begin
  obtain ha | ha := le_total a 0,
  { rw floor_of_nonpos ha,
    exact nat.zero_le _ },
  { exact le_floor ((floor_le ha).trans h) }
end

lemma le_floor_iff' (hn : n ≠ 0) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a :=
begin
  obtain ha | ha := le_total a 0,
  { rw floor_of_nonpos ha,
    exact iff_of_false (nat.pos_of_ne_zero hn).not_le
      (not_le_of_lt $ ha.trans_lt $ cast_pos.2 $ nat.pos_of_ne_zero hn) },
  { exact le_floor_iff ha }
end

lemma floor_lt' (hn : n ≠ 0) : ⌊a⌋₊ < n ↔ a < n := lt_iff_lt_of_le_iff_le $ le_floor_iff' hn

lemma floor_pos : 0 < ⌊a⌋₊ ↔ 1 ≤ a :=
by { convert le_floor_iff' nat.one_ne_zero, exact cast_one.symm }

lemma pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a :=
(le_or_lt a 0).resolve_left (λ ha, lt_irrefl 0 $ by rwa floor_of_nonpos ha at h)

lemma lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a :=
(nat.cast_lt.2 h).trans_le $ floor_le (pos_of_floor_pos $ (nat.zero_le n).trans_lt h).le

lemma floor_eq_zero : ⌊a⌋₊ = 0 ↔ a < 1 :=
by { rw [←lt_one_iff, ←@cast_one α], exact floor_lt' nat.one_ne_zero }

lemma floor_eq_iff (ha : 0 ≤ a) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 :=
by rw [←le_floor_iff ha, ←nat.cast_one, ←nat.cast_add, ←floor_lt ha, nat.lt_add_one_iff,
  le_antisymm_iff, and.comm]

lemma floor_eq_on_Ico (n : ℕ) : ∀ a ∈ (set.Ico n (n+1) : set α), ⌊a⌋₊ = n :=
λ a ⟨h₀, h₁⟩, (floor_eq_iff $ n.cast_nonneg.trans h₀).mpr ⟨h₀, h₁⟩

lemma floor_eq_on_Ico' (n : ℕ) : ∀ a ∈ (set.Ico n (n+1) : set α), (⌊a⌋₊ : α) = n :=
λ x hx, by exact_mod_cast floor_eq_on_Ico n x hx

/-! #### Ceil -/

lemma gc_ceil_coe : galois_connection (ceil : α → ℕ) coe := floor_semiring.gc_ceil

@[simp] lemma ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n := gc_ceil_coe _ _

lemma lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a := lt_iff_lt_of_le_iff_le ceil_le

lemma le_ceil (a : α) : a ≤ ⌈a⌉₊ := ceil_le.1 le_rfl

lemma ceil_mono : monotone (ceil : α → ℕ) := gc_ceil_coe.monotone_l

@[simp] lemma ceil_coe (n : ℕ) : ⌈(n : α)⌉₊ = n :=
eq_of_forall_ge_iff $ λ a, ceil_le.trans nat.cast_le

@[simp] lemma ceil_zero : ⌈(0 : α)⌉₊ = 0 := ceil_coe 0

@[simp] lemma ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a ≤ 0 := le_zero_iff.symm.trans ceil_le

lemma lt_of_ceil_lt (h : ⌈a⌉₊ < n) : a < n := (le_ceil a).trans_lt (nat.cast_lt.2 h)

lemma le_of_ceil_le (h : ⌈a⌉₊ ≤ n) : a ≤ n := (le_ceil a).trans (nat.cast_le.2 h)

lemma floor_lt_ceil_of_lt_of_pos {a b : α} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉₊ :=
begin
  rcases le_or_lt 0 a with ha|ha,
  { rw floor_lt ha, exact h.trans_le (le_ceil _) },
  { rwa [floor_of_nonpos ha.le, lt_ceil] }
end

end linear_ordered_semiring

section linear_ordered_ring
variables [linear_ordered_ring α] [floor_semiring α] {a : α} {n : ℕ}

lemma floor_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌊a + n⌋₊ = ⌊a⌋₊ + n :=
eq_of_forall_le_iff $ λ b, begin
  rw [le_floor_iff (add_nonneg ha n.cast_nonneg), ←sub_le_iff_le_add],
  obtain hb | hb := le_total n b,
  { rw [←cast_sub hb, ←tsub_le_iff_right],
    exact (le_floor_iff ha).symm },
  { exact iff_of_true ((sub_nonpos_of_le $ cast_le.2 hb).trans ha) (le_add_left hb) }
end

lemma floor_add_one (ha : 0 ≤ a) : ⌊a + 1⌋₊ = ⌊a⌋₊ + 1 :=
by { convert floor_add_nat ha 1, exact cast_one.symm }

lemma sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋₊ := sub_lt_iff_lt_add.2 $ lt_floor_add_one a

lemma ceil_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌈a + n⌉₊ = ⌈a⌉₊ + n :=
eq_of_forall_ge_iff $ λ b, begin
  rw [←not_lt, ←not_lt, not_iff_not],
  rw [lt_ceil],
  obtain hb | hb := le_or_lt n b,
  { rw [←tsub_lt_iff_right hb, ←sub_lt_iff_lt_add, ←cast_sub hb],
    exact lt_ceil.symm },
  { exact iff_of_true (lt_add_of_nonneg_of_lt ha $ cast_lt.2 hb) (lt_add_left _ _ _ hb) }
end

lemma ceil_add_one (ha : 0 ≤ a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1 :=
by { convert ceil_add_nat ha 1, exact cast_one.symm }

lemma ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : α) < a + 1 :=
lt_ceil.1 $ (nat.lt_succ_self _).trans_le (ceil_add_one ha).ge

end linear_ordered_ring
end nat

lemma floor_semiring_unique {α} [linear_ordered_semiring α] (inst1 inst2 : floor_semiring α) :
  @nat.floor _ _ inst1 = @nat.floor _ _ inst2 :=
begin
  ext a,
  cases le_total a 0,
  { rw [@nat.floor_of_nonpos α _ inst1 a h, @nat.floor_of_nonpos α _ inst2 a h] },
  { exact (@nat.floor_eq_iff α _ inst1 a _ h).2 ⟨nat.floor_le h, nat.lt_floor_add_one a⟩ }
end

/-! ### Floor rings -/

/--
A `floor_ring` is a linear ordered ring over `α` with a function
`floor : α → ℤ` satisfying `∀ (z : ℤ) (a : α), z ≤ floor a ↔ (z : α) ≤ a)`.
-/
class floor_ring (α) [linear_ordered_ring α] :=
(floor : α → ℤ)
(ceil : α → ℤ)
(gc_coe_floor : galois_connection coe floor)
(gc_ceil_coe : galois_connection ceil coe)

instance : floor_ring ℤ :=
{ floor := id,
  ceil := id,
  gc_coe_floor := λ a b, by { rw int.cast_id, refl },
  gc_ceil_coe := λ a b, by { rw int.cast_id, refl } }

/-- A `floor_ring` constructor from the `floor` function alone. -/
def floor_ring.of_floor (α) [linear_ordered_ring α] (floor : α → ℤ)
  (gc_coe_floor : galois_connection coe floor) : floor_ring α :=
{ floor := floor,
  ceil := λ a, -floor (-a),
  gc_coe_floor := gc_coe_floor,
  gc_ceil_coe := λ a z, by rw [neg_le, ←gc_coe_floor, int.cast_neg, neg_le_neg_iff] }

/-- A `floor_ring` constructor from the `ceil` function alone. -/
def floor_ring.of_ceil (α) [linear_ordered_ring α] (ceil : α → ℤ)
  (gc_ceil_coe : galois_connection ceil coe) : floor_ring α :=
{ floor := λ a, -ceil (-a),
  ceil := ceil,
  gc_coe_floor := λ a z, by rw [le_neg, gc_ceil_coe, int.cast_neg, neg_le_neg_iff],
  gc_ceil_coe := gc_ceil_coe }

namespace int
variables [linear_ordered_ring α] [floor_ring α] {z : ℤ} {a : α}

/-- `int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`. -/
def floor : α → ℤ := floor_ring.floor

/-- `int.ceil a` is the smallest integer `z` such that `a ≤ z`. It is denoted with `⌈a⌉`. -/
def ceil : α → ℤ := floor_ring.ceil

/-- `int.fract a`, the fractional part of `a`, is `a` minus its floor. -/
def fract (a : α) : α := a - floor a

notation `⌊` a `⌋` := int.floor a
notation `⌈` a `⌉` := int.ceil a
-- Mathematical notation for `fract a` is usually `{a}`. Let's not even go there.

@[simp] lemma floor_ring_floor_eq : @floor_ring.floor = @int.floor := rfl

@[simp] lemma floor_ring_ceil_eq : @floor_ring.ceil = @int.ceil := rfl

/-! #### Floor -/

lemma gc_coe_floor : galois_connection (coe : ℤ → α) floor := floor_ring.gc_coe_floor

lemma le_floor : z ≤ ⌊a⌋ ↔ (z : α) ≤ a := (gc_coe_floor z a).symm

lemma floor_lt : ⌊a⌋ < z ↔ a < z := lt_iff_lt_of_le_iff_le le_floor

lemma floor_le (a : α) : (⌊a⌋ : α) ≤ a := gc_coe_floor.l_u_le a

lemma floor_nonneg : 0 ≤ ⌊a⌋ ↔ 0 ≤ a := le_floor

lemma floor_nonpos (ha : a ≤ 0) : ⌊a⌋ ≤ 0 :=
begin
  rw ←@cast_le α,
  exact (floor_le a).trans ha,
end

lemma lt_succ_floor (a : α) : a < ⌊a⌋.succ := floor_lt.1 $ int.lt_succ_self _

lemma lt_floor_add_one (a : α) : a < ⌊a⌋ + 1 :=
by simpa only [int.succ, int.cast_add, int.cast_one] using lt_succ_floor a

lemma sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋ := sub_lt_iff_lt_add.2 (lt_floor_add_one a)

@[simp] lemma floor_coe (z : ℤ) : ⌊(z : α)⌋ = z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor, int.cast_le]

@[simp] lemma floor_zero : ⌊(0 : α)⌋ = 0 := floor_coe 0

@[simp] lemma floor_one : ⌊(1 : α)⌋ = 1 := by rw [← int.cast_one, floor_coe]

@[mono] lemma floor_mono : monotone (floor : α → ℤ) := gc_coe_floor.monotone_u

lemma floor_pos : 0 < ⌊a⌋ ↔ 1 ≤ a :=
by { convert le_floor, exact cast_one.symm }

@[simp] lemma floor_add_int (a : α) (z : ℤ) : ⌊a + z⌋ = ⌊a⌋ + z :=
eq_of_forall_le_iff $ λ a, by rw [le_floor,
  ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, int.cast_sub]

lemma floor_add_one (a : α) : ⌊a + 1⌋ = ⌊a⌋ + 1 :=
by { convert floor_add_int a 1, exact cast_one.symm }

@[simp] lemma floor_int_add (z : ℤ) (a : α) : ⌊↑z + a⌋ = z + ⌊a⌋ :=
by simpa only [add_comm] using floor_add_int a z

@[simp] lemma floor_add_nat (a : α) (n : ℕ) : ⌊a + n⌋ = ⌊a⌋ + n := floor_add_int a n

@[simp] lemma floor_nat_add (n : ℕ) (a : α) : ⌊↑n + a⌋ = n + ⌊a⌋ := floor_int_add n a

@[simp] lemma floor_sub_int (a : α) (z : ℤ) : ⌊a - z⌋ = ⌊a⌋ - z :=
eq.trans (by rw [int.cast_neg, sub_eq_add_neg]) (floor_add_int _ _)

@[simp] lemma floor_sub_nat (a : α) (n : ℕ) : ⌊a - n⌋ = ⌊a⌋ - n := floor_sub_int a n

lemma abs_sub_lt_one_of_floor_eq_floor {α : Type*} [linear_ordered_comm_ring α] [floor_ring α]
  {a b : α} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 :=
begin
  have : a < ⌊a⌋ + 1     := lt_floor_add_one a,
  have : b < ⌊b⌋ + 1     := lt_floor_add_one b,
  have : (⌊a⌋ : α) = ⌊b⌋ := int.cast_inj.2 h,
  have : (⌊a⌋ : α) ≤ a   := floor_le a,
  have : (⌊b⌋ : α) ≤ b   := floor_le b,
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
end

lemma floor_eq_iff : ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < z + 1 :=
by rw [le_antisymm_iff, le_floor, ←int.lt_add_one_iff, floor_lt, int.cast_add, int.cast_one,
  and.comm]

lemma floor_eq_on_Ico (n : ℤ) : ∀ a ∈ set.Ico (n : α) (n + 1), ⌊a⌋ = n :=
λ a ⟨h₀, h₁⟩, floor_eq_iff.mpr ⟨h₀, h₁⟩

lemma floor_eq_on_Ico' (n : ℤ) : ∀ a ∈ set.Ico (n : α) (n + 1), (⌊a⌋ : α) = n :=
λ a ha, congr_arg _ $ floor_eq_on_Ico n a ha

/-! #### Fractional part -/

@[simp] lemma floor_add_fract (a : α) : (⌊a⌋ : α) + fract a = a := add_sub_cancel'_right _ _

@[simp] lemma fract_add_floor (a : α) : fract a + ⌊a⌋ = a := sub_add_cancel _ _

lemma fract_nonneg (a : α) : 0 ≤ fract a := sub_nonneg.2 $ floor_le _

lemma fract_lt_one (a : α) : fract a < 1 := sub_lt.1 $ sub_one_lt_floor _

@[simp] lemma fract_zero : fract (0 : α) = 0 := by rw [fract, floor_zero, cast_zero, sub_self]

@[simp] lemma fract_coe (z : ℤ) : fract (z : α) = 0 :=
by { unfold fract, rw floor_coe, exact sub_self _ }

@[simp] lemma fract_floor (a : α) : fract (⌊a⌋ : α) = 0 := fract_coe _

@[simp] lemma floor_fract (a : α) : ⌊fract a⌋ = 0 :=
floor_eq_iff.2 ⟨fract_nonneg _, by { rw [int.cast_zero, zero_add], exact fract_lt_one a }⟩

lemma fract_eq_iff {a b : α} : fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a - b = z :=
⟨λ h, by { rw ←h, exact ⟨fract_nonneg _, fract_lt_one _, ⟨⌊a⌋, sub_sub_cancel _ _⟩⟩},
  begin
    rintro ⟨h₀, h₁, z, hz⟩,
    show a - ⌊a⌋ = b, apply eq.symm,
    rw [eq_sub_iff_add_eq, add_comm, ←eq_sub_iff_add_eq],
    rw [hz, int.cast_inj, floor_eq_iff, ←hz],
    clear hz, split; simpa [sub_eq_add_neg, add_assoc]
  end⟩

lemma fract_eq_fract {a b : α} : fract a = fract b ↔ ∃ z : ℤ, a - b = z :=
⟨λ h, ⟨⌊a⌋ - ⌊b⌋, begin
  unfold fract at h, rw [int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h],
 end⟩, begin
  rintro ⟨z, hz⟩,
  refine fract_eq_iff.2 ⟨fract_nonneg _, fract_lt_one _, z + ⌊b⌋, _⟩,
  rw [eq_add_of_sub_eq hz, add_comm, int.cast_add],
  exact add_sub_sub_cancel _ _ _,
end⟩

@[simp] lemma fract_fract (a : α) : fract (fract a) = fract a :=
fract_eq_fract.2 ⟨-⌊a⌋, (cast_neg ⌊a⌋).symm.subst (sub_sub_cancel_left a ⌊a⌋)⟩

lemma fract_add (a b : α) : ∃ z : ℤ, fract (a + b) - fract a - fract b = z :=
⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by { unfold fract, simp [sub_eq_add_neg], abel }⟩

lemma fract_mul_nat (a : α) (b : ℕ) : ∃ z : ℤ, fract a * b - fract (a * b) = z :=
begin
  induction b with c hc,
    use 0, simp,
  rcases hc with ⟨z, hz⟩,
  rw [nat.succ_eq_add_one, nat.cast_add, mul_add, mul_add, nat.cast_one, mul_one, mul_one],
  rcases fract_add (a * c) a with ⟨y, hy⟩,
  use z - y,
  rw [int.cast_sub, ←hz, ←hy],
  abel
end

/-! #### Ceil -/

lemma gc_ceil_coe : galois_connection ceil (coe : ℤ → α) := floor_ring.gc_ceil_coe

lemma ceil_le : ⌈a⌉ ≤ z ↔ a ≤ z := gc_ceil_coe a z

lemma floor_neg : ⌊-a⌋ = -⌈a⌉ :=
eq_of_forall_le_iff (λ z, by rw [le_neg, ceil_le, le_floor, int.cast_neg, le_neg])

lemma ceil_neg : ⌈-a⌉ = -⌊a⌋ :=
eq_of_forall_ge_iff (λ z, by rw [neg_le, ceil_le, le_floor, int.cast_neg, neg_le])

lemma lt_ceil : z < ⌈a⌉ ↔ (z : α) < a := lt_iff_lt_of_le_iff_le ceil_le

lemma ceil_le_floor_add_one (a : α) : ⌈a⌉ ≤ ⌊a⌋ + 1 :=
by { rw [ceil_le, int.cast_add, int.cast_one], exact (lt_floor_add_one a).le }

lemma le_ceil (a : α) : a ≤ ⌈a⌉ := gc_ceil_coe.le_u_l a

@[simp] lemma ceil_coe (z : ℤ) : ⌈(z : α)⌉ = z :=
eq_of_forall_ge_iff $ λ a, by rw [ceil_le, int.cast_le]

lemma ceil_mono : monotone (ceil : α → ℤ) := gc_ceil_coe.monotone_l

@[simp] lemma ceil_add_int (a : α) (z : ℤ) : ⌈a + z⌉ = ⌈a⌉ + z :=
by rw [←neg_inj, neg_add', ←floor_neg, ←floor_neg, neg_add', floor_sub_int]

lemma ceil_add_one (a : α) : ⌈a + 1⌉ = ⌈a⌉ + 1 :=
by { convert ceil_add_int a (1 : ℤ), exact cast_one.symm }

lemma ceil_sub_int (a : α) (z : ℤ) : ⌈a - z⌉ = ⌈a⌉ - z :=
eq.trans (by rw [int.cast_neg, sub_eq_add_neg]) (ceil_add_int _ _)

lemma ceil_lt_add_one (a : α) : (⌈a⌉ : α) < a + 1 :=
by { rw [← lt_ceil, ← int.cast_one, ceil_add_int], apply lt_add_one }

lemma ceil_pos : 0 < ⌈a⌉ ↔ 0 < a := lt_ceil

@[simp] lemma ceil_zero : ⌈(0 : α)⌉ = 0 := ceil_coe 0

lemma ceil_nonneg (ha : 0 ≤ a) : 0 ≤ ⌈a⌉ :=
by exact_mod_cast ha.trans (le_ceil a)

lemma ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a ≤ z :=
by rw [←ceil_le, ←int.cast_one, ←int.cast_sub, ←lt_ceil, int.sub_one_lt_iff, le_antisymm_iff,
  and.comm]

lemma ceil_eq_on_Ioc (z : ℤ) : ∀ a ∈ set.Ioc (z - 1 : α) z, ⌈a⌉ = z :=
λ a ⟨h₀, h₁⟩, ceil_eq_iff.mpr ⟨h₀, h₁⟩

lemma ceil_eq_on_Ioc' (z : ℤ) : ∀ a ∈ set.Ioc (z - 1 : α) z, (⌈a⌉ : α) = z :=
λ a ha, by exact_mod_cast ceil_eq_on_Ioc z a ha

lemma floor_lt_ceil_of_lt {a b : α} (h : a < b) : ⌊a⌋ < ⌈b⌉ :=
cast_lt.1 $ (floor_le a).trans_lt $ h.trans_le $ le_ceil b

/-! #### A floor ring as a floor semiring -/

@[priority 100] -- see Note [lower instance priority]
instance _root_.floor_ring.to_floor_semiring : floor_semiring α :=
{ floor := λ a, ⌊a⌋.to_nat,
  ceil := λ a, ⌈a⌉.to_nat,
  floor_of_neg := λ a ha, int.to_nat_of_nonpos (int.floor_nonpos ha.le),
  gc_floor := λ a n ha, by { rw [int.le_to_nat_iff (int.floor_nonneg.2 ha), int.le_floor], refl },
  gc_ceil := λ a n, by { rw [int.to_nat_le, int.ceil_le], refl } }

lemma floor_to_nat (a : α) : ⌊a⌋.to_nat = ⌊a⌋₊ := rfl

lemma ceil_to_nat  (a : α) : ⌈a⌉.to_nat = ⌈a⌉₊ := rfl

/-! #### Intervals -/

@[simp] lemma preimage_Ioo {a b : α} : ((coe : ℤ → α) ⁻¹' (set.Ioo a b)) = set.Ioo ⌊a⌋ ⌈b⌉ :=
by { ext, simp [floor_lt, lt_ceil] }

@[simp] lemma preimage_Ico {a b : α} : ((coe : ℤ → α) ⁻¹' (set.Ico a b)) = set.Ico ⌈a⌉ ⌈b⌉ :=
by { ext, simp [ceil_le, lt_ceil] }

@[simp] lemma preimage_Ioc {a b : α} : ((coe : ℤ → α) ⁻¹' (set.Ioc a b)) = set.Ioc ⌊a⌋ ⌊b⌋ :=
by { ext, simp [floor_lt, le_floor] }

@[simp] lemma preimage_Icc {a b : α} : ((coe : ℤ → α) ⁻¹' (set.Icc a b)) = set.Icc ⌈a⌉ ⌊b⌋ :=
by { ext, simp [ceil_le, le_floor] }

@[simp] lemma preimage_Ioi : ((coe : ℤ → α) ⁻¹' (set.Ioi a)) = set.Ioi ⌊a⌋ :=
by { ext, simp [floor_lt] }

@[simp] lemma preimage_Ici : ((coe : ℤ → α) ⁻¹' (set.Ici a)) = set.Ici ⌈a⌉ :=
by { ext, simp [ceil_le] }

@[simp] lemma preimage_Iio : ((coe : ℤ → α) ⁻¹' (set.Iio a)) = set.Iio ⌈a⌉ :=
by { ext, simp [lt_ceil] }

@[simp] lemma preimage_Iic : ((coe : ℤ → α) ⁻¹' (set.Iic a)) = set.Iic ⌊a⌋ :=
by { ext, simp [le_floor] }

end int

lemma floor_ring_unique {α} [linear_ordered_ring α] (inst1 inst2 : floor_ring α) :
  @int.floor _ _ inst1 = @int.floor _ _ inst2 :=
begin
  ext v,
  suffices : (⌊v⌋ : α) ≤ v ∧ v < ⌊v⌋ + 1, by rwa [int.floor_eq_iff],
  exact ⟨int.floor_le v, int.lt_floor_add_one v⟩
end
