/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.basic
import data.fintype.card
import data.zmod.basic
/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/

namespace mul_action

open fintype equiv finset subgroup
open_locale big_operators classical

variables {G : Type*} (α : Type*) [group G] [mul_action G α] [fintype G] [fintype α]
  [fintype (fixed_points G α)] {p n : ℕ} [fact p.prime] (hG : card G = p ^ n)

include hG

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
lemma card_modeq_card_fixed_points : card α ≡ card (fixed_points G α) [MOD p] :=
calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
  card_congr (sigma_preimage_equiv (@quotient.mk' _ (orbit_rel G α))).symm
... = ∑ a : quotient (orbit_rel G α), card {x // quotient.mk' x = a} : card_sigma _
... ≡ ∑ a : fixed_points G α, 1 [MOD p] :
begin
  rw [←zmod.eq_iff_modeq_nat p, nat.cast_sum, nat.cast_sum],
  refine eq.symm (sum_bij_ne_zero (λ a _ _, quotient.mk' a.1)
    (λ _ _ _, mem_univ _)
    (λ a₁ a₂ _ _ _ _ h,
      subtype.eq ((mem_fixed_points' α).1 a₂.2 a₁.1 (quotient.exact' h)))
      (λ b, _)
      (λ a ha _, by rw [← mem_fixed_points_iff_card_orbit_eq_one.1 a.2];
        simp only [quotient.eq']; congr)),
  { refine quotient.induction_on' b (λ b _ hb, _),
    have : card (orbit G b) ∣ p ^ n,
    { rw [← hG, fintype.card_congr (orbit_equiv_quotient_stabilizer G b)],
      exact card_quotient_dvd_card _ },
    rcases (nat.dvd_prime_pow (fact.out p.prime)).1 this with ⟨k, _, hk⟩,
    have hb' :¬ p ^ 1 ∣ p ^ k,
    { rw [pow_one, ← hk, ← nat.modeq_zero_iff_dvd, ← zmod.eq_iff_modeq_nat,
        nat.cast_zero, ← ne.def],
      exact eq.mpr (by simp only [quotient.eq']; congr) hb },
    have : k = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (pow_dvd_pow p) hb'))),
    refine ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, pow_zero]⟩,
      mem_univ _, _, rfl⟩,
    rw [nat.cast_one], exact one_ne_zero }
end
... = _ : by simp; refl

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
lemma nonempty_fixed_point_of_prime_not_dvd_card
  (hp : ¬ p ∣ fintype.card α) :
  (fixed_points G α).nonempty :=
@set.nonempty_of_nonempty_subtype _ _ begin
  rw [← fintype.card_pos_iff, pos_iff_ne_zero],
  assume h,
  have := card_modeq_card_fixed_points α hG,
  rw [h, nat.modeq_zero_iff_dvd] at this,
  contradiction
end

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
lemma exists_fixed_point_of_prime_dvd_card_of_fixed_point
  (hpα : p ∣ fintype.card α) {a : α} (ha : a ∈ fixed_points G α) :
  ∃ b, b ∈ fixed_points G α ∧ a ≠ b :=
have hpf : p ∣ fintype.card (fixed_points G α),
  from nat.modeq_zero_iff_dvd.1 ((card_modeq_card_fixed_points α hG).symm.trans hpα.modeq_zero_nat),
have hα : 1 < fintype.card (fixed_points G α),
  from (fact.out p.prime).one_lt.trans_le (nat.le_of_dvd (fintype.card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf),
let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩ in
⟨b, hb, λ hab, hba $ by simp [hab]⟩

end mul_action

section cauchy

lemma exists_prime_order_of_dvd_card {G : Type*} [group G] [fintype G] (p : ℕ) [hp : fact p.prime]
  (hdvd : p ∣ fintype.card G) : ∃ x : G, order_of x = p :=
begin
  let S := {v : vector G p | v.to_list.prod = 1},
  let f : ℕ → S → S := λ k s, ⟨⟨s.1.1.rotate k, (s.1.1.length_rotate k).trans s.1.2⟩,
    list.prod_rotate_eq_one_of_prod_eq_one s.2 k⟩,
  have hf1 : ∀ (j k : ℕ) (s : S), f k (f j s) = f (j + k) s :=
  λ j k s, subtype.ext (subtype.ext (s.1.1.rotate_rotate j k)),
  have hf2 : ∀ s : S, f p s = s :=
  λ s, subtype.ext (subtype.ext ((congr_arg _ s.1.2.symm).trans s.1.1.rotate_length)),



  let g : zmod p → S → S := λ k, f k.val,
  let σ : S ≃ S :=
  { to_fun := f 1,
    inv_fun := f (p - 1),
    left_inv := hf 1 (p - 1) (nat.add_sub_cancel' hp.out.pos),
    right_inv := hf (p - 1) 1 (nat.sub_add_cancel hp.out.pos) },
end

end cauchy

section pgroup

variables (p : ℕ) (G : Type*) [group G]

def is_p_group : Prop := ∀ g : G, ∃ k : ℕ, g ^ (p ^ k) = 1

variables {G}

lemma subgroup_is_p_group (hG : is_p_group p G) (H : subgroup G) : is_p_group p H :=
begin
  simp_rw [is_p_group, subtype.ext_iff, subgroup.coe_pow],
  exact λ h, hG h,
end

lemma le_is_p_group {H K : subgroup G} (hK : is_p_group p K) (hHK : H ≤ K) : is_p_group p H :=
begin
  simp_rw [is_p_group, subtype.ext_iff, subgroup.coe_pow] at hK ⊢,
  exact λ h, hK ⟨h, hHK h.2⟩,
end

variables (G)

def p_subgroups : set (subgroup G) :=
{H | is_p_group p H}

variables {G}

instance : semilattice_inf_bot (p_subgroups p G) :=
{ bot := ⟨⊥, λ g, ⟨0, (pow_one g).trans (subtype.ext (subgroup.mem_bot.mp g.2))⟩⟩,
  bot_le := λ P, @bot_le (subgroup G) _ P,
  inf := λ H K, ⟨H ⊓ K, le_is_p_group p H.2 (inf_le_left)⟩,
  inf_le_left := λ H K, @inf_le_left (subgroup G) _ H K,
  inf_le_right := λ H K, @inf_le_right (subgroup G) _ H K,
  le_inf := λ H K L hHK hHL, @le_inf (subgroup G) _ H K L hHK hHL,
  .. subtype.partial_order _ }

def sylow_p_subgroup : set (p_subgroups p G) :=
{H | ∀ K, H ≤ K → H = K}

end pgroup
