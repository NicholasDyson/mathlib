/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import group_theory.perm.cycle_type

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/

section pgroup

variables (p : ℕ) (G : Type*) [group G]

/-- A p-group is a group in which every element has prime power order -/
def is_p_group : Prop := ∀ g : G, ∃ k : ℕ, g ^ (p ^ k) = 1

variables {p} {G}

lemma is_p_group_iff_order_of [hp : fact (p.prime)] :
  is_p_group p G ↔ ∀ g : G, ∃ k : ℕ, order_of g = p ^ k :=
forall_congr (λ g, ⟨λ ⟨k, hk⟩, exists_imp_exists (by exact λ j, Exists.snd)
  ((nat.dvd_prime_pow hp.out).mp (order_of_dvd_of_pow_eq_one hk)),
  exists_imp_exists (λ k hk, by rw [←hk, pow_order_of_eq_one])⟩)

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

lemma is_p_group_iff_card [hp : fact (p.prime)] [fintype G] :
  is_p_group p G ↔ ∃ n : ℕ, fintype.card G = p ^ n :=
begin
  have hG : 0 < fintype.card G := fintype.card_pos_iff.mpr has_one.nonempty,
  refine ⟨λ h, _, λ ⟨n, hn⟩ g, ⟨n, by rw [←hn, pow_card_eq_one]⟩⟩,
  suffices : ∀ q ∈ nat.factors (fintype.card G), q = p,
  { use (fintype.card G).factors.length,
    rw [←list.prod_repeat, ←list.eq_repeat_of_mem this, nat.prod_factors hG] },
  intros q hq,
  obtain ⟨hq1, hq2⟩ := (nat.mem_factors hG).mp hq,
  haveI : fact q.prime := ⟨hq1⟩,
  obtain ⟨g, hg⟩ := equiv.perm.exists_prime_order_of_dvd_card q hq2,
  obtain ⟨k, hk⟩ := h g,
  obtain ⟨j, hj1, hj2⟩ := (nat.dvd_prime_pow hp.out).mp (order_of_dvd_of_pow_eq_one hk),
  have key := hg.symm.trans hj2,
  sorry,
end

variables (p) (G)

/-- The set of p-subgroups of G -/
def p_subgroups : set (subgroup G) :=
{H | is_p_group p H}

variables {p} {G}

instance : semilattice_inf_bot (p_subgroups p G) :=
{ bot := ⟨⊥, λ g, ⟨0, (pow_one g).trans (subtype.ext (subgroup.mem_bot.mp g.2))⟩⟩,
  bot_le := λ P, @bot_le (subgroup G) _ P,
  inf := λ H K, ⟨H ⊓ K, le_is_p_group H.2 (inf_le_left)⟩,
  inf_le_left := λ H K, @inf_le_left (subgroup G) _ H K,
  inf_le_right := λ H K, @inf_le_right (subgroup G) _ H K,
  le_inf := λ H K L hHK hHL, @le_inf (subgroup G) _ H K L hHK hHL,
  .. subtype.partial_order _ }

variables (p) (G)

/-- The set of Sylow p-subgroups of G -/
def sylow_p_subgroup : set (p_subgroups p G) :=
{H | ∀ K, H ≤ K → H = K}

end pgroup

namespace mul_action

open fintype equiv finset subgroup
open_locale big_operators classical

variables {G : Type*} (α : Type*) [group G] [mul_action G α] [fintype G] [fintype α]
  [fintype (fixed_points G α)] {p : ℕ} [fact p.prime] (hG : is_p_group p G)

include hG

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
lemma card_modeq_card_fixed_points : card α ≡ card (fixed_points G α) [MOD p] :=
calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
  card_congr (sigma_preimage_equiv (@quotient.mk' _ (orbit_rel G α))).symm
... = ∑ a : quotient (orbit_rel G α), card {x // quotient.mk' x = a} : card_sigma _
... ≡ ∑ a : fixed_points G α, 1 [MOD p] :
begin
  obtain ⟨n, hG⟩ := is_p_group_iff_card.mp hG,
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
let ⟨⟨b, hb⟩, hba⟩ := fintype.exists_ne_of_one_lt_card hα ⟨a, ha⟩ in
⟨b, hb, λ hab, hba $ by simp [hab]⟩

end mul_action
