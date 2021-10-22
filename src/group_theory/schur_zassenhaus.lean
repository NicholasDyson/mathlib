/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.set_like.fintype
import group_theory.complement
import group_theory.sylow

/-!
# Complements

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `exists_right_complement_of_coprime` : If `H : subgroup G` is normal and has order coprime to
  its index, then there exists a subgroup `K` which is a (right) complement of `H`.
- `exists_left_complement_of_coprime` : If `H : subgroup G` is normal and has order coprime to
  its index, then there exists a subgroup `K` which is a (left) complement of `H`.
-/

open_locale big_operators

namespace subgroup

section schur_zassenhaus_abelian

variables {G : Type*} [group G] {H : subgroup G}

@[to_additive] instance : mul_action G (left_transversals (H : set G)) :=
{ smul := λ g T, ⟨left_coset g T, mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g', by
  { obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g⁻¹ * g'),
    simp_rw [←mul_assoc, ←mul_inv_rev] at ht1 ht2,
    refine ⟨⟨g * t, mem_left_coset g t.2⟩, ht1, _⟩,
    rintros ⟨_, t', ht', rfl⟩ h,
    exact subtype.ext ((mul_right_inj g).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h))) })⟩,
  one_smul := λ T, subtype.ext (one_left_coset T),
  mul_smul := λ g g' T, subtype.ext (left_coset_assoc ↑T g g').symm }

lemma smul_symm_apply_eq_mul_symm_apply_inv_smul
  (g : G) (α : left_transversals (H : set G)) (q : quotient_group.quotient H) :
  ↑((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)).symm q) =
    g * ((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm
      (g⁻¹ • q : quotient_group.quotient H)) :=
begin
  let w := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)),
  let y := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)),
  change ↑(y.symm q) = ↑(⟨_, mem_left_coset g (subtype.mem _)⟩ : (g • α).1),
  refine subtype.ext_iff.mp (y.symm_apply_eq.mpr _),
  change q = g • (w (w.symm (g⁻¹ • q : quotient_group.quotient H))),
  rw [equiv.apply_symm_apply, ←mul_smul, mul_inv_self, one_smul],
end

variables [is_commutative H] [fintype (quotient_group.quotient H)]

variables (α β γ : left_transversals (H : set G))

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff [hH : normal H] : H :=
let α' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm,
    β' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp β.2)).symm in
∏ (q : quotient_group.quotient H), ⟨(α' q) * (β' q)⁻¹,
  hH.mem_comm (quotient.exact' ((β'.symm_apply_apply q).trans (α'.symm_apply_apply q).symm))⟩

@[to_additive] lemma diff_mul_diff [normal H] : diff α β * diff β γ = diff α γ :=
finset.prod_mul_distrib.symm.trans (finset.prod_congr rfl (λ x hx, subtype.ext
  (by rw [coe_mul, coe_mk, coe_mk, coe_mk, mul_assoc, inv_mul_cancel_left])))

@[to_additive] lemma diff_self [normal H] : diff α α = 1 :=
mul_right_eq_self.mp (diff_mul_diff α α α)

@[to_additive] lemma diff_inv [normal H]: (diff α β)⁻¹ = diff β α :=
inv_eq_of_mul_eq_one ((diff_mul_diff α β α).trans (diff_self α))

lemma smul_diff_smul [hH : normal H] (g : G) :
  diff (g • α) (g • β) = ⟨g * diff α β * g⁻¹, hH.conj_mem (diff α β).1 (diff α β).2 g⟩ :=
begin
  let ϕ : H →* H :=
  { to_fun := λ h, ⟨g * h * g⁻¹, hH.conj_mem h.1 h.2 g⟩,
    map_one' := subtype.ext (by rw [coe_mk, coe_one, mul_one, mul_inv_self]),
    map_mul' := λ h₁ h₂, subtype.ext (by rw [coe_mk, coe_mul, coe_mul, coe_mk, coe_mk, mul_assoc,
      mul_assoc, mul_assoc, mul_assoc, mul_assoc, inv_mul_cancel_left]) },
  refine eq.trans (finset.prod_bij' (λ q _, (↑g)⁻¹ * q) (λ _ _, finset.mem_univ _)
    (λ q _, subtype.ext _) (λ q _, ↑g * q) (λ _ _, finset.mem_univ _)
    (λ q _, mul_inv_cancel_left g q) (λ q _, inv_mul_cancel_left g q)) (ϕ.map_prod _ _).symm,
  change _ * _ = g * (_ * _) * g⁻¹,
  simp_rw [smul_symm_apply_eq_mul_symm_apply_inv_smul, mul_inv_rev, mul_assoc],
  refl,
end

lemma smul_diff [H.normal] (h : H) :
  diff (h • α) β = h ^ H.index * diff α β :=
begin
  rw [diff, diff, index_eq_card, ←finset.card_univ, ←finset.prod_const, ←finset.prod_mul_distrib],
  refine finset.prod_congr rfl (λ q _, _),
  rw [subtype.ext_iff, coe_mul, coe_mk, coe_mk, ←mul_assoc, mul_right_cancel_iff],
  rw [show h • α = (h : G) • α, from rfl, smul_symm_apply_eq_mul_symm_apply_inv_smul],
  rw [mul_left_cancel_iff, ←subtype.ext_iff, equiv.apply_eq_iff_eq, inv_smul_eq_iff],
  exact self_eq_mul_left.mpr ((quotient_group.eq_one_iff _).mpr h.2),
end

variables (H)

instance setoid_diff [H.normal] : setoid (left_transversals (H : set G)) :=
setoid.mk (λ α β, diff α β = 1) ⟨λ α, diff_self α, λ α β h₁,
  by rw [←diff_inv, h₁, one_inv], λ α β γ h₁ h₂, by rw [←diff_mul_diff, h₁, h₂, one_mul]⟩

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation -/
def quotient_diff [H.normal] :=
quotient H.setoid_diff

instance [H.normal] : inhabited H.quotient_diff :=
quotient.inhabited

variables {H}

instance [H.normal] : mul_action G H.quotient_diff :=
{ smul := λ g, quotient.map (λ α, g • α) (λ α β h, (smul_diff_smul α β g).trans
    (subtype.ext (mul_inv_eq_one.mpr (mul_right_eq_self.mpr (subtype.ext_iff.mp h))))),
  mul_smul := λ g₁ g₂ q, quotient.induction_on q (λ α, congr_arg quotient.mk (mul_smul g₁ g₂ α)),
  one_smul := λ q, quotient.induction_on q (λ α, congr_arg quotient.mk (one_smul G α)) }

variables [fintype H]

lemma exists_smul_eq [H.normal] (α β : H.quotient_diff)
  (hH : nat.coprime (fintype.card H) H.index) :
  ∃ h : H, h • α = β :=
quotient.induction_on α (quotient.induction_on β
  (λ β α, exists_imp_exists (λ n, quotient.sound)
    ⟨(pow_coprime hH).symm (diff α β)⁻¹, by
    { change diff ((_ : H) • _) _ = 1,
      rw smul_diff,
      change pow_coprime hH ((pow_coprime hH).symm (diff α β)⁻¹) * (diff α β) = 1,
      rw [equiv.apply_symm_apply, inv_mul_self] }⟩))

lemma smul_left_injective [H.normal] (α : H.quotient_diff)
  (hH : nat.coprime (fintype.card H) H.index) :
  function.injective (λ h : H, h • α) :=
λ h₁ h₂, begin
  refine quotient.induction_on α (λ α hα, _),
  replace hα : diff (h₁ • α) (h₂ • α) = 1 := quotient.exact hα,
  rw [smul_diff, ←diff_inv, smul_diff, diff_self, mul_one, mul_inv_eq_one] at hα,
  exact (pow_coprime hH).injective hα,
end

lemma is_complement_stabilizer_of_coprime [fintype G] [H.normal] {α : H.quotient_diff}
  (hH : nat.coprime (fintype.card H) H.index) :
  is_complement (H : set G) (mul_action.stabilizer G α : set G) :=
begin
  classical,
  let ϕ : H ≃ mul_action.orbit G α := equiv.of_bijective (λ h, ⟨h • α, h, rfl⟩)
    ⟨λ h₁ h₂ hh, smul_left_injective α hH (subtype.ext_iff.mp hh),
      λ β, exists_imp_exists (λ h hh, subtype.ext hh) (exists_smul_eq α β hH)⟩,
  have key := card_eq_card_quotient_mul_card_subgroup (mul_action.stabilizer G α),
  rw ← fintype.card_congr (ϕ.trans (mul_action.orbit_equiv_quotient_stabilizer G α)) at key,
  apply is_complement_of_coprime key.symm,
  rw [card_eq_card_quotient_mul_card_subgroup H, mul_comm, mul_right_inj'] at key,
  { rwa [←key, ←index_eq_card] },
  { rw [←pos_iff_ne_zero, fintype.card_pos_iff],
    apply_instance },
end

theorem exists_right_complement_of_coprime_aux0 [fintype G] [H.normal]
  (hH : nat.coprime (fintype.card H) H.index) :
  ∃ K : subgroup G, is_complement (H : set G) (K : set G) :=
nonempty_of_inhabited.elim
  (λ α : H.quotient_diff, ⟨mul_action.stabilizer G α, is_complement_stabilizer_of_coprime hH⟩)

end schur_zassenhaus_abelian

lemma fintype.card_pos {G : Type*} [fintype G] [hG : nonempty G] : 0 < fintype.card G :=
fintype.card_pos_iff.mpr hG

lemma fintype.card_ne_zero {G : Type*} [fintype G] [hG : nonempty G] : fintype.card G ≠ 0 :=
ne_of_gt fintype.card_pos

lemma index_eq_one {G : Type*} [group G] {H : subgroup G} : H.index = 1 ↔ H = ⊤ :=
⟨λ h, quotient_group.subgroup_eq_top_of_subsingleton H (cardinal.to_nat_eq_one_iff_unique.mp h).1,
  λ h, (congr_arg index h).trans index_top⟩

lemma index_ne_one_of_ne_top {G : Type*} [group G] {H : subgroup G} (hH : H ≠ ⊤) : H.index ≠ 1 :=
mt index_eq_one.mp hH

lemma index_ne_zero_of_fintype {G : Type*} [group G] {H : subgroup G}
  [hH : fintype (quotient_group.quotient H)] : H.index ≠ 0 :=
by rw index_eq_card; exact fintype.card_ne_zero

lemma one_lt_index_of_ne_top {G : Type*} [group G] {H : subgroup G}
  [fintype (quotient_group.quotient H)] (hH : H ≠ ⊤) : 1 < H.index :=
nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_fintype, index_ne_one_of_ne_top hH⟩

open_locale classical

universe u

namespace schur_zassenhaus_induction

variables {G : Type u} [group G] [fintype G] {N : subgroup G} [normal N]
  (h1 : nat.coprime (fintype.card N) N.index)
  (h2 : ∀ (G' : Type u) [group G'] [fintype G'], by exactI
    ∀ (hG'3 : fintype.card G' < fintype.card G)
    {N' : subgroup G'} [N'.normal] (hN : nat.coprime (fintype.card N') N'.index),
    ∃ H' : subgroup G', is_complement (N' : set G') (H' : set G'))
  (h3 : ∀ H : subgroup G, ¬ is_complement (N : set G) (H : set G))

include h1 h2 h3

lemma N_ne_bot : N ≠ ⊥ :=
begin
  tactic.unfreeze_local_instances,
  rintro rfl,
  exact h3 ⊤ is_complement_singleton_top,
end

lemma N_ne_top : N ≠ ⊤ :=
begin
  tactic.unfreeze_local_instances,
  rintro rfl,
  exact h3 ⊥ is_complement_top_singleton,
end

lemma step1 (K : subgroup G) (hK1 : K ⊔ N = ⊤) : K = ⊤ :=
begin
  contrapose! h3 with hK2,
  have h31 : fintype.card K < fintype.card G,
  { rw ← K.index_mul_card,
    exact lt_mul_of_one_lt_left fintype.card_pos (one_lt_index_of_ne_top hK2) },
  have h32 : nat.coprime (fintype.card (N.comap K.subtype)) (N.comap K.subtype).index,
  { sorry },
  obtain ⟨H, hH⟩ := h2 K h31 h32,
  refine ⟨H.map K.subtype, _⟩,
  suffices : fintype.card N * fintype.card (H.map K.subtype) = fintype.card G,
  { refine is_complement_of_coprime this _,
    rw [mul_comm, ←N.index_mul_card] at this,
    rwa mul_right_cancel₀ fintype.card_ne_zero this },
  sorry
end

lemma step2 (K : subgroup G) [K.normal] (hK1 : K ≤ N) : K = ⊥ ∨ K = N :=
begin
  have h3 := step1 h1 h2 h3,
  contrapose! h3 with hK2,
    have h41 : fintype.card (quotient_group.quotient K) < fintype.card G,
    { sorry },
    have h42 : nat.coprime (fintype.card (N.map (quotient_group.mk' K)))
      (N.map (quotient_group.mk' K)).index,
    { sorry },
    obtain ⟨H, hh⟩ := h2 (quotient_group.quotient K) h41 h42,
    refine ⟨H.comap (quotient_group.mk' K), _, _⟩,
    { sorry },
    { sorry }
end

lemma step10 : false := sorry

end schur_zassenhaus_induction

/-lemma exists_right_complement_of_coprime_aux5 {G : Type u} [group G] [fintype G]
  {N : subgroup G} [N.normal] (hN1 : nat.coprime (fintype.card N) N.index)
  (ih : ∀ (G' : Type u) [hG'1 : group G'] [hG'2 : fintype G'], by exactI
    ∀ (hG' : fintype.card G' < fintype.card G) {N' : subgroup G'} [N'.normal]
    (hN' : nat.coprime (fintype.card N') N'.index),
    ∃ H' : subgroup G', is_complement (N' : set G') (H' : set G'))
  (ic : ∀ H : subgroup G, ¬ is_complement (N : set G) (H : set G)) :
  false :=
begin
  tactic.unfreeze_local_instances,
  have h1 : N ≠ ⊥,
  { rintro rfl,
    exact ic ⊤ is_complement_singleton_top },
  have h2 : N ≠ ⊤,
  { rintro rfl,
    exact ic ⊥ is_complement_top_singleton },
  have h3 : ∀ K : subgroup G, K ⊔ N = ⊤ → K = ⊤,
  { contrapose! ic,
    obtain ⟨K, hK1, hK2⟩ := ic,
    have h31 : fintype.card K < fintype.card G,
    { sorry },
    have h32 : nat.coprime (fintype.card (N.comap K.subtype)) (N.comap K.subtype).index,
    { sorry },
    obtain ⟨H, hH⟩ := ih K h31 h32,
    refine ⟨H.map K.subtype, _⟩,
    sorry },
  have h4 : ∀ K : subgroup G, K.normal → K ≤ N → (K = ⊥ ∨ K = N),
  { contrapose! h3,
    obtain ⟨K, hK1, hK2, hK3, hK4⟩ := h3,
    have h41 : fintype.card (quotient_group.quotient K) < fintype.card G,
    { sorry },
    have h42 : nat.coprime (fintype.card (N.map (quotient_group.mk' K)))
      (N.map (quotient_group.mk' K)).index,
    { sorry },
    obtain ⟨H, hh⟩ := ih (quotient_group.quotient K) h41 h42,
    refine ⟨H.comap (quotient_group.mk' K), _, _⟩,
    { sorry },
    { sorry } },
  let p := nat.min_fac (fintype.card N),
  haveI : fact (p.prime) := ⟨nat.min_fac_prime sorry⟩,
  refine sylow.nonempty.elim (λ P : sylow p N, _),
  have h5 : (P.1.map N.subtype).normal,
  { suffices : (P.1.map N.subtype).normalizer = ⊤,
    { sorry },
    refine h3 (P.1.map N.subtype).normalizer P.frattini },
  have h6 : is_p_group p N,
  { sorry },
  haveI h7 : is_commutative N,
  { sorry },
  exact not_exists_of_forall_not ic (exists_right_complement_of_coprime_aux0 hN1),
end-/

lemma exists_right_complement_of_coprime_aux4
  {n : ℕ} {G : Type u} [group G] [fintype G] (hG : fintype.card G = n)
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement (N : set G) (H : set G) :=
begin
  tactic.unfreeze_local_instances,
  revert G,
  apply nat.strong_induction_on n,
  rintros n ih G _ _ rfl N _ hN,
  refine not_forall_not.mp (schur_zassenhaus_induction.step10 hN (λ G' _ _ hG', _)),
  apply ih _ hG',
  refl,
end

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement_of_coprime {G : Type u} [group G] [fintype G]
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement (N : set G) (H : set G) :=
exists_right_complement_of_coprime_aux4 rfl hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is abelian, normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement_of_coprime {G : Type u} [group G] [fintype G]
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement (H : set G) (N : set G) :=
Exists.imp (λ _, is_complement.symm) (exists_right_complement_of_coprime hN)

end subgroup
