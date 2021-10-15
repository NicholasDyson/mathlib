/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.quotient_group
import set_theory.cardinal

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.

## Main definitions

- `H.index` : the index of `H : subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.rel_index K` : the relative index of `H : subgroup G` in `K : subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

# Main results

- `index_mul_card` : `H.index * fintype.card H = fintype.card G`
- `index_dvd_card` : `H.index ∣ fintype.card G`
- `index_eq_mul_of_le` : If `H ≤ K`, then `H.index = K.index * (H.subgroup_of K).index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`

-/

universes u v

namespace subgroup

lemma range_inclusion {G : Type*} [group G] {H K : subgroup G} (h_le : H ≤ K) :
  (inclusion h_le).range = H.subgroup_of K :=
subgroup.ext (λ g, set.ext_iff.mp (set.range_inclusion h_le) g)

variables {G : Type*} [group G] (H K L : subgroup G)

/-- The index of a subgroup as a natural number, and returns 0 if the index is infinite. -/
@[to_additive "The index of a subgroup as a natural number,
and returns 0 if the index is infinite."]
noncomputable def index : ℕ :=
(cardinal.mk (quotient_group.quotient H)).to_nat

/-- The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite. -/
@[to_additive "The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite."]
noncomputable def rel_index : ℕ :=
(H.subgroup_of K).index

@[to_additive] lemma index_comap_of_surjective {G' : Type*} [group G'] {f : G' →* G}
  (hf : function.surjective f) : (H.comap f).index = H.index :=
begin
  have h1 : ∀ x y : G', @setoid.r G' (quotient_group.left_rel (H.comap f)) x y ↔
    @setoid.r G (quotient_group.left_rel H) (f x) (f y) :=
  λ x y, iff_of_eq (congr_arg (∈ H) (by rw [f.map_mul, f.map_inv])),
  have h2 := λ x y, (quotient.eq'.trans (h1 x y)).trans quotient.eq'.symm,
  let ϕ : quotient_group.quotient (H.comap f) ≃ quotient_group.quotient H :=
  equiv.of_bijective (quotient.map' f (λ x y, (h1 x y).mp))
    ⟨by { refine quotient.ind' (λ x, _), refine quotient.ind' (λ y, _), exact (h2 x y).mpr },
    by { refine quotient.ind' (λ x, _), obtain ⟨y, hy⟩ := hf x,
      exact ⟨y, (quotient.map'_mk' f _ y).trans (congr_arg quotient.mk' hy)⟩ }⟩,
  rw [index, ←cardinal.to_nat_lift, cardinal.lift_mk_eq.mpr ⟨ϕ⟩, cardinal.to_nat_lift, ←index],
end

@[to_additive] lemma index_comap {G' : Type*} [group G'] (f : G' →* G) :
  (H.comap f).index = H.rel_index f.range :=
eq.trans (congr_arg index (by refl))
  ((H.subgroup_of f.range).index_comap_of_surjective f.range_restrict_surjective)

variables {H K L}

@[to_additive] lemma index_eq_mul_of_le (h : H ≤ K) : H.index = K.index * H.rel_index K :=
(congr_arg cardinal.to_nat (by exact (quotient_equiv_prod_of_le h).cardinal_eq)).trans
  (cardinal.to_nat_mul _ _)

@[to_additive] lemma index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
⟨H.rel_index K, index_eq_mul_of_le h⟩

lemma rel_index_subgroup_of (hKL : K ≤ L) :
  H.rel_index K = (H.subgroup_of L).rel_index (K.subgroup_of L) :=
(index_comap (H.subgroup_of L) (inclusion hKL)).trans (congr_arg _ (range_inclusion hKL))

lemma rel_index_mul_rel_index (hHK : H ≤ K) (hKL : K ≤ L) :
  H.rel_index K * K.rel_index L = H.rel_index L :=
begin
  rw [rel_index_subgroup_of hKL, mul_comm, eq_comm],
  exact index_eq_mul_of_le (λ x hx, hHK hx),
end

variables (H K L)

@[to_additive] lemma index_eq_card [fintype (quotient_group.quotient H)] :
  H.index = fintype.card (quotient_group.quotient H) :=
cardinal.mk_to_nat_eq_card

@[to_additive] lemma index_mul_card [fintype G] [hH : fintype H] :
  H.index * fintype.card H = fintype.card G :=
begin
  classical,
  rw H.index_eq_card,
  apply H.card_eq_card_quotient_mul_card_subgroup.symm,
end

@[to_additive] lemma index_dvd_card [fintype G] : H.index ∣ fintype.card G :=
begin
  classical,
  exact ⟨fintype.card H, H.index_mul_card.symm⟩,
end




lemma ker_subtype : H.subtype.ker = ⊥ :=
H.subtype.ker_eq_bot_iff.mpr subtype.coe_injective

lemma bot_subgroup_of : (⊥ : subgroup G).subgroup_of H = ⊥ :=
H.subtype.comap_bot.trans H.ker_subtype

lemma rel_index_bot [fintype H] : rel_index ⊥ H = fintype.card H :=
begin
  rw rel_index,
  rw bot_subgroup_of,
  rw index_bot,
  --change (⊥ : subgroup H).index = _,
end

end subgroup
