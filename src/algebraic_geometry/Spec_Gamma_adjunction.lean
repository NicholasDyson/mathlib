/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import algebraic_geometry.Spec
import algebraic_geometry.ringed_space
import topology.sheaves.sheaf_condition.basis_le
import topology.sheaves.sheaf_condition.pairwise_intersections

/-!
# Adjunction between `Γ` and `Spec`

-/

noncomputable theory
universe variables u v

namespace algebraic_geometry
open opposite
open category_theory
open structure_sheaf
open prime_spectrum
open topological_space
open algebraic_geometry.LocallyRingedSpace
open Top.presheaf
open Top.presheaf.sheaf_condition

def local_ring.closed_point (R : Type u) [comm_ring R] [local_ring R] :
  prime_spectrum R :=
⟨local_ring.maximal_ideal R, (local_ring.maximal_ideal.is_maximal R).is_prime⟩
-- move to local_ring
-- to do : maximal ideals are closed points in the prime spectrum of any ring
-- minimal primes are generic points of irreducible components

abbreviation Spec' (R : CommRing) := Spec.to_LocallyRingedSpace.obj (op R)

variable (R : CommRing)

/- basic opens on Spec R -/
def basic_open_B : @Top.opens_index_struct (Spec' R).to_Top := ⟨R, λ r, basic_open r⟩
-- lesson: better directly work with the indexing function than the range set!

private def idfo := induced_functor (op ∘ (basic_open_B R).f)

lemma basic_opens_is_basis : Top.is_basis_range (basic_open_B R) :=
begin
  unfold Top.is_basis_range opens.is_basis basic_open_B,
  convert is_topological_basis_basic_opens,
  rw ← set.range_comp, dsimp, congr,
end

lemma to_basic_open_epi (r : R) : epi (to_open R (basic_open r)) :=
⟨λ S f g h, by { change f.comp _ = g.comp _ at h,
  rw [←localization_to_basic_open, ←ring_hom.comp_assoc, ←ring_hom.comp_assoc] at h,
  apply (is_iso.epi_of_iso (show CommRing.of _ ⟶ _, from to_basic_open R r)).1,
  apply is_localization.ring_hom_ext _ h,
  swap, exact localization.is_localization }⟩

lemma is_localization_iso_comp {M : submonoid R} {S T : CommRing}
  [i : algebra R S] [h : is_localization M S] (f : S ≅ T) :
  @is_localization _ _ M T _ (f.hom.comp i.to_ring_hom).to_algebra :=
{ map_units := let hm := h.1 in
    λ t, is_unit.map f.hom.to_monoid_hom (hm t),
  surj := let hs := h.2 in λ t, let ⟨⟨r,s⟩,he⟩ := hs (f.inv t) in ⟨⟨r,s⟩, by {
    convert congr_arg f.hom he, rw [ring_hom.map_mul, ←comp_apply, iso.inv_hom_id], refl}⟩,
  eq_iff_exists := let he := h.3 in λ t t', by { rw ← he, split,
    apply f.CommRing_iso_to_ring_equiv.injective, exact congr_arg f.hom } }

instance (r : R) : algebra R ((structure_sheaf R).1.obj (op $ basic_open r)) :=
  (to_open R (basic_open r)).to_algebra

/- instance of sections of structure sheaf on basic open as localization of the ring -/
instance (r : R) : is_localization.away r ((structure_sheaf R).1.obj (op $ basic_open r)) :=
by { convert is_localization_iso_comp _ (basic_open_iso R r).symm, /- can't replace _ by R -/
  change ring_hom.to_algebra _ = _, congr' 1,
  exact (localization_to_basic_open R r).symm,
  exact localization.is_localization }

instance (x : prime_spectrum R) : algebra R ((structure_sheaf R).1.stalk x) :=
  (to_stalk R x).to_algebra

instance (x : prime_spectrum R) :
  is_localization.at_prime ((structure_sheaf R).1.stalk x) x.as_ideal :=
by { convert is_localization_iso_comp _ (stalk_iso R x).symm,
  change ring_hom.to_algebra _ = _, congr' 1, erw iso.eq_comp_inv,
  exact to_stalk_comp_stalk_to_fiber_ring_hom R x,
  exact localization.is_localization }

namespace LocallyRingedSpace
variable (X : LocallyRingedSpace)
abbreviation Γ' := Γ.obj (op X)

/- map from the global sections to a stalk -/
def Γ_to_stalk (x : X) : Γ' X ⟶ X.presheaf.stalk x :=
  X.presheaf.germ (⟨x,trivial⟩ : (⊤ : opens X))
  -- or @Top.presheaf.germ _ _ _ _ _ ⊤ ⟨x,trivial⟩

/- counit on the underlying set -/
def to_Γ_Spec_fun : X → Spec' (Γ' X) :=
λ x, comap (X.Γ_to_stalk x) (@local_ring.closed_point _ _ (X.local_ring x))

lemma mem_ideal_Γ_to_stalk_iff (r : Γ' X) (x : X) :
  r ∉ (X.to_Γ_Spec_fun x).as_ideal ↔ is_unit (X.Γ_to_stalk x r) :=
begin
  unfold to_Γ_Spec_fun,
  rw [comap_as_ideal, ideal.mem_comap],
  unfold local_ring.closed_point, rw local_ring.mem_maximal_ideal,
  unfold nonunits, rw [set.mem_set_of_eq, not_not],
end

/- preimage of a basic open under the counit is a basic open -/
lemma to_Γ_Spec_preim_basic_open_eq (r : Γ' X) :
  X.to_Γ_Spec_fun⁻¹' (basic_open r).1
  = (X.to_RingedSpace.basic_open r).1 :=
begin
  ext, dsimp,
  rw [set.mem_preimage, opens.mem_coe,
      mem_basic_open, X.to_RingedSpace.mem_basic_open],
  apply mem_ideal_Γ_to_stalk_iff,
end

/- counit is continuous -/
lemma to_Γ_Spec_continuous : continuous X.to_Γ_Spec_fun :=
begin
  apply is_topological_basis_basic_opens.continuous,
  rintro U ⟨r,rfl⟩, convert (X.to_RingedSpace.basic_open r).2,
  exact X.to_Γ_Spec_preim_basic_open_eq r,
end

def to_Γ_Spec_Top : continuous_map X (Spec' (Γ' X)) :=
{ to_fun := X.to_Γ_Spec_fun,
  continuous_to_fun := X.to_Γ_Spec_continuous }

lemma to_Γ_Spec_opens_map_obj_basic_open_eq (r : Γ' X) :
  (opens.map X.to_Γ_Spec_Top).obj (basic_open r) = X.to_RingedSpace.basic_open r
  := subtype.eq (X.to_Γ_Spec_preim_basic_open_eq r)

def to_opens_map_basic_open (r : Γ' X) :=
  X.presheaf.map ((opens.map X.to_Γ_Spec_Top).obj (basic_open r)).le_top.op

def is_unit_res_opens_map_basic_open (r : Γ' X) :=
  by { have h := X.to_RingedSpace.is_unit_res_basic_open r,
  rw ← to_Γ_Spec_opens_map_obj_basic_open_eq at h, exact h }

def to_Γ_Spec_sheaf_app (r : Γ' X) := by {
  let l := is_localization.away.lift r (X.is_unit_res_opens_map_basic_open r),
  swap 5, exact localization.is_localization,
  exact (basic_open_iso _ r).hom ≫ l }

/- characterization of the sheaf morphism on basic opens,
   direction → used in proving naturality of the morphism,
   direction ← ... -/
lemma to_Γ_Spec_sheaf_app_prop (r : Γ' X) :
  ∀ f, to_open _ (basic_open r) ≫ f = X.to_opens_map_basic_open r
  ↔ f = X.to_Γ_Spec_sheaf_app r :=
λ f, begin
  unfold to_Γ_Spec_sheaf_app, rw ← iso.inv_comp_eq,
  rw ← (is_localization.away.away_map.lift_comp r
    (X.is_unit_res_opens_map_basic_open r) : _ = X.to_opens_map_basic_open r),
  swap 5, exact localization.is_localization,
  rw ← localization_to_basic_open _ r,
  change f.comp _ = _ ↔ _, rw ← ring_hom.comp_assoc,
  split, { intro h, apply is_localization.ring_hom_ext _ h,
  swap, exact localization.is_localization },
  { intro h, rw ← h, refl },
end

def to_Γ_Spec_sheaf_basic_opens : idfo _ ⋙ (Spec' (Γ' X)).presheaf
                               ⟶ idfo _ ⋙ X.to_Γ_Spec_Top _* X.presheaf :=
{ app := X.to_Γ_Spec_sheaf_app,
  naturality' := λ r s f, by {
    apply (to_basic_open_epi _ r).1,
    simp only [←category.assoc],
    rw (X.to_Γ_Spec_sheaf_app_prop r _).2 rfl,
    convert (X.to_Γ_Spec_sheaf_app_prop s _).2 rfl,
    apply eq.symm, apply X.presheaf.map_comp } }

def to_Γ_Spec_sheaf := sheaf_hom.uniq_extn_from_basis
  ((is_sheaf_iff_is_sheaf_opens_le_cover _).1 (pushforward_sheaf_of_sheaf X.𝒪.2))
  (basic_opens_is_basis _) X.to_Γ_Spec_sheaf_basic_opens

def to_Γ_Spec_SheafedSpace : X.to_SheafedSpace ⟶ (Spec' (Γ' X)).to_SheafedSpace :=
{ base := X.to_Γ_Spec_Top,
  c := X.to_Γ_Spec_sheaf.lift }

lemma to_Γ_Spec_SheafedSpace_app_eq (r : Γ' X) :
  X.to_Γ_Spec_SheafedSpace.c.app (op (basic_open r)) = X.to_Γ_Spec_sheaf_app r :=
by change (whisker_left (idfo _) _).app r = _; erw X.to_Γ_Spec_sheaf.fac; refl

def to_Γ_Spec_SheafedSpace_app_prop (r : Γ' X) := by {
  have h := X.to_Γ_Spec_sheaf_app_prop r,
  rw ← to_Γ_Spec_SheafedSpace_app_eq at h,
  exact h }

lemma to_stalk_comm (x : X) : to_stalk _ _ ≫
  PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x = X.Γ_to_stalk x :=
begin
  rw PresheafedSpace.stalk_map,
  erw ← to_open_germ _ (basic_open (1 : Γ' X))
    ⟨X.to_Γ_Spec_fun x, by rw basic_open_one; triv⟩,
  rw [←category.assoc, category.assoc (to_open _ _)],
  erw stalk_functor_map_germ,
  rw [←category.assoc (to_open _ _), (X.to_Γ_Spec_SheafedSpace_app_prop 1 _).2 rfl],
  unfold Γ_to_stalk, rw ← stalk_pushforward_germ _ X.to_Γ_Spec_Top X.presheaf ⊤,
  congr' 1, change (X.to_Γ_Spec_Top _* X.presheaf).map le_top.hom.op ≫ _ = _,
  apply germ_res,
end


def to_Γ_Spec : X ⟶ Spec' (Γ' X) :=
begin
  fsplit, exact X.to_Γ_Spec_SheafedSpace,
  intro x, let p : prime_spectrum (Γ' X) := X.to_Γ_Spec_fun x,
  fsplit, intros t ht,
  have h : is_localization.at_prime ((structure_sheaf (Γ' X)).1.stalk p) p.as_ideal,
  apply_instance,
  have he' := h.surj, rcases he' t with ⟨⟨r,s⟩,he⟩,
  have hu := h.map_units,
  let sm := PresheafedSpace.stalk_map X.to_Γ_Spec_SheafedSpace x,
  have hr : is_unit (X.Γ_to_stalk x r),
    apply_fun sm at he,
    rw [←to_stalk_comm, comp_apply],
    erw ← he, rw ring_hom.map_mul,
    apply is_unit.mul ht,
    exact is_unit.map sm.to_monoid_hom (hu s),
  rw ← mem_ideal_Γ_to_stalk_iff at hr,
  have hr' := hu ⟨r,hr⟩, erw ← he at hr',
  exact is_unit_of_mul_is_unit_left hr',
end

end LocallyRingedSpace

end algebraic_geometry
