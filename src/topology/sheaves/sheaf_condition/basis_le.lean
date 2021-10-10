/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import topology.sheaves.presheaf
import category_theory.limits.final
import topology.sheaves.sheaf_condition.opens_le_cover

/-!
# A consequence of the sheaf condition about covers by open sets in a topological basis
-/

universes v u

noncomputable theory

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C]
variables {X : Top.{v}} (B : set (opens X)) (F G : presheaf C X) (U : opens X) (𝒰 : set (opens X))

namespace presheaf

namespace sheaf_condition

def basis_le_s (V : opens X) := V ≤ U ∧ V ∈ B
def basis_le : Type v := { V // basis_le_s B U V }
def basis_le_fam := λ V : basis_le B U, V.val

instance : category (basis_le B U) := category_theory.full_subcategory _

private def fsi := (full_subcategory_inclusion _ : 𝒰 ⥤ opens X)

def basis_le_cocone : cocone (fsi (basis_le_s B U)) :=
{ X := U,
  ι := { app := λ V, V.property.1.hom } }

def basis_le_cocone' : cocone (fsi (basis_le_s B U)) :=
{ X := supr (basis_le_fam B U),
  ι := { app := opens.le_supr _ } }

@[ext]
lemma cocone_ext {c1 c2 : cocone (fsi 𝒰)}
  (h : c1.X = c2.X) : c1 = c2 :=
begin
  cases c1, cases c2, congr, exact h, convert cast_heq _ _, dsimp at h, rw h,
end

lemma self_eq_supr_basis_le (hB : is_basis B) : supr (basis_le_fam B U) = U :=
begin
  apply subtype.eq, rw hB.open_eq_sUnion' U.2,
  dsimp, ext, rw [mem_coe, mem_supr],
  exact ⟨λ⟨⟨V,hVU,hVB⟩,hx⟩, ⟨V,⟨⟨V,hVB,rfl⟩,hVU⟩,hx⟩,
        λ⟨_,⟨⟨V,hVB,rfl⟩,hVU⟩,hx⟩, ⟨⟨V,hVU,hVB⟩,hx⟩⟩,
end

lemma basis_le_cocone_eq (hB : is_basis B) : basis_le_cocone B U = basis_le_cocone' B U :=
  cocone_ext _ (self_eq_supr_basis_le B U hB).symm


private def bl2b : basis_le B U ⥤ B :=
{ obj := λV, ⟨V.1,V.2.2⟩,
  map := λ_ _, id,
  map_id' := by simp,
  map_comp' := λ _ _, by simp }

lemma bl2b2o : bl2b B U ⋙ fsi B = fsi (basis_le_s B U) := rfl

private def bl2bo := (bl2b B U).op

def basis_le_self (V : B) : basis_le B V := ⟨V,le_of_eq rfl,V.2⟩

lemma basis_le_self_bl2bo (V : B) :
  (bl2bo B V).obj (op (basis_le_self B V)) = op V :=
by unfold bl2bo bl2b; dsimp; congr; apply subtype.eq; refl

def basis_le_presheaf_cone := F.map_cone (basis_le_cocone B U).op

lemma basis_le_presheaf_cone_app (V : (basis_le B U)ᵒᵖ) :
  (basis_le_presheaf_cone B F U).π.app V = F.map V.unop.2.1.hom.op := rfl

lemma basis_le_presheaf_cone_app_id (V : B) :
  (basis_le_presheaf_cone B F V).π.app (op (basis_le_self B V)) = 𝟙 (F.obj (op V))
:= by rw [basis_le_presheaf_cone_app, ←F.map_id]; refl

def lim_basis_le : Type (max u v) :=
  Π (U : opens X), is_limit (basis_le_presheaf_cone B F U)


lemma mono_to_cover_of_sheaf_condition (hF : F.sheaf_condition_opens_le_cover)
   ⦃ι : Type v⦄ (𝒰 : ι → opens X) (hU : supr 𝒰 = U) (A : C) (f g : A ⟶ F.obj (op U))
   -- hU is a hack to avoid "motive not type correct" in mono_to_basis_le_of_sheaf_condition below
   (h : ∀ i, f ≫ F.map (hU.rec (opens.le_supr 𝒰 i)).op = g ≫ F.map (hU.rec (opens.le_supr 𝒰 i)).op) :
   f = g :=
begin
  subst hU, apply (hF 𝒰).hom_ext, intro V, dsimp at ⊢, let i := V.unop.2.some,
  let i1 := opens.le_supr 𝒰 i, let i2 := V.unop.2.some_spec.hom,
  have : (opens_le_cover_cocone 𝒰).ι.app V.unop = i2 ≫ i1 := rfl,
  rw [this, op_comp, F.map_comp, ←category.assoc, h i, category.assoc],
end

lemma mono_to_basis_le_of_sheaf_condition (hB : is_basis B)
  (hF : F.sheaf_condition_opens_le_cover) (A : C) (f g : A ⟶ F.obj (op U))
  (h : ∀ V : basis_le B U, f ≫ F.map V.2.1.hom.op = g ≫ F.map V.2.1.hom.op) :
  f = g :=
mono_to_cover_of_sheaf_condition F _ hF _
  (self_eq_supr_basis_le _ U hB) _ _ _ (λ V, by convert h V)

lemma cone_opens_w (c : cone ((fsi 𝒰).op ⋙ F))
  {x : 𝒰} {y : opens X} (h : y ∈ 𝒰) (f : op ↑x  ⟶ op y) :
  c.π.app (op x) ≫ F.map f = c.π.app (op ⟨y,h⟩) :=
let f' : (⟨y,h⟩ : 𝒰) ⟶ x := f.unop  in  c.w f'.op

def cone_opens_le_cover_of_cone_basis_le (hB : is_basis B) (hF : F.sheaf_condition_opens_le_cover)
  (c : cone ((fsi (basis_le_s B U)).op ⋙ F)) :
  cone ((fsi (opens_le_cover_s (basis_le_fam B U))).op ⋙ F) :=
begin
  use c.X, refine ⟨λW, c.π.app (op W.unop.2.some) ≫ F.map W.unop.2.some_spec.hom.op, _⟩,
  intros W₁ W₂ _,
  apply mono_to_basis_le_of_sheaf_condition B F W₂.unop.1 hB hF,
  intro W, dsimp at ⊢, simp only [category.id_comp, category.assoc, ←F.map_comp, ←op_comp] at ⊢,
  rw [cone_opens_w, cone_opens_w],
  exact ⟨W.2.1.trans (W₂.unop.2.some_spec.trans W₂.unop.2.some.2.1), W.2.2⟩,
end

theorem lim_basis_le_of_sheaf_condition (hB : is_basis B)
  (hF : F.sheaf_condition_opens_le_cover) : lim_basis_le B F :=
begin
  intro U, unfold basis_le_presheaf_cone, rw basis_le_cocone_eq B U hB,
  let f := cone_opens_le_cover_of_cone_basis_le B F U hB hF,
  have hU := hF (basis_le_fam B U), fsplit,
    exact λc, hU.lift (f c),
    intros c V, abstract fac
    { let hV : ∃ V', V.unop ≤ V' := ⟨V.unop, le_of_eq rfl⟩,
      convert hU.fac (f c) (op ⟨V.unop.1, hV⟩) using 1,
      exact (c.w hV.some_spec.hom.op).symm },
    intros c ι h, apply mono_to_cover_of_sheaf_condition F _ hF _ rfl,
    intro V, specialize h (op V),
    rwa ← lim_basis_le_of_sheaf_condition.fac B F hB hF U hU c (op V) at h,
end


theorem sheaf_hom_extn_from_basis (hG : G.sheaf_condition_opens_le_cover)
  (hB : is_basis B) (α : (fsi B).op ⋙ F ⟶ _ ⋙ G) :
  ∃! αext : F ⟶ G, 𝟙 _ ◫ αext = α :=
begin
  have hl := lim_basis_le_of_sheaf_condition B G hB hG,
  set c : Π U, cone ((fsi (basis_le_s B U)).op ⋙ G) :=
    λ U, let α' := 𝟙 (bl2bo B U) ◫ α in
    ⟨F.obj (op U), (basis_le_presheaf_cone B F U).π ≫ α'⟩ with hc,
    -- must first define α', strange error when α' is inlined
  fsplit, fsplit, exact λ U, (hl U.unop).lift (c U.unop),
  { intros U V i,
    apply mono_to_basis_le_of_sheaf_condition B G V.unop hB hG,
    cases i.unop, cases down, intro W, rw category.assoc,
    convert congr_arg (λ f, F.map i ≫ f) ((hl V.unop).fac (c V.unop) (op W)) using 1,
    convert (hl U.unop).fac (c U.unop) (op ⟨W.1,W.2.1.trans down,W.2.2⟩) using 1,
    rw [category.assoc, ←G.map_comp], refl,
    rw [nat_trans.comp_app, nat_trans.comp_app, ←category.assoc],
    congr, rw [basis_le_presheaf_cone_app, ←F.map_comp], refl },
  split,
  { ext V', set V := V'.unop with hV,
    convert (hl V).fac (c V) (op (basis_le_self B V)) using 1,
    dsimp at ⊢, rw [(fsi B).map_id, op_id, G.map_id, category.comp_id,
      basis_le_presheaf_cone_app_id, category.id_comp], congr,
    rw [basis_le_self_bl2bo, hV], refl },
  { intros β h, ext U, apply (hl U.unop).uniq (c U.unop),
    intro V, rw [basis_le_presheaf_cone_app, ←β.naturality],
    dsimp at ⊢, rw ← h, dsimp at ⊢,
    rw [(fsi B).map_id, op_id, G.map_id, category.comp_id, category.comp_id],
    congr },
end


end sheaf_condition

end presheaf

end Top
