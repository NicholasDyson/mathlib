/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.l2_space

/-! # Conditional expectation

The conditional expectation will be defined for functions in `L²` by an orthogonal projection into
a complete subspace of `L²`. It will then be extended to `L¹`.

For now, this file contains only the definition of the subspace of `Lᵖ` containing functions which
are measurable with respect to a sub-σ-algebra, as well as a proof that it is complete.

-/

noncomputable theory
open topological_space measure_theory.Lp filter
open_locale nnreal ennreal topological_space big_operators measure_theory

namespace measure_theory

/-- A function `f` verifies `ae_measurable' m f μ` if it is `μ`-a.e. equal to an `m`-measurable
function. This is similar to `ae_measurable`, but the `measurable_space` structures used for the
measurability statement and for the measure are different. -/
def ae_measurable' {α β} [measurable_space β] (m : measurable_space α) {m0 : measurable_space α}
  (f : α → β) (μ : measure α) : Prop :=
∃ g : α → β, @measurable α β m _ g ∧ f =ᵐ[μ] g

namespace ae_measurable'

variables {α β 𝕜 : Type*} {m m0 : measurable_space α} {μ : measure α}
  [measurable_space β] [measurable_space 𝕜] {f g : α → β}

lemma congr (hf : ae_measurable' m f μ) (hfg : f =ᵐ[μ] g) : ae_measurable' m g μ :=
by { obtain ⟨f', hf'_meas, hff'⟩ := hf, exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩, }

lemma add [has_add β] [has_measurable_add₂ β] (hf : ae_measurable' m f μ)
  (hg : ae_measurable' m g μ) :
  ae_measurable' m (f+g) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  exact ⟨f' + g', @measurable.add α m _ _ _ _ f' g' h_f'_meas h_g'_meas, hff'.add hgg'⟩,
end

lemma const_smul [has_scalar 𝕜 β] [has_measurable_smul 𝕜 β] (c : 𝕜) (hf : ae_measurable' m f μ) :
  ae_measurable' m (c • f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul α m _ _ _ _ _ _ f' h_f'_meas c, _⟩,
  exact eventually_eq.fun_comp hff' (λ x, c • x),
end

end ae_measurable'

lemma ae_measurable'_of_ae_measurable'_trim {α β} {m m0 m0' : measurable_space α}
  [measurable_space β] (hm0 : m0 ≤ m0') {μ : measure α} {f : α → β}
  (hf : ae_measurable' m f (μ.trim hm0)) :
  ae_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hfg⟩, }

variables {α β γ E E' F F' G G' H 𝕜 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] [measurable_space 𝕜] -- 𝕜 for ℝ or ℂ, together with a measurable_space
  [measurable_space β] -- β for a generic measurable space
  -- E for an inner product space
  [inner_product_space 𝕜 E] [measurable_space E] [borel_space E] [second_countable_topology E]
  -- E' for an inner product space on which we compute integrals
  [inner_product_space 𝕜 E'] [measurable_space E'] [borel_space E'] [second_countable_topology E']
  [complete_space E'] [normed_space ℝ E']
  -- F for a Lp submodule
  [normed_group F] [normed_space 𝕜 F] [measurable_space F] [borel_space F]
  [second_countable_topology F]
  -- F' for integrals on a Lp submodule
  [normed_group F'] [normed_space 𝕜 F'] [measurable_space F'] [borel_space F']
  [second_countable_topology F'] [normed_space ℝ F'] [complete_space F']
  -- G for a Lp add_subgroup
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  -- G' for integrals on a Lp add_subgroup
  [normed_group G'] [measurable_space G'] [borel_space G'] [second_countable_topology G']
  [normed_space ℝ G'] [complete_space G']
  -- H for measurable space and normed group (hypotheses of mem_ℒp)
  [measurable_space H] [normed_group H]

section Lp_meas

variables (F 𝕜)
/-- `Lp_meas F 𝕜 m p μ` is the subspace of `Lp F p μ` containing functions `f` verifying
`ae_measurable' m f μ`, i.e. functions which are `μ`-a.e. equal to an `m`-measurable function. -/
def Lp_meas [opens_measurable_space 𝕜] (m : measurable_space α) [measurable_space α] (p : ℝ≥0∞)
  (μ : measure α) :
  submodule 𝕜 (Lp F p μ) :=
{ carrier   := {f : (Lp F p μ) | ae_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → F), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
  add_mem'  := λ f g hf hg, (hf.add hg).congr (Lp.coe_fn_add f g).symm,
  smul_mem' := λ c f hf, (hf.const_smul c).congr (Lp.coe_fn_smul c f).symm, }
variables {F 𝕜}

variables [opens_measurable_space 𝕜]

lemma mem_Lp_meas_iff_ae_measurable' {m m0 : measurable_space α} {μ : measure α} {f : Lp F p μ} :
  f ∈ Lp_meas F 𝕜 m p μ ↔ ae_measurable' m f μ :=
by simp_rw [← set_like.mem_coe, ← submodule.mem_carrier, Lp_meas, set.mem_set_of_eq]

lemma Lp_meas.ae_measurable' {m m0 : measurable_space α} {μ : measure α} (f : Lp_meas F 𝕜 m p μ) :
  ae_measurable' m f μ :=
mem_Lp_meas_iff_ae_measurable'.mp f.mem

lemma mem_Lp_meas_self {m0 : measurable_space α} (μ : measure α) (f : Lp F p μ) :
  f ∈ Lp_meas F 𝕜 m0 p μ :=
mem_Lp_meas_iff_ae_measurable'.mpr (Lp.ae_measurable f)

lemma Lp_meas_coe {m m0 : measurable_space α} {μ : measure α} {f : Lp_meas F 𝕜 m p μ} :
  ⇑f = (f : Lp F p μ) :=
coe_fn_coe_base f

lemma mem_Lp_meas_indicator_const_Lp {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} {s : set α} (hs : @measurable_set α m s) {hμs : μ s ≠ ∞} {c : F} :
  indicator_const_Lp p (hm s hs) hμs c ∈ Lp_meas F 𝕜 m p μ :=
⟨s.indicator (λ x : α, c),
  @measurable.indicator α _ m _ _ s (λ x, c) (@measurable_const _ α _ m _) hs,
  indicator_const_Lp_coe_fn⟩

section complete_subspace

/-! ## The subspace `Lp_meas` is complete.

We define a `linear_isometry_equiv` between `Lp_meas` and the `Lp` space corresponding to the
measure `μ.trim hm`. As a consequence, the completeness of `Lp` implies completeness of
`Lp_meas`. -/

variables {ι : Type*} {m m0 : measurable_space α} {μ : measure α}

/-- If `f` belongs to `Lp_meas F 𝕜 m p μ`, then the measurable function it is almost everywhere
equal to (given by `ae_measurable.mk`) belongs to `ℒp` for the measure `μ.trim hm`. -/
lemma mem_ℒp_trim_of_mem_Lp_meas (hm : m ≤ m0) (f : Lp F p μ) (hf_meas : f ∈ Lp_meas F 𝕜 m p μ) :
  @mem_ℒp α F m _ _ (mem_Lp_meas_iff_ae_measurable'.mp hf_meas).some p (μ.trim hm) :=
begin
  have hf : ae_measurable' m f μ, from (mem_Lp_meas_iff_ae_measurable'.mp hf_meas),
  let g := hf.some,
  obtain ⟨hg, hfg⟩ := hf.some_spec,
  change @mem_ℒp α F m _ _ g p (μ.trim hm),
  refine ⟨@measurable.ae_measurable _ _ m _ g (μ.trim hm) hg, _⟩,
  have h_snorm_fg : @snorm α _ m _ g p (μ.trim hm) = snorm f p μ,
    by { rw snorm_trim hm hg, exact snorm_congr_ae hfg.symm, },
  rw h_snorm_fg,
  exact Lp.snorm_lt_top f,
end

/-- If `f` belongs to `Lp` for the measure `μ.trim hm`, then it belongs to the subspace
`Lp_meas F 𝕜 m p μ`. -/
lemma mem_Lp_meas_to_Lp_of_trim (hm : m ≤ m0) (f : @Lp α F m _ _ _ _ p (μ.trim hm)) :
  (mem_ℒp_of_mem_ℒp_trim hm (@Lp.mem_ℒp _ _ m _ _ _ _ _ _ f)).to_Lp f ∈ Lp_meas F 𝕜 m p μ :=
begin
  let hf_mem_ℒp := mem_ℒp_of_mem_ℒp_trim hm (@Lp.mem_ℒp _ _ m _ _ _ _ _ _ f),
  rw mem_Lp_meas_iff_ae_measurable',
  refine ae_measurable'.congr _ (mem_ℒp.coe_fn_to_Lp hf_mem_ℒp).symm,
  refine ae_measurable'_of_ae_measurable'_trim hm _,
  exact (@Lp.ae_measurable _ _ m _ _ _ _ _ _ f),
end

variables (F 𝕜 p μ)
/-- Map from `Lp_meas` to `Lp F p (μ.trim hm)`. -/
def Lp_meas_to_Lp_trim (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) : @Lp α F m _ _ _ _ p (μ.trim hm) :=
@mem_ℒp.to_Lp _ _ m p (μ.trim hm) _ _ _ _ (mem_Lp_meas_iff_ae_measurable'.mp f.mem).some
  (mem_ℒp_trim_of_mem_Lp_meas hm f f.mem)

/-- Map from `Lp F p (μ.trim hm)` to `Lp_meas`, inverse of `Lp_meas_to_Lp_trim`. -/
def Lp_trim_to_Lp_meas (hm : m ≤ m0) (f : @Lp α F m _ _ _ _ p (μ.trim hm)) :
  Lp_meas F 𝕜 m p μ :=
⟨(mem_ℒp_of_mem_ℒp_trim hm (@Lp.mem_ℒp _ _ m _ _ _ _ _ _ f)).to_Lp f,
  mem_Lp_meas_to_Lp_of_trim hm f⟩

variables {F 𝕜 p μ}

lemma Lp_meas_to_Lp_trim_ae_eq (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) :
  Lp_meas_to_Lp_trim F 𝕜 p μ hm f =ᵐ[μ] f :=
(ae_eq_of_ae_eq_trim
    (@mem_ℒp.coe_fn_to_Lp _ _ m _ _ _ _ _ _ _ (mem_ℒp_trim_of_mem_Lp_meas hm ↑f f.mem))).trans
  (mem_Lp_meas_iff_ae_measurable'.mp f.mem).some_spec.2.symm

lemma Lp_trim_to_Lp_meas_ae_eq (hm : m ≤ m0) (f : @Lp α F m _ _ _ _ p (μ.trim hm)) :
  Lp_trim_to_Lp_meas F 𝕜 p μ hm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

/-- `Lp_trim_to_Lp_meas` is a right inverse of `Lp_meas_to_Lp_trim`. -/
lemma Lp_meas_to_Lp_trim_right_inv (hm : m ≤ m0) :
  function.right_inverse (Lp_trim_to_Lp_meas F 𝕜 p μ hm) (Lp_meas_to_Lp_trim F 𝕜 p μ hm) :=
begin
  intro f,
  ext1,
  refine ae_eq_trim_of_measurable hm _ _ _,
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact (Lp_meas_to_Lp_trim_ae_eq hm _).trans (Lp_trim_to_Lp_meas_ae_eq hm _), },
end

/-- `Lp_trim_to_Lp_meas` is a left inverse of `Lp_meas_to_Lp_trim`. -/
lemma Lp_meas_to_Lp_trim_left_inv (hm : m ≤ m0) :
  function.left_inverse (Lp_trim_to_Lp_meas F 𝕜 p μ hm) (Lp_meas_to_Lp_trim F 𝕜 p μ hm) :=
begin
  intro f,
  ext1,
  ext1,
  rw ← Lp_meas_coe,
  exact (Lp_trim_to_Lp_meas_ae_eq hm _).trans (Lp_meas_to_Lp_trim_ae_eq hm _),
end

lemma Lp_meas_to_Lp_trim_add (hm : m ≤ m0) (f g : Lp_meas F 𝕜 m p μ) :
  Lp_meas_to_Lp_trim F 𝕜 p μ hm (f + g)
    = Lp_meas_to_Lp_trim F 𝕜 p μ hm f + Lp_meas_to_Lp_trim F 𝕜 p μ hm g :=
begin
  ext1,
  refine eventually_eq.trans _ (@Lp.coe_fn_add _ _ m _ _ _ _ _ _ _ _).symm,
  refine ae_eq_trim_of_measurable hm _ _ _,
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact @measurable.add _ m _ _ _ _ _ _ (@Lp.measurable _ _ m _ _ _ _ _ _ _)
      (@Lp.measurable _ _ m _ _ _ _ _ _ _), },
  refine (Lp_meas_to_Lp_trim_ae_eq hm _).trans _,
  refine eventually_eq.trans _
    (eventually_eq.add (Lp_meas_to_Lp_trim_ae_eq hm f).symm (Lp_meas_to_Lp_trim_ae_eq hm g).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  simp_rw Lp_meas_coe,
  refine eventually_of_forall (λ x, _),
  refl,
end

lemma Lp_meas_to_Lp_trim_smul (hm : m ≤ m0) (c : 𝕜) (f : Lp_meas F 𝕜 m p μ) :
  Lp_meas_to_Lp_trim F 𝕜 p μ hm (c • f) = c • Lp_meas_to_Lp_trim F 𝕜 p μ hm f :=
begin
  ext1,
  refine eventually_eq.trans _ (@Lp.coe_fn_smul _ _ m _ _ _ _ _ _ _ _ _ _ _ _ _).symm,
  refine ae_eq_trim_of_measurable hm _ _ _,
  { exact @Lp.measurable _ _ m _ _ _ _ _ _ _, },
  { exact @measurable.const_smul _ m _ _ _ _ _ _ _ (@Lp.measurable _ _ m _ _ _ _ _ _ _) c, },
  refine (Lp_meas_to_Lp_trim_ae_eq hm _).trans _,
  refine (Lp.coe_fn_smul c _).trans _,
  refine (Lp_meas_to_Lp_trim_ae_eq hm f).mono (λ x hx, _),
  rw [pi.smul_apply, pi.smul_apply, hx, Lp_meas_coe],
  refl,
end

/-- `Lp_meas_to_Lp_trim` preserves the norm. -/
lemma Lp_meas_to_Lp_trim_norm_map [hp : fact (1 ≤ p)] (hm : m ≤ m0) (f : Lp_meas F 𝕜 m p μ) :
  ∥Lp_meas_to_Lp_trim F 𝕜 p μ hm f∥ = ∥f∥ :=
begin
  rw [norm_def, snorm_trim hm (@Lp.measurable _ _ m _ _ _ _ _ _ _)],
  swap, { apply_instance, },
  rw [snorm_congr_ae (Lp_meas_to_Lp_trim_ae_eq hm _), Lp_meas_coe, ← norm_def],
  congr,
end

variables (F 𝕜 p μ)
/-- A linear isometry equivalence between `Lp_meas` and `Lp F p (μ.trim hm)`. -/
def Lp_meas_to_Lp_trim_lie [hp : fact (1 ≤ p)] (hm : m ≤ m0) :
  Lp_meas F 𝕜 m p μ ≃ₗᵢ[𝕜] @Lp α F m _ _ _ _ p (μ.trim hm) :=
{ to_fun    := Lp_meas_to_Lp_trim F 𝕜 p μ hm,
  map_add'  := Lp_meas_to_Lp_trim_add hm,
  map_smul' := Lp_meas_to_Lp_trim_smul hm,
  inv_fun   := Lp_trim_to_Lp_meas F 𝕜 p μ hm,
  left_inv  := Lp_meas_to_Lp_trim_left_inv hm,
  right_inv := Lp_meas_to_Lp_trim_right_inv hm,
  norm_map' := Lp_meas_to_Lp_trim_norm_map hm, }
variables {F 𝕜 p μ}

instance [hm : fact (m ≤ m0)] [complete_space F] [hp : fact (1 ≤ p)] :
  complete_space (Lp_meas F 𝕜 m p μ) :=
by { rw (Lp_meas_to_Lp_trim_lie F 𝕜 p μ hm.elim).to_isometric.complete_space_iff, apply_instance, }

end complete_subspace

end Lp_meas

section condexp_L2_clm

local attribute [instance] fact_one_le_two_ennreal

variables [borel_space 𝕜] {m m0 : measurable_space α} {μ : measure α} {s t : set α}

lemma integrable_on_Lp_of_measure_ne_top (f : Lp G p μ) (hp : 1 ≤ p) (hμs : μ s ≠ ∞) :
  integrable_on f s μ :=
begin
  refine mem_ℒp_one_iff_integrable.mp _,
  have hμ_restrict_univ : (μ.restrict s) set.univ < ∞,
    by simpa only [set.univ_inter, measurable_set.univ, measure.restrict_apply, lt_top_iff_ne_top],
  haveI hμ_finite : finite_measure (μ.restrict s) := ⟨hμ_restrict_univ⟩,
  exact ((Lp.mem_ℒp _).restrict s).mem_ℒp_of_exponent_le hp,
end

variables (𝕜)
/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2_clm [complete_space E] (hm : m ≤ m0) : (α →₂[μ] E) →L[𝕜] (Lp_meas E 𝕜 m 2 μ) :=
@orthogonal_projection 𝕜 (α →₂[μ] E) _ _ (Lp_meas E 𝕜 m 2 μ)
  (by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact infer_instance, })
variables {𝕜}

lemma integrable_on_condexp_L2_of_measure_ne_top [complete_space E] (hm : m ≤ m0) (hμs : μ s ≠ ∞)
  (f : Lp E 2 μ) :
  integrable_on (condexp_L2_clm 𝕜 hm f) s μ :=
integrable_on_Lp_of_measure_ne_top ((condexp_L2_clm 𝕜 hm f) : Lp E 2 μ)
  fact_one_le_two_ennreal.elim hμs

lemma integrable_condexp_L2_of_finite_measure [complete_space E] (hm : m ≤ m0) [finite_measure μ]
  {f : Lp E 2 μ} :
  integrable (condexp_L2_clm 𝕜 hm f) μ :=
integrable_on_univ.mp $ integrable_on_condexp_L2_of_measure_ne_top hm (measure_ne_top _ _) f

lemma norm_condexp_L2_le_one [complete_space E] (hm : m ≤ m0) :
  ∥@condexp_L2_clm α E 𝕜 _ _ _ _ _ _ _ _ _ μ _ hm∥ ≤ 1 :=
by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact orthogonal_projection_norm_le _, }

lemma norm_condexp_L2_apply_le [complete_space E] (hm : m ≤ m0) (f : Lp E 2 μ) :
  ∥condexp_L2_clm 𝕜 hm f∥ ≤ ∥f∥ :=
begin
  refine ((@condexp_L2_clm α E 𝕜 _ _ _ _ _ _ _ _ _ μ _ hm).le_op_norm _).trans _,
  nth_rewrite 1 ← one_mul (∥f∥),
  exact mul_le_mul (norm_condexp_L2_le_one hm) le_rfl (norm_nonneg _) zero_le_one,
end

lemma snorm_condexp_L2_le [complete_space E] (hm : m ≤ m0) (f : Lp E 2 μ) :
  snorm (condexp_L2_clm 𝕜 hm f) 2 μ ≤ snorm f 2 μ :=
begin
  rw [Lp_meas_coe, ← ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _), ← norm_def,
    ← norm_def, submodule.norm_coe],
  exact norm_condexp_L2_apply_le hm f,
end

lemma norm_condexp_L2_coe_le [complete_space E] (hm : m ≤ m0) (f : Lp E 2 μ) :
  ∥(condexp_L2_clm 𝕜 hm f : Lp E 2 μ)∥ ≤ ∥f∥ :=
begin
  rw [norm_def, norm_def, ← Lp_meas_coe],
  refine (ennreal.to_real_le_to_real _ (Lp.snorm_ne_top _)).mpr (snorm_condexp_L2_le hm f),
  exact Lp.snorm_ne_top _,
end

lemma inner_condexp_L2_left_eq_right [complete_space E] (hm : m ≤ m0) {f g : Lp E 2 μ} :
  @inner 𝕜 _ _ (condexp_L2_clm 𝕜 hm f : Lp E 2 μ) g
    = inner f (condexp_L2_clm 𝕜 hm g : Lp E 2 μ) :=
by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact inner_orthogonal_projection_left_eq_right _ f g, }

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local notation `⟪`x`, `y`⟫'` := @inner 𝕜 E' _ x y

lemma inner_indicator_const_Lp_eq_set_integral_inner (f : Lp E 2 μ) {s : set α}
  (hs : measurable_set s) (c : E) (hμs : μ s ≠ ∞) :
  inner (indicator_const_Lp 2 hs hμs c) f = ∫ x in s, ⟪c, f x⟫ ∂μ :=
begin
  simp_rw L2.inner_def,
  rw ← integral_add_compl hs (L2.integrable_inner _ f),
  have h_left : ∫ x in s, ⟪(indicator_const_Lp 2 hs hμs c) x, f x⟫ ∂μ = ∫ x in s, ⟪c, f x⟫ ∂μ,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∈ s → ⟪indicator_const_Lp 2 hs hμs c x, f x⟫ = ⟪c, f x⟫,
      from set_integral_congr_ae hs h_ae_eq,
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∈ s → (indicator_const_Lp 2 hs hμs c x) = c,
      from indicator_const_Lp_coe_fn_mem,
    refine h_indicator.mono (λ x hx hxs, _),
    congr,
    exact hx hxs, },
  have h_right : ∫ x in sᶜ, ⟪(indicator_const_Lp 2 hs hμs c) x, f x⟫ ∂μ = 0,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∉ s → ⟪indicator_const_Lp 2 hs hμs c x, f x⟫ = 0,
    { simp_rw ← set.mem_compl_iff at h_ae_eq,
      suffices h_int_zero : ∫ x in sᶜ, inner (indicator_const_Lp 2 hs hμs c x) (f x) ∂μ
        = ∫ x in sᶜ, (0 : 𝕜) ∂μ,
      { rw h_int_zero,
        simp, },
      exact set_integral_congr_ae hs.compl h_ae_eq, },
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∉ s → (indicator_const_Lp 2 hs hμs c x) = 0,
      from indicator_const_Lp_coe_fn_nmem,
    refine h_indicator.mono (λ x hx hxs, _),
    rw hx hxs,
    exact inner_zero_left, },
  rw [h_left, h_right, add_zero],
end

lemma integral_zero_of_forall_integral_inner_zero [is_scalar_tower ℝ 𝕜 E'] (f : α → E')
  (hf : integrable f μ) (hf_int : ∀ (c : E'), ∫ x, ⟪c, f x⟫' ∂μ = 0) :
  ∫ x, f x ∂μ = 0 :=
by { specialize hf_int (∫ x, f x ∂μ), rwa [integral_inner hf, inner_self_eq_zero] at hf_int }

variables (𝕜)
lemma inner_indicator_const_Lp_eq_inner_set_integral [is_scalar_tower ℝ 𝕜 E']
  (hs : measurable_set s) (hμs : μ s ≠ ∞) (c : E') (f : Lp E' 2 μ) :
  inner (indicator_const_Lp 2 hs hμs c) f = ⟪c, ∫ x in s, f x ∂μ⟫' :=
by rw [← integral_inner (integrable_on_Lp_of_measure_ne_top f fact_one_le_two_ennreal.elim hμs),
    inner_indicator_const_Lp_eq_set_integral_inner]
variables {𝕜}

lemma inner_indicator_const_Lp_one (hm : m ≤ m0)
  (hs : @measurable_set α m s) (hμs : μ s ≠ ∞) (f : Lp ℝ 2 μ) :
  inner (indicator_const_Lp 2 (hm s hs) hμs (1 : ℝ)) f = ∫ x in s, f x ∂μ :=
begin
  rw inner_indicator_const_Lp_eq_inner_set_integral ℝ (hm s hs) hμs (1 : ℝ) f,
  simp only [is_R_or_C.inner_apply, is_R_or_C.conj_to_real, one_mul],
end

lemma condexp_L2_indicator_of_measurable [complete_space E] (hm : m ≤ m0)
  (hs : @measurable_set _ m s) (hμs : μ s ≠ ∞) (c : E) :
  (condexp_L2_clm 𝕜 hm (indicator_const_Lp 2 (hm s hs) hμs c) : Lp E 2 μ)
    = indicator_const_Lp 2 (hm s hs) hμs c :=
begin
  rw condexp_L2_clm,
  haveI : fact(m ≤ m0) := ⟨hm⟩,
  have h_mem : indicator_const_Lp 2 (hm s hs) hμs c ∈ Lp_meas E 𝕜 m 2 μ,
    from mem_Lp_meas_indicator_const_Lp hm hs,
  let ind := (⟨indicator_const_Lp 2 (hm s hs) hμs c, h_mem⟩ : Lp_meas E 𝕜 m 2 μ),
  have h_coe_ind : (ind : Lp E 2 μ) = indicator_const_Lp 2 (hm s hs) hμs c, by refl,
  have h_orth_mem := orthogonal_projection_mem_subspace_eq_self ind,
  rw [← h_coe_ind, h_orth_mem],
end

lemma inner_condexp_L2_eq_inner_fun [complete_space E] (hm : m ≤ m0) (f g : Lp E 2 μ)
  (hg : ae_measurable' m g μ) :
  @inner 𝕜 _ _ (↑(condexp_L2_clm 𝕜 hm f) : Lp E 2 μ) g = inner f g :=
begin
  symmetry,
  rw [← sub_eq_zero, ← inner_sub_left, condexp_L2_clm],
  simp only [mem_Lp_meas_iff_ae_measurable'.mpr hg, orthogonal_projection_inner_eq_zero],
end

end condexp_L2_clm

end measure_theory
