/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.charted_space
import analysis.normed_space.inner_product

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put a smooth manifold structure on the sphere.

-/

noncomputable theory

open metric

section to_inner_prod
/-! Lemmas for `analysis.normed_space.inner_product_space`. -/

variables (𝕜 : Type*) [is_R_or_C 𝕜]
variables {E : Type*} [inner_product_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]

def orthogonal_projection_of_complete' {K : submodule 𝕜 E} (h : is_complete (K : set E)) :
  E →ₗ[𝕜] K :=
(orthogonal_projection (K : submodule 𝕜 E)).cod_restrict K (orthogonal_projection_mem h)

lemma orthogonal_projection_is_complete [complete_space E] (K : submodule 𝕜 E) :
  is_complete (K.orthogonal : set E) :=
begin
  sorry
end

include 𝕜

lemma inner_product_space.mem_sphere (v w : E) (r : ℝ) : w ∈ sphere v r ↔ ∥w - v∥ = r :=
by simp [dist_eq_norm]

lemma inner_product_space.mem_sphere_zero {w : E} {r : ℝ} : w ∈ sphere (0:E) r ↔ ∥w∥ = r :=
by simp [dist_eq_norm]

end to_inner_prod


section
/-! Lemmas for `algebra.ordered_field` and similar. -/

variables {α : Type*} [linear_ordered_field α]

/- this lemma would work for `ordered_integral_domain`, if that typeclass existed -/
@[simp] lemma eq_of_pow_two_eq_pow_two {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b :=
begin
  split,
  { intros h,
    refine (eq_or_eq_neg_of_pow_two_eq_pow_two _ _ h).elim id _,
    intros h',
    linarith },
  { rintros rfl,
    simp },
end

lemma foo (a : α) : (a ^ 2 + 1)⁻¹ * (a ^ 2 - 1) < 1 :=
begin
  refine (inv_mul_lt_iff' _).mpr _,
  { nlinarith },
  linarith
end

lemma abs_sq_eq (a : ℝ) : (abs a) ^ 2 = a ^ 2 :=
begin
  by_cases h : 0 ≤ a,
  { simp [abs_of_nonneg h] },
  { simp [abs_of_neg (not_le.mp h)] }
end

end

variables {E : Type*} [inner_product_space ℝ E] [complete_space E]
variables (v : E)

open inner_product_space submodule

lemma span_complete : is_complete (((span ℝ {v}) : submodule ℝ E) : set E) :=
(span ℝ {v}).complete_of_finite_dimensional

def orthog : submodule ℝ E := (span ℝ {v}).orthogonal

lemma prod_zero_left {w : E} (hw : w ∈ orthog v) : ⟪w, v⟫_ℝ = 0 :=
inner_left_of_mem_orthogonal (mem_span_singleton_self v) hw

lemma prod_zero_right {w : E} (hw : w ∈ orthog v) : ⟪v, w⟫_ℝ = 0 :=
inner_right_of_mem_orthogonal (mem_span_singleton_self v) hw

def proj : E →ₗ[ℝ] (span ℝ {v} : submodule ℝ E) :=
orthogonal_projection_of_complete' ℝ (span_complete v)

def projR : E →L[ℝ] ℝ :=
(is_bounded_bilinear_map_inner.is_bounded_linear_map_right v).to_continuous_linear_map

def proj' : E →ₗ[ℝ] (orthog v) :=
orthogonal_projection_of_complete' ℝ (orthogonal_projection_is_complete ℝ (span ℝ {v}))

def proj'' : E →L[ℝ] (orthog v) :=
linear_map.mk_continuous
(proj' v)
1
sorry

def in_sphere {v} (hv : ∥v∥ = 1) : sphere (0:E) 1 :=
⟨v, (inner_product_space.mem_sphere_zero ℝ).mpr hv⟩

lemma sphere_inter_hyperplane {v : E} (hv : ∥v∥ = 1) {w : sphere (0:E) 1} (hw : projR v w = 1) :
  w = in_sphere hv :=
begin
  suffices : ↑w = v,
  { ext,
    exact this },
  sorry
end

lemma sphere_inter_hyperplane'  {v : E} (hv : ∥v∥ = 1) :
  ({(in_sphere hv)}ᶜ : set (sphere (0:E) 1)) ⊆ coe ⁻¹' {w : E | projR v w ≠ 1} :=
begin
  intros w,
  simp,
  contrapose!,
  exact sphere_inter_hyperplane hv
end

/-- Stereographic projection, forward direction. This is a map from an inner product space `E` to
the orthogonal complement of an element `v` of `E`. It is smooth away from the affine hyperplane
through `v` parallel to the orthogonal complement.  It restricts on the sphere to the stereographic
projection. -/
def stereo_to_fun (w : E) : orthog v := (2 / (1 - projR v w)) • proj'' v w

lemma stereo_to_fun_continuous_on : continuous_on (stereo_to_fun v) {w : E | projR v w ≠ 1} :=
begin
  refine continuous_on.smul _ _,
  { refine continuous_const.continuous_on.div _ _,
    { exact continuous.continuous_on (continuous_const.sub (projR v).continuous) },
    intros x,
    contrapose!,
    intros h,
    simp,
    linarith },
  { exact (proj'' v).continuous.continuous_on }
end

def stereo_inv_fun_aux (w : E) : E := (∥w∥ ^ 2 + 1)⁻¹ • ((2:ℝ) • w + (∥w∥ ^ 2 - 1) • v)

variables {v}

lemma stereo_inv_fun_aux_mem (hv : ∥v∥ = 1) {w : E} (hw : w ∈ orthog v) :
  stereo_inv_fun_aux v w ∈ (sphere (0:E) 1) :=
begin
  have h₁ : 0 ≤ ∥w∥ ^ 2 + 1 := by nlinarith,
  suffices : ∥stereo_inv_fun_aux v w∥ = 1,
  { rwa inner_product_space.mem_sphere_zero },
  suffices : ∥(2:ℝ) • w + (∥w∥ ^ 2 - 1) • v∥ = ∥w∥ ^ 2 + 1,
  { rw stereo_inv_fun_aux,
    rw norm_smul,
    rw real.norm_eq_abs,
    rw abs_inv,
    rw this,
    have h₂ : ∥w∥ ^ 2 + 1 ≠ 0 := ne_of_gt (by nlinarith),
    rw abs_of_nonneg h₁,
    field_simp [h₂] },
  suffices : ∥(2:ℝ) • w + (∥w∥ ^ 2 - 1) • v∥ ^ 2 = (∥w∥ ^ 2 + 1) ^ 2,
  { have h₃ : 0 ≤ ∥stereo_inv_fun_aux v w∥ := norm_nonneg _,
    simpa [h₁, h₃, -one_pow] using this },
  rw norm_add_pow_two_real,
  simp [norm_smul],
  rw inner_smul_left,
  rw inner_smul_right,
  rw prod_zero_left _ hw,
  simp,
  ring,
  rw real.norm_eq_abs,
  rw abs_sq_eq,
  rw hv,
  ring,
end

/-- Stereographic projection, reverse direction.  This is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. -/
def stereo_inv_fun (hv : ∥v∥ = 1) (w : orthog v) : sphere (0:E) 1 :=
⟨stereo_inv_fun_aux v (w:E), stereo_inv_fun_aux_mem hv w.2⟩

@[simp] lemma stereo_inv_fun_apply (hv : ∥v∥ = 1) (w : orthog v) :
  (stereo_inv_fun hv w : E) = (∥w∥ ^ 2 + 1)⁻¹ • ((2:ℝ) • w + (∥w∥ ^ 2 - 1) • v) :=
rfl

lemma mem_north_pole_compl (hv : ∥v∥ = 1) (w : orthog v) :
  stereo_inv_fun hv w ∈ ({in_sphere hv} : set (sphere (0:E) 1))ᶜ :=
begin
  suffices : (stereo_inv_fun hv w : E) ≠ v,
  { simp [in_sphere hv],
    revert this,
    contrapose!,
    intros h,
    rw h,
    refl },
  have hv' : ⟪v, v⟫_ℝ = 1,
  { simp [hv, real_inner_self_eq_norm_square] },
  suffices : ⟪v, stereo_inv_fun hv w⟫_ℝ < 1,
  { intros contra,
    rw contra at this,
    linarith },
  convert foo (∥(w : E)∥),
  have hwv : ⟪v, ↑w⟫_ℝ = 0 := prod_zero_right v w.2,
  rw stereo_inv_fun_apply,
  simp [inner_add_right, inner_smul_right, hv', hwv],
  refl,
end

lemma continuous_stereo_inv_fun (hv : ∥v∥ = 1) :
  continuous (stereo_inv_fun hv) :=
begin
  let c : sphere (0:E) 1 → E := coe,
  suffices : continuous (c ∘ (stereo_inv_fun hv)),
  { exact continuous_induced_rng this },
  have h₀ : continuous (λ w : E, ∥w∥ ^ 2) := (continuous_pow 2).comp continuous_norm,
  have h₁ : continuous (λ w : E, (∥w∥ ^ 2 + 1)⁻¹),
  { refine (h₀.add continuous_const).inv' _,
    intros w,
    refine ne_of_gt _,
    nlinarith },
  have h₂ : continuous (λ w, (2:ℝ) • w + (∥w∥ ^ 2 - 1) • v),
  { refine (continuous_const.smul continuous_id).add _,
    refine (h₀.sub continuous_const).smul continuous_const },
  convert (h₁.smul h₂).comp continuous_subtype_coe
end

/-- Stereographic projection from the unit sphere in `E`, centred at a unit vector `v` in `E`; this
is the version as a local homeomorphism. -/
def stereographic (hv : ∥v∥ = 1) : local_homeomorph (sphere (0:E) 1) (orthog v) :=
{ to_fun := (stereo_to_fun v) ∘ coe,
  inv_fun := stereo_inv_fun hv,
  source := {(in_sphere hv)}ᶜ,
  target := set.univ,
  map_source' := by simp,
  map_target' := λ w _, mem_north_pole_compl hv w,
  left_inv' := _,
  right_inv' := _,
  open_source := is_open_compl_singleton,
  open_target := is_open_univ,
  continuous_to_fun := (stereo_to_fun_continuous_on v).comp continuous_subtype_coe.continuous_on
    (sphere_inter_hyperplane' hv),
  continuous_inv_fun := (continuous_stereo_inv_fun hv).continuous_on }
