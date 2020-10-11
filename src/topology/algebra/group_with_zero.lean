import topology.algebra.monoid

open_locale topological_space
open filter

class topological_group_with_zero (G₀ : Type*) [group_with_zero G₀] [topological_space G₀] :=
(continuous_at_inv' : ∀ ⦃x : G₀⦄, x ≠ 0 → continuous_at has_inv.inv x)

variables {α G₀ : Type*} [group_with_zero G₀] [topological_space G₀]
  [topological_group_with_zero G₀]

export topological_group_with_zero (continuous_at_inv')

lemma tendsto_inv' {a : G₀}  (ha : a ≠ 0) : tendsto has_inv.inv (𝓝 a) (𝓝 a⁻¹) :=
continuous_at_inv' ha

lemma filter.tendsto.inv' {l : filter α} {f : α → G₀} {a : G₀} (hf : tendsto f l (𝓝 a))
  (ha : a ≠ 0) :
  tendsto (λ x, (f x)⁻¹) l (𝓝 a⁻¹) :=
(tendsto_inv' ha).comp hf

variables [topological_space α]

lemma continuous_within_at.inv' {f : α → G₀} {s a} (hf : continuous_within_at f s a)
  (ha : f a ≠ 0) :
  continuous_within_at (λ x, (f x)⁻¹) s a :=
hf.inv' ha

lemma continuous_at.inv' {f : α → G₀} {a} (hf : continuous_at f a) (ha : f a ≠ 0) :
  continuous_at (λ x, (f x)⁻¹) a :=
hf.inv' ha

lemma continuous.inv' {f : α → G₀} (hf : continuous f) (h0 : ∀ x, f x ≠ 0) :
  continuous (λ x, (f x)⁻¹) :=
continuous_iff_continuous_at.2 $ λ x, (hf.tendsto x).inv' (h0 x)
