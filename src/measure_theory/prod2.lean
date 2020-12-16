/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.prod
/-!
# The product measure space

TODO:

finitary products

-/

noncomputable theory
open fintype set function equiv
open_locale big_operators classical

lemma pi_congr {ι} {α β : ι → Type*} (h : ∀ i, α i = β i) : (Π i, α i) = (Π i, β i) :=
by { cases (show α = β, from funext h), refl }


namespace set

section prod
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {s s₁ s₂ : set α} {t t₁ t₂ : set β}

lemma prod_subset_prod (hs : s ⊆ s₁) (ht : t ⊆ t₁) : s.prod t ⊆ s₁.prod t₁ :=
prod_subset_prod_iff.mpr $ or.inl ⟨hs, ht⟩

end prod

end set

namespace function

variables {ι : Type*} [decidable_eq ι] {α : ι → Type*} {s : set ι} {i : ι}

/-- Extending a function on `s` to `insert i s` -/
def extend_insert (f : Π (j : ι), j ∈ s → α j) (x : α i) (j : ι) (hj : j ∈ insert i s) : α j :=
if h : j = i then by { subst h, exact x } else f j (mem_of_mem_insert_of_ne hj h)

@[simp] lemma extend_insert_of_mem (f : Π (j : ι), j ∈ s → α j) (x : α i) {j : ι} (hj : j ∈ s)
  (hi : i ∉ s) : extend_insert f x j (mem_insert_of_mem _ hj) = f j hj :=
begin
  have : j ≠ i, { rintro rfl, exact hi hj },
  simp [extend_insert, this]
end

@[simp] lemma extend_insert_self (f : Π (j : ι), j ∈ s → α j) (x : α i) :
  extend_insert f x i (mem_insert i s) = x :=
by simp [extend_insert]


end function
open function

namespace finset
variables {α : Type*}

lemma mem_insert_coe {s : finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : set α) :=
by simp

end finset


namespace equiv
/-- The type of maps from `true` is equivalent to the codomain. -/
def true_arrow_equiv (α : Sort*) : (true → α) ≃ α :=
⟨λ f, f trivial, λ a u, a, λ f, by { ext ⟨⟩, refl }, λ u, rfl⟩

variables {ι : Type*} (α : ι → Type*)

/-- A pi-type over an empty type has a unique element. -/
def pi_unique_of_empty (α : ι → Type*) (e : ι → false) : unique (Π i : ι, α i) :=
⟨⟨λ x, false.elim (e x)⟩, λ f, funext (λ x, false.elim (e x))⟩

/-- A pi-type over the empty set has a unique element. -/
def unique_pi_mem_empty : unique (Π i ∈ (∅ : set ι), α i) :=
⟨⟨λ _, false.elim⟩, λ f, funext $ λ x, funext $ λ hx, false.elim hx⟩

/-- A pi-type over an empty type is equivalent to `punit`. Similar to `pempty_arrow_equiv_punit`. -/
def pi_equiv_punit_of_empty (α : ι → Type*) (e : ι → false) : (Π i : ι, α i) ≃ punit :=
@equiv_punit_of_unique _ (pi_unique_of_empty α e)

/-- A pi-type over the empty set is equivalent to `punit`. Similar to `pi_equiv_punit_of_empty`. -/
def pi_mem_empty_equiv : (Π i ∈ (∅ : set ι), α i) ≃ punit :=
@equiv_punit_of_unique _ (unique_pi_mem_empty α)

-- /- A pi-type over the empty `finset` is equivalent to `punit`.
--   Definitionally equal to `pi_mem_empty_equiv`. -/
-- def pi_mem_finset_empty_equiv : (Π i ∈ (∅ : finset ι), α i) ≃ punit :=
-- pi_mem_empty_equiv α

/-- A pi-type over the set `insert i s` is equivalent to a binary product. -/
def pi_mem_insert_equiv {s : set ι} {i : ι} (hi : i ∉ s) :
  (Π j ∈ (insert i s), α j) ≃ α i × (Π j ∈ s, α j) :=
{ to_fun := λ f, ⟨f i (set.mem_insert _ _), λ j hj, f j (mem_insert_of_mem _ hj)⟩,
  inv_fun := λ xg, extend_insert xg.2 xg.1,
  left_inv := begin
    intro f, ext j (rfl|hj),
    { apply extend_insert_self },
    { exact extend_insert_of_mem _ _ hj hi },
  end,
  right_inv := begin
    rintro ⟨x, g⟩, simp only [true_and, prod.mk.inj_iff, eq_self_iff_true, extend_insert_self],
    ext j hj, exact extend_insert_of_mem _ _ hj hi
  end }

/-- A pi-type over the `list` `i :: l` is a binary product. -/
def pi_mem_list_cons_equiv {l : list ι} {i : ι} (hx : i ∉ l) :
  (Π j ∈ i :: l, α j) ≃ α i × (Π j ∈ l, α j) :=
pi_mem_insert_equiv α hx

end equiv
open equiv


namespace list

section
variables {α : Type*}

lemma to_finset_surj_on : surj_on to_finset {l : list α | l.nodup} univ :=
begin
  rintro s -,
  induction s with t hl,
  induction t using quot.ind with l,
  refine ⟨l, hl, (to_finset_eq hl).symm⟩
end

end

end list

section
variables {ι : Type*} (α : ι → Type*) {i j : ι} {l : list ι} {f : Π i, α i}

/-- The product of a family of types over a list. -/
@[nolint has_inhabited_instance] def tprod (l : list ι) : Type* :=
l.foldr (λ i β, α i × β) punit

variable {α}

namespace tprod

open list

/-- Turning a function `f : Π i, α i` into an element of the iterated product `tprod α l`. -/
protected def mk : ∀ (l : list ι) (f : Π i, α i), tprod α l
| []        := λ f, punit.star
| (i :: is) := λ f, (f i, mk is f)

-- @[simp] lemma nil_mk : tprod.mk [] = const (Π i, α i) punit.star := rfl
@[simp] lemma fst_mk (i : ι) (l : list ι) (f : Π i, α i) : (tprod.mk (i::l) f).1 = f i := rfl

@[simp]
lemma snd_mk (i : ι) (l : list ι) (f : Π i, α i) : (tprod.mk (i::l) f).2 = tprod.mk l f := rfl

/-- Given an element of the iterated product `l.prod α`, take a projection into direction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in direction `i`. -/
protected noncomputable def elim : ∀ {l : list ι} (v : tprod α l) {i : ι} (hi : i ∈ l), α i
| (i :: is) v j hj :=
  if hji : j = i then by { subst hji, exact v.1 } else elim v.2 (hj.resolve_left hji)

@[simp] lemma elim_self (v : tprod α (i :: l)) : v.elim (l.mem_cons_self i) = v.1 :=
by simp [tprod.elim]

@[simp] lemma elim_of_ne (hj : j ∈ i :: l) (hji : j ≠ i) (v : tprod α (i :: l)) :
  v.elim hj = tprod.elim v.2 (hj.resolve_left hji) :=
by simp [tprod.elim, hji]

@[simp] lemma elim_of_mem (hl : (i :: l).nodup) (hj : j ∈ l) (v : tprod α (i :: l)) :
  v.elim (mem_cons_of_mem _ hj) = tprod.elim v.2 hj :=
by { apply elim_of_ne, rintro rfl, exact not_mem_of_nodup_cons hl hj }

lemma elim_mk : ∀ (l : list ι) (f : Π i, α i) {i : ι} (hi : i ∈ l),
  (tprod.mk l f).elim hi = f i
| (i :: is) f j hj := begin
      by_cases hji : j = i,
      { subst hji, simp },
      { rw [elim_of_ne _ hji, snd_mk, elim_mk] }
  end

@[ext] lemma ext : ∀ {l : list ι} (hl : l.nodup) {v w : tprod α l}
  (hvw : ∀ i (hi : i ∈ l), v.elim hi = w.elim hi), v = w
| []        hl v w hvw := punit.ext
| (i :: is) hl v w hvw := begin
    ext, rw [← elim_self v, hvw, elim_self],
    refine ext (nodup_cons.mp hl).2 (λ j hj, _),
    rw [← elim_of_mem hl, hvw, elim_of_mem hl]
  end

/-- A version of `tprod.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp] protected def elim' (h : ∀ i, i ∈ l) (v : tprod α l) (i : ι) : α i :=
v.elim (h i)

lemma mk_elim (hnd : l.nodup) (h : ∀ i, i ∈ l) (v : tprod α l) : tprod.mk l (v.elim' h) = v :=
tprod.ext hnd (λ i hi, by simp [elim_mk])

/-- Pi-types are equivalent to iterated products. -/
def pi_equiv_tprod (hnd : l.nodup) (h : ∀ i, i ∈ l) : (Π i, α i) ≃ tprod α l :=
⟨tprod.mk l, tprod.elim' h, λ f, funext $ λ i, elim_mk l f (h i), mk_elim hnd h⟩

end tprod

namespace set

open list
/-- A product of sets in `tprod α l`. -/
@[simp] protected def tprod : ∀ (l : list ι) (t : Π i, set (α i)), set (tprod α l)
| []        t := univ
| (i :: is) t := (t i).prod (tprod is t)

lemma mk_preimage_tprod : ∀ (l : list ι) (t : Π i, set (α i)),
  tprod.mk l ⁻¹' set.tprod l t = {i | i ∈ l}.pi t
| []        t := by simp [set.tprod]
| (i :: l) t := begin
  ext f,
  have : f ∈ tprod.mk l ⁻¹' set.tprod l t ↔ f ∈ {x | x ∈ l}.pi t, { rw [mk_preimage_tprod l t] },
  change tprod.mk l f ∈ set.tprod l t ↔ ∀ (i : ι), i ∈ l → f i ∈ t i at this,
  /- `simp [set.tprod, tprod.mk, this]` can close this goal but is slow. -/
  rw [set.tprod, tprod.mk, mem_preimage, mem_pi, prod_mk_mem_set_prod_eq],
  simp_rw [mem_set_of_eq, mem_cons_iff],
  rw [forall_eq_or_imp, and.congr_right_iff],
  exact λ _, this
end

lemma elim_preimage_pi {l : list ι} (hnd : l.nodup) (h : ∀ i, i ∈ l) (t : Π i, set (α i)) :
  tprod.elim' h ⁻¹' pi univ t = set.tprod l t :=
begin
  have : { i | i ∈ l} = univ, { ext i, simp [h] },
  rw [← this, ← mk_preimage_tprod, preimage_preimage],
  convert preimage_id, simp [tprod.mk_elim hnd h, id_def]
end

end set

end
open set

instance : measurable_space punit := ⊤
instance measurable_space.pi_prop {δ : Prop} {π : δ → Type*} [m : Π a, measurable_space (π a)] :
  measurable_space (Π a, π a) :=
⨆ a, (m a).comap (λ b, b a)

section
variables {α δ : Type*} {π : δ → Type*} [measurable_space α] [∀ x, measurable_space (π x)]
lemma measurable.eval {a : δ} {g : α → Π a, π a}
  (hg : measurable g) : measurable (λ x, g x a) :=
(measurable_pi_apply a).comp hg

lemma measurable_pi_iff {g : α → Π a, π a} :
  measurable g ↔ ∀ a, measurable (λ x, g x a) :=
by simp_rw [measurable_iff_comap_le, measurable_space.pi, measurable_space.comap_supr,
    measurable_space.comap_comp, function.comp, supr_le_iff]


instance tprod.measurable_space : ∀ (l : list δ), measurable_space (tprod π l)
| []        := punit.measurable_space
| (i :: is) := @prod.measurable_space _ _ _ (tprod.measurable_space is)

lemma measurable_tprod_mk (l : list δ) : measurable (@tprod.mk δ π l) :=
begin
  induction l with i l ih,
  { exact measurable_const },
  { exact (measurable_pi_apply i).prod_mk ih }
end

lemma measurable_tprod_elim : ∀ {l : list δ} {i} (hi : i ∈ l),
  measurable (λ (v : tprod π l), v.elim hi)
| (i :: is) j hj := begin
  by_cases hji : j = i,
  { subst hji, simp [measurable_fst] },
  { rw [funext $ tprod.elim_of_ne _ hji],
    exact (measurable_tprod_elim (hj.resolve_left hji)).comp measurable_snd }
end

lemma measurable_tprod_elim' {l : list δ} (h : ∀ i, i ∈ l) : measurable (@tprod.elim' δ π l h) :=
measurable_pi_lambda _ (λ i, measurable_tprod_elim (h i))

lemma is_measurable_tprod (l : list δ) {s : ∀ i, set (π i)} (hs : ∀ i, is_measurable (s i)) :
  is_measurable (set.tprod l s) :=
by { induction l with i l ih, exact is_measurable.univ, exact (hs i).prod ih }


-- variables [decidable_eq δ] {s : set δ} {i : δ}
-- #print piecewise_preimage
-- lemma measurable.extend_insert (x : π i) :
--   measurable (λ f : Π (j : δ), j ∈ s → π j, extend_insert f x) :=
-- begin
--   intros t ht,

-- end


-- {s : set α} {_ : decidable_pred s} {f g : α → β}
--   (hs : is_measurable s) (hf : measurable f) (hg : measurable g) :
--   measurable (piecewise s f g) :=
-- begin
--   intros t ht,
--   simp only [piecewise_preimage],
--   exact (hs.inter $ hf ht).union (hs.compl.inter $ hg ht)
-- end
-- variables {ι : Type*} [decidable_eq ι] {α : ι → Type*} {s : set ι} {i : ι}

-- def extend_insert (f : Π (j : ι), j ∈ s → α j) (x : α i) (j : ι) (hj : j ∈ insert i s) : α j :=
-- if h : j = i then by { subst h, exact x } else f j (mem_of_mem_insert_of_ne hj h)


namespace measure_theory

namespace measure
open list
/-- A product of measures in `tprod α l`. -/
-- for some reason the equation compiler doesn't like this definition
protected def tprod (l : list δ) (μ : Π i, measure (π i)) : measure (tprod π l) :=
by { induction l with i l ih, exact dirac punit.star, exact (μ i).prod ih }

@[simp] lemma tprod_nil (μ : Π i, measure (π i)) :
  measure.tprod [] μ = dirac punit.star :=
rfl

@[simp] lemma tprod_cons (i : δ) (l : list δ) (μ : Π i, measure (π i)) :
  measure.tprod (i :: l) μ = (μ i).prod (measure.tprod l μ) :=
rfl

instance sigma_finite_tprod (l : list δ) (μ : Π i, measure (π i)) [∀ i, sigma_finite (μ i)] :
  sigma_finite (measure.tprod l μ) :=
begin
  induction l with i l ih,
  { rw [tprod_nil], apply_instance },
  { rw [tprod_cons], resetI, apply_instance }
end

lemma tprod_tprod (l : list δ) (μ : Π i, measure (π i)) [∀ i, sigma_finite (μ i)]
  {s : Π i, set (π i)} (hs : ∀ i, is_measurable (s i)) :
  measure.tprod l μ (set.tprod l s) = (l.map (λ i, (μ i) (s i))).prod :=
begin
  induction l with i l ih, { simp },
  simp_rw [tprod_cons, set.tprod, prod_prod (hs i) (is_measurable_tprod l hs), map_cons,
    prod_cons, ih]
end


end measure

end measure_theory

end

section

variables {α β: Type*} {δ : Prop} {π : δ → Type*} [measurable_space α] [measurable_space β]
  [∀ x, measurable_space (π x)]
lemma measurable_pi_prop_apply (a : δ) : measurable (λ f : Π a, π a, f a) :=
measurable.of_comap_le $ le_supr _ a

lemma measurable_pi_prop_iff {g : α → Π a, π a} :
  measurable g ↔ ∀ a, measurable (λ x, g x a) :=
begin
  simp_rw [measurable_iff_comap_le, measurable_space.pi_prop, measurable_space.comap_supr,
    measurable_space.comap_comp, function.comp, supr_le_iff],
  exact forall_congr (λ i, measurable_iff_comap_le.symm),
end

lemma measurable.eval_prop {a : δ} {g : α → Π a, π a}
  (hg : measurable g) : measurable (λ x, g x a) :=
(measurable_pi_prop_apply a).comp hg

lemma measurable.eval_prop' {a : δ} {g : α → δ → β}
  (hg : measurable g) : measurable (λ x, g x a) :=
hg.eval_prop

lemma measurable_pi_lambda_prop (f : α → Π a, π a) (hf : ∀ a, measurable (λ c, f c a)) :
  measurable f :=
measurable.of_le_map $ supr_le $ assume a, measurable_space.comap_le_iff_le_map.2 (hf a)


end
namespace measurable_equiv

variables {α ι : Type*} [measurable_space α] (π π' : ι → Type*) [∀ x, measurable_space (π x)]
  [∀ x, measurable_space (π' x)]

/-- If `α` is a singleton, then it is measurably equivalent to any `punit`. -/
def measurable_equiv_punit_of_unique [unique α] : α ≃ᵐ punit :=
{ to_equiv := equiv_punit_of_unique,
  measurable_to_fun := subsingleton.measurable,
  measurable_inv_fun := subsingleton.measurable }

/-- A pi-type over an empty type is measurably equivalent to `punit`. -/
def pi_of_empty (e : ι → false) : (Π i : ι, π i) ≃ᵐ punit :=
@measurable_equiv_punit_of_unique _ _ (pi_unique_of_empty π e)

/-- A pi-type over the empty set is measurably equivalent to `punit`. -/
def pi_mem_empty : (Π i ∈ (∅ : set ι), π i) ≃ᵐ punit :=
@measurable_equiv_punit_of_unique _ _ (unique_pi_mem_empty π)

-- /- A pi-type over the empty `finset` is measurably equivalent to `punit`. -/
-- def pi_mem_finset_empty : (Π i ∈ (∅ : finset ι), π i) ≃ᵐ punit :=
-- pi_mem_empty π

/-- A pi-type over the set `insert i s` is measurably equivalent to a binary product. -/
def pi_mem_insert {s : set ι} {i : ι} (hi : i ∉ s) :
  (Π j ∈ (insert i s), π j) ≃ᵐ π i × (Π j ∈ s, π j) :=
{ to_equiv := pi_mem_insert_equiv π hi,
  measurable_to_fun := begin
    simp_rw [pi_mem_insert_equiv, _root_.measurable_prod, measurable_pi_iff,
      measurable_pi_prop_iff],
    split,
    { exact (@measurable_pi_apply _ (λ j, j ∈ insert i s → π j) _ i).eval_prop },
    { intros j hj, exact (@measurable_pi_apply _ (λ j, j ∈ insert i s → π j) _ j).eval_prop },
  end,
  measurable_inv_fun := begin
    simp_rw [pi_mem_insert_equiv, measurable_pi_iff, measurable_pi_prop_iff],
    intros j hj, rcases hj with rfl|hj,
    { simp [extend_insert, measurable_fst] },
    { have : j ≠ i, { rintro rfl, exact hi hj },
      simp only [extend_insert, this, dif_neg, not_false_iff],
      exact measurable.eval_prop (@measurable.eval _ _ (λ j, j ∈ s → π j) _ _ _ _ measurable_snd) }
  end }

/-- A pi-type over the `list` `i :: l` is a binary product. -/
def pi_mem_list_cons {l : list ι} {i : ι} (hx : i ∉ l) :
  (Π j ∈ i :: l, π j) ≃ᵐ π i × (Π j ∈ l, π j) :=
pi_mem_insert π hx

variables {π π'}
/-- A family of measurable equivalences `Π a, β₁ a ≃ᵐ β₂ a` generates a measurable equivalence
  between  `Π a, β₁ a` and `Π a, β₂ a`. -/
def Pi_congr_right (e : Π a, π a ≃ᵐ π' a) : (Π a, π a) ≃ᵐ (Π a, π' a) :=
{ to_equiv := Pi_congr_right (λ a, (e a).to_equiv),
  measurable_to_fun :=
    measurable_pi_lambda _ (λ i, (e i).measurable_to_fun.comp (measurable_pi_apply i)),
  measurable_inv_fun :=
    measurable_pi_lambda _ (λ i, (e i).measurable_inv_fun.comp (measurable_pi_apply i)) }

variable (α)
/-- The type of maps from `true` is measurably equivalent to the codomain. -/
def true_arrow : (true → α) ≃ᵐ α :=
{ to_equiv := true_arrow_equiv α,
  measurable_to_fun := measurable_pi_prop_apply _,
  measurable_inv_fun := measurable_pi_lambda_prop _ (λ x, measurable_id) }


/-- Pi-types are measurably equivalent to iterated products. -/
def pi_measurable_equiv_tprod {l : list ι} (hnd : l.nodup) (h : ∀ i, i ∈ l)
  (v : tprod π l) :
  (Π i, π i) ≃ᵐ tprod π l :=
{ to_equiv := tprod.pi_equiv_tprod hnd h,
  measurable_to_fun := measurable_tprod_mk l,
  measurable_inv_fun := measurable_tprod_elim' h }

end measurable_equiv


-- /-- A pi-type over a `list` is equivalent to an iterated product. -/
-- def pi_list_equiv_tprod {l : list ι} (h : l.nodup) : (Π i ∈ l, α i) ≃ tprod α l :=
-- begin
--   induction l with i l ih,
--   { exact pi_mem_empty_equiv α },
--   { rw [nodup_cons] at h,
--     exact (pi_mem_list_cons_equiv α h.1).trans ((equiv.refl _).prod_congr (ih h.2)) }
-- end

-- /-- A pi-type over a `fintype` is equivalent to an iterated product. -/
-- lemma exists_pi_fintype_equiv_tprod [fintype ι] :
--   ∃ l : list ι, nodup l ∧ nonempty ((Π i, α i) ≃ tprod α l) :=
-- begin
--   obtain ⟨l, lnd, hl⟩ := fintype.exists_univ_list ι,
--   refine ⟨l, lnd, ⟨_⟩⟩,
--   refine (equiv.symm _).trans (pi_list_equiv_tprod _ lnd),
--   refine Pi_congr_right _, intro i,
--   refine (arrow_congr (prop_equiv_punit $ hl i) (equiv.refl _)).trans _,
--   exact punit_arrow_equiv _
-- end



-- def pi_list_measurable_equiv_tprod [∀ i, measurable_space (α i)]
--   {l : list ι} (h : l.nodup) : (Π i ∈ l, α i) ≃ᵐ tprod α l :=
-- begin
--   induction l with i l ih,
--   { exact measurable_equiv.pi_mem_empty α },
--   { rw [nodup_cons] at h,
--     refine (measurable_equiv.pi_mem_list_cons α h.1).trans _,
--     exact (measurable_equiv.refl _).prod_congr (ih h.2) }
-- end

-- lemma exists_pi_fintype_measurable_equiv_tprod [fintype ι] [∀ i, measurable_space (α i)] :
--   ∃ l : list ι, l.nodup ∧ nonempty ((Π i, α i) ≃ᵐ tprod α l) :=
-- begin
--   obtain ⟨l, lnd, hl⟩ := fintype.exists_univ_list ι,
--   refine ⟨l, lnd, ⟨_⟩⟩,
--   refine measurable_equiv.trans _ (pi_list_measurable_equiv_tprod _ lnd),
--   refine measurable_equiv.Pi_congr_right _, intro i, rw [eq_true_intro (hl i)],
--   exact (measurable_equiv.true_arrow (α i)).symm
-- end

open measure_theory


section

variables {α β : Type*} [measurable_space α]

lemma is_measurable.Union_fintype [fintype β] {f : β → set α} (h : ∀ b, is_measurable (f b)) :
  is_measurable (⋃ b, f b) :=
begin
  have := encodable.trunc_encodable_of_fintype β,
  induction this using trunc.rec_on_subsingleton,
  exactI is_measurable.Union h
end

lemma is_measurable.Inter_fintype [fintype β] {f : β → set α} (h : ∀ b, is_measurable (f b)) :
  is_measurable (⋂ b, f b) :=
is_measurable.compl_iff.1 $
  by { rw compl_Inter, exact is_measurable.Union_fintype (λ b, (h b).compl) }

end

section measurable_pi
variables {δ : Type*} {π : δ → Type*} [Π a, measurable_space (π a)]
#print countable

lemma is_measurable.pi {s : set δ} {t : Π i : δ, set (π i)} (hs : countable s)
  (ht : ∀ i ∈ s, is_measurable (t i)) : is_measurable (s.pi t) :=
is_measurable_pi hs ht

lemma is_measurable.pi_fintype [fintype δ] {s : set δ} {t : Π i, set (π i)}
  (ht : ∀ i ∈ s, is_measurable (t i)) : is_measurable (pi s t) :=
begin
  have := encodable.trunc_encodable_of_fintype δ,
  induction this using trunc.rec_on_subsingleton,
  exactI is_measurable.pi (countable_encodable _) ht
end

/-- The function `update f a : π a → Π a, π a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
lemma measurable_update (f : Π (a : δ), π a) {a : δ} : measurable (update f a) :=
begin
  apply measurable_pi_lambda,
  intro x, by_cases hx : x = a,
  { cases hx, convert measurable_id, ext, simp },
  simp_rw [update_noteq hx], apply measurable_const,
end

lemma is_measurable_pi_of_nonempty [encodable δ] {t : Π i, set (π i)} (h : (pi univ t).nonempty) :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) :=
begin
  rcases h with ⟨f, hf⟩, refine ⟨λ hst i, _, is_measurable.pi⟩,
  convert measurable_update f hst, rw [update_preimage_univ_pi], exact λ j _, hf j (mem_univ j)
end

lemma is_measurable_pi' [encodable δ] {t : Π i, set (π i)} :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) ∨ ∃ i, t i = ∅ :=
begin
  cases (pi univ t).eq_empty_or_nonempty with h h,
  { have := univ_pi_eq_empty_iff.mp h, simp [h, univ_pi_eq_empty_iff.mp h] },
  { simp [←not_nonempty_iff_eq_empty, univ_pi_nonempty_iff.mp h, is_measurable_pi_of_nonempty h] }
end

lemma measurable_pi {γ} [measurable_space γ] {f : γ → Π i, π i} :
  measurable f ↔ ∀ x, measurable (λ c, f c x) :=
⟨λ hf x, (measurable_pi_apply _).comp hf, measurable_pi_lambda f⟩

end measurable_pi

namespace measure_theory

/- finitary products -/
namespace outer_measure

lemma trim_of_function {α} [measurable_space α] {m : set α → ennreal} (m_empty : m ∅ = 0)
  (h : ∀ s, ¬ is_measurable s → m s = 0) :
  (outer_measure.of_function m m_empty).trim = outer_measure.of_function m m_empty :=
sorry

end outer_measure
open outer_measure measure

/-
 FALSE IN GENERAL: `is_measurable s -> is_measurable (prod.fst '' s)`. (see Analytic sets)
 prod_prod works sometimes for nonmeasurable sets (e.g. of reals: https://math.stackexchange.com/questions/1180475/product-of-outer-measure-equals-outer-measure-of-product)
-/
namespace measure

variables {α β : Type*} [measurable_space α] [measurable_space β]
variables {μ : measure α} {ν : measure β}

/-- A variant of `measure_eq_infi` which has a single `infi`. This is useful when applying a
  lemma next that only works for non-empty infima. -/
lemma measure_eq_infi' (μ : measure α) (s : set α) :
  μ s = ⨅ t : { t // s ⊆ t ∧ is_measurable t}, μ t :=
by simp_rw [infi_subtype, infi_and, subtype.coe_mk, ← measure_eq_infi]

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
lemma nonempty_measurable_superset (s : set α) : nonempty { t // s ⊆ t ∧ is_measurable t} :=
⟨⟨univ, subset_univ s, is_measurable.univ⟩⟩

local attribute [instance] nonempty_measurable_superset

lemma prod_prod_le [sigma_finite ν] {s : set α} {t : set β} :
  μ.prod ν (s.prod t) ≤ μ s * ν t :=
begin
  by_cases hs0 : μ s = 0,
  { rcases (exists_is_measurable_superset_of_measure_eq_zero hs0) with ⟨s', hs', h2s', h3s'⟩,
    convert measure_mono (prod_subset_prod hs' (subset_univ _)),
    simp_rw [hs0, prod_prod h2s' is_measurable.univ, h3s', zero_mul] },
  by_cases hti : ν t = ⊤,
  { convert le_top, simp_rw [hti, ennreal.mul_top, hs0, if_false] },
  rw [measure_eq_infi' μ],
  simp_rw [ennreal.infi_mul hti], refine le_infi _, rintro ⟨s', h1s', h2s'⟩,
  rw [subtype.coe_mk],
  by_cases ht0 : ν t = 0,
  { rcases (exists_is_measurable_superset_of_measure_eq_zero ht0) with ⟨t', ht', h2t', h3t'⟩,
    convert measure_mono (prod_subset_prod (subset_univ _) ht'),
    simp_rw [ht0, prod_prod is_measurable.univ h2t', h3t', mul_zero] },
  by_cases hsi : μ s' = ⊤,
  { convert le_top, simp_rw [hsi, ennreal.top_mul, ht0, if_false] },
  rw [measure_eq_infi' ν],
  simp_rw [ennreal.mul_infi hsi], refine le_infi _, rintro ⟨t', h1t', h2t'⟩,
  convert measure_mono (prod_subset_prod h1s' h1t'),
  simp [prod_prod h2s' h2t'],
end

lemma prod_prod' [sigma_finite ν] {s : set α} {t : set β} :
  μ.prod ν (s.prod t) = μ s * ν t :=
begin
  apply le_antisymm,
  -- { rw [@measure_eq_infi _ _ μ], simp_rw [infi_and', infi_subtype'],
  --   rw [@ennreal.infi_mul _ _], refine le_infi _, rintro ⟨s', h1s', h2s'⟩,
  --   rw [@measure_eq_infi _ _ ν], simp_rw [infi_and', infi_subtype'],
  --   rw [@ennreal.mul_infi _ _], refine le_infi _, rintro ⟨t', h1t', h2t'⟩,
  --   convert measure_mono (prod_subset_prod_iff.2 (or.inl ⟨h1s', h1t'⟩)),
  --   simp [prod_prod h2s' h2t'], repeat {sorry} },
  sorry,
  { rw [@measure_eq_infi _ _ (μ.prod ν)], refine le_binfi (λ st hst, le_infi (λ h2st, _)),

    sorry }
end

end measure



section measure_pi

variables {ι : Type*} [fintype ι] {α : ι → Type*} {m : Π i, outer_measure (α i)}

/-- An upper bound for the measure in a product space.
  It is defined to be the product of the measures of all its projections.
  For boxes it should be equal to the correct measure. -/
def pi_premeasure (m : Π i, outer_measure (α i)) (s : set (Π i, α i)) : ennreal :=
∏ i, m i (eval i '' s)

@[simp] lemma pi_premeasure_def {s : set (Π i, α i)} :
  pi_premeasure m s = ∏ i, m i (eval i '' s) := rfl

lemma pi_premeasure_pi {s : Π i, set (α i)} (hs : (pi univ s).nonempty) :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
by simp [hs]

lemma pi_premeasure_pi' [nonempty ι] {s : Π i, set (α i)} :
  pi_premeasure m (pi univ s) = ∏ i, m i (s i) :=
begin
  cases (pi univ s).eq_empty_or_nonempty with h h,
  { rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩,
    have : ∃ i, m i (s i) = 0 := ⟨i, by simp [hi]⟩,
    simpa [h, finset.card_univ, zero_pow (fintype.card_pos_iff.mpr _inst_2),
      @eq_comm _ (0 : ennreal), finset.prod_eq_zero_iff] },
  { simp [h] }
end

lemma pi_premeasure_pi_mono {s t : set (Π i, α i)} (h : s ⊆ t) :
  pi_premeasure m s ≤ pi_premeasure m t :=
finset.prod_le_prod' (λ i _, (m i).mono' (image_subset _ h))

lemma pi_premeasure_pi_eval [nonempty ι] {s : set (Π i, α i)} :
  pi_premeasure m (pi univ (λ i, eval i '' s)) = pi_premeasure m s :=
by simp [pi_premeasure_pi']

namespace outer_measure
/-- `outer_measure.pi m` is the finite product of the outer measures `{m i | i : ι}`.
  It is defined to be the maximal outer measure `n` with the property that
  `n (pi univ s) ≤ ∏ i, m i (s i)`, where `pi univ s` is the product of the sets
  `{ s i | i : ι }`. -/
protected def pi (m : Π i, outer_measure (α i)) : outer_measure (Π i, α i) :=
bounded_by (pi_premeasure m)

lemma pi_pi_le (m : Π i, outer_measure (α i)) (s : Π i, set (α i)) :
  outer_measure.pi m (pi univ s) ≤ ∏ i, m i (s i) :=
by { cases (pi univ s).eq_empty_or_nonempty with h h, simp [h],
     exact (bounded_by_le _).trans_eq (pi_premeasure_pi h) }


lemma le_pi {m : Π i, outer_measure (α i)} {n : outer_measure (Π i, α i)} :
  n ≤ outer_measure.pi m ↔ ∀ (s : Π i, set (α i)), (pi univ s).nonempty →
    n (pi univ s) ≤ ∏ i, m i (s i) :=
begin
  rw [outer_measure.pi, le_bounded_by'], split,
  { intros h s hs, refine (h _ hs).trans_eq (pi_premeasure_pi hs) },
  { intros h s hs, refine le_trans (n.mono $ subset_pi_eval_image univ s) (h _ _),
    simp [univ_pi_nonempty_iff, hs] }
end

-- lemma pi_pi_false [encodable ι] (s : Π i, set (α i))
--   (h2s : (pi univ s).nonempty) : outer_measure.pi m (pi univ s) = ∏ i, m i (s i) :=
-- begin
--   simp_rw [← pi_premeasure_pi h2s],
--   refine le_antisymm (bounded_by_le _) _,
--   refine le_binfi _, dsimp only, intros t ht,
--   sorry
--   -- refine le_trans _ (ennreal.tsum_le_tsum $ λ i, _),
-- end
end outer_measure

namespace measure

variables [Π i, measurable_space (α i)] (μ : Π i, measure (α i))

protected lemma caratheodory {α} [measurable_space α] (μ : measure α) {s t : set α}
  (hs : is_measurable s) : μ (t ∩ s) + μ (t \ s) = μ t :=
(le_to_outer_measure_caratheodory μ s hs t).symm

lemma pi_caratheodory :
  measurable_space.pi ≤ (outer_measure.pi (λ i, (μ i).to_outer_measure)).caratheodory :=
begin
  refine supr_le _, intros i s hs,
  rw [measurable_space.comap] at hs, rcases hs with ⟨s, hs, rfl⟩,
  apply bounded_by_caratheodory, intro t,
  simp_rw [pi_premeasure_def],
  refine finset.prod_add_prod_le' (finset.mem_univ i) _ _ _,
  { simp [image_inter_preimage, image_diff_preimage, (μ i).caratheodory hs, le_refl] },
  { rintro j - hj, apply mono', apply image_subset, apply inter_subset_left },
  { rintro j - hj, apply mono', apply image_subset, apply diff_subset }
end

/-- `measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be the maximal product measure, i.e.
  the maximal measure `ν` with the property that `ν (pi univ s) ≤ ∏ i, μ i (s i)`,
  where `pi univ s` is the product of the sets `{ s i | i : ι }`.
  For sigma-finite measures we know that `ν (pi univ s) = ∏ i, μ i (s i)`. -/
protected def pi : measure (Π i, α i) :=
to_measure (outer_measure.pi (λ i, (μ i).to_outer_measure)) (pi_caratheodory μ)

-- @[simp] lemma to_outer_measure_pi :
--   (measure.pi μ).to_outer_measure = outer_measure.pi (λ i, (μ i).to_outer_measure) :=
-- by simp [measure.pi]

protected def pi2 [encodable ι] [∀ i, sigma_finite (μ i)] : measure (Π i, α i) :=
measure.map (tprod.elim' encodable.mem_sorted_univ) (measure.tprod (encodable.sorted_univ ι) μ)

lemma pi2_pi [encodable ι] [∀ i, sigma_finite (μ i)] {s : Π i, set (α i)}
  (hs : ∀ i, is_measurable (s i)) : measure.pi2 μ (pi univ s) = ∏ i, μ i (s i) :=
begin
  have hl := λ i : ι, encodable.mem_sorted_univ i,
  have hnd := @encodable.sorted_univ_nodup ι _ _,
  rw [measure.pi2, map_apply (measurable_tprod_elim' hl) (is_measurable.pi hs),
    elim_preimage_pi hnd, tprod_tprod _ μ hs, ← list.prod_to_finset _ hnd],
  congr' with i, simp [hl]
end

lemma exists_product_measure [encodable ι] [∀ i, sigma_finite (μ i)] :
  ∃ ν : measure (Π i, α i), ∀ (s : Π i, set (α i)), (∀ i, is_measurable (s i)) →
  ν (pi univ s) = ∏ i, μ i (s i) :=
begin
  let l := encodable.sorted_univ ι,
  have hl := λ i : ι, encodable.mem_sorted_univ i,
  have hnd := @encodable.sorted_univ_nodup ι _ _,
  refine ⟨measure.map (tprod.elim' hl) (measure.tprod l μ), _⟩,
  intros s hs,
  rw [map_apply (measurable_tprod_elim' hl) (is_measurable.pi hs), elim_preimage_pi hnd,
    tprod_tprod l μ hs, ← list.prod_to_finset _ hnd],
  congr' with i, simp [hl]
end

lemma pi_pi [fintype ι] [encodable ι] [∀ i, sigma_finite (μ i)] (s : Π i, set (α i))
  (h1s : ∀ i, is_measurable (s i))
  (h2s : (pi univ s).nonempty) : measure.pi μ (pi univ s) = ∏ i, μ i (s i) :=
begin
  refine le_antisymm _ _,
  { rw [measure.pi, to_measure_apply _ _ (is_measurable.pi h1s)], apply outer_measure.pi_pi_le },
  { rcases exists_product_measure μ with ⟨ν, hν⟩, rw [← hν s h1s],
    simp_rw [measure.pi, to_measure_apply _ _ (is_measurable.pi h1s), ← to_outer_measure_apply],
    suffices : ν.to_outer_measure ≤ outer_measure.pi (λ i, (μ i).to_outer_measure),
    { exact this _ },
    clear h1s h2s s,
    rw [outer_measure.le_pi], intros s hs,
    simp_rw [to_outer_measure_apply],
     },

  have : ν ≤ measure.pi (λ i, (μ i)),
  { intros s hs, sorry },

  -- simp_rw [← to_outer_measure_apply, ← pi_premeasure_pi h2s],
  -- refine le_antisymm (bounded_by_le _) _,
  -- refine le_binfi _, dsimp only, intros t ht,
end

end measure

end measure_pi

end measure_theory

open measure_theory measure_theory.outer_measure
