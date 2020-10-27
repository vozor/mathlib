import measure_theory.measurable_space
import algebra.big_operators.pi
import data.real.basic

open_locale big_operators

variables {α : Type*} [measurable_space α]

/-!
### Binary operations: `(+)`, `(*)`, `(-)`, `(/)`
-/

/-- We say that a type `has_measurable_add` if `((+) c)` and `(+ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (+)` see `has_measurable_add₂`. -/
class has_measurable_add (M : Type*) [measurable_space M] [has_add M] : Prop :=
(measurable_const_add : ∀ c : M, measurable ((+) c))
(measurable_add_const : ∀ c : M, measurable (+ c))

/-- We say that a type `has_measurable_add` if `uncurry (+)` is a measurable functions.
For a typeclass assuming measurability of `((+) c)` and `(+ c)` see `has_measurable_add`. -/
class has_measurable_add₂ (M : Type*) [measurable_space M] [has_add M] : Prop :=
(measurable_add : measurable (λ p : M × M, p.1 + p.2))

export has_measurable_add₂ (measurable_add)

/-- We say that a type `has_measurable_mul` if `((*) c)` and `(* c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `has_measurable_mul₂`. -/
@[to_additive]
class has_measurable_mul (M : Type*) [measurable_space M] [has_mul M] : Prop :=
(measurable_const_mul : ∀ c : M, measurable ((*) c))
(measurable_mul_const : ∀ c : M, measurable (* c))

/-- We say that a type `has_measurable_mul` if `uncurry (*)` is a measurable functions.
For a typeclass assuming measurability of `((*) c)` and `(* c)` see `has_measurable_mul`. -/
@[to_additive has_measurable_add₂]
class has_measurable_mul₂ (M : Type*) [measurable_space M] [has_mul M] : Prop :=
(measurable_mul : measurable (λ p : M × M, p.1 * p.2))

export has_measurable_mul₂ (measurable_mul)

section mul

variables {M : Type*} [measurable_space M] [has_mul M]

@[to_additive]
lemma measurable.mul [has_measurable_mul₂ M] {f g : α → M} (hf : measurable f) (hg : measurable g) :
measurable (λ a, f a * g a) :=
measurable_mul.comp (hf.prod_mk hg)

@[priority 100, to_additive]
instance has_measurable_mul₂.to_has_measurable_mul [has_measurable_mul₂ M] :
has_measurable_mul M :=
⟨λ c, measurable_const.mul measurable_id, λ c, measurable_id.mul measurable_const⟩

@[to_additive]
lemma measurable.const_mul [has_measurable_mul M] {f : α → M} (hf : measurable f) (c : M) :
measurable (λ x, c * f x) :=
(has_measurable_mul.measurable_const_mul c).comp hf

@[to_additive]
lemma measurable.mul_const [has_measurable_mul M] {f : α → M} (hf : measurable f) (c : M) :
measurable (λ x, f x * c) :=
(has_measurable_mul.measurable_mul_const c).comp hf

end mul

/-- We say that a type `has_measurable_sub` if `(λ x, c - x)` and `(λ x, x - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `has_measurable_sub₂`. -/
class has_measurable_sub (G : Type*) [measurable_space G] [has_sub G] : Prop :=
(measurable_const_sub : ∀ c : G, measurable (λ x, c - x))
(measurable_sub_const : ∀ c : G, measurable (λ x, x - c))

/-- We say that a type `has_measurable_sub` if `uncurry (-)` is a measurable functions.
For a typeclass assuming measurability of `((-) c)` and `(- c)` see `has_measurable_sub`. -/
class has_measurable_sub₂ (G : Type*) [measurable_space G] [has_sub G] : Prop :=
(measurable_sub : measurable (λ p : G × G, p.1 - p.2))

export has_measurable_sub₂ (measurable_sub)

section sub

variables {G : Type*} [measurable_space G] [has_sub G]

lemma measurable.sub [has_measurable_sub₂ G] {f g : α → G} (hf : measurable f) (hg : measurable g) :
measurable (λ a, f a - g a) :=
measurable_sub.comp (hf.prod_mk hg)

@[priority 100]
instance has_measurable_sub₂.to_has_measurable_sub [has_measurable_sub₂ G] :
has_measurable_sub G :=
⟨λ c, measurable_const.sub measurable_id, λ c, measurable_id.sub measurable_const⟩

lemma measurable.const_sub [has_measurable_sub G] {f : α → G} (hf : measurable f) (c : G) :
measurable (λ x, c - f x) :=
(has_measurable_sub.measurable_const_sub c).comp hf

lemma measurable.sub_const [has_measurable_sub G] {f : α → G} (hf : measurable f) (c : G) :
measurable (λ x, f x - c) :=
(has_measurable_sub.measurable_sub_const c).comp hf

end sub

/-- We say that a type `has_measurable_div` if `((/) c)` and `(/ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (/)` see `has_measurable_div₂`. -/
class has_measurable_div (G₀: Type*) [measurable_space G₀] [has_div G₀] : Prop :=
(measurable_const_div : ∀ c : G₀, measurable ((/) c))
(measurable_div_const : ∀ c : G₀, measurable (/ c))

/-- We say that a type `has_measurable_div` if `uncurry (/)` is a measurable functions.
For a typeclass assuming measurability of `((/) c)` and `(/ c)` see `has_measurable_div`. -/
class has_measurable_div₂ (G₀: Type*) [measurable_space G₀] [has_div G₀] : Prop :=
(measurable_div : measurable (λ p : G₀× G₀, p.1 / p.2))

export has_measurable_div₂ (measurable_div)

section div

variables {G₀: Type*} [measurable_space G₀] [has_div G₀]

lemma measurable.div [has_measurable_div₂ G₀] {f g : α → G₀} (hf : measurable f) (hg : measurable g) :
measurable (λ a, f a / g a) :=
measurable_div.comp (hf.prod_mk hg)

@[priority 100]
instance has_measurable_div₂.to_has_measurable_div [has_measurable_div₂ G₀] :
has_measurable_div G₀ :=
⟨λ c, measurable_const.div measurable_id, λ c, measurable_id.div measurable_const⟩

lemma measurable.const_div [has_measurable_div G₀] {f : α → G₀} (hf : measurable f) (c : G₀) :
measurable (λ x, c / f x) :=
(has_measurable_div.measurable_const_div c).comp hf

lemma measurable.div_const [has_measurable_div G₀] {f : α → G₀} (hf : measurable f) (c : G₀) :
measurable (λ x, f x / c) :=
(has_measurable_div.measurable_div_const c).comp hf

end div

class is_measurable_action (M α : Type*) [has_scalar M α] [measurable_space α] 

/-!
### Big operators: `∏` and `∑`
-/

@[to_additive]
lemma list.measurable_prod' {M : Type*} [monoid M] [measurable_space M] [has_measurable_mul₂ M]
  (l : list (α → M)) (hl : ∀ f ∈ l, measurable f) :
  measurable l.prod :=
begin
  induction l with f l ihl, { exact @measurable_const _ _ _ _ 1 },
  rw [list.forall_mem_cons] at hl,
  rw [list.prod_cons],
  exact hl.1.mul (ihl hl.2)
end

@[to_additive]
lemma list.measurable_prod {M : Type*} [monoid M] [measurable_space M] [has_measurable_mul₂ M]
  (l : list (α → M)) (hl : ∀ f ∈ l, measurable f) :
  measurable (λ x, (l.map (λ f : α → M, f x)).prod) :=
by simpa only [← pi.list_prod_apply] using l.measurable_prod' hl

@[to_additive]
lemma multiset.measurable_prod' {M : Type*} [comm_monoid M] [measurable_space M]
  [has_measurable_mul₂ M] (l : multiset (α → M)) (hl : ∀ f ∈ l, measurable f) :
  measurable l.prod :=
by { rcases l with ⟨l⟩, simp [l.measurable_prod (by simpa using hl)] }

@[to_additive]
lemma multiset.measurable_prod {M : Type*} [comm_monoid M] [measurable_space M]
  [has_measurable_mul₂ M] (s : multiset (α → M)) (hs : ∀ f ∈ s, measurable f) :
  measurable (λ x, (s.map (λ f : α → M, f x)).prod) :=
by simpa only [← pi.multiset_prod_apply] using s.measurable_prod' hs

@[to_additive]
lemma finset.measurable_prod' {ι M : Type*} [comm_monoid M] [measurable_space M]
  [has_measurable_mul₂ M] {f : ι → α → M} (s : finset ι) (hf : ∀i ∈ s, measurable (f i)) :
  measurable (∏ i in s, f i) :=
finset.prod_induction _ _ (λ _ _, measurable.mul) (@measurable_const _ _ _ _ 1) hf

@[to_additive]
lemma finset.measurable_prod {ι M : Type*} [comm_monoid M] [measurable_space M]
  [has_measurable_mul₂ M] {f : ι → α → M} (s : finset ι) (hf : ∀i ∈ s, measurable (f i)) :
  measurable (λ a, ∏ i in s, f i a) :=
by simpa only [← finset.prod_apply] using s.measurable_prod' hf

