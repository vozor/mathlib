/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison
-/
import category_theory.types
import category_theory.equivalence
import data.opposite

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory
open opposite

variables {C : Type u₁}

section has_hom

variables [has_hom.{v₁} C]

/-- The hom types of the opposite of a category (or graph).

  As with the objects, we'll make this irreducible below.
  Use `f.op` and `f.unop` to convert between morphisms of C
  and morphisms of Cᵒᵖ.
-/
instance has_hom.opposite : has_hom Cᵒᵖ :=
{ hom := λ X Y, unop Y ⟶ unop X }

/--
The opposite of a morphism in `C`.
-/
def has_hom.hom.op {X Y : C} (f : X ⟶ Y) : op Y ⟶ op X := f
/--
Given a morphism in `Cᵒᵖ`, we can take the "unopposite" back in `C`.
-/
def has_hom.hom.unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := f

attribute [irreducible] has_hom.opposite

lemma has_hom.hom.op_inj {X Y : C} :
  function.injective (has_hom.hom.op : (X ⟶ Y) → (op Y ⟶ op X)) :=
λ _ _ H, congr_arg has_hom.hom.unop H

lemma has_hom.hom.unop_inj {X Y : Cᵒᵖ} :
  function.injective (has_hom.hom.unop : (X ⟶ Y) → (unop Y ⟶ unop X)) :=
λ _ _ H, congr_arg has_hom.hom.op H

@[simp] lemma has_hom.hom.unop_op {X Y : C} {f : X ⟶ Y} : f.op.unop = f := rfl
@[simp] lemma has_hom.hom.op_unop {X Y : Cᵒᵖ} {f : X ⟶ Y} : f.unop.op = f := rfl

end has_hom

variables [category.{v₁} C]

/--
The opposite category.

See https://stacks.math.columbia.edu/tag/001M.
-/
instance category.opposite : category.{v₁} Cᵒᵖ :=
{ comp := λ _ _ _ f g, (g.unop ≫ f.unop).op,
  id   := λ X, (𝟙 (unop X)).op }

@[simp] lemma op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} :
  (f ≫ g).op = g.op ≫ f.op := rfl
@[simp] lemma op_id {X : C} : (𝟙 X).op = 𝟙 (op X) := rfl

@[simp] lemma unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} :
  (f ≫ g).unop = g.unop ≫ f.unop := rfl
@[simp] lemma unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X) := rfl

@[simp] lemma unop_id_op {X : C} : (𝟙 (op X)).unop = 𝟙 X := rfl
@[simp] lemma op_id_unop {X : Cᵒᵖ} : (𝟙 (unop X)).op = 𝟙 X := rfl

section
variables (C)

/-- The functor from the double-opposite of a category to the underlying category. -/
@[simps]
def op_op : (Cᵒᵖ)ᵒᵖ ⥤ C :=
{ obj := λ X, unop (unop X),
  map := λ X Y f, f.unop.unop }

/-- The functor from a category to its double-opposite.  -/
@[simps]
def unop_unop : C ⥤ Cᵒᵖᵒᵖ :=
{ obj := λ X, op (op X),
  map := λ X Y f, f.op.op }

/-- The double opposite category is equivalent to the original. -/
@[simps]
def op_op_equivalence : Cᵒᵖᵒᵖ ≌ C :=
{ functor := op_op C,
  inverse := unop_unop C,
  unit_iso := iso.refl (𝟭 Cᵒᵖᵒᵖ),
  counit_iso := iso.refl (unop_unop C ⋙ op_op C) }

end

/--
If `f.op` is an isomorphism `f` must be too.
(This cannot be an instance as it would immediately loop!)
-/
def is_iso_of_op {X Y : C} (f : X ⟶ Y) [is_iso f.op] : is_iso f :=
{ inv := (inv (f.op)).unop,
  hom_inv_id' := has_hom.hom.op_inj (by simp),
  inv_hom_id' := has_hom.hom.op_inj (by simp) }

namespace functor

section

variables {D : Type u₂} [category.{v₂} D]

variables {C D}

/--
The opposite of a functor, i.e. considering a functor `F : C ⥤ D` as a functor `Cᵒᵖ ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made between these.
-/
@[simps]
protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ :=
{ obj := λ X, op (F.obj (unop X)),
  map := λ X Y f, (F.map f.unop).op }

/--
Given a functor `F : Cᵒᵖ ⥤ Dᵒᵖ` we can take the "unopposite" functor `F : C ⥤ D`.
In informal mathematics no distinction is made between these.
-/
@[simps]
protected def unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D :=
{ obj := λ X, unop (F.obj (op X)),
  map := λ X Y f, (F.map f.op).unop }

/-- The isomorphism between `F.op.unop` and `F`. -/
def op_unop_iso (F : C ⥤ D) : F.op.unop ≅ F :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

/-- The isomorphism between `F.unop.op` and `F`. -/
def unop_op_iso (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op ≅ F :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

variables (C D)

/--
Taking the opposite of a functor is functorial.
-/
@[simps]
def op_hom : (C ⥤ D)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Dᵒᵖ) :=
{ obj := λ F, (unop F).op,
  map := λ F G α,
  { app := λ X, (α.unop.app (unop X)).op,
    naturality' := λ X Y f, has_hom.hom.unop_inj (α.unop.naturality f.unop).symm } }

/--
Take the "unopposite" of a functor is functorial.
-/
@[simps]
def op_inv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ :=
{ obj := λ F, op F.unop,
  map := λ F G α, has_hom.hom.op
  { app := λ X, (α.app (op X)).unop,
    naturality' := λ X Y f, has_hom.hom.op_inj $ (α.naturality f.op).symm } }

-- TODO show these form an equivalence

variables {C D}

/--
Another variant of the opposite of functor, turning a functor `C ⥤ Dᵒᵖ` into a functor `Cᵒᵖ ⥤ D`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def left_op (F : C ⥤ Dᵒᵖ) : Cᵒᵖ ⥤ D :=
{ obj := λ X, unop (F.obj (unop X)),
  map := λ X Y f, (F.map f.unop).unop }

/--
Another variant of the opposite of functor, turning a functor `Cᵒᵖ ⥤ D` into a functor `C ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made.
-/
@[simps]
protected def right_op (F : Cᵒᵖ ⥤ D) : C ⥤ Dᵒᵖ :=
{ obj := λ X, op (F.obj (op X)),
  map := λ X Y f, (F.map f.op).op }

-- TODO show these form an equivalence

instance {F : C ⥤ D} [full F] : full F.op :=
{ preimage := λ X Y f, (F.preimage f.unop).op }

instance {F : C ⥤ D} [faithful F] : faithful F.op :=
{ map_injective' := λ X Y f g h,
    has_hom.hom.unop_inj $ by simpa using map_injective F (has_hom.hom.op_inj h) }

/-- If F is faithful then the right_op of F is also faithful. -/
instance right_op_faithful {F : Cᵒᵖ ⥤ D} [faithful F] : faithful F.right_op :=
{ map_injective' := λ X Y f g h, has_hom.hom.op_inj (map_injective F (has_hom.hom.op_inj h)) }

/-- If F is faithful then the left_op of F is also faithful. -/
instance left_op_faithful {F : C ⥤ Dᵒᵖ} [faithful F] : faithful F.left_op :=
{ map_injective' := λ X Y f g h, has_hom.hom.unop_inj (map_injective F (has_hom.hom.unop_inj h)) }

end

end functor

namespace nat_trans

variables {D : Type u₂} [category.{v₂} D]

section
variables {F G : C ⥤ D}

local attribute [semireducible] has_hom.opposite

/-- The opposite of a natural transformation. -/
@[simps] protected def op (α : F ⟶ G) : G.op ⟶ F.op :=
{ app         := λ X, (α.app (unop X)).op,
  naturality' := begin tidy, erw α.naturality, refl, end }

@[simp] lemma op_id (F : C ⥤ D) : nat_trans.op (𝟙 F) = 𝟙 (F.op) := rfl

/-- The "unopposite" of a natural transformation. -/
@[simps] protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) : G.unop ⟶ F.unop :=
{ app         := λ X, (α.app (op X)).unop,
  naturality' := begin tidy, erw α.naturality, refl, end }

@[simp] lemma unop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : nat_trans.unop (𝟙 F) = 𝟙 (F.unop) := rfl

/--
Given a natural transformation `α : F.op ⟶ G.op`,
we can take the "unopposite" of each component obtaining a natural transformation `G ⟶ F`.
-/
@[simps] protected def remove_op (α : F.op ⟶ G.op) : G ⟶ F :=
{ app         := λ X, (α.app (op X)).unop,
  naturality' :=
  begin
    intros X Y f,
    have := congr_arg has_hom.hom.op (α.naturality f.op),
    dsimp at this,
    erw this,
    refl,
  end }

@[simp] lemma remove_op_id (F : C ⥤ D) : nat_trans.remove_op (𝟙 F.op) = 𝟙 F := rfl

end

section
variables {F G : C ⥤ Dᵒᵖ}

local attribute [semireducible] has_hom.opposite
/--
Given a natural transformation `α : F ⟶ G`, for `F G : C ⥤ Dᵒᵖ`,
taking `unop` of each component gives a natural transformation `G.left_op ⟶ F.left_op`.
-/
@[simps] protected def left_op (α : F ⟶ G) : G.left_op ⟶ F.left_op :=
{ app         := λ X, (α.app (unop X)).unop,
  naturality' := begin tidy, erw α.naturality, refl, end }

/--
Given a natural transformation `α : F.left_op ⟶ G.left_op`, for `F G : C ⥤ Dᵒᵖ`,
taking `op` of each component gives a natural transformation `G ⟶ F`.
-/
@[simps] protected def remove_left_op (α : F.left_op ⟶ G.left_op) : G ⟶ F :=
{ app         := λ X, (α.app (op X)).op,
  naturality' :=
  begin
    intros X Y f,
    have := congr_arg has_hom.hom.op (α.naturality f.op),
    dsimp at this,
    erw this
  end }

end
end nat_trans

namespace iso

variables {X Y : C}

/--
The opposite isomorphism.
-/
protected def op (α : X ≅ Y) : op Y ≅ op X :=
{ hom := α.hom.op,
  inv := α.inv.op,
  hom_inv_id' := has_hom.hom.unop_inj α.inv_hom_id,
  inv_hom_id' := has_hom.hom.unop_inj α.hom_inv_id }

@[simp] lemma op_hom {α : X ≅ Y} : α.op.hom = α.hom.op := rfl
@[simp] lemma op_inv {α : X ≅ Y} : α.op.inv = α.inv.op := rfl

end iso

namespace nat_iso

variables {D : Type u₂} [category.{v₂} D]
variables {F G : C ⥤ D}

/-- The natural isomorphism between opposite functors `G.op ≅ F.op` induced by a natural
isomorphism between the original functors `F ≅ G`. -/
protected def op (α : F ≅ G) : G.op ≅ F.op :=
{ hom := nat_trans.op α.hom,
  inv := nat_trans.op α.inv,
  hom_inv_id' := begin ext, dsimp, rw ←op_comp, rw α.inv_hom_id_app, refl, end,
  inv_hom_id' := begin ext, dsimp, rw ←op_comp, rw α.hom_inv_id_app, refl, end }

@[simp] lemma op_hom (α : F ≅ G) : (nat_iso.op α).hom = nat_trans.op α.hom := rfl
@[simp] lemma op_inv (α : F ≅ G) : (nat_iso.op α).inv = nat_trans.op α.inv := rfl

/-- The natural isomorphism between functors `G ≅ F` induced by a natural isomorphism
between the opposite functors `F.op ≅ G.op`. -/
@[simps] protected def remove_op (α : F.op ≅ G.op) : G ≅ F :=
{ hom := nat_trans.remove_op α.hom,
  inv := nat_trans.remove_op α.inv,
  hom_inv_id' := begin ext, dsimp, rw ←unop_comp, rw α.inv_hom_id_app, refl, end,
  inv_hom_id' := begin ext, dsimp, rw ←unop_comp, rw α.hom_inv_id_app, refl, end }

/-- The natural isomorphism between functors `G.unop ≅ F.unop` induced by a natural isomorphism
between the original functors `F ≅ G`. -/
@[simps] protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : G.unop ≅ F.unop :=
{ hom := nat_trans.unop α.hom,
  inv := nat_trans.unop α.inv,
  hom_inv_id' := begin ext, dsimp, rw ←unop_comp, rw α.inv_hom_id_app, refl, end,
  inv_hom_id' := begin ext, dsimp, rw ←unop_comp, rw α.hom_inv_id_app, refl, end }

end nat_iso

namespace equivalence

variables {D : Type u₂} [category.{v₂} D]

/--
An equivalence between categories gives an equivalence between the opposite categories.
-/
@[simps]
def op (e : C ≌ D) : Cᵒᵖ ≌ Dᵒᵖ :=
{ functor := e.functor.op,
  inverse := e.inverse.op,
  unit_iso := (nat_iso.op e.unit_iso).symm,
  counit_iso := (nat_iso.op e.counit_iso).symm,
  functor_unit_iso_comp' := λ X, by { apply has_hom.hom.unop_inj, dsimp, simp, }, }

/--
An equivalence between opposite categories gives an equivalence between the original categories.
-/
@[simps]
def unop (e : Cᵒᵖ ≌ Dᵒᵖ) : C ≌ D :=
{ functor := e.functor.unop,
  inverse := e.inverse.unop,
  unit_iso := (nat_iso.unop e.unit_iso).symm,
  counit_iso := (nat_iso.unop e.counit_iso).symm,
  functor_unit_iso_comp' := λ X, by { apply has_hom.hom.op_inj, dsimp, simp, }, }

end equivalence

/-- The equivalence between arrows of the form `A ⟶ B` and `B.unop ⟶ A.unop`. Useful for building
adjunctions.
Note that this (definitionally) gives variants
```
def op_equiv' (A : C) (B : Cᵒᵖ) : (opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
op_equiv _ _

def op_equiv'' (A : Cᵒᵖ) (B : C) : (A ⟶ opposite.op B) ≃ (B ⟶ A.unop) :=
op_equiv _ _

def op_equiv''' (A B : C) : (opposite.op A ⟶ opposite.op B) ≃ (B ⟶ A) :=
op_equiv _ _
```
-/
@[simps] def op_equiv (A B : Cᵒᵖ) : (A ⟶ B) ≃ (B.unop ⟶ A.unop) :=
{ to_fun := λ f, f.unop,
  inv_fun := λ g, g.op,
  left_inv := λ _, rfl,
  right_inv := λ _, rfl }

universes v
variables {α : Type v} [preorder α]

/-- Construct a morphism in the opposite of a preorder category from an inequality. -/
def op_hom_of_le {U V : αᵒᵖ} (h : unop V ≤ unop U) : U ⟶ V :=
has_hom.hom.op (hom_of_le h)

lemma le_of_op_hom {U V : αᵒᵖ} (h : U ⟶ V) : unop V ≤ unop U :=
le_of_hom (h.unop)

end category_theory
