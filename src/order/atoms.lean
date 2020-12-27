/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author:  Aaron Anderson.
-/

import order.complete_boolean_algebra
import order.order_dual
import order.lattice_intervals
import order.rel_iso
import data.fintype.basic

/-!
# Atoms, Coatoms, and Simple Lattices

This module defines atoms, which are minimal non-`⊥` elements in bounded lattices, simple lattices,
which are lattices with only two elements, and related ideas.

## Main definitions

### Atoms and Coatoms
  * `is_atom a` indicates that the only element below `a` is `⊥`.
  * `is_coatom a` indicates that the only element above `a` is `⊤`.

### Simple Lattices
  * `is_simple_lattice` indicates that a bounded lattice has only two elements, `⊥` and `⊤`.
  * Given an instance of `is_simple_lattice`, we provide the following definitions. These are not
    made global instances as they contain data :
    * `is_simple_lattice.bounded_distrib_lattice`
    * `is_simple_lattice.boolean_algebra`
    * `is_simple_lattice.complete_lattice`
    * `is_simple_lattice.complete_boolean_algebra`

## Main results
  * `is_atom_iff_is_coatom_dual` and `is_coatom_iff_is_atom_dual` express the (definitional) duality
   of `is_atom` and `is_coatom`.
  * `is_simple_lattice_iff_is_atom_top` and `is_simple_lattice_iff_is_coatom_bot` express the
  connection between atoms, coatoms, and simple lattices

-/

variable {α : Type*}

section atoms

section is_atom

variable [order_bot α]

/-- An atom of an `order_bot` is an element with no other element between it and `⊥`,
  which is not `⊥`. -/
def is_atom (a : α) : Prop := a ≠ ⊥ ∧ (∀ b, b < a → b = ⊥)

lemma eq_bot_or_eq_of_le_atom {a b : α} (ha : is_atom a) (hab : b ≤ a) : b = ⊥ ∨ b = a :=
or.imp_left (ha.2 b) (lt_or_eq_of_le hab)

end is_atom

section is_coatom

variable [order_top α]

/-- A coatom of an `order_top` is an element with no other element between it and `⊤`,
  which is not `⊤`. -/
def is_coatom (a : α) : Prop := a ≠ ⊤ ∧ (∀ b, a < b → b = ⊤)

lemma eq_top_or_eq_of_coatom_le {a b : α} (ha : is_coatom a) (hab : a ≤ b) : b = ⊤ ∨ b = a :=
or.imp (ha.2 b) eq_comm.2 (lt_or_eq_of_le hab)

end is_coatom

variables [bounded_lattice α] {a : α}

lemma is_atom_iff_is_coatom_dual : is_atom a ↔ is_coatom (order_dual.to_dual a) := iff.refl _

lemma is_coatom_iff_is_atom_dual : is_coatom a ↔ is_atom (order_dual.to_dual a) := iff.refl _

end atoms

/-- A lattice is simple iff it has only two elements, `⊥` and `⊤`. -/
class is_simple_lattice (α : Type*) [bounded_lattice α] extends nontrivial α : Prop :=
(eq_bot_or_eq_top : ∀ (a : α), a = ⊥ ∨ a = ⊤)

export is_simple_lattice (eq_bot_or_eq_top)

theorem is_simple_lattice_iff_is_simple_lattice_order_dual [bounded_lattice α] :
  is_simple_lattice α ↔ is_simple_lattice (order_dual α) :=
begin
  split; intro i; haveI := i,
  { exact { exists_pair_ne := @exists_pair_ne α _,
      eq_bot_or_eq_top := λ a, or.symm (@eq_bot_or_eq_top α _ _ a) } },
  { exact { exists_pair_ne := @exists_pair_ne (order_dual α) _,
      eq_bot_or_eq_top := λ a, or.symm (@eq_bot_or_eq_top (order_dual α) _ _ a) } }
end

section is_simple_lattice

variables [bounded_lattice α] [is_simple_lattice α]

instance : is_simple_lattice (order_dual α) :=
is_simple_lattice_iff_is_simple_lattice_order_dual.1 (by apply_instance)

lemma is_atom_top : is_atom (⊤ : α) :=
⟨top_ne_bot, λ a ha, or.resolve_right (eq_bot_or_eq_top a) (ne_of_lt ha)⟩

lemma is_coatom_bot : is_coatom (⊥ : α) := is_coatom_iff_is_atom_dual.2 is_atom_top

end is_simple_lattice

namespace is_simple_lattice

variables [bounded_lattice α] [is_simple_lattice α]

/-- A simple `bounded_lattice` is also distributive. -/
protected def bounded_distrib_lattice : bounded_distrib_lattice α :=
{ le_sup_inf := λ x y z, by { rcases eq_bot_or_eq_top x with rfl | rfl; simp },
.. (infer_instance : bounded_lattice α) }

section decidable_eq
variable [decidable_eq α]

@[priority 200]
instance : fintype α :=
{ elems := {⊥, ⊤},
  complete := λ x, finset.mem_insert.2 (or.imp_right finset.mem_singleton.2 (eq_bot_or_eq_top x)) }

lemma finset_univ : (finset.univ : finset α) = {⊥, ⊤} := rfl

lemma card : fintype.card α = 2 :=
finset.card_insert_of_not_mem $ λ con, bot_ne_top (finset.mem_singleton.1 con)

/-- A simple `bounded_lattice` is also a `boolean_algebra`. -/
protected def boolean_algebra : boolean_algebra α :=
{ compl := λ x, if x = ⊥ then ⊤ else ⊥,
  sdiff := λ x y, if x = ⊤ ∧ y = ⊥ then ⊤ else ⊥,
  sdiff_eq := λ x y, by { rcases (eq_bot_or_eq_top x) with rfl | rfl; simp [bot_ne_top] },
  inf_compl_le_bot := λ x, by { rcases (eq_bot_or_eq_top x) with rfl | rfl; simp },
  top_le_sup_compl := λ x, by { rcases (eq_bot_or_eq_top x) with rfl | rfl; simp },
.. (is_simple_lattice.bounded_distrib_lattice) }

end decidable_eq

open_locale classical

/-- A simple `bounded_lattice` is also complete. -/
protected noncomputable def complete_lattice : complete_lattice α :=
{ Sup := λ s, if ⊤ ∈ s then ⊤ else ⊥,
  Inf := λ s, if ⊥ ∈ s then ⊥ else ⊤,
  le_Sup := λ s x h, by { rcases (eq_bot_or_eq_top x) with rfl | rfl,
    { exact bot_le },
    { rw if_pos h } },
  Sup_le := λ s x h, by { rcases (eq_bot_or_eq_top x) with rfl | rfl,
    { rw if_neg,
      intro con,
      exact bot_ne_top (eq_top_iff.2 (h ⊤ con)) },
    { exact le_top } },
  Inf_le := λ s x h, by { rcases (eq_bot_or_eq_top x) with rfl | rfl,
    { rw if_pos h },
    { exact le_top } },
  le_Inf := λ s x h, by { rcases (eq_bot_or_eq_top x) with rfl | rfl,
    { exact bot_le },
    { rw if_neg,
      intro con,
      exact top_ne_bot (eq_bot_iff.2 (h ⊥ con)) } },
.. (infer_instance : bounded_lattice α) }

/-- A simple `bounded_lattice` is also a `complete_boolean_algebra`. -/
protected noncomputable def complete_boolean_algebra : complete_boolean_algebra α :=
{ infi_sup_le_sup_Inf := λ x s, by { rcases (eq_bot_or_eq_top x) with rfl | rfl,
    { simp only [bot_sup_eq, ← Inf_eq_infi], apply le_refl },
    { simp only [top_sup_eq, le_top] }, },
  inf_Sup_le_supr_inf := λ x s, by { rcases (eq_bot_or_eq_top x) with rfl | rfl,
    { simp only [bot_inf_eq, bot_le] },
    { simp only [top_inf_eq, ← Sup_eq_supr], apply le_refl } },
  .. (is_simple_lattice.complete_lattice),
  .. (is_simple_lattice.boolean_algebra) }

end is_simple_lattice

theorem is_simple_lattice_iff_is_atom_top [bounded_lattice α] :
  is_simple_lattice α ↔ is_atom (⊤ : α) :=
⟨λ h, @is_atom_top _ _ h, λ h, {
  exists_pair_ne := ⟨⊤, ⊥, h.1⟩,
  eq_bot_or_eq_top := λ a, ((eq_or_lt_of_le (@le_top _ _ a)).imp_right (h.2 a)).symm }⟩

theorem is_simple_lattice_iff_is_coatom_bot [bounded_lattice α] :
  is_simple_lattice α ↔ is_coatom (⊥ : α) :=
iff.trans is_simple_lattice_iff_is_simple_lattice_order_dual is_simple_lattice_iff_is_atom_top

namespace set

theorem is_simple_lattice_Iic_iff_is_atom [bounded_lattice α] {a : α} :
  is_simple_lattice (Iic a) ↔ is_atom a :=
is_simple_lattice_iff_is_atom_top.trans $ and_congr (not_congr subtype.mk_eq_mk)
  ⟨λ h b ab, subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab),
    λ h ⟨b, hab⟩ hbotb, subtype.mk_eq_mk.2 (h b (subtype.mk_lt_mk.1 hbotb))⟩

theorem is_simple_lattice_Ici_iff_is_coatom [bounded_lattice α] {a : α} :
  is_simple_lattice (Ici a) ↔ is_coatom a :=
is_simple_lattice_iff_is_coatom_bot.trans $ and_congr (not_congr subtype.mk_eq_mk)
  ⟨λ h b ab, subtype.mk_eq_mk.1 (h ⟨b, le_of_lt ab⟩ ab),
    λ h ⟨b, hab⟩ hbotb, subtype.mk_eq_mk.2 (h b (subtype.mk_lt_mk.1 hbotb))⟩

end set

namespace order_iso

variables [bounded_lattice α] {β : Type*} [bounded_lattice β] (f : α ≃o β)
include f

lemma is_atom_iff (a : α) : is_atom a ↔ is_atom (f a) :=
and_congr (not_congr ⟨λ h, f.map_bot ▸ (congr rfl h), λ h, (f.injective (f.map_bot.symm ▸ h))⟩)
  ⟨λ h b hb, f.symm.injective begin
    rw f.symm.map_bot,
    apply h,
    rw [← f.symm_apply_apply a],
    exact (order_embedding.map_lt_iff ↑f.symm).1 hb,
  end,
  λ h b hb, f.injective (eq.trans (h (f b) ((order_embedding.map_lt_iff ↑f).1 hb)) f.map_bot.symm) ⟩

lemma is_coatom_iff (a : α) : is_coatom a ↔ is_coatom (f a) := f.dual.is_atom_iff a

lemma is_simple_lattice_iff (f : α ≃o β) : is_simple_lattice α ↔ is_simple_lattice β :=
by rw [is_simple_lattice_iff_is_atom_top, is_simple_lattice_iff_is_atom_top,
  f.is_atom_iff ⊤, f.map_top]

end order_iso