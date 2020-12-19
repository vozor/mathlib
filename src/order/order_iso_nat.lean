/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.nat.basic
import order.rel_iso
import order.preorder_hom
import order.well_founded
import logic.function.iterate

namespace rel_embedding

variables {α : Type*} {r : α → α → Prop}

/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
def nat_lt [is_strict_order α r] (f : ℕ → α) (H : ∀ n:ℕ, r (f n) (f (n+1))) :
  ((<) : ℕ → ℕ → Prop) ↪r r :=
of_monotone f $ λ a b h, begin
  induction b with b IH, {exact (nat.not_lt_zero _ h).elim},
  cases nat.lt_succ_iff_lt_or_eq.1 h with h e,
  { exact trans (IH h) (H _) },
  { subst b, apply H }
end

/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def nat_gt [is_strict_order α r] (f : ℕ → α) (H : ∀ n:ℕ, r (f (n+1)) (f n)) :
  ((>) : ℕ → ℕ → Prop) ↪r r :=
by haveI := is_strict_order.swap r; exact rel_embedding.swap (nat_lt f H)

theorem well_founded_iff_no_descending_seq [is_strict_order α r] :
  well_founded r ↔ ¬ nonempty (((>) : ℕ → ℕ → Prop) ↪r r) :=
⟨λ ⟨h⟩ ⟨⟨f, o⟩⟩,
  suffices ∀ a, acc r a → ∀ n, a ≠ f n, from this (f 0) (h _) 0 rfl,
  λ a ac, begin
    induction ac with a _ IH, intros n h, subst a,
    exact IH (f (n+1)) (o.1 (nat.lt_succ_self _)) _ rfl
  end,
λ N, ⟨λ a, classical.by_contradiction $ λ na,
  let ⟨f, h⟩ := classical.axiom_of_choice $
    show ∀ x : {a // ¬ acc r a}, ∃ y : {a // ¬ acc r a}, r y.1 x.1,
    from λ ⟨x, h⟩, classical.by_contradiction $ λ hn, h $
      ⟨_, λ y h, classical.by_contradiction $ λ na, hn ⟨⟨y, na⟩, h⟩⟩ in
  N ⟨nat_gt (λ n, (f^[n] ⟨a, na⟩).1) $ λ n,
    by { rw [function.iterate_succ'], apply h }⟩⟩⟩

end rel_embedding

namespace partial_order

variables (α : Type*) [partial_order α]

/-- For partial orders, one of the many equivalent forms of well-foundedness is the following
flavour of "ascending chain condition". -/
def satisfies_acc := ∀ (a : ℕ →ₘ α), ∃ n, ∀ m, n ≤ m → a n = a m

lemma wf_iff_satisfies_acc (α : Type*) [partial_order α] :
  well_founded ((>) : α → α → Prop) ↔ satisfies_acc α :=
begin
  split; intros h,
  { rw well_founded.well_founded_iff_has_max' at h,
    intros a, have hne : (set.range a).nonempty, { use a 0, simp, },
    obtain ⟨x, ⟨n, hn⟩, range_bounded⟩ := h _ hne,
    use n, intros m hm, rw ← hn at range_bounded, symmetry,
    apply range_bounded (a m) (set.mem_range_self _) (a.monotone hm), },
  { rw rel_embedding.well_founded_iff_no_descending_seq, rintros ⟨a⟩,
    obtain ⟨n, hn⟩ := h a.swap.to_preorder_hom,
    exact n.succ_ne_self.symm (rel_embedding.to_preorder_hom_injective _ (hn _ n.le_succ)), },
end

end partial_order
