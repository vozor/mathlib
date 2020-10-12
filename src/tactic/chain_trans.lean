/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import meta.rb_map
import meta.expr
import tactic.core
/-!
# `chain_trans` tactic

This file defines the `chain_trans` tactic which prove goals of the
shape `x ≤ y` or `x < y` by finding assumptions of the shape `x ≤ z`,
`x < z` or `x = z` and combining them using transitivity. In order
to prove `x < y`, at least one of the assumptions must be
a strict ordering. Whatever is found, `x ≤ y` can be proved.

```lean
variables {w x y z : ℕ}
example (h₀ : w ≤ x) (h₁ : x = y) (h₂ : y < z) : w < z :=
begin
  chain_trans,
end
```

## Implementation

`chain_trans` builds a graph where vertices are expressions of type
`α`, with a preorder on `α`, and edges are assumptions stating an
order between its source and its target. It then uses depth first
search to find a path through that graph between two vertices.
the edges along that path can then be combined through transitivity
to prove an order between the two vertices.
-/

universes u v

namespace tactic

open expr

namespace chain_trans

/-- A label for the edges of a graph of assumptions to
specify whether the assumption is a strict ordering
(i.e. `<`) or non-strict ordering (i.e. `≤`). -/
@[derive inhabited]
inductive edge
| lt | le

instance : has_to_string edge :=
⟨ λ e, match e with
      | edge.lt := "lt"
      | edge.le := "le"
      end ⟩

meta instance edge.has_to_format : has_to_format edge :=
⟨ λ e, to_fmt $ to_string e ⟩

open native

/-- A graph, represented as adjacency lists, where edges are
expressions of type `α` and where an edge between `u` and `v` contains
a proof that `u ≤ v` or `u < v`. -/
meta def graph := native.rb_lmap expr (expr × edge × expr)

meta instance graph.has_to_format : has_to_tactic_format graph :=
by delta graph; apply_instance

private meta def dfs_trans' (g : graph) (r : ref expr_set) (v : expr) : expr → list (edge × expr) → tactic expr
| x hs := do
  vs ← read_ref r,
  if vs.contains x then failed
  else if v = x then do
    (h :: hs) ← pure hs | mk_mapp ``le_refl [none, none, x],
    prod.snd <$> hs.mfoldl (λ ⟨e',h'⟩ ⟨e, h⟩,
              match e, e' with
              | edge.lt, edge.lt := prod.mk edge.lt <$> mk_app ``lt_trans [h, h']
              | edge.lt, edge.le := prod.mk edge.lt <$> mk_app ``lt_of_lt_of_le [h, h']
              | edge.le, edge.lt := prod.mk edge.lt <$> mk_app ``lt_of_le_of_lt [h, h']
              | edge.le, edge.le := prod.mk edge.le <$> mk_app ``le_trans [h, h']
              end) h
  else do
    write_ref r $ vs.insert x,
    (g.find x).mfirst $ λ ⟨h',e',y⟩, dfs_trans' y ((e', h') :: hs)

/--
Depth first search in a graph of ordered relation. Finds a proof
of `v ≤ v'` or `v < v'`, whichever is strongest and true.
-/
meta def dfs_trans (g : graph) (v v' : expr) : tactic expr :=
using_new_ref mk_expr_set $ λ r, dfs_trans' g r v' v []

end chain_trans

namespace interactive
open chain_trans

/--
Prove a goal of the shape `x ≤ y` or `x < y` by finding assumptions of
the shape `x ≤ z`, `x < z` or `x = z` and combining them using
transitivity.

```lean
variables {w x y z : ℕ}
example (h₀ : w ≤ x) (h₁ : x = y) (h₂ : y < z) : w < z :=
begin
  chain_trans,
end
```
-/
meta def chain_trans : tactic unit := do
tgt ← target,
(x, y) ← match_le tgt <|> match_lt tgt,
α ← infer_type x,
ls ← local_context >>= list.mmap_filter'
  (λ h, do t ← infer_type h,
           do { (e, x, y) ← prod.mk edge.le <$> match_le t <|>
                    prod.mk edge.lt <$> match_lt t,
                infer_type x >>= is_def_eq α,
                pure [(h, e, x, y)] } <|>
           do { (x, y) ← match_eq t,
                infer_type x >>= is_def_eq α,
                h₀ ← mk_eq_symm h >>= mk_app ``le_of_eq ∘ list.ret,
                h₁ ← mk_app ``le_of_eq [h],
                pure [(h₀, edge.le, y, x), (h₁, edge.le, x, y)] }),
let m := list.foldl  (λ (m : graph) (e : _ × _ × _ × _),
  let ⟨pr,e,x,y⟩ := e in
  m.insert x (pr,e,y)) (native.rb_lmap.mk expr (expr × edge × expr)) ls.join,
pr ← dfs_trans m x y <|> fail!"no chain of inequalities can be found between `{x}` and `{y}`",
tactic.apply pr <|>
  mk_app ``le_of_lt [pr] >>= tactic.apply <|>
  fail!"`{tgt}` cannot be proved from `{infer_type pr}`",
skip

end interactive

end tactic