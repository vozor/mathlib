/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import data.rat
import data.fintype.card
import data.nat.choose.binomial
import algebra.big_operators.nat_antidiagonal

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, 1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the Taylor series of trigonometric
and hyperbolic functions, and they are related to the values that the Riemann Zeta
function takes at negative integers. If $2 \leq k$ is even then

$$\sum_{n\geq1}n^{-k}=B_k\pi^k.$$

Note however that many of these things are not yet formalised.

The Bernoulli numbers can be formally defined thus:

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* though, and need not concern the mathematician).

## Implementation detail

```
def bernoulli : ℕ → ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli, 1 - ∑ k : fin n, (n.choose k) * bernoulli k k.2 / (n + 1 - k))
```
The formal definition has the property that `bernoulli 0 = 1`

-- Should use finset, not fin?

--
According to Wikipedia https://en.wikipedia.org/wiki/Bernoulli_number there are
two conventions for Bernoulli numbers. Lean's `bernoulli (n : ℕ) : ℚ` is the
convention denoted $$B_n^+$$ on Wikipedia.  `n`'th
Bernoulli number.

For example, they show up in the Taylor series of many trigonometric and hyperbolic functions,
and also as (integral multiples of products of powers of `π` and)
special values of the Riemann zeta function.
(Note: these facts are not yet available in mathlib)

In this file, we provide the definition,
and the basic fact (`sum_bernoulli`) that
$$ \sum_{k < n} \binom{n}{k} * B_k = n, $$
where $B_k$ denotes the the $k$-th Bernoulli number.

-/

open_locale big_operators

/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli : ℕ → ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli, 1 - ∑ k : fin n, (k : ℕ).binomial (n - k) / (n - k + 1) * bernoulli k k.2)

lemma bernoulli_def' (n : ℕ) :
  bernoulli n = 1 - ∑ k : fin n, (k : ℕ).binomial (n - k) / (n - k + 1) * bernoulli k :=
well_founded.fix_eq _ _ _

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - ∑ k in finset.range n, (k : ℕ).binomial (n - k) / (n - k + 1) * bernoulli k :=
by { rw [bernoulli_def', ← fin.sum_univ_eq_sum_range], refl }

lemma bernoulli_spec (n : ℕ) :
  ∑ k in finset.range n.succ, (k.binomial (n - k) : ℚ) / (n - k + 1) * bernoulli k = 1 :=
by simp [finset.sum_range_succ, bernoulli_def n]

@[simp] lemma finset.mem_range_succ_iff {a b : ℕ} : a ∈ finset.range b.succ ↔ a ≤ b :=
by simp only [nat.lt_succ_iff, finset.mem_range]

open finset

lemma sum_range_succ_eq_sum_antidiagonal {M : Type*} [add_comm_monoid M]
  (f : ℕ → ℕ → M) (n : ℕ) : ∑ k in range n.succ, f k (n - k) =
    ∑ ij in finset.nat.antidiagonal n, f ij.1 ij.2 :=
begin
  refine finset.sum_bij'
  (λ a _, (a, n - a) : Π (a : ℕ), a ∈ finset.range n.succ → ℕ × ℕ)
  _ (by simp)
  (λ (ij : ℕ × ℕ) _, ij.1)
  _ (by simp) _,
  { intros a ha, simp [nat.add_sub_cancel' (mem_range_succ_iff.1 ha)], },
  { intros _ ha, simp [nat.le.intro (nat.mem_antidiagonal.1 ha)] },
  { rintro ⟨i, j⟩ ha, ext, refl, rw ← (nat.mem_antidiagonal.1 ha), exact nat.add_sub_cancel_left _ _ },
end

lemma this_is_so_stupid (n : ℕ) :
∑ (k : ℕ) in range n.succ, (k.binomial (n - k) : ℚ) / (n - k + 1) * bernoulli k
=
∑ (k : ℕ) in range n.succ, k.binomial (n - k) / ((n - k : ℕ) + 1) * bernoulli k
:=
begin
  apply finset.sum_congr rfl,
  intros k hk,
-- next line was written with
--  congr', symmetry, apply nat.cast_sub, library_search,
  rw nat.cast_sub (finset.mem_range_succ_iff.mp hk),
end

lemma bernoulli_spec' (n : ℕ) :
  ∑ k in finset.nat.antidiagonal n,
  (k.1.binomial k.2 : ℚ) / (k.2 + 1) * bernoulli k.1 = 1 :=
begin
  convert bernoulli_spec n using 1,
  rw this_is_so_stupid,
  symmetry,
  convert sum_range_succ_eq_sum_antidiagonal (λ i j, (i.binomial j : ℚ) / (j + 1) * bernoulli i) n,
end

@[simp] lemma bernoulli_zero  : bernoulli 0 = 1   := rfl
@[simp] lemma bernoulli_one   : bernoulli 1 = 1/2 :=
begin
  rw [bernoulli_def, sum_range_one], norm_num
end
@[simp] lemma bernoulli_two   : bernoulli 2 = 1/6 :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_one], norm_num
end
@[simp] lemma bernoulli_three : bernoulli 3 = 0   :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_succ, sum_range_one], norm_num,
end
@[simp] lemma bernoulli_four  : bernoulli 4 = -1/30 :=
begin
  rw [bernoulli_def, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_one], norm_num,
end

open_locale nat

lemma what_am_i_doing_wrong (n : ℕ) : ∑ (k : ℕ) in range n.succ, ↑(k.binomial (n.succ - k)) * bernoulli k =
∑ (k : ℕ) in range n.succ, ↑(k.binomial (n - k).succ) * bernoulli k :=
begin
  apply finset.sum_congr rfl,
  intros k hk,
  rw nat.succ_sub (finset.mem_range_succ_iff.mp hk),
end

open nat

@[simp] lemma sum_bernoulli' (n : ℕ) :
  ∑ k in finset.range n, (k.binomial (n - k) : ℚ) * bernoulli k = n :=
begin
  -- n = 0 is a special case so let's prove it for n of the form d + 1.
  cases n with d, simp, -- checking special case n = 0 with `simp`
  -- n = d + 1 case: By definition of B_d, goal obviously equivalent to
  -- $$\Sum_{k\leq d}\binom{d+1}k\cdot B_k=\Sum_{k\leq d}(d+1)\binom{d}{x}\frac{B_k}{d+1-k}$$
  rw [← mul_one (d.succ : ℚ), ← bernoulli_spec' d, finset.mul_sum],
  -- change other sum to antidiag
  rw what_am_i_doing_wrong,
  rw sum_range_succ_eq_sum_antidiagonal (λ k dmk, (k.binomial dmk.succ : ℚ) * bernoulli k) d,
  apply finset.sum_congr rfl,
  rintro ⟨i, j⟩ hd, rw finset.nat.mem_antidiagonal at hd, subst hd, dsimp,
  -- eliminate bernoulli
  rw ← mul_assoc, congr',
  field_simp [(show (j : ℚ) + 1 ≠ 0, from ne_of_gt (by norm_cast; linarith))],
  norm_cast,
  rw succ_mul_binomial',
  ring,
end
