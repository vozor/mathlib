/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import data.rat
import data.fintype.card

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, 1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the Taylor series of trigonometric
and hyperbolic functions, and they are related to the values that the Riemann Zeta function
takes at negative integers. If $2 \leq k$ is even then

$$\sum_{n\geq1}n^{-k}=B_k\pi^k.$$


relate  multiples of products of powers of `π` and)
special values of the Riemann zeta function, although many of these things are not
yet formalised.

The Bernoulli numbers can be formally defined thus:

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* though, and need not concern the mathematician).

-- TODO : prove the displayed equation above

Note: Not all of these facts are available in mathlib.

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
  (λ n bernoulli, 1 - ∑ k : fin n, (n.choose k) / (n - k + 1) * bernoulli k k.2)

lemma bernoulli_def' (n : ℕ) :
  bernoulli n = 1 - ∑ k : fin n, (n.choose k) * (bernoulli k) / (n + 1 - k) :=
well_founded.fix_eq _ _ _

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - ∑ k in finset.range n, (n.choose k) * (bernoulli k) / (n + 1 - k) :=
by { rw [bernoulli_def', ← fin.sum_univ_eq_sum_range], refl }

@[simp] lemma bernoulli_zero  : bernoulli 0 = 1   := rfl
@[simp] lemma bernoulli_one   : bernoulli 1 = 1/2 :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end
@[simp] lemma bernoulli_two   : bernoulli 2 = 1/6 :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end
@[simp] lemma bernoulli_three : bernoulli 3 = 0   :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end
@[simp] lemma bernoulli_four  : bernoulli 4 = -1/30 :=
begin
  rw [bernoulli_def],
  repeat { try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1 }
end

@[simp] lemma sum_bernoulli (n : ℕ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = n :=
begin
  induction n with n ih, { simp },
  rw [finset.sum_range_succ],
  rw [nat.choose_succ_self_right],
  rw [bernoulli_def, mul_sub, mul_one, sub_add_eq_add_sub, sub_eq_iff_eq_add],
  rw [add_left_cancel_iff, finset.mul_sum, finset.sum_congr rfl],
  intros k hk, rw finset.mem_range at hk,
  rw [mul_div_right_comm, ← mul_assoc],
  congr' 1,
  rw [← mul_div_assoc, eq_div_iff],
  { rw [mul_comm ((n+1 : ℕ) : ℚ)],
    have hk' : k ≤ n + 1, by linarith,
    rw_mod_cast nat.choose_mul_succ_eq n k },
  { contrapose! hk with H, rw sub_eq_zero at H, norm_cast at H, linarith }
end
