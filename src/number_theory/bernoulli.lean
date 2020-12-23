/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import data.rat
import data.fintype.card
import data.nat.choose.binomial

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
  (λ n bernoulli, 1 - ∑ k : fin n, (k : ℕ).binomial (n - k) / (n - k + 1) * bernoulli k k.2)

lemma bernoulli_def' (n : ℕ) :
  bernoulli n = 1 - ∑ k : fin n, (k : ℕ).binomial (n - k) / (n - k + 1) * bernoulli k :=
well_founded.fix_eq _ _ _

lemma bernoulli_def (n : ℕ) :
  bernoulli n = 1 - ∑ k in finset.range n, (k : ℕ).binomial (n - k) / (n - k + 1) * bernoulli k :=
by { rw [bernoulli_def', ← fin.sum_univ_eq_sum_range], refl }

lemma bernoulli_spec (n : ℕ) :
  ∑ k in finset.range n.succ, ((k : ℕ).binomial (n - k) : ℚ) / (n - k + 1) * bernoulli k = 1 :=
begin
  rw [finset.sum_range_succ, bernoulli_def, nat.sub_self, nat.binomial_zero_right],
  simp,
end

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

@[simp] lemma sum_bernoulli' (n : ℕ) :
  ∑ k in finset.range n, (k.binomial (n - k) : ℚ) * bernoulli k = n :=
begin
  -- n = 0 is a special case so let's prove it for n of the form d + 1.
  cases n with d, simp, -- checking special case n = 0 with `simp`
  -- n = d + 1 case: By definition of B_d, goal obviously equivalent to
  -- $$\Sum_{k\leq d}\binom{d+1}k\cdot B_k=\Sum_{k\leq d}(d+1)\binom{d}{x}\frac{B_k}{d+1-k}$$
  rw [← mul_one (d.succ : ℚ), ← bernoulli_spec d, finset.mul_sum],
  -- It suffices to show the summands are equal paorwise
  apply finset.sum_congr rfl,
  -- So assume k <= d are naturals and we've got to show
  -- $$\binom{d+1}k=\frac{d+1}{d+1-k}\binom{d}{k}$$.
  -- We do this by rewriting eveything in terms of factorials,
  -- because it seems less painless than casting everything to nat (I tried).
  -- Let's start from he beginning. Let `k ≤ d` be naturals.
  intros k hkd_nat, rw [finset.mem_range, nat.lt_succ_iff] at hkd_nat, -- now in the right form
  -- Because k ≤ d, \binom{d}{k} is not pathological.
  -- We also remark that the binomial coefficient binom{d+1}{k} is not pathological
  have hlinarith_solves_me_over_nat : k ≤ d + 1 := by linarith,
  -- So we can rewrite eveyrthing in terms of factorials.
  simp only [nat.choose_eq_factorial_div_factorial', hlinarith_solves_me_over_nat, hkd_nat],
  -- We stay working over ℚ. Next we want to clear denominators. So we need to get
  -- good at proving things are nonzero. First let's move our canonical fact k ≤ d up to ℚ.
  have hcoe_can_do_me : (k : ℚ) ≤ d := by assumption_mod_cast,
  -- Now we can use linarith to ensure all our denominators are nonzero
  -- Next clear denominators. Lean seems to help even though linarith closes all the
  -- obvious goals.
  have hlinarith_solves_me_over_rat : (d : ℚ) + 1 - k ≠ 0 := by linarith,
  -- why doesn't field_simp try linarith?
  field_simp [hlinarith_solves_me_over_rat],
  -- Turns out that we need to change (d + 1) - k to (d - k) + 1 in nat world
  -- this is an annoying technical issue that probably `omega` should be solving,
  rw [nat.succ_sub hkd_nat, factorial_succ, succ_eq_add_one], push_cast [hkd_nat],
  --  rw (show d.succ - k = (d - k).succ, by omega), should work
  -- and it's now finally trivial
  ring,
end


@[simp] lemma sum_bernoulli (n : ℕ) :
  ∑ k in finset.range n, ((n - k).binomial k : ℚ) * bernoulli k = n :=
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
