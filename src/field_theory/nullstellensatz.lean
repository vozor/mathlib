import ring_theory.jacobson
import field_theory.algebraic_closure

open ideal

-- These should be moved out later

lemma ideal.radical_radical {R : Type*} [comm_ring R] (I : ideal R) :
  I.radical.radical = I.radical :=
le_antisymm (λ x hx, let ⟨n, ⟨m, hm⟩⟩ := hx in ⟨n * m, by rwa pow_mul x n m⟩) le_radical

lemma jacobson_radical_eq_jacobson {R : Type*} [comm_ring R] (I : ideal R) :
  I.radical.jacobson = I.jacobson :=
begin
  refine le_antisymm _ (jacobson_mono le_radical),
  rw radical_eq_Inf,
  exact Inf_le_Inf (λ J hJ, ⟨Inf_le ⟨hJ.1, hJ.2.is_prime⟩, hJ.2⟩),
end

lemma radical_eq_jacobson_of_is_jacobson {R : Type*} [comm_ring R] [H : is_jacobson R]
  (I : ideal R ): I.jacobson = I.radical :=
trans (jacobson_radical_eq_jacobson I).symm (H I.radical I.radical_radical)

lemma ring_equiv.bot_maximal_iff {R S : Type*} [comm_ring R] [comm_ring S] (e : R ≃+* S) :
  (⊥ : ideal R).is_maximal ↔ (⊥ : ideal S).is_maximal :=
⟨λ h, (@map_bot _ _ _ _ e.to_ring_hom) ▸ map.is_maximal e.to_ring_hom e.bijective h,
  λ h, (@map_bot _ _ _ _ e.symm.to_ring_hom) ▸ map.is_maximal e.symm.to_ring_hom e.symm.bijective h⟩

-- Proof of the classical hilbert nullstellensatz

noncomputable theory

variables {k : Type*} [field k] [is_alg_closed k]
variables {σ : Type*} [fintype σ]

def V' (I : ideal (mv_polynomial σ k)) : set (σ → k) :=
  {x : σ → k | ∀ p ∈ I, mv_polynomial.eval x p = 0}

lemma V'_anti_mono (I J : ideal (mv_polynomial σ k)) (h : I ≤ J) : V' J ≤ V' I :=
λ x hx p hp, hx p $ h hp

lemma V'_bot : V' (⊥ : ideal (mv_polynomial σ k)) = ⊤ :=
begin
  refine le_antisymm le_top (λ x hx p hp, _),
  rw mem_bot.1 hp,
  exact (mv_polynomial.eval x).map_zero,
end

def I' (V : set (σ → k)) : ideal (mv_polynomial σ k) :=
{ carrier := {p | ∀ x ∈ V, mv_polynomial.eval x p = 0},
  zero_mem' := λ x hx, ring_hom.map_zero _,
  add_mem' := λ p q hp hq x hx, by simp only [hq x hx, hp x hx, add_zero, ring_hom.map_add],
  smul_mem' := λ p q hq x hx,
    by simp only [hq x hx, algebra.id.smul_eq_mul, mul_zero, ring_hom.map_mul] }

lemma I'_anti_mono {A B : set (σ → k)} (h : A ≤ B) : I' B ≤ I' A :=
λ p hp x hx, hp x $ h hx

lemma I'_bot : I' (∅ : set (σ → k)) = ⊤ :=
le_antisymm le_top (λ p hp x hx, absurd hx (set.not_mem_empty x))

lemma le_zariski_closure (I : ideal (mv_polynomial σ k)) : I ≤ I' (V' I) :=
λ p hp x hx, hx p hp

lemma lemma1 (x : σ → k) (p : mv_polynomial σ k) :
  (mv_polynomial.eval x p = 0) ↔ p ∈ (I' {x} : ideal (mv_polynomial σ k)) :=
⟨λ hpx y hy, hy.symm ▸ hpx, λ h, h x rfl⟩

def lemma_iso (x : σ → k) : (I' {x} : ideal (mv_polynomial σ k)).quotient ≃+* k :=
ring_equiv.of_bijective (ideal.quotient.lift _ (mv_polynomial.eval x) (λ p hp, (lemma1 x p).mpr hp))
begin
  refine ⟨_, λ z, ⟨(ideal.quotient.mk (I' {x})) (mv_polynomial.C z), by simp⟩⟩,
  rw ring_hom.injective_iff,
  intros p hp,
  obtain ⟨q, rfl⟩ := quotient.mk_surjective p,
  rw quotient.lift_mk at hp,
  rwa [quotient.eq_zero_iff_mem, ← lemma1],
end

lemma ideal_singleton_maximal (x : σ → k) : (I' {x} : ideal (mv_polynomial σ k)).is_maximal :=
begin
  rw [← bot_quotient_is_maximal_iff, (lemma_iso x).bot_maximal_iff],
  exact bot_is_maximal,
end

-- Generally for any Jacobson ring R, if there exists a field K of finite type over R,
--  then R is a field and K/R is a finite field extension.
-- In the case R is already algebraicly closed, this implies K is just R
-- So since I.quotient is a field for any I maximal, I.quotient ≃+* k
def zariski_lemma (I : ideal (mv_polynomial σ k)) [I.is_maximal] :
  I.quotient ≃+* k :=
begin
  sorry,
end

lemma lemma3 (I : ideal (mv_polynomial σ k)) :
  I.is_maximal ↔ ∃ (x : σ → k), I' {x} = I :=
begin
  haveI H : ideal.is_jacobson (mv_polynomial σ k) := by apply_instance,
  refine ⟨λ hI, _, λ h, let ⟨x, hx⟩ := h in hx ▸ ideal_singleton_maximal x⟩,
  haveI : I.is_maximal := hI,
  -- S/I is algebraic over k by jacobson stuff, which is already algebraicly closed, so equal
  have e : I.quotient ≃+* k := zariski_lemma I,
  let x : σ → k := λ s, e.to_ring_hom ((ideal.quotient.mk I) (mv_polynomial.X s)),
  refine ⟨x, _⟩,
  have : I' {x} ≤ I, {
    intros p hp,
    rw ← lemma1 at hp,

    rw ← quotient.eq_zero_iff_mem,
    refine e.injective (trans _ (e.to_ring_hom.map_zero).symm),
    convert hp,

    rw mv_polynomial.eval_eq',
    -- Eisenbud just states this, but I think in lean it is nontrivial to prove
    sorry,
  },
  -- have := local_ring.eq_maximal_ideal,
  exact is_maximal.eq_of_le (ideal_singleton_maximal x) hI.1 this,
end

theorem nullstellensatz (I : ideal (mv_polynomial σ k)) :
  I' (V' (I)) = I.radical :=
begin
  rw (radical_eq_jacobson I),
  refine le_antisymm _ _,
  { refine le_Inf _,
    rintros J ⟨hJI, hJ⟩,
    obtain ⟨x, hx⟩ := (lemma3 J).1 hJ,
    refine hx ▸ I'_anti_mono (λ y hy p hp, _),
    rw [lemma1, set.mem_singleton_iff.1 hy, hx],
    refine hJI hp },
  { refine λ p hp x hx, _,
    rw lemma1 x p,
    refine (mem_Inf.mp hp) ⟨le_trans (le_zariski_closure I)
      (I'_anti_mono (λ y hy, hy.symm ▸ hx)), ideal_singleton_maximal x⟩ },
end
