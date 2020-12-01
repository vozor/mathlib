import ring_theory.jacobson
import field_theory.algebraic_closure

-- Proof of the classical hilbert nullstellensatz

noncomputable theory

open ideal

variables {k : Type*} [field k] [is_alg_closed k]
variables {σ : Type*} [fintype σ]

lemma jacobson_radical_eq_jacobson {R : Type*} [comm_ring R] (I : ideal R) :
  I.radical.jacobson = I.jacobson :=
begin
  refine le_antisymm _ (jacobson_mono le_radical),
  rw radical_eq_Inf,
  refine Inf_le_Inf (λ J hJ, ⟨Inf_le ⟨hJ.1, hJ.2.is_prime⟩, hJ.2⟩),
end

lemma radical_eq_jacobson_of_is_jacobson {R : Type*} [comm_ring R] [H : is_jacobson R]
  (I : ideal R ): I.jacobson = I.radical :=
begin
  specialize H I.radical sorry,
  refine trans _ H,
  refine (jacobson_radical_eq_jacobson I).symm,
end

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

-- I don't think this is the right inverse function
def lemma_iso (x : σ → k) : (I' {x} : ideal (mv_polynomial σ k)).quotient ≃+* k := {
  to_fun := ideal.quotient.lift _ (mv_polynomial.eval x) (λ p hp, (lemma1 x p).mpr hp),
  inv_fun := (ideal.quotient.mk (I' {x})).comp mv_polynomial.C,
  left_inv := sorry,
  right_inv := sorry,
  map_add' := sorry,
  map_mul' := sorry,
}

lemma lemma4' (x : σ → k) : (I' {x} : ideal (mv_polynomial σ k)).is_maximal :=
begin
  rw ← bot_quotient_is_maximal_iff,
  have : (⊥ : ideal k).is_maximal := bot_is_maximal,
  sorry,
end


lemma lemma4 (x : σ → k) : (I' {x} : ideal (mv_polynomial σ k)).is_maximal :=
begin
  refine ⟨_, _⟩,
  {
    rw ne_top_iff_one,
    refine λ h, by simpa using h x rfl,
  },
  {
    intros J hJ,
    rw eq_top_iff_one,
    sorry,
  },
end

-- Should be able to prove easily with facts about k being jacobson
lemma lemma3 (I : ideal (mv_polynomial σ k)) :
  I.is_maximal ↔ ∃ (x : σ → k), I = I' {x} :=
begin
  sorry,
end

theorem nullstellensatz (I : ideal (mv_polynomial σ k)) :
  I' (V' (I)) = I.radical :=
begin
  haveI H : ideal.is_jacobson (mv_polynomial σ k) := by apply_instance,
  rw (radical_eq_jacobson I),
  refine le_antisymm _ _,
  { refine le_Inf _,
    rintros J ⟨hJI, hJ⟩,
    obtain ⟨x, hx⟩ := (lemma3 J).1 hJ,
    refine hx.symm ▸ I'_anti_mono (λ y hy p hp, _),
    rw [lemma1, set.mem_singleton_iff.1 hy, ← hx],
    refine hJI hp },
  { refine λ p hp x hx, _,
    rw lemma1 x p,
    refine (mem_Inf.mp hp) _,
    refine ⟨le_trans (le_zariski_closure I) (I'_anti_mono (λ y hy, hy.symm ▸ hx)), lemma4 x⟩,
  },
end
