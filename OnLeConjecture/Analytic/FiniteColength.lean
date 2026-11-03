/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Finite colength in analytic germ rings

Modulo a power of the maximal ideal, every analytic germ is represented by a
linear combination of finitely many coordinate monomials. This proves finite
dimensionality of quotients by ideals that contain such a power.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- A finite set of coordinate monomials that represents every germ modulo
the `N`th power of the maximal ideal. -/
@[expose] noncomputable def jetMonomials (n N : ℕ) : Finset (Germ n) := by
  classical
  induction N with
  | zero => exact ∅
  | succ N monomials =>
      exact {1} ∪ Finset.univ.biUnion fun i : Fin n ↦
        monomials.image fun q ↦ Germ.coordinate i * q

theorem one_mem_jetMonomials_succ (n N : ℕ) :
    1 ∈ Germ.jetMonomials n (N + 1) := by
  classical
  simp [Germ.jetMonomials]

theorem coordinate_mul_mem_jetMonomials_succ {n N : ℕ}
    (i : Fin n) {q : Germ n} (hq : q ∈ Germ.jetMonomials n N) :
    Germ.coordinate i * q ∈ Germ.jetMonomials n (N + 1) := by
  classical
  simp only [Germ.jetMonomials, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  exact Or.inr ⟨i, q, hq, rfl⟩

/-- Multiplication by one coordinate carries the span of the monomials of
order below `N` into the span for order below `N + 1`. -/
theorem coordinate_mul_mem_span_jetMonomials_succ {n N : ℕ}
    (i : Fin n) {q : Germ n}
    (hq : q ∈ Submodule.span ℂ (Germ.jetMonomials n N : Set (Germ n))) :
    Germ.coordinate i * q ∈
      Submodule.span ℂ (Germ.jetMonomials n (N + 1) : Set (Germ n)) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
  · intro q hq
    exact Submodule.subset_span
      (Germ.coordinate_mul_mem_jetMonomials_succ i hq)
  · simp
  · intro q r _ _ hq hr
    rw [mul_add]
    exact add_mem hq hr
  · intro c q _ hq
    have hsmul := Submodule.smul_mem
      (Submodule.span ℂ
        (Germ.jetMonomials n (N + 1) : Set (Germ n))) c hq
    simpa only [Algebra.smul_def, mul_assoc, mul_left_comm,
      mul_comm] using hsmul

/-- Every analytic germ has a representative in the span of
`jetMonomials n N` modulo the `N`th power of the maximal ideal. -/
theorem exists_jetApproximation (n N : ℕ) (g : Germ n) :
    ∃ p : Germ n,
      p ∈ Submodule.span ℂ (Germ.jetMonomials n N : Set (Germ n)) ∧
      g - p ∈ Germ.maximalIdeal n ^ N := by
  induction N generalizing g with
  | zero =>
      exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ N ih =>
      let c : ℂ := Germ.valueRingHom n g
      let g₀ : Germ n := g - Germ.constRingHom n c
      have hg₀ : g₀ ∈ Germ.maximalIdeal n := by
        rw [Germ.mem_maximalIdeal_iff]
        simp [g₀, c]
      rcases Germ.exists_eq_sum_coordinate_mul hg₀ with ⟨a, ha⟩
      choose p hpSpan hpRem using fun i : Fin n ↦ ih (a i)
      let P : Germ n := Germ.constRingHom n c +
        ∑ i, Germ.coordinate i * p i
      refine ⟨P, ?_, ?_⟩
      · apply Submodule.add_mem
        · change (algebraMap ℂ (Germ n)) c ∈
            Submodule.span ℂ
              (Germ.jetMonomials n (N + 1) : Set (Germ n))
          rw [← mul_one ((algebraMap ℂ (Germ n)) c),
            ← Algebra.smul_def]
          exact Submodule.smul_mem _ c
            (Submodule.subset_span (Germ.one_mem_jetMonomials_succ n N))
        · exact Submodule.sum_mem _ fun i _ ↦
            Germ.coordinate_mul_mem_span_jetMonomials_succ i (hpSpan i)
      · have hterms : ∀ i : Fin n,
            Germ.coordinate i * (a i - p i) ∈
              Germ.maximalIdeal n ^ (N + 1) := by
          intro i
          rw [pow_succ]
          have hmul := Ideal.mul_mem_mul (hpRem i)
            (Germ.coordinate_mem_maximalIdeal i)
          simpa only [mul_comm] using hmul
        have hsum :
            ∑ i, Germ.coordinate i * (a i - p i) ∈
              Germ.maximalIdeal n ^ (N + 1) :=
          Submodule.sum_mem _ fun i _ ↦ hterms i
        have hg : g = Germ.constRingHom n c +
            ∑ i, Germ.coordinate i * a i := by
          have hc : g = Germ.constRingHom n c + g₀ := by
            simp [g₀]
          rw [hc, ha]
        rw [hg]
        change Germ.constRingHom n c +
            ∑ i, Germ.coordinate i * a i -
              (Germ.constRingHom n c +
                ∑ i, Germ.coordinate i * p i) ∈
            Germ.maximalIdeal n ^ (N + 1)
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        simpa only [mul_sub] using hsum

/-- A quotient by an ideal that contains a power of the maximal ideal is a
finite dimensional complex vector space. -/
theorem quotient_moduleFinite_of_maximalIdeal_pow_le {n N : ℕ}
    (I : Ideal (Germ n)) (hpow : Germ.maximalIdeal n ^ N ≤ I) :
    Module.Finite ℂ (Germ n ⧸ I) := by
  let S : Submodule ℂ (Germ n) :=
    Submodule.span ℂ (Germ.jetMonomials n N : Set (Germ n))
  let _ : Module.Finite ℂ S :=
    Module.Finite.span_finset ℂ (Germ.jetMonomials n N)
  let quotientMap : S →ₗ[ℂ] (Germ n ⧸ I) :=
    (Ideal.Quotient.mkₐ ℂ I).toLinearMap.comp S.subtype
  apply Module.Finite.of_surjective quotientMap
  intro q
  rcases Ideal.Quotient.mk_surjective q with ⟨g, rfl⟩
  rcases Germ.exists_jetApproximation n N g with ⟨p, hp, hgp⟩
  refine ⟨⟨p, hp⟩, ?_⟩
  change Ideal.Quotient.mk I p = Ideal.Quotient.mk I g
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simpa only [neg_sub] using I.neg_mem (hpow hgp)

/-- A quotient of the analytic germ ring is finite dimensional exactly when
its defining ideal contains a power of the maximal ideal. -/
theorem quotient_moduleFinite_iff_exists_maximalIdeal_pow_le {n : ℕ}
    (I : Ideal (Germ n)) :
    Module.Finite ℂ (Germ n ⧸ I) ↔
      ∃ N : ℕ, Germ.maximalIdeal n ^ N ≤ I := by
  constructor
  · intro hfinite
    let _ : Module.Finite ℂ (Germ n ⧸ I) := hfinite
    let _ : IsArtinianRing (Germ n ⧸ I) :=
      IsArtinianRing.of_finite ℂ (Germ n ⧸ I)
    simpa only [Germ.maximalIdeal_eq_isLocalRing] using
      (IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I)
  · rintro ⟨N, hN⟩
    exact Germ.quotient_moduleFinite_of_maximalIdeal_pow_le I hN

end Germ

/-- The coordinate quotient of a finite pointed map germ is a finite
dimensional complex vector space. -/
theorem PointedMapGerm.coordinateQuotient_moduleFinite {n m : ℕ}
    (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin) :
    Module.Finite ℂ (Germ n ⧸ f.1.coordinateIdeal) := by
  rcases PointedMapGerm.exists_maximalIdeal_pow_le_coordinateIdeal
    f hfinite with ⟨N, hN⟩
  exact Germ.quotient_moduleFinite_of_maximalIdeal_pow_le
    f.1.coordinateIdeal hN

end OnLeConjecture.Analytic
