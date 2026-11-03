/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Birational
public import OnLeConjecture.Analytic.PlaneInjectiveFiniteness

/-!
# The meromorphic descent criterion for birationality

Birationality of a pointed analytic map germ is equivalent to meromorphic
descent of every scalar source germ to the analytic image ring. This module
proves the algebraic equivalence and records the analytic descent principle
needed to deduce birationality from an injective representative.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- Every scalar source germ is a quotient of two elements of the analytic
image ring. The equation is written without fractions in the source ring. -/
@[expose] def HasMeromorphicDescent {n m : ℕ} (f : PointedMapGerm n m) : Prop :=
  ∀ a : Germ n, ∃ p q : f.ImageRing,
    q ≠ 0 ∧ (q : Germ n) * a = (p : Germ n)

/-- Meromorphic descent can be stated using scalar target germs and the
pullback homomorphism. -/
theorem hasMeromorphicDescent_iff_pullback_crossMultiplication {n m : ℕ}
    (f : PointedMapGerm n m) :
    f.HasMeromorphicDescent ↔
      ∀ a : Germ n, ∃ p q : Germ m,
        f.pullbackRingHom q ≠ 0 ∧
          f.pullbackRingHom q * a = f.pullbackRingHom p := by
  constructor
  · intro h a
    obtain ⟨p, q, hq, hcross⟩ := h a
    obtain ⟨pTarget, rfl⟩ := f.pullbackToImageRing_surjective p
    obtain ⟨qTarget, rfl⟩ := f.pullbackToImageRing_surjective q
    refine ⟨pTarget, qTarget, ?_, ?_⟩
    · simpa only [ne_eq, Subtype.ext_iff, coe_pullbackToImageRing,
        Subring.coe_zero] using hq
    · simpa only [coe_pullbackToImageRing] using hcross
  · intro h a
    obtain ⟨p, q, hq, hcross⟩ := h a
    refine ⟨f.pullbackToImageRing p, f.pullbackToImageRing q, ?_, ?_⟩
    · simpa only [ne_eq, Subtype.ext_iff, coe_pullbackToImageRing,
        Subring.coe_zero] using hq
    · simpa only [coe_pullbackToImageRing] using hcross

/-- Surjectivity of the fraction field map can be checked on scalar source
germs. -/
theorem isBirationalAtOrigin_iff_algebraMap_lifts {n m : ℕ}
    (f : PointedMapGerm n m) :
    f.IsBirationalAtOrigin ↔
      ∀ a : Germ n, ∃ x : FractionRing f.ImageRing,
        f.fractionFieldMap x =
          algebraMap (Germ n) (FractionRing (Germ n)) a := by
  constructor
  · intro h a
    exact h (algebraMap (Germ n) (FractionRing (Germ n)) a)
  · intro h z
    obtain ⟨a, b, _, hab⟩ :=
      IsFractionRing.div_surjective (Germ n) z
    obtain ⟨x, hx⟩ := h a
    obtain ⟨y, hy⟩ := h b
    refine ⟨x / y, ?_⟩
    rw [map_div₀, hx, hy, hab]

/-- Meromorphic descent is equivalent to lifting each scalar source germ to
the fraction field of the image ring. -/
theorem hasMeromorphicDescent_iff_algebraMap_lifts {n m : ℕ}
    (f : PointedMapGerm n m) :
    f.HasMeromorphicDescent ↔
      ∀ a : Germ n, ∃ x : FractionRing f.ImageRing,
        f.fractionFieldMap x =
          algebraMap (Germ n) (FractionRing (Germ n)) a := by
  constructor
  · intro h a
    obtain ⟨p, q, hq, hcross⟩ := h a
    refine ⟨algebraMap f.ImageRing (FractionRing f.ImageRing) p /
        algebraMap f.ImageRing (FractionRing f.ImageRing) q, ?_⟩
    rw [map_div₀, f.fractionFieldMap_algebraMap,
      f.fractionFieldMap_algebraMap]
    have hqSource : (q : Germ n) ≠ 0 := by
      intro hqZero
      apply hq
      exact Subtype.ext hqZero
    have hqFraction :
        algebraMap (Germ n) (FractionRing (Germ n)) (q : Germ n) ≠ 0 :=
      by
        simpa only [map_zero] using
          (IsFractionRing.injective (Germ n)
            (FractionRing (Germ n))).ne hqSource
    apply (div_eq_iff hqFraction).2
    simpa only [map_mul, mul_comm] using congrArg
      (algebraMap (Germ n) (FractionRing (Germ n))) hcross.symm
  · intro h a
    obtain ⟨x, hx⟩ := h a
    obtain ⟨p, q, hqRegular, hpq⟩ :=
      IsFractionRing.div_surjective f.ImageRing x
    have hq : q ≠ 0 :=
      mem_nonZeroDivisors_iff_ne_zero.mp hqRegular
    have hqSource : (q : Germ n) ≠ 0 := by
      intro hqZero
      apply hq
      exact Subtype.ext hqZero
    have hqFraction :
        algebraMap (Germ n) (FractionRing (Germ n)) (q : Germ n) ≠ 0 :=
      by
        simpa only [map_zero] using
          (IsFractionRing.injective (Germ n)
            (FractionRing (Germ n))).ne hqSource
    have hpqMapped := congrArg f.fractionFieldMap hpq
    rw [map_div₀, f.fractionFieldMap_algebraMap,
      f.fractionFieldMap_algebraMap, hx] at hpqMapped
    have hcrossFraction := (div_eq_iff hqFraction).1 hpqMapped
    have hcrossSource : (p : Germ n) = a * (q : Germ n) :=
      (IsFractionRing.injective (Germ n) (FractionRing (Germ n))) (by
        simpa only [map_mul] using hcrossFraction)
    exact ⟨p, q, hq, by simpa only [mul_comm] using hcrossSource.symm⟩

/-- A pointed analytic map germ is birational exactly when every scalar
source germ has meromorphic descent to its analytic image ring. -/
theorem isBirationalAtOrigin_iff_hasMeromorphicDescent {n m : ℕ}
    (f : PointedMapGerm n m) :
    f.IsBirationalAtOrigin ↔ f.HasMeromorphicDescent := by
  rw [isBirationalAtOrigin_iff_algebraMap_lifts,
    hasMeromorphicDescent_iff_algebraMap_lifts]

/-- Birationality is equivalent to expressing every scalar source germ as a
quotient of pullbacks of scalar target germs. -/
theorem isBirationalAtOrigin_iff_pullback_crossMultiplication {n m : ℕ}
    (f : PointedMapGerm n m) :
    f.IsBirationalAtOrigin ↔
      ∀ a : Germ n, ∃ p q : Germ m,
        f.pullbackRingHom q ≠ 0 ∧
          f.pullbackRingHom q * a = f.pullbackRingHom p := by
  rw [isBirationalAtOrigin_iff_hasMeromorphicDescent,
    hasMeromorphicDescent_iff_pullback_crossMultiplication]

/-- This proposition is the analytic input that is not supplied by the current
germ API. It says that a finite analytic map germ with an injective
representative has meromorphic descent to its analytic image ring. -/
def FiniteInjectiveImpliesMeromorphicDescent (n m : ℕ) : Prop :=
  ∀ f : PointedMapGerm n m,
    f.IsFiniteAtOrigin → f.HasInjectiveRepresentative →
      f.HasMeromorphicDescent

/-- The finite injective meromorphic descent implication yields birationality
for a finite map germ with an injective representative. -/
theorem isBirationalAtOrigin_of_finite_of_injective_of_descent
    {n m : ℕ} (hdescent : FiniteInjectiveImpliesMeromorphicDescent n m)
    (f : PointedMapGerm n m) (hfinite : f.IsFiniteAtOrigin)
    (hinjective : f.HasInjectiveRepresentative) :
    f.IsBirationalAtOrigin :=
  (f.isBirationalAtOrigin_iff_hasMeromorphicDescent).2
    (hdescent f hfinite hinjective)

/-- In source dimension two and target dimension three, existing finiteness
reduces the injective to birational implication to the finite injective
meromorphic descent implication. -/
theorem isBirationalAtOrigin_two_three_of_injective_of_descent
    (hdescent : FiniteInjectiveImpliesMeromorphicDescent 2 3)
    (f : PointedMapGerm 2 3)
    (hinjective : f.HasInjectiveRepresentative) :
    f.IsBirationalAtOrigin := by
  apply isBirationalAtOrigin_of_finite_of_injective_of_descent hdescent f
  · exact f.injective_isFiniteAtOrigin_two_three hinjective
  · exact hinjective

end PointedMapGerm

end OnLeConjecture.Analytic
