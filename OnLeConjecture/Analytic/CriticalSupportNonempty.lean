/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ImageConductorCriticalSupport
public import OnLeConjecture.Analytic.HypersurfaceRegularPair
public import OnLeConjecture.Analytic.CriticalDivisorZeroSet

/-!
# A nonimmersive injective surface germ has a critical curve

If the common Jacobian divisor has empty support, the coordinate-critical
ideal has finite colength. Equality of its radical with the conductor
radical then puts a power of the source maximal ideal in the conductor.
The regular pair in the hypersurface image ring forces the map to be an
immersion. Consequently every nonimmersive injective plane germ in
three-space has a nonempty critical-divisor support.
-/

public noncomputable section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- For a finite injective plane germ, finite colength of the critical
ideal implies finite colength of the conductor. -/
theorem conductor_quotient_finite_of_coordinateMinor_quotient_finite
    {m : ℕ} (g : PointedMapGerm 2 m) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative)
    (hcritical : Module.Finite ℂ (Germ 2 ⧸ g.coordinateMinorIdeal)) :
    Module.Finite ℂ (Germ 2 ⧸ g.imageConductor) := by
  obtain ⟨N, hN⟩ :=
    (Germ.quotient_moduleFinite_iff_exists_maximalIdeal_pow_le g.coordinateMinorIdeal).mp
      hcritical
  apply (Germ.quotient_moduleFinite_iff_exists_maximalIdeal_pow_le g.imageConductor).mpr
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · rw [g.radical_imageConductor_eq_radical_coordinateMinorIdeal hf hi]
    intro a ha
    exact ⟨N, hN (Ideal.pow_mem_pow ha N)⟩
  · exact Germ.maximalIdeal_fg 2

/-- Finite colength of the coordinate-critical ideal forces a finite
injective plane germ in three-space to be an immersion. -/
theorem differential_injective_of_finite_coordinateMinor_quotient
    (g : PointedMapGerm 2 3) (hf : g.IsFiniteAtOrigin)
    (hi : g.HasInjectiveRepresentative)
    (hcritical : Module.Finite ℂ (Germ 2 ⧸ g.coordinateMinorIdeal)) :
    Function.Injective g.differential := by
  obtain ⟨N, hN⟩ :=
    (Germ.quotient_moduleFinite_iff_exists_maximalIdeal_pow_le g.coordinateMinorIdeal).mp
      hcritical
  apply g.differential_injective_of_finite_of_maximalIdeal_le_conductor_radical hf
  rw [g.radical_imageConductor_eq_radical_coordinateMinorIdeal hf hi]
  intro a ha
  exact ⟨N, hN (Ideal.pow_mem_pow ha N)⟩

end PointedMapGerm

namespace CriticalJacobianFactorization

variable {g : PointedMapGerm 2 3} (D : CriticalJacobianFactorization g)

/-- Empty critical-divisor support makes the ideal of all coordinate
Jacobians have finite colength. -/
theorem coordinateMinor_quotient_finite_of_support_eq_empty
    (hempty : D.support = ∅) :
    Module.Finite ℂ (Germ 2 ⧸ g.coordinateMinorIdeal) := by
  obtain ⟨R, hR, hfinite⟩ := D.exists_residual_minors_finite_colength
  have heq : (fun ij : Fin 3 × Fin 3 =>
      Germ.jacobian (g.1.component ij.1) (g.1.component ij.2)) = R := by
    funext ij
    simpa only [divisor, hempty, Finset.prod_empty, one_mul] using hR ij.1 ij.2
  have hideal : g.coordinateMinorIdeal = Ideal.span (Set.range R) :=
    congrArg (fun F => Ideal.span (Set.range F)) heq
  rw [hideal]
  exact hfinite

/-- An injective plane germ in three-space with empty critical-divisor
support is an immersion. -/
theorem differential_injective_of_support_eq_empty
    (hi : g.HasInjectiveRepresentative) (hempty : D.support = ∅) :
    Function.Injective g.differential := by
  exact g.differential_injective_of_finite_coordinateMinor_quotient
    (g.injective_isFiniteAtOrigin_two hi) hi
    (D.coordinateMinor_quotient_finite_of_support_eq_empty hempty)

/-- Every nonimmersive injective plane germ in three-space has a common
irreducible factor of its coordinate Jacobians. -/
theorem support_nonempty_of_not_differential_injective
    (hi : g.HasInjectiveRepresentative) (hd : ¬ Function.Injective g.differential) :
    D.support.Nonempty := by
  by_contra h
  exact hd (D.differential_injective_of_support_eq_empty hi
    (Finset.not_nonempty_iff_eq_empty.mp h))

/-- A zero differential forces nonempty critical-divisor support for an
injective plane germ in three-space. -/
theorem support_nonempty_of_differential_eq_zero
    (hi : g.HasInjectiveRepresentative) (hd : g.differential = 0) :
    D.support.Nonempty := by
  apply D.support_nonempty_of_not_differential_injective hi
  intro hinj
  have h : (1 : Source 2) = 0 := hinj (by rw [hd]; rfl)
  exact one_ne_zero h

/-- In the zero-differential case the maximal transverse multiplicity
constructed from the common Jacobian orders is at least two. -/
theorem two_le_maxMultiplicity_of_differential_eq_zero
    (hi : g.HasInjectiveRepresentative) (hd : g.differential = 0) :
    2 ≤ D.maxMultiplicity := by
  obtain ⟨p, hp⟩ := D.support_nonempty_of_differential_eq_zero hi hd
  have hle : D.order p + 1 ≤ D.maxMultiplicity :=
    Finset.le_sup (f := fun p => D.order p + 1) hp
  have hpos := D.order_pos p hp
  omega

end CriticalJacobianFactorization

namespace PointedMapGerm

/-- The canonical critical-divisor factorization of an injective plane
germ has nonempty support if the differential vanishes. -/
theorem criticalJacobianFactorization_support_nonempty
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (hd : g.differential = 0) :
    (g.criticalJacobianFactorization hi).support.Nonempty :=
  (g.criticalJacobianFactorization hi).support_nonempty_of_differential_eq_zero hi hd

end PointedMapGerm

end OnLeConjecture.Analytic
