/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.TargetLinearSpan
public import OnLeConjecture.Analytic.CriticalJacobianDivisor
public import OnLeConjecture.Analytic.JacobianLinearSpan

/-!
# The critical divisor under linear target changes

Equality of the component spans preserves every common Jacobian divisor,
including each exact power. A factorization can therefore be transported
with the same factors and orders. This retains the original critical bound
when a generic linear form becomes the first target coordinate.
-/

public noncomputable section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

theorem common_jacobian_dvd_iff_of_span_eq {ι κ : Type*}
    (F : ι → Germ 2) (G : κ → Germ 2)
    (hspan : Submodule.span ℂ (Set.range F) = Submodule.span ℂ (Set.range G))
    (d : Germ 2) :
    (∀ i j, d ∣ jacobian (F i) (F j)) ↔ ∀ i j, d ∣ jacobian (G i) (G j) := by
  constructor
  · intro h i j
    apply dvd_jacobian_of_mem_linear_span F d h
    · rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self i)
    · rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self j)
  · intro h i j
    apply dvd_jacobian_of_mem_linear_span G d h
    · rw [← hspan]
      exact Submodule.subset_span (Set.mem_range_self i)
    · rw [← hspan]
      exact Submodule.subset_span (Set.mem_range_self j)

namespace CriticalJacobianFactorization

/-- Transport retains every factor and its order, not merely the maximum. -/
@[expose] def of_component_span_eq {g : PointedMapGerm 2 3}
    (D : CriticalJacobianFactorization g) (f : PointedMapGerm 2 3)
    (hspan : Submodule.span ℂ (Set.range f.1.component) =
      Submodule.span ℂ (Set.range g.1.component)) : CriticalJacobianFactorization f where
  support := D.support
  order := D.order
  irreducible := D.irreducible
  order_pos := D.order_pos
  component_mem := D.component_mem
  pairwise_not_associated := D.pairwise_not_associated
  common_dvd_iff d := (D.common_dvd_iff d).trans
    (common_jacobian_dvd_iff_of_span_eq g.1.component f.1.component hspan.symm d)
  order_maximal p hp n :=
    (common_jacobian_dvd_iff_of_span_eq f.1.component g.1.component hspan (p ^ n)).trans
      (D.order_maximal p hp n)

theorem of_component_span_eq_maxMultiplicity {g : PointedMapGerm 2 3}
    (D : CriticalJacobianFactorization g) (f : PointedMapGerm 2 3)
    (hspan : Submodule.span ℂ (Set.range f.1.component) =
      Submodule.span ℂ (Set.range g.1.component)) :
    (D.of_component_span_eq f hspan).maxMultiplicity = D.maxMultiplicity := rfl

end CriticalJacobianFactorization

theorem PointedMapGerm.criticalJacobian_maxMultiplicity_eq_of_span_eq
    (g f : PointedMapGerm 2 3) (hg : g.HasInjectiveRepresentative)
    (hf : f.HasInjectiveRepresentative)
    (hspan : Submodule.span ℂ (Set.range f.1.component) =
      Submodule.span ℂ (Set.range g.1.component)) :
    (f.criticalJacobianFactorization hf).maxMultiplicity =
      (g.criticalJacobianFactorization hg).maxMultiplicity :=
  (f.criticalJacobianFactorization hf).maxMultiplicity_eq
    ((g.criticalJacobianFactorization hg).of_component_span_eq f hspan)

end OnLeConjecture.Analytic
