/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.SimpleZeroPersistence
public import OnLeConjecture.DThree.ResidueMonomialTransversality

/-!
# Persistence of the residual collisions

This file applies persistence of a simple zero to parameter families whose
fiber at parameter zero is one of the residual affine difference maps.  The
resulting branch remains a collision of two distinct source points for all
parameters in a neighborhood of zero.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DThree

/-- Distinct coordinates remain distinct along a branch converging in a
finite product. -/
theorem eventually_coordinates_ne_of_tendsto
    {branch : ℂ → (Fin 3 → ℂ)} {p : Fin 3 → ℂ}
    (hbranch : Tendsto branch (nhds 0) (nhds p))
    (hp : p 0 ≠ p 1) :
    ∀ᶠ lambda in nhds 0, branch lambda 0 ≠ branch lambda 1 := by
  have hfirst :
      Tendsto (fun lambda => branch lambda 0) (nhds 0) (nhds (p 0)) :=
    tendsto_pi_nhds.mp hbranch 0
  have hsecond :
      Tendsto (fun lambda => branch lambda 1) (nhds 0) (nhds (p 1)) :=
    tendsto_pi_nhds.mp hbranch 1
  have hdifference :
      Tendsto (fun lambda => branch lambda 0 - branch lambda 1)
        (nhds 0) (nhds (p 0 - p 1)) :=
    hfirst.sub hsecond
  simpa [sub_ne_zero] using
    hdifference.eventually_ne (sub_ne_zero.mpr hp)

/-- A strictly differentiable perturbation of the `E` difference map has a
local branch of distinct collisions through every affine collision
certificate. -/
theorem exists_eResidueCollisionBranch
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (eResidueAffineDifferenceMap a M c) eResidueTransverseDeterminant)
    (Phi : ℂ × (Fin 3 → ℂ) → (Fin 3 → ℂ))
    (Phi' : ℂ × (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))
    (hPhi : HasStrictFDerivAt Phi Phi'
      (0, ![C.firstCoordinate, C.secondCoordinate, 1]))
    (hzeroFiber : ∀ q, Phi (0, q) = eResidueAffineDifferenceMap a M c q)
    (hpoint :
      Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) =
        (eResidueAffineDerivativeEquiv a M c
          C.firstCoordinate C.secondCoordinate
          C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero :
            (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))) :
    ∃ branch : ℂ → (Fin 3 → ℂ),
      branch 0 = ![C.firstCoordinate, C.secondCoordinate, 1] ∧
      Tendsto branch (nhds 0)
        (nhds ![C.firstCoordinate, C.secondCoordinate, 1]) ∧
      (∀ᶠ lambda in nhds 0, Phi (lambda, branch lambda) = 0) ∧
      ∀ᶠ lambda in nhds 0, branch lambda 0 ≠ branch lambda 1 := by
  let p : Fin 3 → ℂ := ![C.firstCoordinate, C.secondCoordinate, 1]
  have hzero : Phi (0, p) = 0 := by
    rw [hzeroFiber]
    exact C.difference_eq_zero
  obtain ⟨branch, hbranchZero, hbranchTendsto, hbranchEquation⟩ :=
    OnLeConjecture.Analytic.exists_finThreeSimpleZeroBranch
      Phi p Phi'
        (eResidueAffineDerivativeEquiv a M c
          C.firstCoordinate C.secondCoordinate
          C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero)
        hzero hPhi hpoint
  refine ⟨branch, hbranchZero, hbranchTendsto, hbranchEquation, ?_⟩
  exact eventually_coordinates_ne_of_tendsto hbranchTendsto C.coordinates_ne

/-- A strictly differentiable perturbation of the `H` difference map has a
local branch of distinct collisions through every affine collision
certificate. -/
theorem exists_hResidueCollisionBranch
    (a M : ℕ) (c : ℂ)
    (C : ResidueAffineCollisionCertificate M c
      (hResidueAffineDifferenceMap a M c) hResidueTransverseDeterminant)
    (Phi : ℂ × (Fin 3 → ℂ) → (Fin 3 → ℂ))
    (Phi' : ℂ × (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))
    (hPhi : HasStrictFDerivAt Phi Phi'
      (0, ![C.firstCoordinate, C.secondCoordinate, 1]))
    (hzeroFiber : ∀ q, Phi (0, q) = hResidueAffineDifferenceMap a M c q)
    (hpoint :
      Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 3 → ℂ) =
        (hResidueAffineDerivativeEquiv a M c
          C.firstCoordinate C.secondCoordinate
          C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero :
            (Fin 3 → ℂ) →L[ℂ] (Fin 3 → ℂ))) :
    ∃ branch : ℂ → (Fin 3 → ℂ),
      branch 0 = ![C.firstCoordinate, C.secondCoordinate, 1] ∧
      Tendsto branch (nhds 0)
        (nhds ![C.firstCoordinate, C.secondCoordinate, 1]) ∧
      (∀ᶠ lambda in nhds 0, Phi (lambda, branch lambda) = 0) ∧
      ∀ᶠ lambda in nhds 0, branch lambda 0 ≠ branch lambda 1 := by
  let p : Fin 3 → ℂ := ![C.firstCoordinate, C.secondCoordinate, 1]
  have hzero : Phi (0, p) = 0 := by
    rw [hzeroFiber]
    exact C.difference_eq_zero
  obtain ⟨branch, hbranchZero, hbranchTendsto, hbranchEquation⟩ :=
    OnLeConjecture.Analytic.exists_finThreeSimpleZeroBranch
      Phi p Phi'
        (hResidueAffineDerivativeEquiv a M c
          C.firstCoordinate C.secondCoordinate
          C.transverseDeterminant_ne_zero C.thirdDerivative_ne_zero)
        hzero hPhi hpoint
  refine ⟨branch, hbranchZero, hbranchTendsto, hbranchEquation, ?_⟩
  exact eventually_coordinates_ne_of_tendsto hbranchTendsto C.coordinates_ne

end OnLeConjecture.DThree
