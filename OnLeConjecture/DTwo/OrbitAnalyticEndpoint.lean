/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.OrbitAnalyticNoninjectivityAssembly

/-!
# Endpoint for the analytic quadratic orbit contradiction

This module packages the normalized plane coordinates and the two minor
divisibilities used by the analytic orbit assembly.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic

/-- The normalized analytic data required by the quadratic orbit endpoint. -/
structure OrbitAnalyticEndpoint (F : PointedMapGerm 2 3) where
  plane : PointedMapGerm 2 2
  finite : plane.IsFiniteAtOrigin
  component_zero : F.1.component 0 = plane.1.component 0
  component_one : F.1.component 1 = plane.1.component 1
  phi_tail : plane.1.component 0 -
      Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPhi ℂ) ∈
    Germ.maximalIdeal 2 ^ 3
  psi_tail : plane.1.component 1 -
      Germ.coordinatePolynomialAlgHom 2 (orbitPolynomialPsi ℂ) ∈
    Germ.maximalIdeal 2 ^ 4
  third_order : F.1.component 2 ∈ Germ.maximalIdeal 2 ^ 4
  minor_twelve : Germ.coordinate (1 : Fin 2) ^ 3 ∣
    Germ.jacobian (plane.1.component 0) (plane.1.component 1)
  minor_thirteen : Germ.coordinate (1 : Fin 2) ^ 3 ∣
    Germ.jacobian (plane.1.component 0) (F.1.component 2)

namespace OrbitAnalyticEndpoint

/-- The analytic quadratic orbit endpoint excludes an injective
representative. -/
theorem not_hasInjectiveRepresentative
    {F : PointedMapGerm 2 3} (data : OrbitAnalyticEndpoint F) :
    ¬ F.HasInjectiveRepresentative := by
  exact orbitNormalizedPointedMap_not_hasInjectiveRepresentative
    F data.plane data.finite data.component_zero data.component_one
      data.phi_tail data.psi_tail data.third_order data.minor_twelve
        data.minor_thirteen

end OrbitAnalyticEndpoint

end OnLeConjecture.DTwo
