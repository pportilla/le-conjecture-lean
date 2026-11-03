/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.BranchOrderNumerics
public import OnLeConjecture.DTwo.CenteredIntersection
public import OnLeConjecture.DTwo.MapBranchOrders

/-!
# Numerical reduction for an order two map germ

This file derives the odd and even numerical alternatives directly from a
pointed map germ in quadratic normal form. The local intersection number is
taken before centering the chosen component.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic
open OnLeConjecture.PlaneCurve

namespace PointedMapGerm

/-- The odd numerical conclusion for a selected component of a pointed map
germ in quadratic normal form. -/
theorem odd_numerical_reduction_of_map_component
    (f : PointedMapGerm 2 3) {k a₁ m M : ℕ}
    (hkOdd : Odd k) (hk : 3 ≤ k) (ha₁ : a₁ ≤ k)
    (hM : M = 2 * k - 2 + a₁) (hm : k - 1 + a₁ ≤ m)
    (hfirst : f.1.component (0 : Fin 3) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ k)
    (hminors : ∀ i : Fin 2,
      Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        Germ.jacobian (f.1.component (0 : Fin 3))
          (f.1.component i.succ))
    (hdifferential : f.differential = 0)
    (i : Fin 2)
    (hfinite : HasFiniteIntersection (f.1.component (0 : Fin 3))
      (f.1.component i.succ))
    (hintersection : intersectionMultiplicity
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite = M)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) :
    a₁ = 0 ∧ m = k - 1 := by
  obtain ⟨A, B, hcomponent, _hbound, _hzero⟩ :=
    exists_odd_component_decomposition_and_branch_orders f
      hkOdd (by omega) hfirst hminors hdifferential epsilon hepsilon i
  let u : Germ 2 := Germ.quadraticBaseSubstitutionAlgHom k (by omega) A +
    Germ.coordinate (0 : Fin 2) *
      Germ.quadraticBaseSubstitutionAlgHom k (by omega) B
  have hu : f.1.component i.succ = u := hcomponent
  have huValue : Germ.valueRingHom 2 u = 0 := by
    rw [← hu, MapGerm.valueRingHom_component, f.2]
    rfl
  have hfinitePrepared :
      HasFiniteIntersection (Germ.quadraticBaseEquation k) u := by
    rw [Germ.quadraticBaseEquation, ← hfirst, ← hu]
    exact hfinite
  have hintersectionPrepared :
      intersectionMultiplicity (Germ.quadraticBaseEquation k) u
        hfinitePrepared = M := by
    simpa only [Germ.quadraticBaseEquation, hfirst, hu] using hintersection
  have hjacobian : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ k) u := by
    simpa only [hfirst, hu] using hminors i
  have huDifferential : Germ.differential u = 0 := by
    rw [← hu, MapGerm.germDifferential_component]
    exact (MapGerm.differential_eq_zero_iff f.1).mp hdifferential i.succ
  have hfiniteCentered :=
    Germ.hasFiniteIntersection_centeredQuadraticBaseDecomposition
      k (by omega) A B huValue hfinitePrepared
  have hintersectionCentered : intersectionMultiplicity
      (Germ.quadraticBaseEquation k)
      (Germ.centeredQuadraticBaseDecomposition k (by omega) A B)
        hfiniteCentered = M := by
    exact (Germ.intersectionMultiplicity_centeredQuadraticBaseDecomposition
      k (by omega) A B huValue hfinitePrepared).trans hintersectionPrepared
  exact odd_numerical_reduction_of_prepared_finite_intersection
    hkOdd hk ha₁ hM hm epsilon hepsilon A B hjacobian huDifferential
      hfiniteCentered hintersectionCentered

/-- The even numerical alternatives for a selected component of a pointed
map germ in quadratic normal form. -/
theorem even_numerical_alternatives_of_map_component
    (f : PointedMapGerm 2 3) {a a₁ m : ℕ}
    (ha : 1 ≤ a) (ha₁ : a₁ ≤ 2 * a)
    (hm : 2 * a + a₁ ≤ m)
    (hpolar : 2 * (m - 1) ≤ 6 * a + a₁ - 2)
    (hfirst : f.1.component (0 : Fin 3) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ (2 * a))
    (hminors : ∀ i : Fin 2,
      Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        Germ.jacobian (f.1.component (0 : Fin 3))
          (f.1.component i.succ))
    (hdifferential : f.differential = 0)
    (i : Fin 2)
    (hfinite : HasFiniteIntersection (f.1.component (0 : Fin 3))
      (f.1.component i.succ))
    (hintersection : intersectionMultiplicity
      (f.1.component (0 : Fin 3)) (f.1.component i.succ) hfinite =
        4 * a + a₁)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) :
    (a₁ = 0 ∧ m = 2 * a) ∨
      (a₁ = 2 * a ∧ m = 4 * a) := by
  obtain ⟨A, B, hcomponent, _hplus, _hminus, _hzero⟩ :=
    exists_even_component_decomposition_and_branch_orders f
      ha (by omega) hfirst hminors hdifferential epsilon hepsilon i
  let u : Germ 2 :=
    Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
      Germ.coordinate (0 : Fin 2) *
        Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B
  have hu : f.1.component i.succ = u := hcomponent
  have huValue : Germ.valueRingHom 2 u = 0 := by
    rw [← hu, MapGerm.valueRingHom_component, f.2]
    rfl
  have hfinitePrepared :
      HasFiniteIntersection (Germ.quadraticBaseEquation (2 * a)) u := by
    rw [Germ.quadraticBaseEquation, ← hfirst, ← hu]
    exact hfinite
  have hintersectionPrepared :
      intersectionMultiplicity (Germ.quadraticBaseEquation (2 * a)) u
        hfinitePrepared = 4 * a + a₁ := by
    simpa only [Germ.quadraticBaseEquation, hfirst, hu] using hintersection
  have hjacobian : Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
      Germ.jacobian
        (Germ.coordinate (0 : Fin 2) ^ 2 +
          Germ.coordinate (1 : Fin 2) ^ (2 * a)) u := by
    simpa only [hfirst, hu] using hminors i
  have hfiniteCentered :=
    Germ.hasFiniteIntersection_centeredQuadraticBaseDecomposition
      (2 * a) (by omega) A B huValue hfinitePrepared
  have hintersectionCentered : intersectionMultiplicity
      (Germ.quadraticBaseEquation (2 * a))
      (Germ.centeredQuadraticBaseDecomposition (2 * a) (by omega) A B)
        hfiniteCentered = 4 * a + a₁ := by
    exact (Germ.intersectionMultiplicity_centeredQuadraticBaseDecomposition
      (2 * a) (by omega) A B huValue hfinitePrepared).trans
        hintersectionPrepared
  exact even_numerical_alternatives_of_prepared_finite_intersection
    ha ha₁ hm hpolar epsilon hepsilon A B hjacobian hfiniteCentered
      hintersectionCentered

end PointedMapGerm

end OnLeConjecture.DTwo
