/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.AnalyticBranchPullback
public import OnLeConjecture.Analytic.Jet

/-!
# Branch orders for a quadratic map germ

This file applies the analytic quadratic decomposition and coefficient
recurrence to the second and third components of a pointed map germ whose
first component is `x² + yᵏ`.
-/

public section

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic

namespace PointedMapGerm

/-- For odd `k`, every remaining component admits a quadratic base
decomposition whose centered restriction has the branch order from the
coefficient recurrence. The zero quotient case has the stronger order
forced by the zero differential. -/
theorem exists_odd_component_decomposition_and_branch_orders
    (f : PointedMapGerm 2 3) {k m : ℕ}
    (hkOdd : Odd k) (hm : 1 ≤ m)
    (hfirst : f.1.component (0 : Fin 3) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ k)
    (hminors : ∀ i : Fin 2,
      Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        Germ.jacobian (f.1.component (0 : Fin 3))
          (f.1.component i.succ))
    (hdifferential : f.differential = 0)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) :
    ∀ i : Fin 2, ∃ A B : Germ 2,
      f.1.component i.succ =
          Germ.quadraticBaseSubstitutionAlgHom k (by
            obtain ⟨r, hr⟩ := hkOdd
            omega) A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k (by
            obtain ⟨r, hr⟩ := hkOdd
            omega) B ∧
      ((min (2 * m) ((2 * ((m - 1) / k) + 1) * k) : ℕ) : ℕ∞) ≤
        Germ.vanishingOrder
          ((Germ.oddQuadraticBranchMapGerm k (by
              obtain ⟨r, hr⟩ := hkOdd
              omega) epsilon).pullbackRingHom
            (Germ.centeredQuadraticBaseDecomposition k (by
              obtain ⟨r, hr⟩ := hkOdd
              omega) A B)) ∧
      ((m - 1) / k = 0 →
        ((2 * m : ℕ) : ℕ∞) ≤
          Germ.vanishingOrder
            ((Germ.oddQuadraticBranchMapGerm k (by
                obtain ⟨r, hr⟩ := hkOdd
                omega) epsilon).pullbackRingHom
              (Germ.centeredQuadraticBaseDecomposition k (by
                obtain ⟨r, hr⟩ := hkOdd
                omega) A B))) := by
  let hk : 1 ≤ k := by
    obtain ⟨r, hr⟩ := hkOdd
    omega
  intro i
  obtain ⟨p, hp, _hpUnique⟩ :=
    Germ.existsUnique_quadraticBase_decomposition k hk
      (f.1.component i.succ)
  rcases p with ⟨A, B⟩
  have hminor := hminors i
  rw [hfirst, hp] at hminor
  have hcomponentDifferential :
      Germ.differential (f.1.component i.succ) = 0 := by
    rw [MapGerm.germDifferential_component]
    exact (MapGerm.differential_eq_zero_iff f.1).mp hdifferential i.succ
  have hdecompositionDifferential : Germ.differential
      (Germ.quadraticBaseSubstitutionAlgHom k hk A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom k hk B) = 0 := by
    rw [← hp]
    exact hcomponentDifferential
  refine ⟨A, B, hp, ?_, ?_⟩
  · exact Germ.oddQuadraticBranch_centered_vanishingOrder_of_jacobian_dvd
      hkOdd hm epsilon hepsilon A B hminor
  · intro hquotient
    exact Germ.oddQuadraticBranch_centered_vanishingOrder_of_div_eq_zero
      hkOdd hm epsilon hepsilon A B hquotient hminor
        hdecompositionDifferential

/-- For even `k = 2a`, every remaining component admits a quadratic base
decomposition whose centered restriction has the same order bound on both
branches. The zero quotient case has order at least `m` on both branches. -/
theorem exists_even_component_decomposition_and_branch_orders
    (f : PointedMapGerm 2 3) {a m : ℕ}
    (ha : 1 ≤ a) (hm : 1 ≤ m)
    (hfirst : f.1.component (0 : Fin 3) =
      Germ.coordinate (0 : Fin 2) ^ 2 +
        Germ.coordinate (1 : Fin 2) ^ (2 * a))
    (hminors : ∀ i : Fin 2,
      Germ.coordinate (1 : Fin 2) ^ (m - 1) ∣
        Germ.jacobian (f.1.component (0 : Fin 3))
          (f.1.component i.succ))
    (hdifferential : f.differential = 0)
    (epsilon : ℂ) (hepsilon : epsilon ^ 2 = -1) :
    ∀ i : Fin 2, ∃ A B : Germ 2,
      f.1.component i.succ =
          Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B ∧
      let bound : ℕ∞ :=
        (min m (a + ((m - 1) / (2 * a)) * (2 * a)) : ℕ)
      bound ≤ Germ.vanishingOrder
          ((Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
            (Germ.centeredQuadraticBaseDecomposition
              (2 * a) (by omega) A B)) ∧
        bound ≤ Germ.vanishingOrder
          ((Germ.evenQuadraticBranchMapGerm a ha (-epsilon)).pullbackRingHom
            (Germ.centeredQuadraticBaseDecomposition
              (2 * a) (by omega) A B)) ∧
        ((m - 1) / (2 * a) = 0 →
          (m : ℕ∞) ≤ Germ.vanishingOrder
              ((Germ.evenQuadraticBranchMapGerm a ha epsilon).pullbackRingHom
                (Germ.centeredQuadraticBaseDecomposition
                  (2 * a) (by omega) A B)) ∧
            (m : ℕ∞) ≤ Germ.vanishingOrder
              ((Germ.evenQuadraticBranchMapGerm a ha
                  (-epsilon)).pullbackRingHom
                (Germ.centeredQuadraticBaseDecomposition
                  (2 * a) (by omega) A B))) := by
  intro i
  obtain ⟨p, hp, _hpUnique⟩ :=
    Germ.existsUnique_quadraticBase_decomposition (2 * a) (by omega)
      (f.1.component i.succ)
  rcases p with ⟨A, B⟩
  have hminor := hminors i
  rw [hfirst, hp] at hminor
  have hcomponentDifferential :
      Germ.differential (f.1.component i.succ) = 0 := by
    rw [MapGerm.germDifferential_component]
    exact (MapGerm.differential_eq_zero_iff f.1).mp hdifferential i.succ
  have hdecompositionDifferential : Germ.differential
      (Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) A +
        Germ.coordinate (0 : Fin 2) *
          Germ.quadraticBaseSubstitutionAlgHom (2 * a) (by omega) B) = 0 := by
    rw [← hp]
    exact hcomponentDifferential
  have hbounds :=
    Germ.evenQuadraticBranches_centered_vanishingOrder_of_jacobian_dvd
      ha hm epsilon hepsilon A B hminor
  refine ⟨A, B, hp, hbounds.1, hbounds.2, ?_⟩
  intro hquotient
  exact Germ.evenQuadraticBranches_centered_vanishingOrder_of_div_eq_zero
    ha hm epsilon hepsilon A B hquotient hminor
      hdecompositionDifferential

end PointedMapGerm

end OnLeConjecture.DTwo
