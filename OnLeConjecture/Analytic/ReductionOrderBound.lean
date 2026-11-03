/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LeConjecturePlaneAssembly
public import OnLeConjecture.Numerical.ProximityReduction

/-!
# The coordinate order bound from proximity data

This module identifies the root entry of a connected proximity certificate
with the order of the coordinate ideal. The global and polar inequalities
then imply that this order is two, three, or four.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Numerical

namespace PointedMapGerm

/-- Proximity and intersection data used in the reduction theorem for a
finite plane map germ. -/
structure CoordinateOrderReductionData
    (f : PointedMapGerm 2 3) (hfinite : f.IsFiniteAtOrigin) where
  N : ℕ
  certificate : ProximityCertificate (Fin N)
  connected : ∀ q,
    Relation.ReflTransGen certificate.ParentRelation q certificate.root
  m : ℕ
  n : ℕ
  coordinateOrder_eq_root :
    f.coordinateOrder (by omega) hfinite =
      certificate.multiplicity certificate.root
  branchCount_positive : 1 ≤ certificate.branchCount
  global_estimate :
    certificate.squareMultiplicity + certificate.totalMultiplicity ≤ 3 * m
  root_le_n : certificate.multiplicity certificate.root ≤ n
  polar_estimate :
    n * (m - 1) + certificate.totalMultiplicity + certificate.branchCount ≤
      2 * certificate.squareMultiplicity

namespace CoordinateOrderReductionData

/-- Vanishing of the differential makes the root entry at least two. -/
theorem two_le_root
    {f : PointedMapGerm 2 3} {hfinite : f.IsFiniteAtOrigin}
    (data : CoordinateOrderReductionData f hfinite)
    (hdifferential : f.differential = 0) :
    2 ≤ data.certificate.multiplicity data.certificate.root := by
  rw [← data.coordinateOrder_eq_root]
  exact f.two_le_coordinateOrder_of_differential_eq_zero
    (by omega) hfinite hdifferential

/-- The reduction estimates force the coordinate ideal order to be at most
four. -/
theorem coordinateOrder_le_four
    {f : PointedMapGerm 2 3} {hfinite : f.IsFiniteAtOrigin}
    (data : CoordinateOrderReductionData f hfinite)
    (hdifferential : f.differential = 0) :
    f.coordinateOrder (by omega) hfinite ≤ 4 := by
  rw [data.coordinateOrder_eq_root]
  exact data.certificate.root_multiplicity_le_four_of_estimates
    data.connected data.m data.n (data.two_le_root hdifferential)
      data.branchCount_positive data.global_estimate data.root_le_n
        data.polar_estimate

/-- The only possible coordinate ideal orders are two, three, and four. -/
theorem coordinateOrder_eq_two_or_three_or_four
    {f : PointedMapGerm 2 3} {hfinite : f.IsFiniteAtOrigin}
    (data : CoordinateOrderReductionData f hfinite)
    (hdifferential : f.differential = 0) :
    f.coordinateOrder (by omega) hfinite = 2 ∨
      f.coordinateOrder (by omega) hfinite = 3 ∨
        f.coordinateOrder (by omega) hfinite = 4 := by
  have hcases :=
    data.certificate.root_multiplicity_eq_two_or_three_or_four_of_estimates
      data.connected data.m data.n (data.two_le_root hdifferential)
        data.branchCount_positive data.global_estimate data.root_le_n
          data.polar_estimate
  rw [← data.coordinateOrder_eq_root] at hcases
  exact hcases

end CoordinateOrderReductionData

/-- The existence of the reduction data for every hypothetical injective
germ, together with the three case exclusions, implies Lê's conjecture. -/
theorem leConjecture_of_reductionData_and_caseExclusions
    (hdata : ∀ (f : PointedMapGerm 2 3)
      (hfinite : f.IsFiniteAtOrigin),
      f.differential = 0 → f.HasInjectiveRepresentative →
        Nonempty (CoordinateOrderReductionData f hfinite))
    (hexcludeTwo : ∀ (f : PointedMapGerm 2 3)
      (hfinite : f.IsFiniteAtOrigin),
      f.differential = 0 →
        f.coordinateOrder (by omega) hfinite = 2 →
          ¬ f.HasInjectiveRepresentative)
    (hexcludeThree : ∀ (f : PointedMapGerm 2 3)
      (hfinite : f.IsFiniteAtOrigin),
      f.differential = 0 →
        f.coordinateOrder (by omega) hfinite = 3 →
          ¬ f.HasInjectiveRepresentative)
    (hexcludeFour : ∀ (f : PointedMapGerm 2 3)
      (hfinite : f.IsFiniteAtOrigin),
      f.differential = 0 →
        f.coordinateOrder (by omega) hfinite = 4 →
          ¬ f.HasInjectiveRepresentative) :
    LeConjecture := by
  apply leConjecture_of_no_injective_zero_differential
  intro f hdifferential hinjective
  let hfinite : f.IsFiniteAtOrigin :=
    f.injective_isFiniteAtOrigin_two_three hinjective
  obtain ⟨data⟩ := hdata f hfinite hdifferential hinjective
  rcases data.coordinateOrder_eq_two_or_three_or_four hdifferential with
    htwo | hthree | hfour
  · exact hexcludeTwo f hfinite hdifferential htwo hinjective
  · exact hexcludeThree f hfinite hdifferential hthree hinjective
  · exact hexcludeFour f hfinite hdifferential hfour hinjective

end PointedMapGerm

end OnLeConjecture.Analytic
