/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneFiniteFiberCriterion
public import OnLeConjecture.Analytic.PlaneIsolatedFiberElimination

/-!
# Finiteness of injective plane map germs

Local injectivity isolates the zero fibre. Plane elimination gives finite
coordinate colength, and the finite fibre criterion then gives module
finiteness over the analytic image ring.
-/

public section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- Every injective analytic map germ with plane source is finite at the
origin. -/
theorem injective_isFiniteAtOrigin_two
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hinjective : f.HasInjectiveRepresentative) :
    f.IsFiniteAtOrigin := by
  exact PointedMapGerm.isFiniteAtOrigin_of_injective_two
    (PointedMapGerm.planeIsolatedFiberElimination m)
    (PointedMapGerm.finiteFiberCriterionAtOrigin_two m)
    f hinjective

/-- Every injective analytic germ from the plane to three dimensional
complex space is finite at the origin. -/
theorem injective_isFiniteAtOrigin_two_three
    (f : PointedMapGerm 2 3)
    (hinjective : f.HasInjectiveRepresentative) :
    f.IsFiniteAtOrigin :=
  PointedMapGerm.injective_isFiniteAtOrigin_two f hinjective

end PointedMapGerm

end OnLeConjecture.Analytic
