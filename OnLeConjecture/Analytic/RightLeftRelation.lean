/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LinearCoordinates
public import OnLeConjecture.PlaneCurve.ParametricMorse

/-!
# The right left equivalence relation

Identity and composition of pointed analytic equivalences prove reflexivity
and transitivity of right left equivalence. Symmetry is proved in
`Analytic.Equivalence`.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace PointedEquivGerm

/-- The identity pointed analytic equivalence. -/
@[expose]
noncomputable def identity (n : ℕ) : PointedEquivGerm n :=
  Germ.pointedEquivGermOfContinuousLinearEquiv
    (ContinuousLinearEquiv.refl ℂ (Source n))

@[simp]
theorem identity_forward (n : ℕ) :
    (PointedEquivGerm.identity n).forward =
      PointedMapGerm.identity n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun _z ↦ rfl

@[simp]
theorem identity_inverse (n : ℕ) :
    (PointedEquivGerm.identity n).inverse =
      PointedMapGerm.identity n := by
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun _z ↦ rfl

end PointedEquivGerm

namespace PointedMapGerm

/-- Every pointed analytic map germ is right left equivalent to itself. -/
theorem rightLeftEquivalent_refl {n m : ℕ} (f : PointedMapGerm n m) :
    f.RightLeftEquivalent f := by
  refine ⟨PointedEquivGerm.identity n,
    PointedEquivGerm.identity m, ?_⟩
  rw [PointedEquivGerm.identity_forward,
    PointedEquivGerm.identity_forward,
    PointedMapGerm.comp_identity,
    PointedMapGerm.identity_comp]

/-- Right left equivalence is transitive. -/
theorem RightLeftEquivalent.trans {n m : ℕ}
    {f g h : PointedMapGerm n m}
    (hfg : f.RightLeftEquivalent g)
    (hgh : g.RightLeftEquivalent h) :
    f.RightLeftEquivalent h := by
  rcases hfg with ⟨source₁, target₁, hg⟩
  rcases hgh with ⟨source₂, target₂, hh⟩
  refine ⟨source₁.comp source₂, target₂.comp target₁, ?_⟩
  rw [hh, hg]
  change
    target₂.forward.comp
        ((target₁.forward.comp (f.comp source₁.forward)).comp
          source₂.forward) =
      (target₂.forward.comp target₁.forward).comp
        (f.comp (source₁.forward.comp source₂.forward))
  simp only [PointedMapGerm.comp_assoc]

end PointedMapGerm

end OnLeConjecture.Analytic
