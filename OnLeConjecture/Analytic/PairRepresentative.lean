/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Noninjectivity

/-!
# Analytic representatives on two coordinate spaces

Every pointed analytic map germ has a representative defined at the origin.
For a plane source, the representative may be written on `ℂ × ℂ` through the
standard continuous linear equivalence with `Source 2`.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- Every pointed analytic map germ has an analytic representative that maps
the origin to the origin. -/
theorem PointedMapGerm.exists_ofFunction {n m : ℕ}
    (g : PointedMapGerm n m) :
    ∃ f : Source n → Source m, ∃ hf : AnalyticAt ℂ f 0,
      ∃ h0 : f 0 = 0, g = PointedMapGerm.ofFunction f hf h0 := by
  rcases g with ⟨⟨g, hg⟩, hg0⟩
  change IsAnalyticMapGerm g at hg
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [isAnalyticMapGerm_ofFun] at hg
      change f 0 = 0 at hg0
      refine ⟨f, hg, hg0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl

/-- Every pointed plane map germ has an analytic representative on
`ℂ × ℂ`. -/
theorem PointedMapGerm.exists_ofPairFunction {m : ℕ}
    (g : PointedMapGerm 2 m) :
    ∃ f : ℂ × ℂ → Source m, ∃ hf : AnalyticAt ℂ f 0,
      ∃ h0 : f 0 = 0,
        g = PointedMapGerm.ofPairFunction f hf h0 := by
  obtain ⟨F, hF, hF0, hg⟩ := g.exists_ofFunction
  let e : Source 2 ≃L[ℂ] ℂ × ℂ :=
    ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  let f : ℂ × ℂ → Source m := fun z ↦ F (e.symm z)
  have hf : AnalyticAt ℂ f 0 := by
    have heSymmZero : e.symm (0 : ℂ × ℂ) = 0 := map_zero e.symm
    have hF' : AnalyticAt ℂ F (e.symm (0 : ℂ × ℂ)) := by
      simpa only [heSymmZero] using hF
    exact hF'.comp (e.symm.analyticAt 0)
  have h0 : f 0 = 0 := by
    simp [f, hF0]
  refine ⟨f, hf, h0, ?_⟩
  rw [hg]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    change F z = F (e.symm (e z))
    rw [e.symm_apply_apply]

end OnLeConjecture.Analytic
