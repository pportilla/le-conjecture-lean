/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PairRepresentative
public import OnLeConjecture.DThree.WeightedOrderExpansion

/-!
# Components of a representative on the coordinate product

The component germs extracted from a representative on `ℂ × ℂ` agree with
the components of the pointed plane map germ represented by that function.
-/

public section

namespace OnLeConjecture.DThree

open OnLeConjecture.Analytic

/-- Extracting a component germ from a representative agrees with taking the
same component of `PointedMapGerm.ofPairFunction`. -/
theorem pairRepresentativeComponentGerm_eq_ofPairFunction_component
    {m : ℕ} (representative : ℂ × ℂ → Source m)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0) (i : Fin m) :
    Germ.ofFunction
        (fun z : Source 2 ↦
          representative (ContinuousLinearEquiv.finTwoArrow ℂ ℂ z) i)
        (by
          have hcomponent : AnalyticAt ℂ
              (fun z : ℂ × ℂ ↦ representative z i) 0 :=
            analyticAt_pi_iff.mp hrepresentative i
          have hcomponent' : AnalyticAt ℂ
              (fun z : ℂ × ℂ ↦ representative z i)
                (ContinuousLinearEquiv.finTwoArrow ℂ ℂ (0 : Source 2)) := by
            have hzero :
                ContinuousLinearEquiv.finTwoArrow ℂ ℂ (0 : Source 2) =
                  (0 : ℂ × ℂ) := by
              simp
            rw [hzero]
            exact hcomponent
          exact hcomponent'.fun_comp
            ((ContinuousLinearEquiv.finTwoArrow ℂ ℂ).analyticAt 0)) =
      (PointedMapGerm.ofPairFunction representative
        hrepresentative hzero).1.component i := by
  apply Subtype.ext
  simp [PointedMapGerm.ofPairFunction, PointedMapGerm.ofFunction]

/-- For a representative with three target coordinates, the component germ
used in weighted rescaling is the corresponding map germ component. -/
theorem pairRepresentativeComponentGerm_eq_ofPairFunction_component_finThree
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0) (i : Fin 3) :
    pairRepresentativeComponentGerm representative hrepresentative i =
      (PointedMapGerm.ofPairFunction representative
        hrepresentative hzero).1.component i := by
  exact pairRepresentativeComponentGerm_eq_ofPairFunction_component
    representative hrepresentative hzero i

/-- Every pointed plane map germ with three target coordinates has a
representative on `ℂ × ℂ` whose extracted component germs are its component
germs. -/
theorem PointedMapGerm.exists_pairRepresentative_with_components
    (g : PointedMapGerm 2 3) :
    ∃ representative : ℂ × ℂ → Fin 3 → ℂ,
      ∃ hrepresentative : AnalyticAt ℂ representative 0,
        ∃ hzero : representative 0 = 0,
          g = PointedMapGerm.ofPairFunction representative
              hrepresentative hzero ∧
            ∀ i, pairRepresentativeComponentGerm representative
              hrepresentative i = g.1.component i := by
  obtain ⟨representative, hrepresentative, hzero, hg⟩ :=
    g.exists_ofPairFunction
  refine ⟨representative, hrepresentative, hzero, hg, ?_⟩
  intro i
  rw [hg]
  exact
    pairRepresentativeComponentGerm_eq_ofPairFunction_component_finThree
      representative hrepresentative hzero i

end OnLeConjecture.DThree
