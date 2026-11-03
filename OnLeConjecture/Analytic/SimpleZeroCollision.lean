/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticImplicitFunction
public import OnLeConjecture.Analytic.Noninjectivity

/-!
# Collisions from a simple analytic zero

Two source branches that converge to the origin, remain distinct away from
the parameter origin, and have equal images contradict local injectivity.
The analytic implicit function theorem constructs such branches from a simple
zero of an equation between complex Banach spaces.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

/-- Two distinct branches based at an arbitrary parameter with equal images
preclude injectivity on every neighborhood of the source origin. -/
theorem not_neighborhood_injective_of_tendsto_collision_branches_at
    {P : Type*} [TopologicalSpace P] {parameterBase : P}
    [NeBot (nhdsWithin parameterBase ({parameterBase} : Set P)ᶜ)]
    {n m : ℕ} (representative : Source n → Source m)
    (first second : P → Source n)
    (hfirst : Tendsto first (nhds parameterBase) (nhds 0))
    (hsecond : Tendsto second (nhds parameterBase) (nhds 0))
    (hequal : ∀ᶠ parameter in nhds parameterBase,
      representative (first parameter) = representative (second parameter))
    (hdistinct : ∀ᶠ parameter in
      nhdsWithin parameterBase ({parameterBase} : Set P)ᶜ,
      first parameter ≠ second parameter) :
    ¬ ∃ s ∈ 𝓝 (0 : Source n), Set.InjOn representative s := by
  intro hinjective
  obtain ⟨s, hs, hsInjective⟩ := hinjective
  have hfirstMem : ∀ᶠ parameter in nhds parameterBase,
      first parameter ∈ s :=
    hfirst.eventually hs
  have hsecondMem : ∀ᶠ parameter in nhds parameterBase,
      second parameter ∈ s :=
    hsecond.eventually hs
  have hall : ∀ᶠ parameter in
      nhdsWithin parameterBase ({parameterBase} : Set P)ᶜ,
      first parameter ∈ s ∧
      second parameter ∈ s ∧
      representative (first parameter) = representative (second parameter) ∧
      first parameter ≠ second parameter := by
    filter_upwards [hfirstMem.filter_mono nhdsWithin_le_nhds,
      hsecondMem.filter_mono nhdsWithin_le_nhds,
      hequal.filter_mono nhdsWithin_le_nhds, hdistinct] with
      parameter hfirstAt hsecondAt hequalAt hdistinctAt
    exact ⟨hfirstAt, hsecondAt, hequalAt, hdistinctAt⟩
  obtain ⟨parameter, hfirstAt, hsecondAt, hequalAt, hdistinctAt⟩ :=
    hall.exists
  exact hdistinctAt (hsInjective hfirstAt hsecondAt hequalAt)

/-- Two distinct branches with equal images preclude injectivity on every
neighborhood of the origin. -/
theorem not_neighborhood_injective_of_tendsto_collision_branches
    {n m : ℕ} (representative : Source n → Source m)
    (first second : ℂ → Source n)
    (hfirst : Tendsto first (nhds 0) (nhds 0))
    (hsecond : Tendsto second (nhds 0) (nhds 0))
    (hequal : ∀ᶠ parameter in nhds 0,
      representative (first parameter) = representative (second parameter))
    (hdistinct : ∀ᶠ parameter in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
      first parameter ≠ second parameter) :
    ¬ ∃ s ∈ 𝓝 (0 : Source n), Set.InjOn representative s := by
  exact not_neighborhood_injective_of_tendsto_collision_branches_at
    representative first second hfirst hsecond hequal hdistinct

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An implicit branch that gives two distinct source points with equal images
precludes local injectivity. -/
theorem not_neighborhood_injective_of_analyticImplicitCollision
    {parameterBase : P}
    [NeBot (nhdsWithin parameterBase ({parameterBase} : Set P)ᶜ)]
    {n m : ℕ}
    (representative : Source n → Source m)
    (Phi : P × E → E) (pointBase : E)
    (sourceFirst sourceSecond : P × E → Source n)
    (hPhi : AnalyticAt ℂ Phi (parameterBase, pointBase))
    (hpoint :
      (fderiv ℂ Phi (parameterBase, pointBase) ∘L
        ContinuousLinearMap.inr ℂ P E).IsInvertible)
    (hsourceFirst : ContinuousAt sourceFirst (parameterBase, pointBase))
    (hsourceSecond : ContinuousAt sourceSecond (parameterBase, pointBase))
    (hsourceFirstZero : sourceFirst (parameterBase, pointBase) = 0)
    (hsourceSecondZero : sourceSecond (parameterBase, pointBase) = 0)
    (hequal : ∀ᶠ t in nhds (parameterBase, pointBase),
      Phi t = Phi (parameterBase, pointBase) →
        representative (sourceFirst t) = representative (sourceSecond t))
    (hdistinct : ∀ᶠ t in nhds (parameterBase, pointBase),
      t.1 ≠ parameterBase → sourceFirst t ≠ sourceSecond t) :
    ¬ ∃ s ∈ 𝓝 (0 : Source n), Set.InjOn representative s := by
  let branch := analyticImplicitBranch Phi
    (parameterBase, pointBase) hPhi hpoint
  have hbranchZero : branch parameterBase = pointBase :=
    analyticImplicitBranch_apply_base Phi
      (parameterBase, pointBase) hPhi hpoint
  have hbranchAnalytic : AnalyticAt ℂ branch parameterBase :=
    analyticAt_analyticImplicitBranch Phi
      (parameterBase, pointBase) hPhi hpoint
  have hbranch : Tendsto branch (nhds parameterBase) (nhds pointBase) := by
    rw [← hbranchZero]
    exact hbranchAnalytic.continuousAt
  have hparameter : Tendsto (fun parameter : P =>
      (parameter, branch parameter)) (nhds parameterBase)
      (nhds (parameterBase, pointBase)) :=
    tendsto_id.prodMk_nhds hbranch
  have hfirst : Tendsto (fun parameter : P =>
      sourceFirst (parameter, branch parameter)) (nhds parameterBase)
      (nhds 0) := by
    change Tendsto (sourceFirst ∘ fun parameter : P =>
      (parameter, branch parameter)) (nhds parameterBase) (nhds 0)
    rw [← hsourceFirstZero]
    exact hsourceFirst.tendsto.comp hparameter
  have hsecond : Tendsto (fun parameter : P =>
      sourceSecond (parameter, branch parameter)) (nhds parameterBase)
      (nhds 0) := by
    change Tendsto (sourceSecond ∘ fun parameter : P =>
      (parameter, branch parameter)) (nhds parameterBase) (nhds 0)
    rw [← hsourceSecondZero]
    exact hsourceSecond.tendsto.comp hparameter
  have hbranchEquation : ∀ᶠ parameter in nhds parameterBase,
      Phi (parameter, branch parameter) =
        Phi (parameterBase, pointBase) :=
    eventually_analyticImplicitBranch_eq Phi
      (parameterBase, pointBase) hPhi hpoint
  have hequalBranch : ∀ᶠ parameter in nhds parameterBase,
      representative (sourceFirst (parameter, branch parameter)) =
        representative (sourceSecond (parameter, branch parameter)) := by
    filter_upwards [hparameter.eventually hequal, hbranchEquation] with
      parameter hequalAt hequationAt
    exact hequalAt hequationAt
  have hdistinctNear : ∀ᶠ parameter in nhds parameterBase,
      parameter ≠ parameterBase →
        sourceFirst (parameter, branch parameter) ≠
          sourceSecond (parameter, branch parameter) := by
    filter_upwards [hparameter.eventually hdistinct] with parameter hdistinctAt
    exact hdistinctAt
  have hdistinctBranch : ∀ᶠ parameter in
      nhdsWithin parameterBase ({parameterBase} : Set P)ᶜ,
      sourceFirst (parameter, branch parameter) ≠
        sourceSecond (parameter, branch parameter) := by
    filter_upwards [hdistinctNear.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with parameter hdistinctAt hparameterNe
    exact hdistinctAt (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
        using hparameterNe)
  exact not_neighborhood_injective_of_tendsto_collision_branches_at
    representative
    (fun parameter => sourceFirst (parameter, branch parameter))
    (fun parameter => sourceSecond (parameter, branch parameter))
    hfirst hsecond hequalBranch hdistinctBranch

/-- A simple zero whose implicit branch gives two distinct source points with
equal images precludes local injectivity. -/
theorem not_neighborhood_injective_of_analytic_simpleZeroCollision
    {n m : ℕ}
    (representative : Source n → Source m)
    (Phi : ℂ × E → E) (p : E)
    (sourceFirst sourceSecond : ℂ × E → Source n)
    (hzero : Phi (0, p) = 0)
    (hPhi : AnalyticAt ℂ Phi (0, p))
    (hpoint :
      (fderiv ℂ Phi (0, p) ∘L
        ContinuousLinearMap.inr ℂ ℂ E).IsInvertible)
    (hsourceFirst : ContinuousAt sourceFirst (0, p))
    (hsourceSecond : ContinuousAt sourceSecond (0, p))
    (hsourceFirstZero : sourceFirst (0, p) = 0)
    (hsourceSecondZero : sourceSecond (0, p) = 0)
    (hequal : ∀ᶠ t in nhds (0, p),
      Phi t = 0 →
        representative (sourceFirst t) = representative (sourceSecond t))
    (hdistinct : ∀ᶠ t in nhds (0, p),
      t.1 ≠ 0 → sourceFirst t ≠ sourceSecond t) :
    ¬ ∃ s ∈ 𝓝 (0 : Source n), Set.InjOn representative s := by
  apply not_neighborhood_injective_of_analyticImplicitCollision
    representative Phi p sourceFirst sourceSecond hPhi hpoint
    hsourceFirst hsourceSecond hsourceFirstZero hsourceSecondZero
  · filter_upwards [hequal] with t hequalAt
    intro hPhiAt
    exact hequalAt (hPhiAt.trans hzero)
  · exact hdistinct

/-- A representative arising from an implicit collision does not define a map
germ with an injective representative. -/
theorem PointedMapGerm.ofFunction_not_hasInjectiveRepresentative_of_analyticImplicitCollision
    {parameterBase : P}
    [NeBot (nhdsWithin parameterBase ({parameterBase} : Set P)ᶜ)]
    {n m : ℕ}
    (representative : Source n → Source m)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (hrepresentativeZero : representative 0 = 0)
    (Phi : P × E → E) (pointBase : E)
    (sourceFirst sourceSecond : P × E → Source n)
    (hPhi : AnalyticAt ℂ Phi (parameterBase, pointBase))
    (hpoint :
      (fderiv ℂ Phi (parameterBase, pointBase) ∘L
        ContinuousLinearMap.inr ℂ P E).IsInvertible)
    (hsourceFirst : ContinuousAt sourceFirst (parameterBase, pointBase))
    (hsourceSecond : ContinuousAt sourceSecond (parameterBase, pointBase))
    (hsourceFirstZero : sourceFirst (parameterBase, pointBase) = 0)
    (hsourceSecondZero : sourceSecond (parameterBase, pointBase) = 0)
    (hequal : ∀ᶠ t in nhds (parameterBase, pointBase),
      Phi t = Phi (parameterBase, pointBase) →
        representative (sourceFirst t) = representative (sourceSecond t))
    (hdistinct : ∀ᶠ t in nhds (parameterBase, pointBase),
      t.1 ≠ parameterBase → sourceFirst t ≠ sourceSecond t) :
    ¬ (PointedMapGerm.ofFunction representative hrepresentative
      hrepresentativeZero).HasInjectiveRepresentative := by
  apply PointedMapGerm.not_hasInjectiveRepresentative_ofFunction
  exact not_neighborhood_injective_of_analyticImplicitCollision
    representative Phi pointBase sourceFirst sourceSecond hPhi hpoint
    hsourceFirst hsourceSecond hsourceFirstZero hsourceSecondZero
    hequal hdistinct

/-- A representative arising from a simple zero collision does not define a
map germ with an injective representative. -/
theorem PointedMapGerm.ofFunction_not_hasInjectiveRepresentative_of_analyticSimpleZeroCollision
    {n m : ℕ}
    (representative : Source n → Source m)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (hrepresentativeZero : representative 0 = 0)
    (Phi : ℂ × E → E) (p : E)
    (sourceFirst sourceSecond : ℂ × E → Source n)
    (hzero : Phi (0, p) = 0)
    (hPhi : AnalyticAt ℂ Phi (0, p))
    (hpoint :
      (fderiv ℂ Phi (0, p) ∘L
        ContinuousLinearMap.inr ℂ ℂ E).IsInvertible)
    (hsourceFirst : ContinuousAt sourceFirst (0, p))
    (hsourceSecond : ContinuousAt sourceSecond (0, p))
    (hsourceFirstZero : sourceFirst (0, p) = 0)
    (hsourceSecondZero : sourceSecond (0, p) = 0)
    (hequal : ∀ᶠ t in nhds (0, p),
      Phi t = 0 →
        representative (sourceFirst t) = representative (sourceSecond t))
    (hdistinct : ∀ᶠ t in nhds (0, p),
      t.1 ≠ 0 → sourceFirst t ≠ sourceSecond t) :
    ¬ (PointedMapGerm.ofFunction representative hrepresentative
      hrepresentativeZero).HasInjectiveRepresentative := by
  apply PointedMapGerm.not_hasInjectiveRepresentative_ofFunction
  exact not_neighborhood_injective_of_analytic_simpleZeroCollision
    representative Phi p sourceFirst sourceSecond hzero hPhi hpoint
    hsourceFirst hsourceSecond hsourceFirstZero hsourceSecondZero
    hequal hdistinct

end OnLeConjecture.Analytic
