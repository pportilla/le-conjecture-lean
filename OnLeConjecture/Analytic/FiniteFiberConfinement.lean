/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteGenericCollisionRealization
public import OnLeConjecture.Analytic.Finite
public import OnLeConjecture.Analytic.NonzeroSpecialization

/-!
# Confinement of fibres of finite analytic germs

A finite pointed analytic map has an isolated zero fibre for every analytic
representative. The proof writes a common power of each source coordinate as
a linear combination of the components of the map.

A compactness argument then shows that a family of points in a fixed compact
source set converges to the unique point over the target origin whenever its
images converge to the origin. These results remove the convergence part of
the remaining collision realization problem.
-/

public section

open Filter Metric Set
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic

namespace Germ

/-- Finitely many nonzero analytic germs admit representatives that remain
simultaneously nonzero along a punctured path tending to the origin. The path
can be chosen with norm smaller than the norm of its parameter. -/
theorem exists_punctured_path_forall_ne_zero_of_finite
    {n : ℕ} {ι : Type*} [Finite ι]
    (g : ι → Germ n) (F : ι → Source n → ℂ)
    (hF : ∀ i, AnalyticAt ℂ (F i) 0)
    (hrepresentative : ∀ i, g i = Germ.ofFunction (F i) (hF i))
    (hne : ∀ i, g i ≠ 0) :
    ∃ path : ℂ → Source n,
      path 0 = 0 ∧
      Tendsto path (nhds 0) (nhds 0) ∧
      ∀ parameter : ℂ, parameter ≠ 0 →
        ‖path parameter‖ < ‖parameter‖ ∧
          ∀ i, F i (path parameter) ≠ 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  have hexists (parameter : ℂ) (hparameter : parameter ≠ 0) :
      ∃ z ∈ ball (0 : Source n) ‖parameter‖,
        ∀ i, F i z ≠ 0 := by
    apply Germ.exists_mem_forall_ne_zero_of_finite
      g F hF hrepresentative hne
    exact ball_mem_nhds 0 (norm_pos_iff.mpr hparameter)
  let path : ℂ → Source n := fun parameter =>
    if hparameter : parameter = 0 then 0
    else Classical.choose (hexists parameter hparameter)
  have hpathZero : path 0 = 0 := by
    simp [path]
  have hpath (parameter : ℂ) (hparameter : parameter ≠ 0) :
      path parameter ∈ ball (0 : Source n) ‖parameter‖ ∧
        ∀ i, F i (path parameter) ≠ 0 := by
    rw [show path parameter =
        Classical.choose (hexists parameter hparameter) by
      simp [path, hparameter]]
    exact Classical.choose_spec (hexists parameter hparameter)
  have hpathNorm (parameter : ℂ) (hparameter : parameter ≠ 0) :
      ‖path parameter‖ < ‖parameter‖ := by
    have hmem := (hpath parameter hparameter).1
    simpa only [mem_ball, dist_zero_right] using hmem
  have hpathTendsto : Tendsto path (nhds 0) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro epsilon hepsilon
    have hparameterEventually : ∀ᶠ parameter : ℂ in nhds 0,
        dist parameter 0 < epsilon :=
      ball_mem_nhds 0 hepsilon
    filter_upwards [hparameterEventually] with parameter hparameterSmall
    rw [dist_zero_right]
    by_cases hparameter : parameter = 0
    · rw [hparameter, hpathZero]
      simpa only [norm_zero] using hepsilon
    · calc
        ‖path parameter‖ < ‖parameter‖ := hpathNorm parameter hparameter
        _ = dist parameter 0 := (dist_zero_right parameter).symm
        _ < epsilon := hparameterSmall
  exact ⟨path, hpathZero, hpathTendsto, fun parameter hparameter =>
    ⟨hpathNorm parameter hparameter, (hpath parameter hparameter).2⟩⟩

end Germ

/-- Let a continuous map on a compact set have a unique point over a given
target point. Every family in that compact set whose images converge to the
target point converges to the unique point in the fibre. -/
theorem tendsto_of_eventually_mem_compact_of_tendsto_image_of_unique_fibre
    {P X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {l : Filter P} {K : Set X} {x₀ : X} {y₀ : Y}
    (F : X → Y) (hK : IsCompact K) (hF : ContinuousOn F K)
    (hunique : ∀ x ∈ K, F x = y₀ → x = x₀)
    (x : P → X) (hx : ∀ᶠ p in l, x p ∈ K)
    (himage : Tendsto (fun p => F (x p)) l (nhds y₀)) :
    Tendsto x l (nhds x₀) := by
  rw [tendsto_def]
  intro s hs
  obtain ⟨u, hus, huOpen, hx₀u⟩ := mem_nhds_iff.mp hs
  let bad : Set X := K ∩ uᶜ
  have hbad : IsCompact bad :=
    hK.inter_right huOpen.isClosed_compl
  have hFbad : ContinuousOn F bad :=
    hF.mono inter_subset_left
  have himageCompact : IsCompact (F '' bad) :=
    hbad.image_of_continuousOn hFbad
  have hy₀NotMem : y₀ ∉ F '' bad := by
    rintro ⟨z, hz, hFz⟩
    have hzEq : z = x₀ := hunique z hz.1 hFz
    exact hz.2 (hzEq ▸ hx₀u)
  have himageComplement : (F '' bad)ᶜ ∈ nhds y₀ :=
    himageCompact.isClosed.isOpen_compl.mem_nhds hy₀NotMem
  have himageEventually : ∀ᶠ p in l, F (x p) ∈ (F '' bad)ᶜ :=
    himage.eventually himageComplement
  filter_upwards [hx, himageEventually] with p hpK hpImage
  apply hus
  by_contra hpU
  apply hpImage
  exact ⟨x p, ⟨hpK, hpU⟩, rfl⟩

namespace PointedMapGerm

/-- Every representative of a finite pointed plane map has an isolated zero
fibre at the source origin. -/
theorem exists_isolated_zero_neighborhood_of_isFiniteAtOrigin
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin)
    (representative : Source 2 → Source m)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (hrepresentativeZero : representative 0 = 0)
    (hf : f = PointedMapGerm.ofFunction representative
      hrepresentative hrepresentativeZero) :
    ∃ s ∈ nhds (0 : Source 2),
      ∀ z ∈ s, representative z = 0 → z = 0 := by
  obtain ⟨N, hN⟩ :=
    f.exists_maximalIdeal_pow_le_coordinateIdeal hfinite
  have hcoordinatePower (j : Fin 2) :
      Germ.coordinate j ^ N ∈ f.1.coordinateIdeal := by
    apply hN
    exact Ideal.pow_mem_pow (Germ.coordinate_mem_maximalIdeal j) N
  have hcoordinateIdeal : f.1.coordinateIdeal =
      Ideal.span (Set.range f.1.component) := by
    apply le_antisymm
    · rw [MapGerm.coordinateIdeal_le]
      intro i
      exact Ideal.subset_span (Set.mem_range_self i)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact f.1.component_mem_coordinateIdeal i
  have hlinearCombination (j : Fin 2) :
      ∃ c : Fin m → Germ 2,
        ∑ i, c i * f.1.component i = Germ.coordinate j ^ N := by
    exact (Ideal.mem_span_range_iff_exists_fun.mp
      (show Germ.coordinate j ^ N ∈
        Ideal.span (Set.range f.1.component) from
          hcoordinateIdeal ▸ hcoordinatePower j))
  choose c hc using hlinearCombination
  choose C hC hCRepresentative using fun j i =>
    Germ.exists_analyticRepresentative_allOrders (c j i)
  have hcomponentAnalytic (i : Fin m) :
      AnalyticAt ℂ (fun z : Source 2 => representative z i) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (AnalyticAt.comp (x := (0 : Source 2))
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt
          (representative 0)) hrepresentative)
  have hcomponentGerm (i : Fin m) :
      f.1.component i = Germ.ofFunction
        (fun z : Source 2 => representative z i)
        (hcomponentAnalytic i) := by
    rw [hf]
    apply Subtype.ext
    exact MapGerm.component_ofFunction representative hrepresentative i
  let L : Fin 2 → Source 2 → ℂ := fun j z =>
    ∑ i, C j i z * representative z i
  have hLAnalytic (j : Fin 2) : AnalyticAt ℂ (L j) 0 := by
    dsimp only [L]
    exact Finset.analyticAt_fun_sum Finset.univ fun i _ =>
      (hC j i).mul (hcomponentAnalytic i)
  have hLGerm (j : Fin 2) :
      Germ.ofFunction (L j) (hLAnalytic j) = Germ.coordinate j ^ N := by
    rw [← hc j]
    apply Subtype.ext
    change ((L j : Source 2 → ℂ) : FunctionGerm 2) =
      ((∑ i, c j i * f.1.component i : Germ 2) : FunctionGerm 2)
    calc
      ((L j : Source 2 → ℂ) : FunctionGerm 2) =
          ((∑ i, fun z : Source 2 =>
            C j i z * representative z i : Source 2 → ℂ) :
              FunctionGerm 2) := by
        congr 1
        funext z
        simp only [L, Finset.sum_apply]
      _ = ∑ i, (((fun z : Source 2 =>
          C j i z * representative z i) : Source 2 → ℂ) :
            FunctionGerm 2) := by
        exact map_sum (Filter.Germ.coeRingHom (nhds (0 : Source 2)))
          (fun i z => C j i z * representative z i) Finset.univ
      _ = ((∑ i, c j i * f.1.component i : Germ 2) :
          FunctionGerm 2) := by
        calc
          (∑ i, (((fun z : Source 2 =>
              C j i z * representative z i) : Source 2 → ℂ) :
                FunctionGerm 2)) =
              ∑ i, ((c j i * f.1.component i : Germ 2) :
                FunctionGerm 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            have hci := congrArg (fun q : Germ 2 =>
              (q : FunctionGerm 2)) (hCRepresentative j i)
            have hfi := congrArg (fun q : Germ 2 =>
              (q : FunctionGerm 2)) (hcomponentGerm i)
            calc
              (((fun z : Source 2 => C j i z * representative z i) :
                  Source 2 → ℂ) : FunctionGerm 2) =
                  ((C j i : Source 2 → ℂ) : FunctionGerm 2) *
                    (((fun z : Source 2 => representative z i) :
                      Source 2 → ℂ) : FunctionGerm 2) := rfl
              _ = ((c j i : Germ 2) : FunctionGerm 2) *
                    ((f.1.component i : Germ 2) : FunctionGerm 2) := by
                exact congrArg₂ (fun a b : FunctionGerm 2 => a * b)
                  hci.symm hfi.symm
              _ = ((c j i * f.1.component i : Germ 2) :
                  FunctionGerm 2) := rfl
          _ = ((∑ i, c j i * f.1.component i : Germ 2) :
              FunctionGerm 2) := by
            symm
            exact map_sum (analyticGermSubring 2).subtype
              (fun i => c j i * f.1.component i) Finset.univ
  have hrelation (j : Fin 2) : ∀ᶠ z in nhds (0 : Source 2),
      L j z = z j ^ N := by
    have hj := congrArg (fun q : Germ 2 => (q : FunctionGerm 2)) (hLGerm j)
    have hj' : ((L j : Source 2 → ℂ) : FunctionGerm 2) =
        ((fun z : Source 2 => z j ^ N) : FunctionGerm 2) := by
      calc
        ((L j : Source 2 → ℂ) : FunctionGerm 2) =
            ((Germ.coordinate j ^ N : Germ 2) : FunctionGerm 2) := hj
        _ = ((Germ.coordinate j : Germ 2) : FunctionGerm 2) ^ N := rfl
        _ = (((fun z : Source 2 => z j) : FunctionGerm 2) ^ N) := by
          rw [Germ.coe_coordinate]
        _ = ((fun z : Source 2 => z j ^ N) : FunctionGerm 2) := rfl
    exact Filter.Germ.coe_eq.mp hj'
  have hrelations : ∀ᶠ z in nhds (0 : Source 2),
      ∀ j : Fin 2, L j z = z j ^ N :=
    Filter.eventually_all.mpr hrelation
  refine ⟨{z | ∀ j : Fin 2, L j z = z j ^ N}, hrelations, ?_⟩
  intro z hz hzero
  funext j
  have hpower : z j ^ N = 0 := by
    rw [← hz j]
    simp [L, hzero]
  by_cases hNZero : N = 0
  · subst N
    simp at hpower
  · exact (pow_eq_zero_iff hNZero).mp hpower

/-- A finite pointed plane map admits a closed ball on which the origin is
the only point mapped to the target origin. -/
theorem exists_closedBall_isolated_zero_of_isFiniteAtOrigin
    {m : ℕ} (f : PointedMapGerm 2 m)
    (hfinite : f.IsFiniteAtOrigin)
    (representative : Source 2 → Source m)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (hrepresentativeZero : representative 0 = 0)
    (hf : f = PointedMapGerm.ofFunction representative
      hrepresentative hrepresentativeZero) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ representative (closedBall 0 r) ∧
      ∀ z ∈ closedBall (0 : Source 2) r,
        representative z = 0 → z = 0 := by
  obtain ⟨s, hs, hisolated⟩ :=
    f.exists_isolated_zero_neighborhood_of_isFiniteAtOrigin hfinite
      representative hrepresentative hrepresentativeZero hf
  obtain ⟨r, hr, hrSubset⟩ :=
    nhds_basis_closedBall.mem_iff.mp
      (hrepresentative.eventually_analyticAt.and hs)
  refine ⟨r, hr, fun z hz => (hrSubset hz).1, ?_⟩
  intro z hz hzero
  exact hisolated z (hrSubset hz).2 hzero

/-- A family in a fixed sufficiently small closed ball converges to the
source origin when its images under a finite representative converge to the
target origin. -/
theorem tendsto_zero_of_finite_fibre_lift_in_closedBall
    {P : Type*} {l : Filter P} {m : ℕ}
    (f : PointedMapGerm 2 m) (hfinite : f.IsFiniteAtOrigin)
    (representative : Source 2 → Source m)
    (hrepresentative : AnalyticAt ℂ representative 0)
    (hrepresentativeZero : representative 0 = 0)
    (hf : f = PointedMapGerm.ofFunction representative
      hrepresentative hrepresentativeZero)
    (x : P → Source 2)
    (hxImage : Tendsto (fun p => representative (x p)) l (nhds 0)) :
    ∃ r : ℝ, 0 < r ∧
      ((∀ᶠ p in l, x p ∈ closedBall (0 : Source 2) r) →
        Tendsto x l (nhds 0)) := by
  obtain ⟨r, hr, hanalytic, hisolated⟩ :=
    f.exists_closedBall_isolated_zero_of_isFiniteAtOrigin hfinite
      representative hrepresentative hrepresentativeZero hf
  refine ⟨r, hr, fun hx => ?_⟩
  apply tendsto_of_eventually_mem_compact_of_tendsto_image_of_unique_fibre
    representative (isCompact_closedBall (0 : Source 2) r)
      hanalytic.continuousOn
  · exact hisolated
  · exact hx
  · exact hxImage

/-- A finite nonbirational plane germ has punctured nearby fibres with at
least two points. The witnesses may be chosen in every prescribed closed
ball, and the common image tends to the target origin. -/
@[expose] def PuncturedLocalFiberCollisionRealization (m : ℕ) : Prop :=
  ∀ (f : PointedMapGerm 2 m), f.IsFiniteAtOrigin →
    ¬ f.IsBirationalAtOrigin →
    ∀ (representative : Source 2 → Source m)
      (hrepresentative : AnalyticAt ℂ representative 0)
      (hrepresentativeZero : representative 0 = 0),
      f = PointedMapGerm.ofFunction representative
        hrepresentative hrepresentativeZero →
      ∀ r : ℝ, 0 < r →
        ∃ first second : ℂ → Source 2,
          (∀ᶠ parameter in nhds 0,
            first parameter ∈ closedBall 0 r ∧
              second parameter ∈ closedBall 0 r) ∧
          Tendsto (fun parameter =>
            representative (first parameter)) (nhds 0) (nhds 0) ∧
          (∀ᶠ parameter in nhds 0,
            representative (first parameter) =
              representative (second parameter)) ∧
          ∀ᶠ parameter in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
            first parameter ≠ second parameter

set_option maxHeartbeats 400000 in
-- Elaborating the nested fraction field structures exceeds the default limit.
/-- Realization of punctured fibres in every small ball implies collision
realization for every pair of distinct generic embeddings. Compactness
supplies convergence of both source families. -/
theorem genericEmbeddingCollisionRealization_of_puncturedLocalFiber
    {m : ℕ}
    (hcollision : PuncturedLocalFiberCollisionRealization m) :
    GenericEmbeddingCollisionRealization m := by
  intro f hfinite
  let _ : Algebra (FractionRing f.ImageRing)
      (FractionRing (Germ 2)) := f.genericFractionFieldAlgebra
  change ∀ (sigma tau : Field.Emb (FractionRing f.ImageRing)
      (FractionRing (Germ 2))),
    sigma ≠ tau →
      ∀ (representative : Source 2 → Source m)
        (hrepresentative : AnalyticAt ℂ representative 0)
        (hrepresentativeZero : representative 0 = 0),
        f = PointedMapGerm.ofFunction representative
          hrepresentative hrepresentativeZero →
        ∃ first second : ℂ → Source 2,
          Tendsto first (nhds 0) (nhds 0) ∧
          Tendsto second (nhds 0) (nhds 0) ∧
          (∀ᶠ parameter in nhds 0,
            representative (first parameter) =
              representative (second parameter)) ∧
          ∀ᶠ parameter in nhdsWithin 0 ({0} : Set ℂ)ᶜ,
            first parameter ≠ second parameter
  intro sigma tau hne representative hrepresentative
    hrepresentativeZero hf
  have hnot : ¬ f.IsBirationalAtOrigin := by
    intro hbirational
    apply hne
    apply AlgHom.ext
    intro x
    obtain ⟨a, ha⟩ := hbirational x
    have ha' : algebraMap (FractionRing f.ImageRing)
        (FractionRing (Germ 2)) a = x := by
      rw [RingHom.algebraMap_toAlgebra]
      exact ha
    rw [← ha', sigma.commutes, tau.commutes]
  obtain ⟨r, hr, hanalytic, hisolated⟩ :=
    f.exists_closedBall_isolated_zero_of_isFiniteAtOrigin hfinite
      representative hrepresentative hrepresentativeZero hf
  obtain ⟨first, second, hball, himageFirst, hequal, hdistinct⟩ :=
    hcollision f hfinite hnot representative hrepresentative
      hrepresentativeZero hf r hr
  have hfirst : Tendsto first (nhds 0) (nhds 0) := by
    apply tendsto_of_eventually_mem_compact_of_tendsto_image_of_unique_fibre
      representative (isCompact_closedBall (0 : Source 2) r)
        hanalytic.continuousOn hisolated
    · exact hball.mono fun parameter hparameter => hparameter.1
    · exact himageFirst
  have himageSecond : Tendsto (fun parameter =>
      representative (second parameter)) (nhds 0) (nhds 0) :=
    himageFirst.congr' hequal
  have hsecond : Tendsto second (nhds 0) (nhds 0) := by
    apply tendsto_of_eventually_mem_compact_of_tendsto_image_of_unique_fibre
      representative (isCompact_closedBall (0 : Source 2) r)
        hanalytic.continuousOn hisolated
    · exact hball.mono fun parameter hparameter => hparameter.2
    · exact himageSecond
  exact ⟨first, second, hfirst, hsecond, hequal, hdistinct⟩

end PointedMapGerm

end OnLeConjecture.Analytic
