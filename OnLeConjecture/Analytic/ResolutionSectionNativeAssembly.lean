/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionNativeChoice
public import OnLeConjecture.Analytic.ResolutionSectionCanonicalFloerReduction
public import OnLeConjecture.Analytic.CriticalJacobianStaircaseReduction
public import OnLeConjecture.Analytic.CriticalSupportNonempty
public import OnLeConjecture.KnotFloer.GridBraidMovieStatement
public import OnLeConjecture.KnotFloer.GridFactorLowerBoundStatement
public import OnLeConjecture.KnotFloer.GridConnectedSumIterated
public import OnLeConjecture.KnotFloer.GridCanonicalMoves

/-!
# Final assembly of the native route from its five inputs

This module is stage A of job J23. It states the exterior input `ExteriorNativeMapStatement`
and collects the five inputs of the native route in `NativeRouteInputs`:

* `parity`: the seam positive-path comparisons (jobs J05, J06, J07);
* `second`: the strict-range second torus representative (job J21);
* `braid`: the braid native map statement (job J12);
* `factor`: the factor lower bound statement (jobs J18 and J20);
* `exterior`: the exterior native map statement.

From these inputs it constructs, for every locally injective germ with zero differential,
an assembly `A`, a level `L` and a `ResolutionSectionFloerData A L`, and hence proves Lê's
conjecture. The comparison map is the composite of the braid map for the image word, the
exterior map, and the iterated seam comparison of job J04 into the finite tensor. Its
second shift is the candidate genus by job J16. The factor thresholds are transported from
the factor word grids to the prepared factor grids along grid moves.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

open TauCeti CategoryTheory HomologicalComplex
open OnLeConjecture.KnotFloer OnLeConjecture.KnotFloer.GridFull OnLeConjecture.KnotFloer.Staircase
open OnLeConjecture.KnotTheory OnLeConjecture.PlaneCurve

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The square sum of an assembly of a germ with zero differential is at least four. -/
theorem ResolutionSectionAssembly.four_le_squareSum (A : ResolutionSectionAssembly g hd hi) :
    4 ≤ A.squareSum :=
  A.tree.four_le_square_sum_of_differential_eq_zero hd

/-- Every nearby level has a singular point. -/
theorem ResolutionSectionLevel.card_points_pos {A : ResolutionSectionAssembly g hd hi}
    (L : ResolutionSectionLevel A) : 0 < L.points.card := by
  rw [L.card_eq]
  exact A.count_pos

/-- **Exterior native map statement.** For every locally injective germ with zero
differential there are an assembly, a level, native route choices and prepared factor grids
related by grid moves to the factor word grids, with a native map from the grid of the full
twist followed by the image word to the iterated seam grid, with shifts `(0, μ(v)/2)`,
carrying the normalized class to the normalized class. -/
def ExteriorNativeMapStatement : Prop :=
  ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative),
    ∃ (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A)
      (C : NativeRouteChoice A L) (sizes : Fin L.points.card → ℕ)
      (D : ∀ j, GridDiagram (sizes j)) (hprep : SeamPrepared D) (hD : ∀ j, 2 ≤ sizes j),
      (∀ j, (wordGrid (C.factorWord j)).MovesTo (D j)) ∧
      ∃ ψ : laurentMaslovComplex (wordGrid (fullTwistWord A.squareSum ++ C.imageWord)) (ZMod 2) ⟶
          laurentMaslovComplex (iteratedSeamGrid D hprep) (ZMod 2),
        (laurentMaslovBifiltration (wordGrid (fullTwistWord A.squareSum ++ C.imageWord))
            (ZMod 2)).Shifts (laurentMaslovBifiltration (iteratedSeamGrid D hprep) (ZMod 2)) ψ 0
            ((A.sourceMilnorNumber : ℝ) / 2) ∧
          homologyMap ψ 0 (gridCanonicalClass (wordGrid (fullTwistWord A.squareSum ++ C.imageWord))
              (two_le_wordGrid_size_fullTwist (by have := A.four_le_squareSum; omega)
                C.imageWord)) =
            gridCanonicalClass (iteratedSeamGrid D hprep)
              (two_le_iteratedSeamSize L.card_points_pos hD)

/-- The five inputs of the native route. -/
structure NativeRouteInputs : Prop where
  parity : ∀ n m : ℕ, SeamPositivePathComparisons n m
  second : ∀ n m : ℕ, ∀ hn : 2 ≤ n, 0 < m → 2 * m < n + 1 →
    ((laurentMaslovBifiltration (reflectedTorusGrid n) (ZMod 2)).weighted
      (2 / (m : ℝ))).RepresentedBelow 0 (reflectedTorusAnchorClass n (ZMod 2))
      (consecutiveWeight n (2 / (m : ℝ)) ⟨2, by omega⟩)
  braid : BraidNativeMapStatement
  factor : FactorWordLowerBound
  exterior : ExteriorNativeMapStatement

/-- **Floer data from the native route.** The five inputs of the native route give, for every
locally injective germ with zero differential, an assembly, a level, and Floer comparison data
on them. -/
theorem exists_resolutionSectionFloerData_of_nativeRouteInputs (h : NativeRouteInputs)
    (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative) :
    ∃ (A : ResolutionSectionAssembly g hd hi) (L : ResolutionSectionLevel A),
      Nonempty (ResolutionSectionFloerData A L) := by
  obtain ⟨A, L, C, sizes, D, hprep, hD, hmoves, ψ, hψ, hψc⟩ := h.exterior g hd hi
  have hS4 := A.four_le_squareSum
  have hS2 : 2 ≤ A.squareSum := by omega
  have hN := L.card_points_pos
  set T := (g.criticalJacobianFactorization hi).maxMultiplicity with hT
  have hT2 : 2 ≤ T :=
    (g.criticalJacobianFactorization hi).two_le_maxMultiplicity_of_differential_eq_zero hi hd
  -- The braid map for the image word.
  obtain ⟨φ, hφ, hφc⟩ := h.braid A.squareSum hS2 C.imageWord
  -- The iterated seam comparison into the finite tensor.
  obtain ⟨θ, hθ, hθc⟩ := exists_iteratedSeam_finiteTensor_map hN D hD hprep
  refine ⟨A, L, ⟨ResolutionSectionFloerData.ofCanonicalClasses A L sizes D hD (φ ≫ ψ ≫ θ)
    ?shift ?second ?lower ?mapClass⟩⟩
  case shift =>
    have hcomp := hφ.comp (hψ.comp hθ)
    have hc := C.braid_exterior_count
    simp only [add_zero] at hcomp
    rw [← hc]
    exact hcomp
  case second =>
    intro hlt
    exact h.second (A.squareSum - 1) T (by omega) (by omega) (by omega)
  case lower =>
    intro j
    have ha2 := C.two_le_strands j
    have haT := C.strands_le j
    have hfac := h.factor (C.strands j) ha2 (C.factorWord j) (C.factorWord_cycleCount j)
      (C.factorWord_generators j) (deltaInvariant (localSectionEquation A.H (L.point j)))
      (C.factorWord_length j) (2 / (T : ℝ)) (by positivity) (by
        apply div_le_div_of_nonneg_left (by norm_num)
          (by exact_mod_cast (by omega : 0 < C.strands j))
        exact_mod_cast haT)
    rw [gridCanonicalClass_spectralThreshold_movesTo (wordGrid (C.factorWord j)) (D j)
      (two_le_wordGrid_size_of_generatorIndices ha2 (C.factorWord_generators j)) (hD j)
      (hmoves j) (2 / (T : ℝ))] at hfac
    exact hfac
  case mapClass =>
    rw [homologyMap_comp, homologyMap_comp, CategoryTheory.comp_apply, CategoryTheory.comp_apply,
      hφc, hψc, hθc]

/-- **Lê's conjecture from the native route.** The five inputs of the native route imply
Lê's conjecture. -/
theorem leConjecture_of_nativeRouteInputs (h : NativeRouteInputs) : LeConjecture :=
  leConjecture_of_resolutionSection_floer_data
    (exists_resolutionSectionFloerData_of_nativeRouteInputs h)

end OnLeConjecture.Analytic
