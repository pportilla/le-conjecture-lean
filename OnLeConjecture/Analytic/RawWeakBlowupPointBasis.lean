/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupTreeVertices
public import OnLeConjecture.Analytic.GenericFiniteGermFamilyChoice
public import OnLeConjecture.Analytic.ProjectiveChartProximityLabels
import Mathlib.Tactic

/-!
# An analytic point basis constructed from a finite weak-blowup tree

The same coefficients are used at every vertex. Avoiding the finitely many
proper order conditions constructs a member of the exact ideal order at
every center. Its transform identities are inherited from the actual weak
generators. No principalization or generic-member record is assumed here.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

@[expose] noncomputable def indexEquiv (T : RawProjectiveWeakBlowupTree F) :
    T.Vertex ≃ Fin (Fintype.card T.Vertex) := Fintype.equivFin _

theorem linearCombination_transform (T : RawProjectiveWeakBlowupTree F)
    (q : ι → ℂ) (p : T.Vertex) (hp : p ≠ T.root) :
    (pointBlowupChartGerm (projectiveChartCenter (T.chartPoint p))).pullbackRingHom
        ((projectiveChartSource (T.chartPoint p)).forward.pullbackRingHom
          (germLinearCombination (T.generators (T.predecessor p)) q)) =
      coordinate (1 : Fin 2) ^ T.multiplicity (T.predecessor p) *
        germLinearCombination (T.generators p) q := by
  simp only [germLinearCombination, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, PointedMapGerm.pullback_complex_smul, T.transform_identity p hp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (mul_smul_comm _ _ _).symm

@[expose] noncomputable def pointBasis (T : RawProjectiveWeakBlowupTree F)
    (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    AnalyticPointBasis (Fintype.card T.Vertex) where
  root := T.indexEquiv T.root
  predecessor p := T.indexEquiv (T.predecessor (T.indexEquiv.symm p))
  predecessor_root := by simp only [Equiv.symm_apply_apply, T.predecessor_root]
  generation p := T.generation (T.indexEquiv.symm p)
  generation_decreases p hp := by
    simp only [Equiv.symm_apply_apply]
    apply T.generation_decreases
    intro h
    apply hp
    exact (T.indexEquiv.eq_symm_apply.mp h.symm).symm
  germ p := germLinearCombination (T.generators (T.indexEquiv.symm p)) q
  multiplicity p := T.multiplicity (T.indexEquiv.symm p)
  multiplicity_pos p := T.multiplicity_pos _
  germ_mem p := germLinearCombination_mem _ _ (T.generator_mem _) q
  germ_not_mem_succ p := hq _
  sourceCoordinates p := projectiveChartSource (T.chartPoint (T.indexEquiv.symm p))
  chartCenter p := projectiveChartCenter (T.chartPoint (T.indexEquiv.symm p))
  transform_identity p hp := by
    simp only [Equiv.symm_apply_apply]
    apply T.linearCombination_transform q
    intro h
    apply hp
    exact (T.indexEquiv.eq_symm_apply.mp h.symm).symm

@[expose] noncomputable def weakData (T : RawProjectiveWeakBlowupTree F)
    (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    WeakTransformIdealData (T.pointBasis q hq) ι where
  generators p := T.generators (T.indexEquiv.symm p)
  generator_mem_pow p i := T.generator_mem _ i
  generic_member_mem p := germLinearCombination_mem _ _
    (fun i => Ideal.subset_span (Set.mem_range_self i)) q
  transform_identity p hp i := by
    simp only [pointBasis, Equiv.symm_apply_apply]
    apply T.transform_identity _ _ i
    intro h
    apply hp
    exact (T.indexEquiv.eq_symm_apply.mp h.symm).symm

@[simp] theorem weakData_root (T : RawProjectiveWeakBlowupTree F)
    (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    (T.weakData q hq).generators (T.pointBasis q hq).root = F := by
  simp only [weakData, pointBasis, Equiv.symm_apply_apply, generators_root]

theorem exists_exact_coefficients (T : RawProjectiveWeakBlowupTree F)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U, ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1) := by
  obtain ⟨q, hqU, hq⟩ := exists_coefficients_exact_orders_mem_open
    T.generators T.multiplicity T.generator_mem T.generator_exact U hU hUne
  exact ⟨q, hqU, fun p => (hq p).2⟩

@[expose] noncomputable def rootedChartData (T : RawProjectiveWeakBlowupTree F) :
    RootedProjectiveChartData T.Vertex where
  root := T.root
  predecessor := T.predecessor
  predecessor_root := T.predecessor_root
  generation := T.generation
  generation_decreases := T.generation_decreases
  chartPoint := T.chartPoint

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
