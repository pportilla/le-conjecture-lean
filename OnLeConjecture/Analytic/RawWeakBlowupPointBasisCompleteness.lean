/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RawWeakBlowupPointBasis
public import OnLeConjecture.Analytic.RawProjectiveWeakBlowupExistence
public import OnLeConjecture.Analytic.ProjectiveFixedTangentGenericAvoidance

/-!
# Completeness of the point basis constructed from a raw weak-blowup tree

Every projective common weak zero is a recorded tree child. Uniqueness
after cancellation of the exceptional power identifies any supplied
analytic weak transforms with the canonical ones. This proves the
finite-chart and two-chart completeness records in the literal point-basis
coordinates. The generation increases by exactly one on every edge.
-/

public section

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- Completeness in both projective charts at every vertex, with equality
of the recorded source equivalence itself. -/
theorem pointBasis_realizes_projective_common_zero
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (p : Fin (Fintype.card T.Vertex)) (t : Option ℂ) (G : ι → Germ 2)
    (htransform : ∀ i,
      (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
        ((projectiveChartSource t).forward.pullbackRingHom ((T.weakData q hq).generators p i)) =
      coordinate (1 : Fin 2) ^ (T.pointBasis q hq).multiplicity p * G i)
    (hG : ∀ i, G i ∈ maximalIdeal 2) :
    ∃ r, (T.pointBasis q hq).ParentRelation r p ∧
      (T.pointBasis q hq).chartCenter r = projectiveChartCenter t ∧
      (T.pointBasis q hq).sourceCoordinates r = projectiveChartSource t := by
  have hcanonical (i : ι) :
      projectiveWeakGenerators (T.multiplicity (T.indexEquiv.symm p))
        (T.generators (T.indexEquiv.symm p)) (T.generator_mem (T.indexEquiv.symm p)) t i =
      G i := by
    exact pointBlowupTransform_unique (projectiveChartCenter t)
      (T.multiplicity (T.indexEquiv.symm p))
      ((projectiveChartSource t).forward.pullbackRingHom
        (T.generators (T.indexEquiv.symm p) i)) _ _
      (pointBlowupTransform_factor _ _ _ _) (htransform i)
  obtain ⟨r, hr, hpred, hchart⟩ := T.realizes_common_zero (T.indexEquiv.symm p) t
    (fun i => (hcanonical i).symm ▸ hG i)
  refine ⟨T.indexEquiv r, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro h
    exact hr (T.indexEquiv.injective h)
  · change T.indexEquiv (T.predecessor (T.indexEquiv.symm (T.indexEquiv r))) = p
    rw [Equiv.symm_apply_apply, hpred, Equiv.apply_symm_apply]
  · change projectiveChartCenter (T.chartPoint (T.indexEquiv.symm (T.indexEquiv r))) = _
    rw [Equiv.symm_apply_apply, hchart]
  · change projectiveChartSource (T.chartPoint (T.indexEquiv.symm (T.indexEquiv r))) = _
    rw [Equiv.symm_apply_apply, hchart]

theorem finiteWeakBasepointCompleteness
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    FiniteWeakBasepointCompleteness (T.weakData q hq) := by
  refine ⟨?_⟩
  intro p ζ G htransform hG
  have hprojective : ∀ i,
      (pointBlowupChartGerm (projectiveChartCenter (some ζ))).pullbackRingHom
        ((projectiveChartSource (some ζ)).forward.pullbackRingHom
          ((T.weakData q hq).generators p i)) =
      coordinate (1 : Fin 2) ^ (T.pointBasis q hq).multiplicity p * G i := by
    simpa only [projectiveChartCenter, projectiveChartSource,
      PointedEquivGerm.identity_forward, PointedMapGerm.pullbackRingHom_identity,
      RingHom.id_apply] using htransform
  obtain ⟨r, hr, hcenter, hsource⟩ :=
    T.pointBasis_realizes_projective_common_zero q hq p (some ζ) G hprojective hG
  refine ⟨r, hr, hcenter, ?_⟩
  intro i
  rw [hsource, projectiveChartSource, PointedEquivGerm.identity_forward,
    PointedMapGerm.pullbackRingHom_identity]
  rfl

theorem rootTwoChartWeakBasepointCompleteness
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1)) :
    RootTwoChartWeakBasepointCompleteness (T.weakData q hq) := by
  refine ⟨?_⟩
  intro t G htransform hG
  obtain ⟨r, hr, hcenter, hsource⟩ := T.pointBasis_realizes_projective_common_zero
    q hq (T.pointBasis q hq).root t G htransform hG
  exact ⟨r, hr, hcenter, fun _ => by rw [hsource]⟩

theorem pointBasis_generation_eq_predecessor_add_one
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (p : Fin (Fintype.card T.Vertex)) (hp : p ≠ (T.pointBasis q hq).root) :
    (T.pointBasis q hq).generation p =
      (T.pointBasis q hq).generation ((T.pointBasis q hq).predecessor p) + 1 := by
  change T.generation (T.indexEquiv.symm p) =
    T.generation (T.indexEquiv.symm (T.indexEquiv (T.predecessor (T.indexEquiv.symm p)))) + 1
  rw [Equiv.symm_apply_apply]
  apply T.generation_eq_predecessor_add_one
  intro h
  apply hp
  change p = T.indexEquiv T.root
  rw [← h, Equiv.apply_symm_apply]

theorem pointBasis_root_depth
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (p : Fin (Fintype.card T.Vertex))
    (hp : (T.pointBasis q hq).ParentRelation p (T.pointBasis q hq).root) :
    (T.pointBasis q hq).generation p =
      (T.pointBasis q hq).generation (T.pointBasis q hq).root + 1 := by
  rw [T.pointBasis_generation_eq_predecessor_add_one q hq p hp.1, hp.2]

/-- Finite colength constructs the tree and an exact-order member in
the prescribed open set, together with both completeness records. -/
theorem exists_pointBasis_weakData_complete_mem_open
    (F : ι → Germ 2) (hproper : ∀ i, F i ∈ maximalIdeal 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ (N : ℕ) (c : AnalyticPointBasis N) (d : WeakTransformIdealData c ι) (q : ι → ℂ),
      q ∈ U ∧ d.generators c.root = F ∧
      (∀ p, c.germ p = germLinearCombination (d.generators p) q) ∧
      FiniteWeakBasepointCompleteness d ∧ RootTwoChartWeakBasepointCompleteness d ∧
      ∀ p, c.ParentRelation p c.root → c.generation p = c.generation c.root + 1 := by
  obtain ⟨T⟩ := RawProjectiveWeakBlowupTree.exists_of_finite_colength F hproper hfinite
  obtain ⟨q, hqU, hq⟩ := T.exists_exact_coefficients U hU hUne
  exact ⟨Fintype.card T.Vertex, T.pointBasis q hq, T.weakData q hq, q, hqU,
    T.weakData_root q hq, fun _ => rfl, T.finiteWeakBasepointCompleteness q hq,
    T.rootTwoChartWeakBasepointCompleteness q hq, T.pointBasis_root_depth q hq⟩

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
