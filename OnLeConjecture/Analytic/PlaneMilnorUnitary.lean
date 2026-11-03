/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibreHomology
public import OnLeConjecture.Analytic.LinearCoordinates
public import OnLeConjecture.PlaneCurve.BranchCountInvariance
public import OnLeConjecture.Analytic.TransverseSmoothPreparation
public import OnLeConjecture.Analytic.ReducedPlaneIsolatedCritical

/-!
# Unitary coordinates for Milnor fibres

For a unit vector `v` of `ℂ²` let `U_v` be the unitary map with matrix
`[[v₀, −conj v₁], [v₁, conj v₀]]`, so `U_v e₀ = v`. It preserves the Euclidean
norm, so the Milnor fibre of `H ∘ U_v` is homeomorphic to that of `H` through
`U_v`, and the analytic invariants of the germs agree: squarefreeness, the
Milnor number and the number of branches.

Every nonzero germ is nonzero on some complex line through the origin, so for
a suitable unit vector `v` the germ of `H ∘ U_v` meets the coordinate axis
`x = 0` with finite multiplicity.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-- The matrix with first column `v` and second column `(−conj v₁, conj v₀)`. -/
def unitaryMatrix (v : Source 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![v 0, -(starRingEnd ℂ (v 1)); v 1, starRingEnd ℂ (v 0)]

/-- A unit vector in the Euclidean sense. -/
def IsUnitVec (v : Source 2) : Prop :=
  starRingEnd ℂ (v 0) * v 0 + starRingEnd ℂ (v 1) * v 1 = 1

theorem IsUnitVec.re_im {v : Source 2} (hv : IsUnitVec v) :
    (v 0).re * (v 0).re + (v 0).im * (v 0).im + ((v 1).re * (v 1).re + (v 1).im * (v 1).im) =
      1 := by
  have h := congrArg Complex.re hv
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.one_re] at h
  linarith

theorem unitaryMatrix_mul_conjTranspose {v : Source 2} (hv : IsUnitVec v) :
    unitaryMatrix v * (unitaryMatrix v).conjTranspose = 1 := by
  have h := hv.re_im
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [unitaryMatrix, Fin.isValue, Fin.mk_one, Fin.sum_univ_two, Fin.zero_eta, map_neg,
      Matrix.conjTranspose_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne, mul_neg, ne_eq, neg_mul, neg_neg, not_false_eq_true, one_ne_zero,
      RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply, zero_ne_one] <;>
    apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im] <;>
    first | ring1 | linear_combination h

theorem conjTranspose_mul_unitaryMatrix {v : Source 2} (hv : IsUnitVec v) :
    (unitaryMatrix v).conjTranspose * unitaryMatrix v = 1 := by
  have h := hv.re_im
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [unitaryMatrix, Fin.isValue, Fin.mk_one, Fin.sum_univ_two, Fin.zero_eta, map_neg,
      Matrix.conjTranspose_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne, mul_neg, ne_eq, neg_mul, neg_neg, not_false_eq_true, one_ne_zero,
      RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply, zero_ne_one] <;>
    apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im] <;>
    first | ring1 | linear_combination h

/-- The unitary map as a continuous linear equivalence of `Source 2`. -/
def unitaryEquiv (v : Source 2) (hv : IsUnitVec v) : Source 2 ≃L[ℂ] Source 2 :=
  (LinearEquiv.ofLinearMap (Matrix.toLin' (unitaryMatrix v))
    (Matrix.toLin' (unitaryMatrix v).conjTranspose)
    (by rw [← Matrix.toLin'_mul, unitaryMatrix_mul_conjTranspose hv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, conjTranspose_mul_unitaryMatrix hv,
      Matrix.toLin'_one])).toContinuousLinearEquiv

theorem unitaryEquiv_apply (v : Source 2) (hv : IsUnitVec v) (w : Source 2) :
    unitaryEquiv v hv w =
      ![v 0 * w 0 + -(starRingEnd ℂ (v 1)) * w 1, v 1 * w 0 + starRingEnd ℂ (v 0) * w 1] := by
  funext i
  fin_cases i <;>
    simp [unitaryEquiv, unitaryMatrix, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

theorem unitaryEquiv_smul_e₀ (v : Source 2) (hv : IsUnitVec v) (t : ℂ) :
    unitaryEquiv v hv (t • coordinateVector (0 : Fin 2)) = t • v := by
  rw [unitaryEquiv_apply]
  funext i
  fin_cases i <;> simp [coordinateVector, mul_comm]

/-- Lagrange's identity for the unitary matrix. -/
theorem normSq_unitary (a b x y : ℂ) :
    Complex.normSq (a * x + -(starRingEnd ℂ b) * y) +
        Complex.normSq (b * x + starRingEnd ℂ a * y) =
      (Complex.normSq a + Complex.normSq b) * (Complex.normSq x + Complex.normSq y) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im]
  ring

theorem IsUnitVec.normSq {v : Source 2} (hv : IsUnitVec v) :
    Complex.normSq (v 0) + Complex.normSq (v 1) = 1 := by
  have h := congrArg Complex.re hv
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.one_re] at h
  rw [Complex.normSq_apply, Complex.normSq_apply]
  linarith

/-- The unitary map in Euclidean coordinates. -/
def euclideanUnitary (v : Source 2) (hv : IsUnitVec v) :
    EuclideanSpace ℂ (Fin 2) ≃ₜ EuclideanSpace ℂ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℂ).toHomeomorph.trans
    ((unitaryEquiv v hv).toHomeomorph.trans (EuclideanSpace.equiv (Fin 2) ℂ).symm.toHomeomorph)

theorem euclideanUnitary_apply (v : Source 2) (hv : IsUnitVec v)
    (w : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace.equiv (Fin 2) ℂ (euclideanUnitary v hv w) =
      unitaryEquiv v hv (EuclideanSpace.equiv (Fin 2) ℂ w) :=
  rfl

theorem norm_euclideanUnitary (v : Source 2) (hv : IsUnitVec v)
    (w : EuclideanSpace ℂ (Fin 2)) : ‖euclideanUnitary v hv w‖ = ‖w‖ := by
  have hcoord : ∀ i, (euclideanUnitary v hv w) i =
      unitaryEquiv v hv (EuclideanSpace.equiv (Fin 2) ℂ w) i := fun i => by
    rw [← euclideanUnitary_apply]
    rfl
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_two, Fin.sum_univ_two,
    hcoord, hcoord, unitaryEquiv_apply]
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← Complex.normSq_eq_norm_sq]
  rw [normSq_unitary, hv.normSq, one_mul]
  rfl

/-- The Milnor fibres of `H ∘ U_v` and `H` correspond under `U_v`. -/
def milnorFibreUnitaryHomeomorph (H : Source 2 → ℂ) (v : Source 2) (hv : IsUnitVec v)
    (ε : ℝ) (s : ℂ) :
    ↥(milnorFibre (H ∘ unitaryEquiv v hv) ε s) ≃ₜ ↥(milnorFibre H ε s) :=
  (euclideanUnitary v hv).subtype fun w => by
    simp only [milnorFibre, mem_ofPred_eq, norm_euclideanUnitary, euclideanEquation,
      euclideanUnitary_apply, Function.comp_apply]

/-- The boundaries of the Milnor fibres of `H ∘ U_v` and `H` correspond under `U_v`. -/
def milnorFibreBoundaryUnitaryHomeomorph (H : Source 2 → ℂ) (v : Source 2) (hv : IsUnitVec v)
    (ε : ℝ) (s : ℂ) :
    ↥(milnorFibreBoundary (H ∘ unitaryEquiv v hv) ε s) ≃ₜ ↥(milnorFibreBoundary H ε s) :=
  (euclideanUnitary v hv).subtype fun w => by
    simp only [milnorFibreBoundary, mem_ofPred_eq, norm_euclideanUnitary, euclideanEquation,
      euclideanUnitary_apply, Function.comp_apply]

theorem analyticAt_comp_unitary {H : Source 2 → ℂ} (hH : AnalyticAt ℂ H 0) (v : Source 2)
    (hv : IsUnitVec v) : AnalyticAt ℂ (H ∘ unitaryEquiv v hv) 0 := by
  have h0 : unitaryEquiv v hv 0 = 0 := map_zero _
  exact (by rw [h0]; exact hH : AnalyticAt ℂ H (unitaryEquiv v hv 0)).comp
    ((unitaryEquiv v hv).analyticAt 0)

/-- The germ of `H ∘ U_v` is the pullback of the germ of `H`. -/
theorem ofFunction_comp_unitary {H : Source 2 → ℂ} (hH : AnalyticAt ℂ H 0) (v : Source 2)
    (hv : IsUnitVec v) :
    ofFunction (H ∘ unitaryEquiv v hv) (analyticAt_comp_unitary hH v hv) =
      (pointedEquivGermOfContinuousLinearEquiv (unitaryEquiv v hv)).forward.pullbackRingHom
        (ofFunction H hH) := by
  rw [PointedMapGerm.pullbackRingHom_apply]
  exact (compPointed_ofFunction H hH _ _ (map_zero _)).symm

/-- **Unitary invariance of the analytic invariants.** -/
theorem unitary_invariants {H : Source 2 → ℂ} (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) (v : Source 2) (hv : IsUnitVec v) :
    Squarefree (ofFunction (H ∘ unitaryEquiv v hv) (analyticAt_comp_unitary hH v hv)) ∧
      Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal
          (ofFunction (H ∘ unitaryEquiv v hv) (analyticAt_comp_unitary hH v hv))) =
        Module.finrank ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) ∧
      irreducibleBranchCount
          (ofFunction (H ∘ unitaryEquiv v hv) (analyticAt_comp_unitary hH v hv)) =
        irreducibleBranchCount (ofFunction H hH) := by
  set e := pointedEquivGermOfContinuousLinearEquiv (unitaryEquiv v hv)
  rw [ofFunction_comp_unitary hH v hv]
  have hfm : ofFunction H hH ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff, valueRingHom_ofFunction]
    exact hH0
  have hsq' := PointedEquivGerm.squarefree_pullback e _ hsq
  refine ⟨hsq', ?_, (irreducibleBranchCount_pullback e _).symm⟩
  have hfm' : e.forward.pullbackRingHom (ofFunction H hH) ∈ maximalIdeal 2 :=
    e.forward.pullback_mem_maximalIdeal hfm
  have hfin1 : Module.Finite ℂ (Germ 2 ⧸ jacobianIdeal (ofFunction H hH)) :=
    hasFiniteJacobianAlgebra_of_squarefree _ hfm hsq
  have hfin2 : Module.Finite ℂ
      (Germ 2 ⧸ jacobianIdeal (e.pullbackAlgEquiv (ofFunction H hH))) :=
    hasFiniteJacobianAlgebra_of_squarefree _ hfm' hsq'
  exact (@Germ.quotient_finrank_eq_of_map_eq 2 (jacobianIdeal (ofFunction H hH))
    (jacobianIdeal (e.pullbackAlgEquiv (ofFunction H hH))) e.pullbackAlgEquiv
    (map_jacobianIdeal_pullbackAlgEquiv e _) hfin1 hfin2).symm

/-- **A unitary direction transverse to the curve.** -/
theorem exists_unitVec_axis {H : Source 2 → ℂ} (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∃ v : Source 2, ∃ hv : IsUnitVec v,
      HasFiniteIntersection (ofFunction (H ∘ unitaryEquiv v hv) (analyticAt_comp_unitary hH v hv))
        (coordinate (1 : Fin 2)) := by
  obtain ⟨w, hw⟩ := exists_lineRestriction_ne_zero hsq.ne_zero
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hw
    rw [lineRestriction_zero, valueRingHom_ofFunction, hH0, map_zero]
  -- normalize
  set N : ℝ := Complex.normSq (w 0) + Complex.normSq (w 1) with hN
  have hNpos : 0 < N := by
    by_contra hle
    push Not at hle
    have h0 : Complex.normSq (w 0) = 0 := le_antisymm (by
      have := Complex.normSq_nonneg (w 1)
      linarith) (Complex.normSq_nonneg _)
    have h1 : Complex.normSq (w 1) = 0 := le_antisymm (by
      have := Complex.normSq_nonneg (w 0)
      linarith) (Complex.normSq_nonneg _)
    apply hw0
    funext i
    fin_cases i
    · exact Complex.normSq_eq_zero.mp h0
    · exact Complex.normSq_eq_zero.mp h1
  set c : ℝ := (Real.sqrt N)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hNpos)
  set v : Source 2 := (c : ℂ) • w with hvdef
  have hv : IsUnitVec v := by
    unfold IsUnitVec
    have hcc : c * c * N = 1 := by
      rw [hc, ← mul_inv, Real.mul_self_sqrt hNpos.le, inv_mul_cancel₀ hNpos.ne']
    apply Complex.ext
    · simp only [hvdef, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Complex.add_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
        Complex.mul_im, Complex.one_re]
      rw [hN, Complex.normSq_apply, Complex.normSq_apply] at hcc
      linear_combination hcc
    · simp only [hvdef, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Complex.add_im,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
        Complex.mul_im, Complex.one_im]
      ring
  refine ⟨v, hv, ?_⟩
  rw [hasFiniteIntersection_comm]
  apply hasFiniteIntersection_secondCoordinate_of_firstAxisRestriction_ne_zero
  intro h0
  apply hw
  rw [lineRestriction_ofFunction] at h0 ⊢
  -- the restriction to `w` is a rescaling of the restriction to the axis
  have hz : ∀ᶠ t in 𝓝 (0 : Source 1),
      (H ∘ unitaryEquiv v hv ∘ lineMap (firstCoordinateVector 1)) t = 0 := by
    have := congrArg Subtype.val h0
    exact Filter.Germ.coe_eq.mp this
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have hscale : Tendsto (fun t : Source 1 => (c : ℂ)⁻¹ • t) (𝓝 0) (𝓝 0) := by
    have := (continuous_const_smul ((c : ℂ)⁻¹)).tendsto (0 : Source 1)
    rwa [smul_zero] at this
  filter_upwards [hscale.eventually hz] with t ht
  have hpt : unitaryEquiv v hv (lineMap (firstCoordinateVector 1) ((c : ℂ)⁻¹ • t)) =
      lineMap w t := by
    rw [lineMap_apply, lineMap_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : firstCoordinateVector 1 = coordinateVector (0 : Fin 2) := rfl
    rw [h1, unitaryEquiv_smul_e₀, hvdef, smul_smul]
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    congr 1
    field_simp
  simp only [Function.comp_apply] at ht
  rw [hpt] at ht
  exact ht

end OnLeConjecture.Analytic
