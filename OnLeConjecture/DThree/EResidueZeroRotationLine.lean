/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.ERotationLineNoninjectivity
public import OnLeConjecture.DThree.HResidueZeroInvariantContradiction

/-!
# The E rotation line after a power substitution

The power substitution of an ordinary `E` rotation line has a transverse
weighted rotation pair. The rotation in the new source coordinate is an
`a`th root of the ordinary cubic rotation.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- Apply the power substitution to every coordinate of the ordinary
normalized `E` polynomial map. -/
@[expose]
noncomputable def eResidueZeroPolynomialMap
    (a : ℕ) (R : Form ℂ) : Fin 3 → Form ℂ :=
  fun i ↦ weightedPowerSubstitutionForm a (eInvariantPolynomialMap R i)

/-- The analytic function associated with the zero residue `E` polynomial
map. -/
@[expose]
noncomputable def eResidueZeroInitialMap
    (a : ℕ) (R : Form ℂ) : ℂ × ℂ → Fin 3 → ℂ :=
  weightedPolynomialMap (eResidueZeroPolynomialMap a R)

/-- The three weighted degrees after the power substitution. -/
@[expose]
noncomputable def eResidueZeroDegrees (a N : ℕ) : Fin 3 → ℕ :=
  ![3 * a, 4 * a, N * a]

/-- Multiplication of the ordinary degrees agrees with the substituted
weighted degrees. -/
theorem eResidueZeroDegrees_eq
    (a N : ℕ) :
    (fun i ↦ a * eInvariantDegrees N i) = eResidueZeroDegrees a N := by
  funext i
  fin_cases i
  · simpa [eInvariantDegrees, eResidueZeroDegrees] using Nat.mul_comm a 3
  · simpa [eInvariantDegrees, eResidueZeroDegrees] using Nat.mul_comm a 4
  · simpa [eInvariantDegrees, eResidueZeroDegrees] using Nat.mul_comm a N

/-- Each coordinate of the substituted `E` map has its prescribed weighted
degree. -/
theorem eResidueZeroPolynomialMap_isWeightedHomogeneous
    (a N : ℕ) (R : Form ℂ) (hR : R.IsHomogeneous N) (i : Fin 3) :
    (eResidueZeroPolynomialMap a R i).IsWeightedHomogeneous
      ![a, 1] (eResidueZeroDegrees a N i) := by
  have hhomogeneous :
      (eInvariantPolynomialMap R i).IsHomogeneous
        (eInvariantDegrees N i) := by
    have hweights : (![1, 1] : Fin 2 → ℕ) = 1 := by
      funext j
      fin_cases j
      · rfl
      · rfl
    change (eInvariantPolynomialMap R i).IsWeightedHomogeneous 1
      (eInvariantDegrees N i)
    rw [← hweights]
    exact eInvariantPolynomialMap_isWeightedHomogeneous R N hR i
  have hsubstitution := weightedPowerSubstitutionForm_isWeightedHomogeneous
    a (eInvariantDegrees N i) (eInvariantPolynomialMap R i) hhomogeneous
  change (weightedPowerSubstitutionForm a (eInvariantPolynomialMap R i))
    |>.IsWeightedHomogeneous ![a, 1] (eResidueZeroDegrees a N i)
  rw [← congrFun (eResidueZeroDegrees_eq a N) i]
  exact hsubstitution

/-- The determinant formula for an `E` rotation pair only requires its
`3 * a` power to equal one. -/
theorem det_eResidueRotationPointDerivative_of_three_pow_eq_one
    (a : ℕ) (x zeta : ℂ) (hzeta : zeta ^ (3 * a) = 1) :
    (eResidueRotationPointDerivative a x zeta).det =
      -(36 * (a : ℂ) * zeta ^ (3 * a - 1)) := by
  simpa [eResidueRotationPointDerivative,
    LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    eResidueRotationPointJacobian, Matrix.det_fin_two, hzeta] using
      (show Matrix.det (eResidueRotationPointJacobian a x zeta) =
          -(36 * (a : ℂ) * zeta ^ (3 * a - 1)) by
        simp [eResidueRotationPointJacobian, Matrix.det_fin_two, hzeta]
        ring)

/-- The point derivative is invertible at every nonzero weighted cubic
rotation pair. -/
@[expose]
noncomputable def eResidueRotationPointDerivativeEquivOfThreePow
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a)
    (hzeta : zeta ^ (3 * a) = 1) :
    (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (eResidueRotationPointDerivative a x zeta)
    |>.toContinuousLinearEquivOfDetNeZero <| by
      have hzetaNe : zeta ≠ 0 := by
        intro hzero
        rw [hzero, zero_pow (by omega : 3 * a ≠ 0)] at hzeta
        exact zero_ne_one hzeta
      rw [det_eResidueRotationPointDerivative_of_three_pow_eq_one
        a x zeta hzeta]
      exact neg_ne_zero.mpr <| mul_ne_zero
        (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr ha.ne'))
        (pow_ne_zero _ hzetaNe)

/-- The explicit branch solves the first two weighted `E` equations when
the cubic power of the rotation equals one. -/
theorem e_explicitRotationPlaneBranch_eq_zero_of_three_pow
    (a : ℕ) (x zeta : ℂ) (hzeta : zeta ^ (3 * a) = 1)
    (lambda : ℂ) :
    eResidueRotationPlaneDifference a x
      (lambda, explicitRotationPlaneBranch x zeta lambda) = 0 := by
  funext i
  fin_cases i
  all_goals simp [eResidueRotationPlaneDifference,
    explicitRotationPlaneBranch, hzeta]

/-- Near a weighted cubic rotation pair, the first two `E` fibre equations
consist exactly of the explicit rotation branch. -/
theorem
    eventually_eResidueRotationPlaneDifference_eq_zero_iff_explicitBranch_of_three_pow
    (a : ℕ) (x zeta : ℂ) (ha : 0 < a)
    (hzeta : zeta ^ (3 * a) = 1) :
    ∀ᶠ s in nhds (0, ![x, zeta]),
      eResidueRotationPlaneDifference a x s = 0 ↔
        explicitRotationPlaneBranch x zeta s.1 = s.2 := by
  let Phi := eResidueRotationPlaneDifference a x
  let base : ℂ × (Fin 2 → ℂ) := (0, ![x, zeta])
  let Phi' := fderiv ℂ Phi base
  have hPhi : HasStrictFDerivAt Phi Phi' base := by
    exact
      (analyticAt_eResidueRotationPlaneDifference a x base).hasStrictFDerivAt
  have hpoint :
      (Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ)).IsInvertible := by
    have heq :
        Phi' ∘L ContinuousLinearMap.inr ℂ ℂ (Fin 2 → ℂ) =
          eResidueRotationPointDerivative a x zeta := by
      simpa [Phi, Phi', base] using
        fderiv_eResidueRotationPlaneDifference_point a x zeta
    rw [heq]
    simpa [eResidueRotationPointDerivativeEquivOfThreePow] using
      (ContinuousLinearMap.isInvertible_equiv
        (f := eResidueRotationPointDerivativeEquivOfThreePow
          a x zeta ha hzeta))
  let psi := hPhi.implicitFunctionOfProdDomain hpoint
  have hbaseZero : Phi base = 0 := by
    simpa [Phi, base, explicitRotationPlaneBranch] using
      e_explicitRotationPlaneBranch_eq_zero_of_three_pow
        a x zeta hzeta 0
  have hlocal : ∀ᶠ s in nhds base,
      Phi s = 0 ↔ psi s.1 = s.2 := by
    filter_upwards
      [hPhi.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint]
      with s hs
    simpa [hbaseZero, psi] using hs
  have hexplicitPair : Tendsto
      (fun lambda ↦ (lambda, explicitRotationPlaneBranch x zeta lambda))
      (nhds 0) (nhds base) := by
    simpa [base] using
      tendsto_id.prodMk_nhds (tendsto_explicitRotationPlaneBranch x zeta)
  have hpsiExplicit : ∀ᶠ lambda in nhds 0,
      psi lambda = explicitRotationPlaneBranch x zeta lambda := by
    filter_upwards [hexplicitPair.eventually hlocal] with lambda hlocalAt
    exact hlocalAt.mp <| by
      simpa [Phi] using
        e_explicitRotationPlaneBranch_eq_zero_of_three_pow
          a x zeta hzeta lambda
  have hfst : Tendsto (fun s : ℂ × (Fin 2 → ℂ) ↦ s.1)
      (nhds base) (nhds 0) := by
    simpa [base] using
      (continuousAt_fst : ContinuousAt
        (fun s : ℂ × (Fin 2 → ℂ) ↦ s.1) base).tendsto
  have hpsiExplicitAtFirst : ∀ᶠ s in nhds base,
      psi s.1 = explicitRotationPlaneBranch x zeta s.1 :=
    hfst.eventually hpsiExplicit
  filter_upwards [hlocal, hpsiExplicitAtFirst]
    with s hlocalAt hpsiAt
  rw [hlocalAt, hpsiAt]

/-- At radial parameter zero, the first two differences are the weighted
`E` rotation equations. -/
theorem eResidueZeroRotationPlanePart_zero
    (a : ℕ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x lambda : ℂ) (v : Fin 2 → ℂ) :
    rotationPlanePart
        (weightedRescaledPerturbation
          (eResidueZeroInitialMap a R) remainder)
        x ((0, lambda), v) =
      eResidueRotationPlaneDifference a x (lambda, v) := by
  funext i
  fin_cases i
  · simp [rotationPlanePart, rotationReparametrization,
      rotationAffinePoint, weightedRescaledPerturbation_zero,
      weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, eResidueZeroInitialMap,
      eResidueZeroPolynomialMap, weightedPolynomialMap,
      eInvariantPolynomialMap, weightedPowerSubstitutionForm,
      cubicForm, formX, formT, eResidueRotationPlaneDifference]
    all_goals ring_nf
  · simp [rotationPlanePart, rotationReparametrization,
      rotationAffinePoint, weightedRescaledPerturbation_zero,
      weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, eResidueZeroInitialMap,
      eResidueZeroPolynomialMap, weightedPolynomialMap,
      eInvariantPolynomialMap, weightedPowerSubstitutionForm,
      quarticForm, formX, formT, eResidueRotationPlaneDifference]
    all_goals ring_nf
    all_goals simp

/-- On the explicit weighted branch, the third difference is the ordinary
rotation line polynomial. -/
theorem eResidueZeroRotationThirdPart_zero
    (a : ℕ) (omega : ℂ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x zeta lambda : ℂ) (hzeta : zeta ^ a = omega) :
    rotationThirdPart
        (weightedRescaledPerturbation
          (eResidueZeroInitialMap a R) remainder)
        x ((0, lambda), explicitRotationPlaneBranch x zeta lambda) =
      (eRotationLinePolynomial omega R).eval (x + lambda) := by
  rw [rotationThirdPart, rotationReparametrization,
    weightedRescaledPerturbation_zero]
  simp only [weightedInitialDifference, residueFirstChartPoint,
    residueSecondChartPoint, rotationAffinePoint,
    explicitRotationPlaneBranch, eResidueZeroInitialMap,
    Fin.isValue]
  change
    MvPolynomial.eval ![x + lambda, 1]
          (weightedPowerSubstitutionForm a R) -
        MvPolynomial.eval ![x + lambda, zeta]
          (weightedPowerSubstitutionForm a R) =
      (eRotationLinePolynomial omega R).eval (x + lambda)
  have hfirst :
      MvPolynomial.eval ![x + lambda, 1]
          (weightedPowerSubstitutionForm a R) =
        MvPolynomial.eval ![x + lambda, 1] R := by
    simpa using eval_weightedPowerSubstitutionForm a R (x + lambda, 1)
  have hsecond :
      MvPolynomial.eval ![x + lambda, zeta]
          (weightedPowerSubstitutionForm a R) =
        MvPolynomial.eval ![x + lambda, omega] R := by
    simpa [hzeta] using
      eval_weightedPowerSubstitutionForm a R (x + lambda, zeta)
  rw [hfirst, hsecond, eRotationLinePolynomial_eval]
  change MvPolynomial.eval ![x + lambda, 1] R -
      MvPolynomial.eval ![x + lambda, omega] R =
    MvPolynomial.eval ![x + lambda, 1] (R - eRotateForm omega R)
  rw [map_sub, eRotateForm_eval]
  simp

/-- The third difference on the explicit weighted branch is the restricted
rotation difference with exponent `a`. -/
theorem eResidueZeroRotationThirdPart_explicit
    (a : ℕ) (omega : ℂ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (x zeta lambda : ℂ) (hzeta : zeta ^ a = omega)
    (homega : omega ≠ 1) :
    rotationThirdPart
        (weightedRescaledPerturbation
          (eResidueZeroInitialMap a R) remainder)
        x ((0, lambda), explicitRotationPlaneBranch x zeta lambda) =
      residueRotationThirdDifference a
        (eRotationLineNormalizedPolynomial omega R) x
          (lambda, explicitRotationPlaneBranch x zeta lambda) := by
  let p := eRotationLineNormalizedPolynomial omega R
  have hrestricted :
      rotationRestrictedDifference zeta a p =
        rotationRestrictedDifference omega 1 p := by
    rw [rotationRestrictedDifference_eq, rotationRestrictedDifference_eq]
    simp [hzeta]
  calc
    rotationThirdPart
          (weightedRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder)
          x ((0, lambda), explicitRotationPlaneBranch x zeta lambda) =
        (eRotationLinePolynomial omega R).eval (x + lambda) :=
      eResidueZeroRotationThirdPart_zero
        a omega R remainder x zeta lambda hzeta
    _ = (rotationRestrictedDifference omega 1 p).eval (x + lambda) := by
      rw [rotationRestrictedDifference_normalizedRotationLine homega]
    _ = (rotationRestrictedDifference zeta a p).eval (x + lambda) := by
      rw [hrestricted]
    _ = residueRotationThirdDifference a p x
        (lambda, explicitRotationPlaneBranch x zeta lambda) := by
      rw [residueRotationThirdDifference]
      exact (explicitRotationThirdDifference_eq
        a p x zeta lambda).symm

/-- An ordinary `E` rotation line collision persists after every positive
power substitution. -/
theorem eventually_exists_eResidueZeroRotationZero_mem_nhds
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (a : ℕ) (ha : 0 < a)
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (data : ERotationLineCollisionCertificate omega R)
    (zeta : ℂ) (hzeta : zeta ^ a = omega)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder
      (0, (data.x / data.t, 1)))
    (hsecond : AnalyticAt ℂ remainder
      (0, (data.x / data.t, zeta)))
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds
      (0, ![data.x / data.t, data.x / data.t, zeta])) :
    ∀ᶠ tau in nhds 0,
      ∃ q : Fin 3 → ℂ,
        (tau, q) ∈ U ∧
          weightedRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder (tau, q) = 0 := by
  let x := data.x / data.t
  let p := eRotationLineNormalizedPolynomial omega R
  let Phi := weightedRescaledPerturbation
    (eResidueZeroInitialMap a R) remainder
  have homegaCube : omega ^ 3 = 1 := homega.pow_eq_one
  have homegaOne : omega ≠ 1 := homega.ne_one (by norm_num)
  have hzetaThreeA : zeta ^ (3 * a) = 1 := by
    calc
      zeta ^ (3 * a) = zeta ^ (a * 3) := by
        congr 1
        omega
      _ = (zeta ^ a) ^ 3 := by rw [pow_mul]
      _ = 1 := by rw [hzeta, homegaCube]
  have hzetaA : zeta ^ a ≠ 1 := by
    rw [hzeta]
    exact homegaOne
  have hpBase : eRotationLinePolynomial omega R ≠ 0 :=
    eRotationLinePolynomial_ne_zero hR data.rotationDifference_ne_zero
  have hp : p ≠ 0 :=
    eRotationLineNormalizedPolynomial_ne_zero homegaOne hpBase
  have hx : p.IsRoot x :=
    eRotationLineNormalizedPolynomial_isRoot (data.chart_root hR)
  have hPhi : AnalyticAt ℂ Phi (0, ![x, x, zeta]) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (eResidueZeroPolynomialMap a R) _
    · simpa [x, residueFirstChartPoint] using hfirst
    · simpa [x, residueSecondChartPoint] using hsecond
  apply eventually_exists_rotationZero_mem_nhds_of_explicitThird
    Phi (eResidueRotationPlaneDifference a x)
      (eResidueRotationPointDerivativeEquivOfThreePow
        a x zeta ha hzetaThreeA)
      x zeta a p hPhi
  · exact eResidueZeroRotationPlanePart_zero a R remainder x
  · simpa [eResidueRotationPointDerivativeEquivOfThreePow] using
      hasStrictFDerivAt_eResidueRotationPlaneDifference_point a x zeta
  · simpa [explicitRotationPlaneBranch] using
      e_explicitRotationPlaneBranch_eq_zero_of_three_pow
        a x zeta hzetaThreeA 0
  · exact
      eventually_eResidueRotationPlaneDifference_eq_zero_iff_explicitBranch_of_three_pow
        a x zeta ha hzetaThreeA
  · intro lambda
    exact eResidueZeroRotationThirdPart_explicit
      a omega R remainder x zeta lambda hzeta homegaOne
  · exact hzetaA
  · exact hp
  · exact hx
  · simpa [x] using hU

/-- Weighted tails above a substituted `E` rotation line exclude an
injective representative. -/
theorem
    eRotationLineResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    {omega : ℂ} {R : Form ℂ} {N : ℕ}
    (a : ℕ) (ha : 0 < a)
    (homega : IsPrimitiveRoot omega 3)
    (hR : R.IsHomogeneous N)
    (data : ERotationLineCollisionCertificate omega R)
    (representative : ℂ × ℂ → Fin 3 → ℂ)
    (hanalytic : AnalyticAt ℂ representative 0)
    (hzero : representative 0 = 0)
    (htail : ∀ i,
      pairRepresentativeComponentGerm representative hanalytic i -
          Germ.coordinatePolynomialAlgHom 2
            (eResidueZeroPolynomialMap a R i) ∈
        Germ.weightedOrderIdeal a
          (eResidueZeroDegrees a N i + 1)) :
    ¬ PointedMapGerm.HasInjectiveRepresentative
      (PointedMapGerm.ofPairFunction representative hanalytic hzero) := by
  obtain ⟨zeta, hzeta⟩ := IsAlgClosed.exists_pow_nat_eq omega ha
  have hzetaNe : zeta ≠ 1 := by
    intro hζ
    apply homega.ne_one (by norm_num)
    rw [← hzeta, hζ, one_pow]
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (eResidueZeroDegrees a N) (eResidueZeroPolynomialMap a R)
        (eResidueZeroPolynomialMap_isWeightedHomogeneous a N R hR)
          representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_weightedRotationZeros
    a (eResidueZeroDegrees a N) (eResidueZeroInitialMap a R)
      representative remainder (data.x / data.t) zeta ha hzetaNe
  · simpa [eResidueZeroInitialMap] using
      hexpansion (data.x / data.t, 1)
  · simpa [eResidueZeroInitialMap] using
      hexpansion (data.x / data.t, zeta)
  · intro U hU
    exact eventually_exists_eResidueZeroRotationZero_mem_nhds
      a ha homega hR data zeta hzeta remainder
        (hexpansion (data.x / data.t, 1)).remainder_analyticAt
        (hexpansion (data.x / data.t, zeta)).remainder_analyticAt U hU

end OnLeConjecture.DThree
