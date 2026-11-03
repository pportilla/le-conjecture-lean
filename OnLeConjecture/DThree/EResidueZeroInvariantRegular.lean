/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DThree.EResidueZeroRotationLine
public import OnLeConjecture.DThree.EInvariantRegularContradiction

/-!
# Regular invariant E collisions after a power substitution

At a regular invariant collision, the second coordinate of the second chart
point is nonzero. An analytic root chart transports ordinary collision
persistence to every positive source weight.
-/

public section

open Filter Metric Set
open scoped Topology

namespace OnLeConjecture.DThree

open _root_.Polynomial
open OnLeConjecture.Analytic

/-- A nonzero point and a chosen `a`th root determine an analytic root of
the identity near that point. -/
theorem exists_analyticAt_root_identity_with_value
    (a : ℕ) (ha : 0 < a) (w c : ℂ)
    (hw : w ≠ 0) (hc : c ^ a = w) :
    ∃ root : ℂ → ℂ,
      AnalyticAt ℂ root w ∧ root w = c ∧
        ∀ z, root z ^ a = z := by
  let translated : ℂ → ℂ := fun z ↦ w + z
  have htranslated : AnalyticAt ℂ translated 0 :=
    analyticAt_const.add analyticAt_id
  have htranslatedZero : translated 0 = w := by
    simp [translated]
  obtain ⟨localRoot, hlocalRoot, hlocalRootZero, hlocalRootPower⟩ :=
    exists_analyticAt_root_with_value translated htranslated
      (by simpa [htranslatedZero] using hw) a ha.ne' c
        (by simpa [htranslatedZero] using hc)
  let root : ℂ → ℂ := fun z ↦ localRoot (z - w)
  have hargument : AnalyticAt ℂ (fun z : ℂ ↦ z - w) w :=
    analyticAt_id.sub analyticAt_const
  have hroot : AnalyticAt ℂ root w := by
    have hlocalAt : AnalyticAt ℂ localRoot (w - w) := by
      simpa using hlocalRoot
    exact AnalyticAt.fun_comp
      (x := w) (g := localRoot) (f := fun z : ℂ ↦ z - w)
        hlocalAt hargument
  refine ⟨root, hroot, ?_, ?_⟩
  · simp [root, hlocalRootZero]
  · intro z
    change localRoot (z - w) ^ a = z
    rw [hlocalRootPower]
    simp [translated]

/-- Replace the second coordinate of the second chart point by an analytic
root. -/
@[expose]
noncomputable def eResidueZeroRootChart
    (root : ℂ → ℂ) (q : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![q 0, q 1, root (q 2)]

/-- Pull an analytic perturbation back through a root chart. -/
@[expose]
noncomputable def eResidueZeroRootPullback
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (root : ℂ → ℂ) (q : ℂ × (Fin 3 → ℂ)) : Fin 3 → ℂ :=
  Phi (q.1, eResidueZeroRootChart root q.2)

theorem analyticAt_eResidueZeroRootChart
    (root : ℂ → ℂ) (q : Fin 3 → ℂ)
    (hroot : AnalyticAt ℂ root (q 2)) :
    AnalyticAt ℂ (eResidueZeroRootChart root) q := by
  have hcoordinate (i : Fin 3) : AnalyticAt ℂ
      (fun value : Fin 3 → ℂ ↦ value i) q :=
    (ContinuousLinearMap.proj (R := ℂ) i).analyticAt q
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i
  · exact hcoordinate 0
  · exact hcoordinate 1
  · exact AnalyticAt.fun_comp
      (x := q) (g := root) (f := fun value : Fin 3 → ℂ ↦ value 2)
        hroot (hcoordinate 2)

theorem analyticAt_eResidueZeroRootPullback
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (root : ℂ → ℂ) (q : ℂ × (Fin 3 → ℂ))
    (hroot : AnalyticAt ℂ root (q.2 2))
    (hPhi : AnalyticAt ℂ Phi
      (q.1, eResidueZeroRootChart root q.2)) :
    AnalyticAt ℂ (eResidueZeroRootPullback Phi root) q := by
  have hlift : AnalyticAt ℂ
      (fun value : ℂ × (Fin 3 → ℂ) ↦
        (value.1, eResidueZeroRootChart root value.2)) q :=
    analyticAt_fst.prod
      ((analyticAt_eResidueZeroRootChart root q.2 hroot).fun_comp
        analyticAt_snd)
  exact AnalyticAt.fun_comp
    (x := q) (g := Phi)
      (f := fun value : ℂ × (Fin 3 → ℂ) ↦
        (value.1, eResidueZeroRootChart root value.2))
      hPhi hlift

/-- The pulled back special fibre has the ordinary invariant plane
difference. -/
theorem eInvariantPlanePart_eResidueZeroRootPullback_zero
    (a : ℕ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (root : ℂ → ℂ) (hroot : ∀ z, root z ^ a = z)
    (z lambda : ℂ) (v : Fin 2 → ℂ) :
    eInvariantPlanePart
        (eResidueZeroRootPullback
          (weightedRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder) root)
        z ((0, lambda), v) =
      eInvariantPlaneDifference z (lambda, v) := by
  funext i
  fin_cases i
  · simp [eInvariantPlanePart, eInvariantReparametrization,
      eInvariantAffinePoint, eResidueZeroRootPullback,
      eResidueZeroRootChart, weightedRescaledPerturbation_zero,
      weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, eResidueZeroInitialMap,
      eResidueZeroPolynomialMap, weightedPolynomialMap,
      eInvariantPolynomialMap, weightedPowerSubstitutionForm,
      cubicForm, formX, formT, eInvariantPlaneDifference, hroot]
    all_goals ring_nf
  · simp [eInvariantPlanePart, eInvariantReparametrization,
      eInvariantAffinePoint, eResidueZeroRootPullback,
      eResidueZeroRootChart, weightedRescaledPerturbation_zero,
      weightedInitialDifference, residueFirstChartPoint,
      residueSecondChartPoint, eResidueZeroInitialMap,
      eResidueZeroPolynomialMap, weightedPolynomialMap,
      eInvariantPolynomialMap, weightedPowerSubstitutionForm,
      quarticForm, formX, formT, eInvariantPlaneDifference, hroot]
    all_goals ring_nf

/-- The third coordinate of the pulled back special fibre is the ordinary
third initial difference. -/
theorem eInvariantThirdPart_eResidueZeroRootPullback_zero
    (a : ℕ) (R : Form ℂ)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (root : ℂ → ℂ) (hroot : ∀ z, root z ^ a = z)
    (z lambda : ℂ) (v : Fin 2 → ℂ) :
    eInvariantThirdPart
        (eResidueZeroRootPullback
          (weightedRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder) root)
        z ((0, lambda), v) =
      weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 0 * (z + lambda), 1) 2 -
        weightedPolynomialMap (eInvariantPolynomialMap R)
          (v 0, v 1) 2 := by
  rw [eInvariantThirdPart, eInvariantReparametrization,
    eInvariantAffinePoint, eResidueZeroRootPullback,
    eResidueZeroRootChart, weightedRescaledPerturbation_zero]
  change
    MvPolynomial.eval ![v 0 * (z + lambda), 1]
          (weightedPowerSubstitutionForm a R) -
        MvPolynomial.eval ![v 0, root (v 1)]
          (weightedPowerSubstitutionForm a R) =
      MvPolynomial.eval ![v 0 * (z + lambda), 1] R -
        MvPolynomial.eval ![v 0, v 1] R
  have hfirst := eval_weightedPowerSubstitutionForm
    a R (v 0 * (z + lambda), 1)
  have hsecond := eval_weightedPowerSubstitutionForm
    a R (v 0, root (v 1))
  simpa [hroot] using congrArg₂ (· - ·) hfirst hsecond

/-- A regular invariant collision persists after a positive power
substitution when a root of its second chart coordinate is fixed. -/
theorem eventually_exists_eResidueZeroInvariantRegularZero_mem_nhds
    (a : ℕ) (ha : 0 < a)
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n : ℕ)
    (z s g eta : ℂ) (heta : eta ^ a = g)
    (remainder : ℂ × (ℂ × ℂ) → Fin 3 → ℂ)
    (hfirst : AnalyticAt ℂ remainder (0, (s * z, 1)))
    (hsecond : AnalyticAt ℂ remainder (0, (s, eta)))
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hhomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hs : s ^ 3 * eResidualW z 1 = 1)
    (hg : g ^ 3 = s ^ 3 * eResidualW 1 z)
    (hW : eResidualW 1 z ≠ 0)
    (U : Set (ℂ × (Fin 3 → ℂ)))
    (hU : U ∈ nhds (0, ![s * z, s, eta])) :
    ∀ᶠ tau in nhds 0,
      ∃ point : Fin 3 → ℂ,
        (tau, point) ∈ U ∧
          weightedRescaledPerturbation
            (eResidueZeroInitialMap a R) remainder (tau, point) = 0 := by
  have hgNe : g ≠ 0 := eInvariant_chart_g_ne_zero hs hg hW
  obtain ⟨root, hrootAnalytic, hrootValue, hrootPower⟩ :=
    exists_analyticAt_root_identity_with_value
      a ha g eta hgNe heta
  let Phi := weightedRescaledPerturbation
    (eResidueZeroInitialMap a R) remainder
  let Psi := eResidueZeroRootPullback Phi root
  let ordinaryBase : Fin 3 → ℂ := ![s * z, s, g]
  let weightedBase : Fin 3 → ℂ := ![s * z, s, eta]
  have hchartBase :
      eResidueZeroRootChart root ordinaryBase = weightedBase := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · simp [eResidueZeroRootChart, ordinaryBase, weightedBase,
        hrootValue]
  have hPhi : AnalyticAt ℂ Phi (0, weightedBase) := by
    apply analyticAt_weightedRescaledPerturbation
    · exact analyticAt_weightedInitialDifference_weightedPolynomialMap
        (eResidueZeroPolynomialMap a R) weightedBase
    · simpa [weightedBase, residueFirstChartPoint] using hfirst
    · simpa [weightedBase, residueSecondChartPoint] using hsecond
  have hPsi : AnalyticAt ℂ Psi (0, ordinaryBase) := by
    apply analyticAt_eResidueZeroRootPullback
    · simpa [ordinaryBase] using hrootAnalytic
    · simpa [hchartBase] using hPhi
  let lift : ℂ × (Fin 3 → ℂ) → ℂ × (Fin 3 → ℂ) := fun q ↦
    (q.1, eResidueZeroRootChart root q.2)
  let V : Set (ℂ × (Fin 3 → ℂ)) := lift ⁻¹' U
  have hliftAnalytic : AnalyticAt ℂ lift (0, ordinaryBase) := by
    have hchart : AnalyticAt ℂ
        (eResidueZeroRootChart root) ordinaryBase :=
      analyticAt_eResidueZeroRootChart root ordinaryBase (by
        simpa [ordinaryBase] using hrootAnalytic)
    exact analyticAt_fst.prod (hchart.fun_comp analyticAt_snd)
  have hliftBase : lift (0, ordinaryBase) = (0, weightedBase) := by
    simp [lift, hchartBase]
  have hV : V ∈ nhds (0, ordinaryBase) := by
    have ht := hliftAnalytic.continuousAt
    change Tendsto lift (nhds (0, ordinaryBase))
      (nhds (lift (0, ordinaryBase))) at ht
    rw [hliftBase] at ht
    exact ht.eventually hU
  have hzero :=
    eventually_exists_eInvariantRegularZero_mem_nhds_of_analyticPerturbation
      Psi Rzero R c n z s g hdescent hdecomposition hhomogeneous hp
        hzRoot hzOne hs hg hW hPsi
        (eInvariantPlanePart_eResidueZeroRootPullback_zero
          a R remainder root hrootPower z)
        (eInvariantThirdPart_eResidueZeroRootPullback_zero
          a R remainder root hrootPower z)
        V hV
  filter_upwards [hzero] with tau htau
  obtain ⟨point, hmem, hzeroAt⟩ := htau
  exact ⟨eResidueZeroRootChart root point, hmem, hzeroAt⟩

/-- Weighted tails exclude an injective representative at a regular
invariant residual root after every positive power substitution. -/
theorem
    eInvariantRegularResidueZeroWeightedOrderTails_not_hasInjectiveRepresentative
    (a : ℕ) (ha : 0 < a)
    (Rzero : ESourceRing ℂ) (R : Form ℂ)
    (c : Fin 4 → EBaseRing ℂ) (n N : ℕ) (z : ℂ)
    (hR : R.IsHomogeneous N)
    (hdescent : eSourceCubeSubstitutionForm Rzero = R)
    (hdecomposition :
      Rzero = ∑ i : Fin 4,
        eBaseToSource ℂ (c i) * eSourceX ℂ ^ (i : ℕ))
    (hThetaHomogeneous : EPairIsHomogeneous (eThetaPolynomial ℂ c) n)
    (hp : ePairDehomogenize (eThetaPolynomial ℂ c) ≠ 0)
    (hzRoot :
      (ePairDehomogenize (eThetaPolynomial ℂ c)).IsRoot z)
    (hzOne : z ≠ 1)
    (hw : eResidualW z 1 ≠ 0)
    (hW : eResidualW 1 z ≠ 0)
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
  obtain ⟨s, g, hs, hg⟩ :=
    exists_eInvariantRegularChartCoordinates z hw
  have hgNe : g ≠ 0 := eInvariant_chart_g_ne_zero hs hg hW
  obtain ⟨eta, heta⟩ := IsAlgClosed.exists_pow_nat_eq g ha
  have hetaNe : eta ≠ 0 := by
    intro hzeroEta
    apply hgNe
    rw [← heta, hzeroEta, zero_pow ha.ne']
  have hsNe : s ≠ 0 := eInvariant_chart_s_ne_zero hs
  have hdistinct : s * z ≠ s := by
    intro hequal
    apply hzOne
    apply mul_left_cancel₀ hsNe
    simpa using hequal
  obtain ⟨remainder, hexpansion⟩ :=
    exists_hasWeightedRadialExpansionAt_of_mem_weightedOrderIdeal
      a ha (eResidueZeroDegrees a N) (eResidueZeroPolynomialMap a R)
        (eResidueZeroPolynomialMap_isWeightedHomogeneous a N R hR)
          representative hanalytic htail
  apply PointedMapGerm.ofPairFunction_not_hasInjectiveRepresentative
  apply not_neighborhood_injective_of_weightedZeros_at_distinct_first
    a (eResidueZeroDegrees a N) (eResidueZeroInitialMap a R)
      representative remainder (s * z) s eta ha hdistinct
  · simpa [eResidueZeroInitialMap] using hexpansion (s * z, 1)
  · simpa [eResidueZeroInitialMap] using hexpansion (s, eta)
  · intro U hU
    exact eventually_exists_eResidueZeroInvariantRegularZero_mem_nhds
      a ha Rzero R c n z s g eta heta remainder
        (hexpansion (s * z, 1)).remainder_analyticAt
        (hexpansion (s, eta)).remainder_analyticAt
        hdescent hdecomposition hThetaHomogeneous hp hzRoot hzOne
          hs hg hW U hU

end OnLeConjecture.DThree
