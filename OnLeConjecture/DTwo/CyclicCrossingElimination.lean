/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicMixedBranches
public import OnLeConjecture.Analytic.QuadraticCrossingPersistence

/-!
# Analytic elimination at a cyclic quadratic crossing

The second plane equation eliminates the second `y` coordinate. The first
equation then has a quadratic crossing in its special fibre. Nonzero
restrictions of the third equation on both branches imply persistence.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.DTwo

open OnLeConjecture.Analytic OnLeConjecture.DThree MvPolynomial

/-- Coordinates are `(X,tau,x)` before adjoining the second `y` coordinate. -/
@[expose] def cyclicCrossingInput (q : Source 3 × ℂ) : ℂ × (Fin 3 → ℂ) :=
  (q.1 1, ![q.1 2, q.1 0, q.2])

theorem cyclicCrossingInput_analyticAt (q : Source 3 × ℂ) :
    AnalyticAt ℂ cyclicCrossingInput q := by
  apply AnalyticAt.prod
  · exact analyticAt_pi_iff.mp analyticAt_fst 1
  · apply AnalyticAt.pi
    intro index
    fin_cases index
    · exact analyticAt_pi_iff.mp analyticAt_fst 2
    · exact analyticAt_pi_iff.mp analyticAt_fst 0
    · exact analyticAt_snd

@[simp] theorem cyclicCrossingInput_base (ζ : ℂ) :
    cyclicCrossingInput (0, ζ) = (0, ![0, 0, ζ]) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Eliminate the second plane equation, and identify both special-fibre
branches using uniqueness in the analytic implicit function theorem. -/
theorem exists_cyclicCrossing_implicit_branch
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p) (c ζ : ℂ)
    (hc : c ≠ 0) (hζzero : ζ ≠ 0) (hζ : ζ ^ k = 1)
    (hPhi : AnalyticAt ℂ Phi (0, ![0, 0, ζ]))
    (hspecial : ∀ q, Phi (0, q) 1 = q 0 ^ p + c - (q 1 ^ p + c * q 2 ^ k))
    (Y : ℂ → ℂ) (hY : AnalyticAt ℂ Y 0) (hYzero : Y 0 = ζ)
    (hYplane : ∀ x, x ^ p + c - ((-x) ^ p + c * Y x ^ k) = 0) :
    ∃ b : Source 3 → ℂ, AnalyticAt ℂ b 0 ∧ b 0 = ζ ∧
      (∀ᶠ z in nhds 0, Phi (cyclicCrossingInput (z, b z)) 1 = 0) ∧
      (∀ᶠ x in nhds 0, b ![x, 0, x] = ζ) ∧
      (∀ᶠ x in nhds 0, b ![-x, 0, x] = Y x) := by
  let plane : Source 3 × ℂ → ℂ := fun q ↦ Phi (cyclicCrossingInput q) 1
  have hplane : AnalyticAt ℂ plane (0, ζ) :=
    (analyticAt_pi_iff.mp hPhi 1).comp_of_eq (cyclicCrossingInput_analyticAt (0, ζ)) rfl
  let d : ℂ := -c * (k : ℂ) * ζ ^ (k - 1)
  have hd : d ≠ 0 := mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr hc) (Nat.cast_ne_zero.mpr hk.ne'))
    (pow_ne_zero _ hζzero)
  have hfixed : (fun y ↦ plane (0, y)) = fun y ↦ c - c * y ^ k := by
    funext y
    simp [plane, cyclicCrossingInput, hspecial, zero_pow hp.ne']
  have hderivative : HasDerivAt (fun y : ℂ ↦ plane (0, y)) d ζ := by
    rw [hfixed]
    have hvalue : d = -((k : ℂ) * ζ ^ (k - 1) * c) := by dsimp [d]; ring
    have hfunction : (fun y : ℂ ↦ c - c * y ^ k) = fun y ↦ c - y ^ k * c := by
      funext y
      ring
    rw [hvalue, hfunction]
    exact ((hasDerivAt_pow k ζ).mul_const c).const_sub c
  have hpointEq : fderiv ℂ plane (0, ζ) ∘L ContinuousLinearMap.inr ℂ (Source 3) ℂ =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d := by
    have hcomposition := hplane.hasStrictFDerivAt.comp ζ
      ((hasStrictFDerivAt_const (𝕜 := ℂ) (0 : Source 3) ζ).prodMk
        (hasStrictFDerivAt_id ζ))
    have hinr : (0 : ℂ →L[ℂ] Source 3).prod (ContinuousLinearMap.id ℂ ℂ) =
        ContinuousLinearMap.inr ℂ (Source 3) ℂ := by ext z <;> rfl
    rw [hinr] at hcomposition
    exact hcomposition.hasFDerivAt.unique hderivative.hasFDerivAt
  have hpoint : (fderiv ℂ plane (0, ζ) ∘L
      ContinuousLinearMap.inr ℂ (Source 3) ℂ).IsInvertible := by
    rw [hpointEq]
    exact ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d hd), rfl⟩
  have hplaneZero : plane (0, ζ) = 0 := by
    simp [plane, cyclicCrossingInput, hspecial, zero_pow hp.ne', hζ]
  let b := analyticImplicitBranch plane (0, ζ) hplane hpoint
  have hb : AnalyticAt ℂ b 0 := analyticAt_analyticImplicitBranch plane (0, ζ) hplane hpoint
  have hbzero : b 0 = ζ := analyticImplicitBranch_apply_base plane (0, ζ) hplane hpoint
  have hlocal := hplane.hasStrictFDerivAt
    |>.eventually_apply_eq_iff_implicitFunctionOfProdDomain hpoint
  have hidentify (s : ℂ) (Z : ℂ → ℂ) (hZ : AnalyticAt ℂ Z 0) (hZzero : Z 0 = ζ)
      (hZplane : ∀ x, x ^ p + c - ((s * x) ^ p + c * Z x ^ k) = 0) :
      ∀ᶠ x in nhds 0, b ![s * x, 0, x] = Z x := by
    have hparameter : AnalyticAt ℂ (fun x : ℂ ↦ (![s * x, 0, x], Z x)) 0 := by
      apply AnalyticAt.prod
      · apply AnalyticAt.pi
        intro index
        fin_cases index
        · exact analyticAt_const.mul analyticAt_id
        · exact analyticAt_const
        · exact analyticAt_id
      · exact hZ
    have ht : Tendsto (fun x : ℂ ↦ (![s * x, 0, x], Z x))
        (nhds 0) (nhds ((0 : Source 3), ζ)) := by
      have hzero : (![s * (0 : ℂ), 0, 0], Z 0) = ((0 : Source 3), ζ) := by
        refine Prod.ext ?_ hZzero
        ext index
        fin_cases index <;> simp
      simpa only [hzero] using hparameter.continuousAt.tendsto
    filter_upwards [ht.eventually hlocal] with x hx
    apply hx.mp
    change plane (![s * x, 0, x], Z x) = plane (0, ζ)
    rw [hplaneZero]
    simpa [plane, cyclicCrossingInput, hspecial] using hZplane x
  refine ⟨b, hb, hbzero, ?_, ?_, ?_⟩
  · simpa only [hplaneZero] using eventually_analyticImplicitBranch_eq plane (0, ζ) hplane hpoint
  · simpa only [one_mul] using hidentify 1 (fun _ ↦ ζ) analyticAt_const rfl
      (fun x ↦ by simp [hζ])
  · simpa only [neg_one_mul] using hidentify (-1) Y hY hYzero
      (fun x ↦ by simpa only [neg_one_mul] using hYplane x)

/-- Full analytic perturbations have zeros near the cyclic crossing if
the original third polynomial is nonzero on both plane branches. -/
theorem eventually_exists_cyclicCrossingZero_mem_nhds
    (Phi : ℂ × (Fin 3 → ℂ) → Fin 3 → ℂ)
    (k p : ℕ) (hk : 0 < k) (hp : 0 < p) (c ζ : ℂ)
    (hc : c ≠ 0) (hζzero : ζ ≠ 0) (hζ : ζ ^ k = 1)
    (R : MvPolynomial (Fin 2) ℂ)
    (hPhi : AnalyticAt ℂ Phi (0, ![0, 0, ζ]))
    (hspecial : ∀ q, Phi (0, q) =
      weightedInitialDifference (cyclicResidualInitialMap k p c R) q)
    (Y : ℂ → ℂ) (hY : AnalyticAt ℂ Y 0) (hYzero : Y 0 = ζ)
    (hYplane : ∀ x, x ^ p + c - ((-x) ^ p + c * Y x ^ k) = 0)
    (hRzero : eval ![0, 1] R - eval ![0, ζ] R = 0)
    (hplus : ¬ ∀ᶠ x in nhds 0, eval ![x, 1] R - eval ![x, ζ] R = 0)
    (hminus : ¬ ∀ᶠ x in nhds 0, eval ![x, 1] R - eval ![-x, Y x] R = 0)
    (U : Set (ℂ × (Fin 3 → ℂ))) (hU : U ∈ nhds (0, ![0, 0, ζ])) :
    ∀ᶠ tau in nhds 0, ∃ q : Fin 3 → ℂ, (tau, q) ∈ U ∧ Phi (tau, q) = 0 := by
  obtain ⟨b, hb, hbzero, hbplane, hbplus, hbminus⟩ :=
    exists_cyclicCrossing_implicit_branch Phi k p hk hp c ζ hc hζzero hζ hPhi
      (fun q ↦ by simp [hspecial, weightedInitialDifference, cyclicResidualInitialMap,
        residueFirstChartPoint, residueSecondChartPoint]) Y hY hYzero hYplane
  let lift : Source 3 → ℂ × (Fin 3 → ℂ) := fun z ↦ cyclicCrossingInput (z, b z)
  have hlift : AnalyticAt ℂ lift 0 := (cyclicCrossingInput_analyticAt (0, ζ)).comp_of_eq
    (analyticAt_id.prod hb) (by simp [hbzero])
  have hliftzero : lift 0 = (0, ![0, 0, ζ]) := by simp [lift, hbzero]
  let G : Source 3 → ℂ := fun z ↦ -Phi (lift z) 0
  let F : Source 3 → ℂ := fun z ↦ Phi (lift z) 2
  have hG : AnalyticAt ℂ G 0 :=
    ((analyticAt_pi_iff.mp hPhi 0).comp_of_eq hlift hliftzero).neg
  have hF : AnalyticAt ℂ F 0 := (analyticAt_pi_iff.mp hPhi 2).comp_of_eq hlift hliftzero
  have hGspecial : ∀ᶠ z in nhds (0 : Source 2),
      G (QuadraticCrossing.specialFunction z) = z 0 ^ 2 - z 1 ^ 2 := by
    apply Filter.Eventually.of_forall
    intro z
    simp [G, lift, cyclicCrossingInput, QuadraticCrossing.specialFunction,
      hspecial, weightedInitialDifference, cyclicResidualInitialMap,
      residueFirstChartPoint, residueSecondChartPoint]
  have hFzero : F 0 = 0 := by
    simpa [F, hliftzero, hspecial, weightedInitialDifference, cyclicResidualInitialMap,
      residueFirstChartPoint, residueSecondChartPoint] using hRzero
  have hFplus : ¬ ∀ᶠ x in nhds 0, F ![x, 0, x] = 0 := by
    intro hzero
    apply hplus
    filter_upwards [hzero, hbplus] with x hx hbAt
    simpa [F, lift, cyclicCrossingInput, hbAt, hspecial, weightedInitialDifference,
      cyclicResidualInitialMap, residueFirstChartPoint, residueSecondChartPoint] using hx
  have hFminus : ¬ ∀ᶠ x in nhds 0, F ![-x, 0, x] = 0 := by
    intro hzero
    apply hminus
    filter_upwards [hzero, hbminus] with x hx hbAt
    simpa [F, lift, cyclicCrossingInput, hbAt, hspecial, weightedInitialDifference,
      cyclicResidualInitialMap, residueFirstChartPoint, residueSecondChartPoint] using hx
  let V : Set (Source 3) := lift ⁻¹' U ∩ {z | Phi (lift z) 1 = 0}
  have hliftTendsto : Tendsto lift (nhds 0) (nhds (0, ![0, 0, ζ])) := by
    simpa only [hliftzero] using hlift.continuousAt.tendsto
  have hV : V ∈ nhds 0 := Filter.inter_mem (hliftTendsto.eventually hU) hbplane
  have hpersist := QuadraticCrossing.eventually_exists_quadraticCrossingZero_mem_nhds
    G F hG hF hGspecial hFzero hFplus hFminus V hV
  filter_upwards [hpersist] with tau htau
  obtain ⟨z, hz, hparameter, hGAt, hFAt⟩ := htau
  have hliftparameter : (lift z).1 = tau := hparameter
  refine ⟨(lift z).2, ?_, ?_⟩
  · simpa only [← hliftparameter, Prod.mk.eta] using (show lift z ∈ U from hz.1)
  · rw [← hliftparameter]
    change Phi (lift z) = 0
    ext index
    fin_cases index
    · exact neg_eq_zero.mp hGAt
    · exact hz.2
    · exact hFAt

end OnLeConjecture.DTwo
