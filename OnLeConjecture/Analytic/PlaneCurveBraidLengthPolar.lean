/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneCurveBraidLengthCount
public import OnLeConjecture.Analytic.CurveNormalizationOrder
public import OnLeConjecture.Analytic.AllOrdersPreparation
public import OnLeConjecture.Analytic.PointBlowupPolynomial
public import OnLeConjecture.Analytic.GeneralTeissierPolarIdentity
public import OnLeConjecture.Analytic.MilnorDelta
public import OnLeConjecture.Analytic.WeightedMonomialDivision
public import OnLeConjecture.Analytic.ProjectiveCriticalFirstBlowup
public import OnLeConjecture.Analytic.SupportedFiniteBlowupLift
public import OnLeConjecture.PlaneCurve.IrreducibleFiniteIntersection
public import OnLeConjecture.PlaneCurve.ExceptionalAxisIntersection
public import OnLeConjecture.PlaneCurve.BranchCountInvariance
public import Mathlib.LinearAlgebra.Lagrange

/-!
# The polar intersection of a branch from its sheet differences

Let `f` be an irreducible plane germ and `G` an injective analytic
parametrization of its branch with `G(z)_i = z ^ a`. Write `Y(z) = G(z)_{i.rev}`
and `ω = e^{2πi/a}`. The Weierstrass preparation `f = P u` in the fibre
coordinate `i.rev` has a monic polynomial `P` of degree `a = i₀(f, x_i)`. Its
pullback along the power map `t ↦ t ^ a` has the `a` distinct roots
`Y(ω^m t)` in the domain of one-variable germs, so it is the product of the
corresponding linear factors. Hence the pullback of `∂_{i.rev} f` along `G` is
a unit times `∏_{m ≠ 0} (Y(t) - Y(ω^m t))`. The parametrization formula for
intersection multiplicities gives
`i₀(f, ∂_{i.rev} f) = ∑_{m ≠ 0} ord₀ (Y(ω^m t) - Y(t))`.

Teissier's polar identity and Milnor's formula then give
`∑_{m ≠ 0} ord₀ (Y(ω^m t) - Y(t)) + 1 = 2 δ(f) + a`.
-/

@[expose] public noncomputable section

open Set Filter Topology Metric

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ OnLeConjecture.PlaneCurve

/-! ### Germ bookkeeping -/

theorem PointedMapGerm.ofFunction_eq_of_eventuallyEq {n m : ℕ} {f g : Source n → Source m}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (h : f =ᶠ[𝓝 0] g) :
    PointedMapGerm.ofFunction f hf hf0 = PointedMapGerm.ofFunction g hg hg0 :=
  Subtype.ext (Subtype.ext h.germ_eq)

theorem PointedMapGerm.pullbackRingHom_ofFunction_ofFunction {n m : ℕ}
    (G : Source n → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (q : Source m → ℂ) (hq : AnalyticAt ℂ q 0) :
    (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom (Germ.ofFunction q hq) =
      Germ.ofFunction (q ∘ G) (hq.comp_of_eq hG hG0) := by
  rw [PointedMapGerm.pullbackRingHom_apply]
  exact Germ.compPointed_ofFunction q hq G hG hG0

theorem Germ.eventuallyEq_of_ofFunction_eq {n : ℕ} {f g : Source n → ℂ}
    {hf : AnalyticAt ℂ f 0} {hg : AnalyticAt ℂ g 0}
    (h : Germ.ofFunction f hf = Germ.ofFunction g hg) : f =ᶠ[𝓝 0] g :=
  Filter.Germ.coe_eq.mp (congrArg Subtype.val h)

theorem Germ.ofFunction_sub' {n : ℕ} (f g : Source n → ℂ) (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) :
    Germ.ofFunction f hf - Germ.ofFunction g hg =
      Germ.ofFunction (fun z => f z - g z) (hf.sub hg) :=
  rfl

theorem Germ.ofFunction_neg' {n : ℕ} (f : Source n → ℂ) (hf : AnalyticAt ℂ f 0) :
    -Germ.ofFunction f hf = Germ.ofFunction (fun z => -f z) hf.neg :=
  rfl

theorem Germ.ofFunction_pow' {n : ℕ} (f : Source n → ℂ) (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    Germ.ofFunction f hf ^ k = Germ.ofFunction (fun z => f z ^ k) (hf.pow k) :=
  rfl

theorem Germ.vanishingOrder_neg (g : Germ 1) : vanishingOrder (-g) = vanishingOrder g := by
  have h : -g = (-1) * g := by ring
  rw [h, vanishingOrder_mul]
  have hu : IsUnit (-1 : Germ 1) := isUnit_one.neg
  rw [vanishingOrder_eq_zero_iff_isUnit.mpr hu, zero_add]

theorem curveParameterEquiv_symm_apply_zero (z : Source 1) :
    curveParameterEquiv.symm (z 0) = z := by
  funext j
  fin_cases j
  simp

theorem curveParameterEquiv_symm_mul (ζ : ℂ) (z : Source 1) :
    curveParameterEquiv.symm (ζ * z 0) = ζ • z := by
  funext j
  fin_cases j
  simp

/-- The rotation `z ↦ ζ z` of the one-variable source as a pointed map germ. -/
def sourceRotationGerm (ζ : ℂ) : PointedMapGerm 1 1 :=
  PointedMapGerm.ofFunction (fun z : Source 1 => ζ • z) (by fun_prop) (smul_zero ζ)

/-- The `a`th power map of the one-variable source as a pointed map germ. -/
def sourcePowerGerm (a : ℕ) [NeZero a] : PointedMapGerm 1 1 :=
  PointedMapGerm.ofFunction (fun z : Source 1 => fun _ => z 0 ^ a)
    (analyticAt_pi_iff.mpr fun _ =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _).pow a)
    (by funext j; simp [NeZero.ne a])

theorem sourcePowerGerm_comp_rotation (a : ℕ) [NeZero a] {ζ : ℂ} (hζ : ζ ^ a = 1) :
    (sourcePowerGerm a).comp (sourceRotationGerm ζ) = sourcePowerGerm a := by
  rw [sourcePowerGerm, sourceRotationGerm, PointedMapGerm.comp_ofFunction]
  congr 1
  funext z j
  simp [mul_pow, hζ]

/-! ### The polar order in the fibre coordinate `0` -/

/-- For an injective branch parametrization with second coordinate `z ^ a`, the
polar intersection with the first partial derivative is the sum of the orders of
the nontrivial sheet differences. -/
theorem exists_intersectionMultiplicity_partialDerivative_zero_eq_sum_sheetOrder
    (f : Germ 2) (hf : Irreducible f)
    (G : Source 1 → Source 2) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hzero : (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom f = 0)
    {a : ℕ} [NeZero a] {R : ℝ} (hR : 0 < R)
    (hFa : AnalyticOnNhd ℂ (fun z => G (curveParameterEquiv.symm z)) (ball 0 R))
    (hFi : InjOn (fun z => G (curveParameterEquiv.symm z)) (ball 0 R))
    (hp : ∀ z ∈ ball (0 : ℂ) R, G (curveParameterEquiv.symm z) 1 = z ^ a) :
    ∃ hfin : HasFiniteIntersection f (partialDerivative (0 : Fin 2) f),
      intersectionMultiplicity f (partialDerivative (0 : Fin 2) f) hfin =
        ∑ m ∈ Finset.univ.filter (fun m : Fin a => m ≠ 0),
          analyticOrderNatAt (planeBranchSheetDifference
            (fun z => G (curveParameterEquiv.symm z)) 1 (planeBranchBraidRoot a m)) 0 := by
  classical
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  set F : ℂ → Source 2 := fun z => G (curveParameterEquiv.symm z) with hFdef
  set γ := PointedMapGerm.ofFunction G hG hG0 with hγ
  have hGF : ∀ z : Source 1, G z = F (z 0) := fun z => by
    simp only [hFdef, curveParameterEquiv_symm_apply_zero]
  have hnhds : {z : Source 1 | z 0 ∈ ball (0 : ℂ) R} ∈ 𝓝 (0 : Source 1) :=
    (continuous_apply 0).continuousAt.preimage_mem_nhds (by simpa using ball_mem_nhds (0 : ℂ) hR)
  have hinj : γ.HasInjectiveRepresentative := by
    refine ⟨G, hG, hG0, rfl, {z | z 0 ∈ ball (0 : ℂ) R}, hnhds, ?_⟩
    intro z hz w hw hzw
    have h := hFi hz hw (by
      rw [← hGF, ← hGF]
      exact hzw)
    funext j
    fin_cases j
    exact h
  have hF0 : AnalyticAt ℂ F 0 := hFa 0 (mem_ball_self hR)
  -- The pulled back coordinates.
  have hcoord : ∀ j : Fin 2, γ.pullbackRingHom (coordinate j) =
      Germ.ofFunction (fun z => G z j)
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) j).analyticAt _).comp_of_eq
          hG hG0) := by
    intro j
    exact PointedMapGerm.pullbackRingHom_ofFunction_ofFunction G hG hG0 (fun z => z j) _
  have hpowev : (fun z : Source 1 => G z 1) =ᶠ[𝓝 0] fun z => z 0 ^ a := by
    filter_upwards [hnhds] with z hz
    rw [hGF]
    exact hp _ hz
  have hcpow : coordinate (0 : Fin 1) ^ a = Germ.ofFunction (fun z : Source 1 => z 0 ^ a)
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _).pow a) :=
    rfl
  have hX : γ.pullbackRingHom (coordinate 1) = coordinate (0 : Fin 1) ^ a := by
    rw [hcoord, hcpow]
    exact Germ.ofFunction_eq_of_eventuallyEq _ _ hpowev
  -- The intersection with the projection coordinate and regularity.
  have hfx : HasFiniteIntersection f (coordinate 1) := by
    apply hasFiniteIntersection_of_irreducible_not_dvd _ _ hf
    rintro ⟨q, hq⟩
    have h := congrArg γ.pullbackRingHom hq
    rw [map_mul, hzero, zero_mul, hX] at h
    exact pow_ne_zero a coordinate_zero_ne_zero h
  have hix : intersectionMultiplicity f (coordinate 1) hfx = a := by
    rw [γ.intersectionMultiplicity_eq_pullback_order_of_injective_curve hinj f hf hzero _ hfx,
      hX, vanishingOrder_pow, vanishingOrder_coordinate]
    simp
  have hreg : IsRegularInFirstCoordinateOfOrder f a := by
    have h1 := intersectionMultiplicity_comm f (coordinate 1) hfx
    rw [hix, intersectionMultiplicity_secondCoordinate_eq_firstAxisRestrictionOrder] at h1
    change vanishingOrder (lineRestriction (firstCoordinateVector 1) f) = (a : ℕ∞)
    by_cases htop : vanishingOrder (lineRestriction (firstCoordinateVector 1) f) = ⊤
    · rw [htop] at h1
      simp at h1
      omega
    · rw [← ENat.natCast_toNat htop, ← h1]
  obtain ⟨p, u, hpm, hpdeg, _hpdist, hu, hfac⟩ :=
    hasAnalyticWeierstrassFactorizationOfOrder_of_pos ha hreg
  have hγu : IsUnit (γ.pullbackRingHom u) := hu.map _
  have hev0 : γ.pullbackRingHom (firstCoordinatePolynomialEvaluation p) = 0 := by
    have h := hzero
    rw [hfac, map_mul] at h
    exact hγu.mul_left_eq_zero.mp h
  -- The coefficient ring homomorphism and the pulled back polynomial.
  let φ : Germ 1 →+* Germ 1 := γ.pullbackRingHom.comp (hyperplaneExtension 1)
  have hevalγ : ∀ q : Polynomial (Germ 1),
      γ.pullbackRingHom (firstCoordinatePolynomialEvaluation q) =
        (q.map φ).eval (γ.pullbackRingHom (coordinate 0)) := by
    intro q
    rw [firstCoordinatePolynomialEvaluation, Polynomial.hom_eval₂, Polynomial.eval_map]
  have hπ : (hyperplaneTailGerm 1).comp γ = sourcePowerGerm a := by
    rw [hyperplaneTailGerm, hγ, PointedMapGerm.comp_ofFunction, sourcePowerGerm]
    apply PointedMapGerm.ofFunction_eq_of_eventuallyEq
    filter_upwards [hpowev] with z hz
    funext j
    fin_cases j
    simpa [hyperplaneTail_apply] using hz
  have hφ : φ = (sourcePowerGerm a).pullbackRingHom := by
    rw [← hπ, PointedMapGerm.pullbackRingHom_comp]
    rfl
  let ρ : Fin a → PointedMapGerm 1 1 := fun m => sourceRotationGerm (planeBranchBraidRoot a m)
  have hφρ : ∀ m, (ρ m).pullbackRingHom.comp φ = φ := by
    intro m
    rw [hφ, ← PointedMapGerm.pullbackRingHom_comp,
      sourcePowerGerm_comp_rotation a (planeBranchBraidRoot_pow ha m)]
  set Y₀ := γ.pullbackRingHom (coordinate 0) with hY₀
  set Pt := p.map φ with hPt
  let Y : Fin a → Germ 1 := fun m => (ρ m).pullbackRingHom Y₀
  have hroot : ∀ m, Pt.eval (Y m) = 0 := by
    intro m
    have h := congrArg (ρ m).pullbackRingHom ((hevalγ p).symm.trans hev0)
    rw [map_zero, ← Polynomial.eval_map_apply, Polynomial.map_map, hφρ m] at h
    exact h
  have hYm : ∀ m, Y m = Germ.ofFunction (fun z => G (planeBranchBraidRoot a m • z) 0)
      ((((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt _).comp_of_eq
          hG hG0).comp_of_eq (by fun_prop) (smul_zero _)) := by
    intro m
    change (ρ m).pullbackRingHom Y₀ = _
    rw [hY₀, hcoord 0]
    exact PointedMapGerm.pullbackRingHom_ofFunction_ofFunction _ _ _ _ _
  -- The sheets are distinct.
  have hnorm : ∀ m : Fin a, ‖planeBranchBraidRoot a m‖ = 1 := fun m =>
    (norm_pow_eq_one_iff ha _).mp (by rw [planeBranchBraidRoot_pow ha m, norm_one])
  have hYinj : Function.Injective Y := by
    intro m m' hmm
    rw [hYm, hYm] at hmm
    have hev := Germ.eventuallyEq_of_ofFunction_eq hmm
    have hev' : ∀ᶠ w in 𝓝 (0 : ℂ),
        F (planeBranchBraidRoot a m * w) 0 = F (planeBranchBraidRoot a m' * w) 0 := by
      have ht := curveParameterEquiv.symm.continuous.continuousAt.tendsto (x := 0)
      rw [map_zero] at ht
      filter_upwards [ht.eventually hev] with w hw
      simp only [hFdef]
      rw [show curveParameterEquiv.symm (planeBranchBraidRoot a m * w) =
          planeBranchBraidRoot a m • curveParameterEquiv.symm w by
            rw [← curveParameterEquiv_symm_mul]; simp,
        show curveParameterEquiv.symm (planeBranchBraidRoot a m' * w) =
          planeBranchBraidRoot a m' • curveParameterEquiv.symm w by
            rw [← curveParameterEquiv_symm_mul]; simp]
      exact hw
    obtain ⟨w, ⟨hw, hwR⟩, hw0⟩ := (((hev'.and (ball_mem_nhds (0 : ℂ) hR)).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin).exists (f := 𝓝[≠] (0 : ℂ))
    have hmw : planeBranchBraidRoot a m * w ∈ ball (0 : ℂ) R := by
      simpa [mem_ball, dist_zero_right, norm_mul, hnorm] using hwR
    have hmw' : planeBranchBraidRoot a m' * w ∈ ball (0 : ℂ) R := by
      simpa [mem_ball, dist_zero_right, norm_mul, hnorm] using hwR
    have heqF : F (planeBranchBraidRoot a m * w) = F (planeBranchBraidRoot a m' * w) := by
      funext j
      fin_cases j
      · exact hw
      · change F (planeBranchBraidRoot a m * w) 1 = F (planeBranchBraidRoot a m' * w) 1
        have hpF : ∀ z ∈ ball (0 : ℂ) R, F z 1 = z ^ a := hp
        rw [hpF _ hmw, hpF _ hmw', mul_pow, mul_pow, planeBranchBraidRoot_pow ha,
          planeBranchBraidRoot_pow ha]
    have h := hFi hmw hmw' heqF
    exact planeBranchBraidRoot_injective ha (mul_right_cancel₀ hw0 h)
  -- The pulled back polynomial is the product of its linear factors.
  have hPtmonic : Pt.Monic := hpm.map φ
  have hPtdeg : Pt.natDegree = a := by rw [hpm.natDegree_map, hpdeg]
  have hS : (Finset.univ.image Y).card = a := by
    rw [Finset.card_image_of_injective _ hYinj, Finset.card_univ, Fintype.card_fin]
  have hroots : Pt.roots = (Finset.univ.image Y).val :=
    Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
      (fun x hx => by
        obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hx
        exact hroot m)
      (by rw [hPtdeg, hS]) hPtmonic.ne_zero
  have hPtnodal : Pt = Lagrange.nodal Finset.univ Y := by
    have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPtmonic
      (by rw [hroots, Finset.card_val, hS, hPtdeg])
    rw [← h, hroots, Lagrange.nodal_eq, ← Finset.prod_eq_multiset_prod,
      Finset.prod_image (fun x _ y _ hxy => hYinj hxy)]
  have hY0 : Y 0 = Y₀ := by
    rw [hYm, hY₀, hcoord 0]
    congr 1
    funext z
    simp [planeBranchBraidRoot]
  -- The pullback of the partial derivative.
  have hdf : γ.pullbackRingHom (partialDerivative (0 : Fin 2) f) =
      (∏ m ∈ Finset.univ.erase 0, (Y 0 - Y m)) * γ.pullbackRingHom u := by
    rw [hfac, partialDerivative_mul, partialDerivative_firstCoordinatePolynomialEvaluation,
      map_add, map_mul, map_mul, hev0, zero_mul, add_zero, hevalγ, ← Polynomial.derivative_map,
      ← hPt, hPtnodal, ← hY0, Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ 0),
      Lagrange.eval_nodal]
  -- Each linear factor is a sheet difference.
  have hG0an : AnalyticAt ℂ (fun z : Source 1 => G z 0) 0 :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt _).comp_of_eq
      hG hG0
  have hfactor : ∀ m : Fin a, Y 0 - Y m =
      -planeBranchSheetDifferenceGerm hF0 1 (planeBranchBraidRoot a m) := by
    intro m
    have hGm : AnalyticAt ℂ (fun z : Source 1 => G (planeBranchBraidRoot a m • z) 0) 0 :=
      hG0an.comp_of_eq (by fun_prop) (smul_zero _)
    have hsd : AnalyticAt ℂ (fun z => planeBranchSheetDifference F 1 (planeBranchBraidRoot a m)
        (curveParameterEquiv z)) 0 :=
      (planeBranchSheetDifference_analyticAt hF0 1 _).comp_of_eq
        (curveParameterEquiv.analyticAt 0) (map_zero _)
    calc Y 0 - Y m = Germ.ofFunction (fun z => G z 0) hG0an -
          Germ.ofFunction (fun z => G (planeBranchBraidRoot a m • z) 0) hGm := by
          rw [hY0, hYm, hY₀, hcoord 0]
      _ = Germ.ofFunction (fun z => G z 0 - G (planeBranchBraidRoot a m • z) 0)
          (hG0an.sub hGm) := rfl
      _ = Germ.ofFunction (fun z => -planeBranchSheetDifference F 1 (planeBranchBraidRoot a m)
          (curveParameterEquiv z)) hsd.neg := by
          apply Germ.ofFunction_eq_of_eventuallyEq
          refine Filter.Eventually.of_forall fun z => ?_
          have hz1 : curveParameterEquiv.symm (curveParameterEquiv z) = z :=
            curveParameterEquiv.symm_apply_apply z
          have hz2 : curveParameterEquiv.symm
              (planeBranchBraidRoot a m * curveParameterEquiv z) =
              planeBranchBraidRoot a m • z := by
            rw [curveParameterEquiv_apply]
            exact curveParameterEquiv_symm_mul _ z
          simp only [planeBranchSheetDifference, hFdef, hz1, hz2]
          rw [show (1 : Fin 2).rev = 0 from rfl]
          ring
      _ = -planeBranchSheetDifferenceGerm hF0 1 (planeBranchBraidRoot a m) := rfl
  have hneterm : ∀ m ∈ Finset.univ.erase (0 : Fin a), Y 0 - Y m ≠ 0 := by
    intro m hm
    exact sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hm).1 (hYinj h).symm
  have hne : γ.pullbackRingHom (partialDerivative (0 : Fin 2) f) ≠ 0 := by
    rw [hdf]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr hneterm) hγu.ne_zero
  have hfin : HasFiniteIntersection f (partialDerivative (0 : Fin 2) f) := by
    apply hasFiniteIntersection_of_irreducible_not_dvd _ _ hf
    rintro ⟨q, hq⟩
    apply hne
    rw [hq, map_mul, hzero, zero_mul]
  refine ⟨hfin, ?_⟩
  rw [γ.intersectionMultiplicity_eq_pullback_order_of_injective_curve hinj f hf hzero _ hfin,
    hdf, vanishingOrder_mul, vanishingOrder_eq_zero_iff_isUnit.mpr hγu, add_zero,
    Germ.vanishingOrder_finset_prod, Finset.filter_ne' Finset.univ (0 : Fin a)]
  have hterm : ∀ m ∈ Finset.univ.erase (0 : Fin a), vanishingOrder (Y 0 - Y m) =
      (analyticOrderNatAt (planeBranchSheetDifference F 1 (planeBranchBraidRoot a m)) 0 : ℕ∞) := by
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    rw [hfactor, Germ.vanishingOrder_neg]
    have hp' : ∀ z ∈ ball (0 : ℂ) R, F z 1 = z ^ a := hp
    have hnz := planeBranchSheetDifference_not_eventually_zero ha hR hFi hp'
      (planeBranchBraidRoot_pow ha m) (planeBranchBraidRoot_ne_one hm0)
    have htop : analyticOrderAt (planeBranchSheetDifference F 1 (planeBranchBraidRoot a m)) 0 ≠
        ⊤ := fun ht => hnz (analyticOrderAt_eq_top.mp ht)
    exact planeBranchSheetDifferenceGerm_vanishingOrder hF0 1 _
      (Nat.cast_analyticOrderNatAt htop).symm
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum, ENat.toNat_natCast]

/-! ### The general projection coordinate and the polar identity -/

theorem coordinateSwapEquiv_one_apply_one (w : Source 2) :
    coordinateSwapEquiv (1 : Fin 2) w 1 = w 0 := by
  have h := Equiv.piCongrLeft_apply_apply (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1) w 0
  change (Equiv.piCongrLeft (fun _ : Fin 2 ↦ ℂ) (Equiv.swap 0 1)) w 1 = w 0
  simpa using h

/-- An analytic parametrization which is injective on a disc after the scalar
parameter identification has an injective representative. -/
theorem hasInjectiveRepresentative_ofFunction_of_injOn
    (G : Source 1 → Source 2) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0) {R : ℝ} (hR : 0 < R)
    (hFi : InjOn (fun z => G (curveParameterEquiv.symm z)) (ball 0 R)) :
    (PointedMapGerm.ofFunction G hG hG0).HasInjectiveRepresentative := by
  have hnhds : {z : Source 1 | z 0 ∈ ball (0 : ℂ) R} ∈ 𝓝 (0 : Source 1) :=
    (continuous_apply 0).continuousAt.preimage_mem_nhds (by simpa using ball_mem_nhds (0 : ℂ) hR)
  refine ⟨G, hG, hG0, rfl, {z | z 0 ∈ ball (0 : ℂ) R}, hnhds, ?_⟩
  intro z hz w hw hzw
  have h := hFi hz hw (by
    simp only [curveParameterEquiv_symm_apply_zero]
    exact hzw)
  funext j
  fin_cases j
  exact h

/-- The projection coordinate of a normalized branch meets the branch with
multiplicity `a`. -/
theorem exists_intersectionMultiplicity_coordinate_eq_of_power
    (f : Germ 2) (hf : Irreducible f)
    (G : Source 1 → Source 2) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hzero : (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom f = 0)
    {a : ℕ} [NeZero a] {R : ℝ} (hR : 0 < R)
    (hFi : InjOn (fun z => G (curveParameterEquiv.symm z)) (ball 0 R)) (i : Fin 2)
    (hp : ∀ z ∈ ball (0 : ℂ) R, G (curveParameterEquiv.symm z) i = z ^ a) :
    ∃ hfi : HasFiniteIntersection f (coordinate i),
      intersectionMultiplicity f (coordinate i) hfi = a := by
  set γ := PointedMapGerm.ofFunction G hG hG0 with hγ
  have hinj := hasInjectiveRepresentative_ofFunction_of_injOn G hG hG0 hR hFi
  have hnhds : {z : Source 1 | z 0 ∈ ball (0 : ℂ) R} ∈ 𝓝 (0 : Source 1) :=
    (continuous_apply 0).continuousAt.preimage_mem_nhds (by simpa using ball_mem_nhds (0 : ℂ) hR)
  have hcpow : coordinate (0 : Fin 1) ^ a = Germ.ofFunction (fun z : Source 1 => z 0 ^ a)
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _).pow a) :=
    rfl
  have hX : γ.pullbackRingHom (coordinate i) = coordinate (0 : Fin 1) ^ a := by
    rw [hcpow]
    refine (PointedMapGerm.pullbackRingHom_ofFunction_ofFunction G hG hG0 (fun z => z i) _).trans ?_
    apply Germ.ofFunction_eq_of_eventuallyEq
    filter_upwards [hnhds] with z hz
    have h := hp _ hz
    simp only [curveParameterEquiv_symm_apply_zero] at h
    exact h
  have hfx : HasFiniteIntersection f (coordinate i) := by
    apply hasFiniteIntersection_of_irreducible_not_dvd _ _ hf
    rintro ⟨q, hq⟩
    have h := congrArg γ.pullbackRingHom hq
    rw [map_mul, hzero, zero_mul, hX] at h
    exact pow_ne_zero a coordinate_zero_ne_zero h
  refine ⟨hfx, ?_⟩
  rw [γ.intersectionMultiplicity_eq_pullback_order_of_injective_curve hinj f hf hzero _ hfx,
    hX, vanishingOrder_pow, vanishingOrder_coordinate]
  simp

/-- The polar order in the fibre coordinate for either projection coordinate. -/
theorem exists_intersectionMultiplicity_partialDerivative_rev_eq_sum_sheetOrder
    (f : Germ 2) (hf : Irreducible f)
    (G : Source 1 → Source 2) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hzero : (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom f = 0)
    {a : ℕ} [NeZero a] {R : ℝ} (hR : 0 < R)
    (hFa : AnalyticOnNhd ℂ (fun z => G (curveParameterEquiv.symm z)) (ball 0 R))
    (hFi : InjOn (fun z => G (curveParameterEquiv.symm z)) (ball 0 R)) (i : Fin 2)
    (hp : ∀ z ∈ ball (0 : ℂ) R, G (curveParameterEquiv.symm z) i = z ^ a) :
    ∃ hfin : HasFiniteIntersection f (partialDerivative i.rev f),
      intersectionMultiplicity f (partialDerivative i.rev f) hfin =
        ∑ m ∈ Finset.univ.filter (fun m : Fin a => m ≠ 0),
          analyticOrderNatAt (planeBranchSheetDifference
            (fun z => G (curveParameterEquiv.symm z)) i (planeBranchBraidRoot a m)) 0 := by
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · -- The projection coordinate is `0`. Exchange the two coordinates.
    let G' : Source 1 → Source 2 := fun z => coordinateSwapEquiv (1 : Fin 2) (G z)
    have hG' : AnalyticAt ℂ G' 0 := ((coordinateSwapEquiv (1 : Fin 2)).analyticAt _).comp hG
    have hG'0 : G' 0 = 0 := by simp [G', hG0]
    have hcomp : PointedMapGerm.ofFunction G' hG' hG'0 =
        (coordinateSwapPointedEquiv (1 : Fin 2)).forward.comp
          (PointedMapGerm.ofFunction G hG hG0) := by
      simp only [coordinateSwapPointedEquiv, Germ.pointedEquivGermOfContinuousLinearEquiv]
      rw [PointedMapGerm.comp_ofFunction]
      rfl
    have hf' : Irreducible ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f) :=
      (MulEquiv.irreducible_iff
        (coordinateSwapPointedEquiv (1 : Fin 2)).pullbackRingEquiv.toMulEquiv).mpr hf
    have hzero' : (PointedMapGerm.ofFunction G' hG' hG'0).pullbackRingHom
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f) = 0 := by
      rw [hcomp, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
        Germ.coordinateSwapPointedEquiv_pullback_twice, hzero]
    have hFa' : AnalyticOnNhd ℂ (fun z => G' (curveParameterEquiv.symm z)) (ball 0 R) :=
      fun z hz => ((coordinateSwapEquiv (1 : Fin 2)).analyticAt _).comp (hFa z hz)
    have hFi' : InjOn (fun z => G' (curveParameterEquiv.symm z)) (ball 0 R) :=
      fun z hz w hw h => hFi hz hw ((coordinateSwapEquiv (1 : Fin 2)).injective h)
    have hp' : ∀ z ∈ ball (0 : ℂ) R, G' (curveParameterEquiv.symm z) 1 = z ^ a := by
      intro z hz
      simp only [G', coordinateSwapEquiv_one_apply_one]
      exact hp z hz
    obtain ⟨hfin', heq'⟩ := exists_intersectionMultiplicity_partialDerivative_zero_eq_sum_sheetOrder
      _ hf' G' hG' hG'0 hzero' hR hFa' hFi' hp'
    have hd := Germ.partialDerivative_zero_coordinateSwap_pullback f
    have hfin : HasFiniteIntersection f (partialDerivative (1 : Fin 2) f) := by
      have h := hfin'.pullback (coordinateSwapPointedEquiv (1 : Fin 2))
      simp only [PointedEquivGerm.pullbackAlgEquiv_apply,
        PointedEquivGerm.pullbackRingEquiv_apply, hd] at h
      rw [Germ.coordinateSwapPointedEquiv_pullback_twice,
        Germ.coordinateSwapPointedEquiv_pullback_twice] at h
      exact h
    have hsheet : ∀ ζ : ℂ, planeBranchSheetDifference (fun z => G' (curveParameterEquiv.symm z))
        1 ζ = planeBranchSheetDifference (fun z => G (curveParameterEquiv.symm z)) 0 ζ := by
      intro ζ
      funext w
      simp only [planeBranchSheetDifference, G']
      rw [show (1 : Fin 2).rev = 0 from rfl, show (0 : Fin 2).rev = 1 from rfl,
        coordinateSwapEquiv_apply_zero, coordinateSwapEquiv_apply_zero]
    refine ⟨hfin, ?_⟩
    change intersectionMultiplicity f (partialDerivative (1 : Fin 2) f) hfin = _
    rw [intersectionMultiplicity_pullback (coordinateSwapPointedEquiv (1 : Fin 2)) hfin]
    rw [intersectionMultiplicity_congr
      (a' := (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f)
      (b' := partialDerivative (0 : Fin 2)
        ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom f))
      (by simp) (by rw [PointedEquivGerm.pullbackAlgEquiv_apply,
        PointedEquivGerm.pullbackRingEquiv_apply, hd]) _ hfin', heq']
    exact Finset.sum_congr rfl fun m _ => by rw [hsheet]
  · exact exists_intersectionMultiplicity_partialDerivative_zero_eq_sum_sheetOrder
      f hf G hG hG0 hzero hR hFa hFi hp

/-- Teissier's polar identity and Milnor's formula for an irreducible germ and
the polar of a coordinate. -/
theorem intersectionMultiplicity_partialDerivative_rev_add_one
    (f : Germ 2) (hf : Irreducible f) (i : Fin 2)
    (hfi : HasFiniteIntersection f (coordinate i))
    (hfin : HasFiniteIntersection f (partialDerivative i.rev f)) :
    intersectionMultiplicity f (partialDerivative i.rev f) hfin + 1 =
      2 * deltaInvariant f + intersectionMultiplicity f (coordinate i) hfi := by
  have hmax : f ∈ maximalIdeal 2 := by
    by_contra h
    exact hf.not_isUnit (isUnit_of_valueRingHom_ne_zero (fun h0 => h (mem_maximalIdeal_iff.mpr h0)))
  have hsq : Squarefree f := hf.squarefree
  obtain ⟨hpolar, _hJ, heq⟩ := exists_polar_intersection_identity f (coordinate i) hmax
    (coordinate_mem_maximalIdeal i) hsq hfi
  have hideal : polarIdeal f (coordinate i) = pairIdeal f (partialDerivative i.rev f) := by
    rw [polarIdeal, jacobian_eq]
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · simp only [partialDerivative_coordinate_same,
        partialDerivative_coordinate_ne (by decide : (1 : Fin 2) ≠ 0), mul_zero, mul_one,
        zero_sub, pairIdeal]
      rw [show ((0 : Fin 2)).rev = 1 from rfl, Ideal.span_insert, Ideal.span_insert,
        Ideal.span_singleton_neg]
    · simp only [partialDerivative_coordinate_same,
        partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1), mul_zero, mul_one,
        sub_zero, pairIdeal]
      rfl
  have hpol : polarIntersectionMultiplicity f (coordinate i) hpolar =
      intersectionMultiplicity f (partialDerivative i.rev f) hfin := by
    change Module.finrank ℂ (Germ 2 ⧸ polarIdeal f (coordinate i)) =
      Module.finrank ℂ (Germ 2 ⧸ pairIdeal f (partialDerivative i.rev f))
    rw [hideal]
  have hmilnor := jacobianColength_add_irreducibleBranchCount hmax hsq
  rw [irreducibleBranchCount_eq_one_of_irreducible f hf] at hmilnor
  omega

/-- The branch identity: the orders of the nontrivial sheet differences of an
injective normalized parametrization sum to `2 δ(f) + a - 1`. -/
theorem sum_sheetOrder_add_one_eq_two_mul_deltaInvariant_add
    (f : Germ 2) (hf : Irreducible f)
    (G : Source 1 → Source 2) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hzero : (PointedMapGerm.ofFunction G hG hG0).pullbackRingHom f = 0)
    {a : ℕ} [NeZero a] {R : ℝ} (hR : 0 < R)
    (hFa : AnalyticOnNhd ℂ (fun z => G (curveParameterEquiv.symm z)) (ball 0 R))
    (hFi : InjOn (fun z => G (curveParameterEquiv.symm z)) (ball 0 R)) (i : Fin 2)
    (hp : ∀ z ∈ ball (0 : ℂ) R, G (curveParameterEquiv.symm z) i = z ^ a) :
    (∑ m ∈ Finset.univ.filter (fun m : Fin a => m ≠ 0),
        analyticOrderNatAt (planeBranchSheetDifference
          (fun z => G (curveParameterEquiv.symm z)) i (planeBranchBraidRoot a m)) 0) + 1 =
      2 * deltaInvariant f + a := by
  obtain ⟨hfin, heq⟩ := exists_intersectionMultiplicity_partialDerivative_rev_eq_sum_sheetOrder
    f hf G hG hG0 hzero hR hFa hFi i hp
  obtain ⟨hfi, hai⟩ := exists_intersectionMultiplicity_coordinate_eq_of_power
    f hf G hG hG0 hzero hR hFi i hp
  rw [← heq, intersectionMultiplicity_partialDerivative_rev_add_one f hf i hfi hfin, hai]

end OnLeConjecture.Analytic
