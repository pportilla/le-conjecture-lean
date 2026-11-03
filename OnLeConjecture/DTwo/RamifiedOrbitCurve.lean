/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RamifiedCurveRoot
public import OnLeConjecture.DTwo.OrbitTransversality
public import OnLeConjecture.DTwo.RamifiedOrbitPolynomials
public import OnLeConjecture.DTwo.OrbitCollisionPersistence

/-!
# Ramified lifts of the orbit conic curves

Both conic points lift to analytic curves after the parameter substitution
`z + τ^a`. The construction allows either second coordinate to vanish.
It asserts an analytic curve lift, not a local equivalence at a ramification point.
-/

public section

open Filter
open scoped Topology

namespace OnLeConjecture.DTwo

/-- The source substitution relating the homogeneous orbit model to its
weighted version. -/
@[expose] noncomputable def ramifiedOrbitSourcePoint (a : ℕ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1, Complex.I * p.2 ^ a)

/-- A plane analytic curve lifts through the source power substitution
after the same power substitution in its parameter. -/
theorem exists_ramifiedOrbitSourcePoint_curve
    (a : ℕ) (ha : 0 < a) (p : ℂ → ℂ × ℂ) (z γ : ℂ)
    (hp : AnalyticAt ℂ p z) (hγ : Complex.I * γ ^ a = (p z).2) :
    ∃ x : ℂ → ℂ × ℂ, AnalyticAt ℂ x 0 ∧ x 0 = ((p z).1, γ) ∧
      (∀ τ, (x τ).1 = (p (z + τ ^ a)).1) ∧
      ∀ᶠ τ in 𝓝 (0 : ℂ), ramifiedOrbitSourcePoint a (x τ) = p (z + τ ^ a) := by
  have hpower : γ ^ a = (p z).2 / Complex.I := by
    rw [← hγ, mul_div_cancel_left₀ _ Complex.I_ne_zero]
  obtain ⟨η, hη, hη0, hηpower⟩ := Analytic.exists_analytic_ramified_root_at
    a ha (fun w ↦ (p w).2 / Complex.I) z γ
      (analyticAt_snd.comp hp).div_const hpower
  have hparam : AnalyticAt ℂ (fun τ : ℂ ↦ z + τ ^ a) 0 :=
    analyticAt_const.add (analyticAt_id.pow a)
  have hfirst : AnalyticAt ℂ (fun τ : ℂ ↦ (p (z + τ ^ a)).1) 0 :=
    (analyticAt_fst.comp hp).comp_of_eq hparam (by simp [ha.ne'])
  refine ⟨fun τ ↦ ((p (z + τ ^ a)).1, η τ), hfirst.prod hη, ?_,
    fun _ ↦ rfl, ?_⟩
  · simp only [zero_pow ha.ne', add_zero, hη0]
  · filter_upwards [hηpower] with τ hτ
    apply Prod.ext
    · rfl
    · change Complex.I * η τ ^ a = (p (z + τ ^ a)).2
      rw [hτ, mul_div_cancel₀ _ Complex.I_ne_zero]

/-- The two source curves on the finite conic chart admit simultaneous
analytic lifts with prescribed compatible second coordinates at the origin. -/
theorem exists_ramifiedOrbitFiniteChartPair_curves
    (a : ℕ) (ha : 0 < a) (delta z γ₁ γ₂ : ℂ)
    (hγ₁ : Complex.I * γ₁ ^ a = (orbitFiniteChartFirstPoint delta z).2)
    (hγ₂ : Complex.I * γ₂ ^ a = (orbitFiniteChartSecondPoint delta z).2) :
    ∃ (x : ℂ → ℂ × ℂ) (v : ℂ → Fin 2 → ℂ),
      AnalyticAt ℂ x 0 ∧ AnalyticAt ℂ v 0 ∧
      x 0 = ((orbitFiniteChartFirstPoint delta z).1, γ₁) ∧
      v 0 = ![(orbitFiniteChartSecondPoint delta z).1, γ₂] ∧
      (∀ τ, (x τ).1 = (orbitFiniteChartFirstPoint delta (z + τ ^ a)).1) ∧
      (∀ τ, v τ 0 = (orbitFiniteChartSecondPoint delta (z + τ ^ a)).1) ∧
      ∀ᶠ τ in 𝓝 (0 : ℂ),
        ramifiedOrbitSourcePoint a (x τ) = orbitFiniteChartFirstPoint delta (z + τ ^ a) ∧
        ramifiedOrbitSourcePoint a (orbitPointOfFinTwo (v τ)) =
          orbitFiniteChartSecondPoint delta (z + τ ^ a) := by
  have hfirst : AnalyticAt ℂ (orbitFiniteChartFirstPoint delta) z := by
    change AnalyticAt ℂ (fun w ↦ orbitFiniteChartFirstPoint delta w) z
    simp only [orbitFiniteChartFirstPoint, orbitConicS_eval, orbitConicLambda_eval,
      orbitConicRhoValue_eq, orbitConicAlphaValue_eq, orbitConicBetaValue_eq]
    fun_prop
  have hsecond : AnalyticAt ℂ (orbitFiniteChartSecondPoint delta) z := by
    change AnalyticAt ℂ (fun w ↦ orbitFiniteChartSecondPoint delta w) z
    simp only [orbitFiniteChartSecondPoint, orbitConicT_eval, orbitConicZeta_eval,
      orbitConicRhoValue_eq, orbitConicAlphaValue_eq, orbitConicBetaValue_eq]
    fun_prop
  obtain ⟨x, hx, hx0, hxfirst, hximage⟩ := exists_ramifiedOrbitSourcePoint_curve
    a ha (orbitFiniteChartFirstPoint delta) z γ₁ hfirst hγ₁
  obtain ⟨v, hv, hv0, hvfirst, hvimage⟩ := exists_ramifiedOrbitSourcePoint_curve
    a ha (orbitFiniteChartSecondPoint delta) z γ₂ hsecond hγ₂
  have hvfin : AnalyticAt ℂ (fun τ ↦ orbitFinTwoOfPoint (v τ)) 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact analyticAt_fst.comp hv
    · exact analyticAt_snd.comp hv
  refine ⟨x, fun τ ↦ orbitFinTwoOfPoint (v τ), hx, hvfin, hx0, ?_, hxfirst,
    hvfirst, ?_⟩
  · change orbitFinTwoOfPoint (v 0) = _
    rw [hv0]
    rfl
  · filter_upwards [hximage, hvimage] with τ hxτ hvτ
    exact ⟨hxτ, hvτ⟩

/-- The polynomial map evaluated on a ramified point is the weighted
polynomial map evaluated on its lift. -/
theorem weightedPolynomialMap_ramifiedOrbitPolynomials
    (a : ℕ) (R : OrbitSourceForm) (p : ℂ × ℂ) :
    DThree.weightedPolynomialMap (ramifiedOrbitPolynomials a R) p =
      DThree.weightedPolynomialMap (orbitInitialPolynomialMap R)
        (ramifiedOrbitSourcePoint a p) := by
  funext i
  exact ramifiedOrbitSubstitution_eval a (orbitInitialPolynomialMap R i) ![p.1, p.2]

/-- The pair difference also commutes with the ramified source substitution. -/
theorem orbitPairInitialDifference_ramifiedOrbitPolynomials
    (a : ℕ) (R : OrbitSourceForm) (p : (ℂ × ℂ) × (ℂ × ℂ)) :
    orbitPairInitialDifference (DThree.weightedPolynomialMap (ramifiedOrbitPolynomials a R)) p =
      orbitPairInitialDifference (DThree.weightedPolynomialMap (orbitInitialPolynomialMap R))
        (ramifiedOrbitSourcePoint a p.1, ramifiedOrbitSourcePoint a p.2) := by
  simp only [orbitPairInitialDifference, weightedPolynomialMap_ramifiedOrbitPolynomials]

/-- Along the lifted conic pair the first two differences vanish, and the
third is the conic polynomial evaluated at the ramified parameter. -/
theorem eventually_ramifiedOrbitFiniteChartPair_difference
    (a : ℕ) (R : OrbitSourceForm) {delta : ℂ} (hdelta : delta ^ 2 = 3) (z : ℂ)
    (x : ℂ → ℂ × ℂ) (v : ℂ → Fin 2 → ℂ)
    (hlift : ∀ᶠ τ in 𝓝 (0 : ℂ),
      ramifiedOrbitSourcePoint a (x τ) = orbitFiniteChartFirstPoint delta (z + τ ^ a) ∧
      ramifiedOrbitSourcePoint a (orbitPointOfFinTwo (v τ)) =
        orbitFiniteChartSecondPoint delta (z + τ ^ a)) :
    ∀ᶠ τ in 𝓝 (0 : ℂ),
      orbitPairInitialDifference (DThree.weightedPolynomialMap (ramifiedOrbitPolynomials a R))
        (x τ, orbitPointOfFinTwo (v τ)) =
          ![0, 0, (orbitParameterDehomogenize (orbitConicDifference delta R)).eval
            (z + τ ^ a)] := by
  filter_upwards [hlift] with τ hτ
  rw [orbitPairInitialDifference_ramifiedOrbitPolynomials, hτ.1, hτ.2]
  exact orbitPairInitialDifference_finiteChart hdelta R (z + τ ^ a)

/-- Every finite conic collision lifts to analytic curves with distinct
base points and a positive finite order of the third difference. At least
one base point lies off the ramification axis. -/
theorem exists_ramifiedOrbitFiniteChartPair_finiteOrder
    (a : ℕ) (ha : 0 < a) {delta : ℂ} {R : OrbitSourceForm}
    (hdelta : delta ^ 2 = 3) (data : OrbitFiniteChartCollisionData delta R) :
    ∃ (x : ℂ → ℂ × ℂ) (v : ℂ → Fin 2 → ℂ) (m : ℕ) (u : ℂ → ℂ),
      AnalyticAt ℂ x 0 ∧ AnalyticAt ℂ v 0 ∧ 0 < m ∧
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      x 0 ≠ orbitPointOfFinTwo (v 0) ∧
      ((x 0).2 ≠ 0 ∨ v 0 1 ≠ 0) ∧
      ∀ᶠ τ in 𝓝 (0 : ℂ),
        orbitPairInitialDifference
          (DThree.weightedPolynomialMap (ramifiedOrbitPolynomials a R))
          (x τ, orbitPointOfFinTwo (v τ)) = ![0, 0, τ ^ m * u τ] := by
  obtain ⟨γ₁, hγ₁pow⟩ := IsAlgClosed.exists_pow_nat_eq
    ((orbitFiniteChartFirstPoint delta data.parameter).2 / Complex.I) ha
  obtain ⟨γ₂, hγ₂pow⟩ := IsAlgClosed.exists_pow_nat_eq
    ((orbitFiniteChartSecondPoint delta data.parameter).2 / Complex.I) ha
  have hγ₁ : Complex.I * γ₁ ^ a =
      (orbitFiniteChartFirstPoint delta data.parameter).2 := by
    rw [hγ₁pow, mul_div_cancel₀ _ Complex.I_ne_zero]
  have hγ₂ : Complex.I * γ₂ ^ a =
      (orbitFiniteChartSecondPoint delta data.parameter).2 := by
    rw [hγ₂pow, mul_div_cancel₀ _ Complex.I_ne_zero]
  obtain ⟨x, v, hx, hv, hx0, hv0, _hxfirst, _hvfirst, hlift⟩ :=
    exists_ramifiedOrbitFiniteChartPair_curves a ha delta data.parameter γ₁ γ₂ hγ₁ hγ₂
  obtain ⟨m, hm, u, hu, hu0, hfactor⟩ := exists_orbitFiniteChartThirdFactorization data
  have hfirstImage : ramifiedOrbitSourcePoint a (x 0) =
      (orbitFiniteChartPair delta data.parameter).1 := by
    rw [hx0]
    exact Prod.ext rfl hγ₁
  have hsecondImage : ramifiedOrbitSourcePoint a (orbitPointOfFinTwo (v 0)) =
      (orbitFiniteChartPair delta data.parameter).2 := by
    rw [hv0]
    exact Prod.ext rfl hγ₂
  have hdistinct : x 0 ≠ orbitPointOfFinTwo (v 0) := by
    intro heq
    apply data.first_ne_second
    rw [← hfirstImage, ← hsecondImage, heq]
  have hoffAxis : (x 0).2 ≠ 0 ∨ v 0 1 ≠ 0 := by
    rcases data.second_coordinates_ne with hfirst | hsecond
    · left
      intro hzero
      apply hfirst
      rw [← hfirstImage]
      change Complex.I * (x 0).2 ^ a = 0
      rw [hzero, zero_pow ha.ne', mul_zero]
    · right
      intro hzero
      apply hsecond
      rw [← hsecondImage]
      change Complex.I * v 0 1 ^ a = 0
      rw [hzero, zero_pow ha.ne', mul_zero]
  have hunew : AnalyticAt ℂ (fun τ : ℂ ↦ u (τ ^ a)) 0 :=
    hu.comp_of_eq (analyticAt_id.pow a) (zero_pow ha.ne')
  refine ⟨x, v, a * m, fun τ ↦ u (τ ^ a), hx, hv, Nat.mul_pos ha hm, hunew,
    ?_, hdistinct, hoffAxis, ?_⟩
  · simpa only [zero_pow ha.ne'] using hu0
  · filter_upwards [eventually_ramifiedOrbitFiniteChartPair_difference
      a R hdelta data.parameter x v hlift] with τ hτ
    rw [hτ, hfactor, ← pow_mul]

/-- The lifted pair can be oriented so that the second point is off the
ramification axis. Swapping the points negates the analytic unit factor. -/
theorem exists_ramifiedOrbitFiniteChartPair_finiteOrder_transverse
    (a : ℕ) (ha : 0 < a) {delta : ℂ} {R : OrbitSourceForm}
    (hdelta : delta ^ 2 = 3) (data : OrbitFiniteChartCollisionData delta R) :
    ∃ (x : ℂ → ℂ × ℂ) (v : ℂ → Fin 2 → ℂ) (m : ℕ) (u : ℂ → ℂ),
      AnalyticAt ℂ x 0 ∧ AnalyticAt ℂ v 0 ∧ 0 < m ∧
      AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      x 0 ≠ orbitPointOfFinTwo (v 0) ∧ v 0 1 ≠ 0 ∧
      ∀ᶠ τ in 𝓝 (0 : ℂ),
        orbitPairInitialDifference
          (DThree.weightedPolynomialMap (ramifiedOrbitPolynomials a R))
          (x τ, orbitPointOfFinTwo (v τ)) = ![0, 0, τ ^ m * u τ] := by
  obtain ⟨x, v, m, u, hx, hv, hm, hu, hu0, hdistinct, hoff, hfactor⟩ :=
    exists_ramifiedOrbitFiniteChartPair_finiteOrder a ha hdelta data
  by_cases hsecond : v 0 1 ≠ 0
  · exact ⟨x, v, m, u, hx, hv, hm, hu, hu0, hdistinct, hsecond, hfactor⟩
  have hfirst : (x 0).2 ≠ 0 := hoff.resolve_right hsecond
  have hvpoint : AnalyticAt ℂ (fun τ ↦ orbitPointOfFinTwo (v τ)) 0 := by
    exact ((ContinuousLinearMap.proj (R := ℂ) (0 : Fin 2)).analyticAt _ |>.comp hv).prod
      ((ContinuousLinearMap.proj (R := ℂ) (1 : Fin 2)).analyticAt _ |>.comp hv)
  have hxfin : AnalyticAt ℂ (fun τ ↦ orbitFinTwoOfPoint (x τ)) 0 := by
    rw [analyticAt_pi_iff]
    intro i
    fin_cases i
    · exact analyticAt_fst.comp hx
    · exact analyticAt_snd.comp hx
  refine ⟨fun τ ↦ orbitPointOfFinTwo (v τ), fun τ ↦ orbitFinTwoOfPoint (x τ),
    m, fun τ ↦ -u τ, hvpoint, hxfin, hm, hu.neg, neg_ne_zero.mpr hu0,
    ?_, hfirst, ?_⟩
  · exact Ne.symm hdistinct
  · filter_upwards [hfactor] with τ hτ
    change DThree.weightedPolynomialMap (ramifiedOrbitPolynomials a R)
        (orbitPointOfFinTwo (v τ)) -
      DThree.weightedPolynomialMap (ramifiedOrbitPolynomials a R) (x τ) =
        ![0, 0, τ ^ m * -u τ]
    rw [← neg_sub]
    change -orbitPairInitialDifference
      (DThree.weightedPolynomialMap (ramifiedOrbitPolynomials a R))
      (x τ, orbitPointOfFinTwo (v τ)) = _
    rw [hτ]
    funext i
    fin_cases i <;> simp

end OnLeConjecture.DTwo
