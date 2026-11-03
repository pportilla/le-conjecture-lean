/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.QuadraticPreparedPersistence

/-!
# Analytic persistence of an isolated quadratic crossing

The prepared remainder conditions are derived from the original branch
restrictions, and the resulting common roots are lifted through an actual
analytic equivalence fixing the parameter.
-/

public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic.QuadraticCrossing

open OnLeConjecture.Analytic.Germ

@[expose] def parameterPoint (z : ℂ × ℂ) : Source 2 := ![z.1, z.2]

theorem parameterPoint_analyticAt : AnalyticAt ℂ parameterPoint (0, 0) := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_fst
  · exact analyticAt_snd

private theorem parameterPoint_zero : parameterPoint ((0, 0) : ℂ × ℂ) = 0 := by
  ext i
  fin_cases i <;> rfl

private theorem parameterPoint_zero_scalar (z : Source 1) :
    parameterPoint (0, z 0) = hyperplaneInclusion 1 z := by
  ext i
  fin_cases i <;> rfl

private theorem exists_pointedRepresentative {n m : ℕ} (p : PointedMapGerm n m) :
    ∃ F : Source n → Source m, ∃ hF : AnalyticAt ℂ F 0, ∃ hzero : F 0 = 0,
      p = PointedMapGerm.ofFunction F hF hzero := by
  rcases p with ⟨⟨F, hF⟩, hzero⟩
  induction F using Filter.Germ.inductionOn with
  | _ F =>
      have hF' := (isAnalyticMapGerm_ofFun F).mp hF
      change F 0 = 0 at hzero
      exact ⟨F, hF', hzero, rfl⟩

private theorem restriction_eq_neg_square_eventually
    (h : Germ 2) (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0)
    (hrep : h = ofFunction H hH)
    (hres : hyperplaneRestriction 1 h = -(coordinate (0 : Fin 1) ^ 2)) :
    ∀ᶠ x in nhds 0, H (parameterPoint (0, x)) = -(x ^ 2) := by
  rw [hrep, hyperplaneRestriction_ofFunction] at hres
  have heq := Filter.Germ.coe_eq.mp (congrArg Subtype.val hres)
  change ∀ᶠ z in nhds (0 : Source 1), H (hyperplaneInclusion 1 z) = -(z 0 ^ 2) at heq
  let scalarPoint : ℂ → Source 1 := fun x _ ↦ x
  have ht : Tendsto scalarPoint (nhds 0) (nhds 0) := by
    exact (continuous_pi fun _ ↦ continuous_id).continuousAt.tendsto
  filter_upwards [ht.eventually heq] with x hx
  simpa only [← parameterPoint_zero_scalar, scalarPoint] using hx

private theorem restriction_linear_not_eventually_zero
    (a b : Germ 2) (A B : Source 2 → ℂ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0)
    (ha : a = ofFunction A hA) (hb : b = ofFunction B hB)
    (s : ℂ)
    (hne : hyperplaneRestriction 1 a + constRingHom 1 s * coordinate 0 *
      hyperplaneRestriction 1 b ≠ 0) :
    ¬ ∀ᶠ x in nhds 0, A (parameterPoint (0, x)) + s * x * B (parameterPoint (0, x)) = 0 := by
  intro hzero
  apply hne
  rw [ha, hb, hyperplaneRestriction_ofFunction, hyperplaneRestriction_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have ht : Tendsto (fun z : Source 1 ↦ z 0) (nhds 0) (nhds 0) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).continuous.continuousAt.tendsto
  filter_upwards [ht.eventually hzero] with z hz
  change A (hyperplaneInclusion 1 z) + s * z 0 * B (hyperplaneInclusion 1 z) = 0
  simpa only [parameterPoint_zero_scalar] using hz

/-- An isolated quadratic crossing persists for the original analytic
functions. The coefficient of `tau` is an analytic germ, not a polynomial
or a prescribed prepared remainder. -/
theorem eventually_exists_crossing_zero_mem_nhds_of_coordinate_factor
    (G F : Source 3 → ℂ) (hG : AnalyticAt ℂ G 0) (hF : AnalyticAt ℂ F 0)
    (D : Germ 3)
    (hGform : ofFunction G hG = coordinate 0 ^ 2 - coordinate 2 ^ 2 + coordinate 1 * D)
    (hFzero : F 0 = 0)
    (hplus : (branchGerm 1).pullbackRingHom (ofFunction F hF) ≠ 0)
    (hminus : (branchGerm (-1)).pullbackRingHom (ofFunction F hF) ≠ 0)
    (U : Set (Source 3)) (hU : U ∈ nhds 0) :
    ∀ᶠ tau in nhds 0, ∃ z : Source 3,
      z ∈ U ∧ z 1 = tau ∧ G z = 0 ∧ F z = 0 := by
  obtain ⟨e, h, a, b, q, hnormal, hdivision, hfix, _, ha, hhres, harem, hbrem⟩ :=
    exists_crossing_morse_pair_preparation (ofFunction G hG) D (ofFunction F hF) hGform
      (by simpa only [mem_maximalIdeal_iff, valueRingHom_ofFunction] using hFzero) hplus hminus
  obtain ⟨H, hH, hhrep⟩ := exists_analyticRepresentative_allOrders h
  obtain ⟨A, hA, harep⟩ := exists_analyticRepresentative_allOrders a
  obtain ⟨B, hB, hbrep⟩ := exists_analyticRepresentative_allOrders b
  obtain ⟨Q, hQ, hqrep⟩ := exists_analyticRepresentative_allOrders q
  obtain ⟨E, hE, hEzero, herep⟩ := exists_pointedRepresentative e.forward
  have hHpair : AnalyticAt ℂ (fun p ↦ H (parameterPoint p)) (0, 0) :=
    hH.comp_of_eq parameterPoint_analyticAt parameterPoint_zero
  have hApair : AnalyticAt ℂ (fun p ↦ A (parameterPoint p)) (0, 0) :=
    hA.comp_of_eq parameterPoint_analyticAt parameterPoint_zero
  have hBpair : AnalyticAt ℂ (fun p ↦ B (parameterPoint p)) (0, 0) :=
    hB.comp_of_eq parameterPoint_analyticAt parameterPoint_zero
  have hAzero : A (parameterPoint (0, 0)) = 0 := by
    rw [mem_maximalIdeal_iff, harep, valueRingHom_ofFunction] at ha
    simpa only [parameterPoint_zero] using ha
  have hplusFunction : ¬ ∀ᶠ x in nhds 0,
      A (parameterPoint (0, x)) + x * B (parameterPoint (0, x)) = 0 := by
    have hr := restriction_linear_not_eventually_zero a b A B hA hB harep hbrep 1
      (by simpa only [map_one, one_mul] using harem)
    simpa only [one_mul] using hr
  have hminusFunction : ¬ ∀ᶠ x in nhds 0,
      A (parameterPoint (0, x)) - x * B (parameterPoint (0, x)) = 0 := by
    have hr := restriction_linear_not_eventually_zero a b A B hA hB harep hbrep (-1)
      (by simpa only [map_neg, map_one, neg_one_mul, neg_mul, one_mul,
        ← sub_eq_add_neg] using hbrem)
    simpa only [neg_one_mul, neg_mul, one_mul, ← sub_eq_add_neg] using hr
  have hGidentity : ∀ᶠ z in nhds 0,
      G (E z) = z 0 ^ 2 + H (hyperplaneTail 2 z) := by
    change e.forward.pullbackRingHom (ofFunction G hG) = _ at hnormal
    rw [herep, hhrep, hyperplaneExtension_ofFunction] at hnormal
    exact Filter.Germ.coe_eq.mp (congrArg Subtype.val hnormal)
  have hFidentity : ∀ᶠ z in nhds 0,
      F (E z) = (z 0 ^ 2 + H (hyperplaneTail 2 z)) * Q z +
        A (hyperplaneTail 2 z) + z 0 * B (hyperplaneTail 2 z) := by
    change e.forward.pullbackRingHom (ofFunction F hF) = _ at hdivision
    rw [herep, hhrep, harep, hbrep, hqrep, hyperplaneExtension_ofFunction,
      hyperplaneExtension_ofFunction, hyperplaneExtension_ofFunction] at hdivision
    exact Filter.Germ.coe_eq.mp (congrArg Subtype.val hdivision)
  have hparameter : ∀ᶠ z in nhds 0, E z 1 = z 1 := by
    have htail := equiv_fixes_tail_of_fixes_hyperplaneExtension e hfix
    have heone : e.forward.1.component 1 = coordinate 1 := htail 0
    rw [herep] at heone
    have heq := congrArg Subtype.val heone
    change ((MapGerm.ofFunction E hE).component 1).1 = _ at heq
    rw [MapGerm.component_ofFunction] at heq
    exact Filter.Germ.coe_eq.mp heq
  have hEinto : ∀ᶠ z in nhds 0, E z ∈ U := by
    have ht := hE.continuousAt.tendsto
    rw [hEzero] at ht
    exact ht.eventually hU
  let V : Set (Source 3) := {z | E z ∈ U ∧ E z 1 = z 1 ∧
    G (E z) = z 0 ^ 2 + H (hyperplaneTail 2 z) ∧
    F (E z) = (z 0 ^ 2 + H (hyperplaneTail 2 z)) * Q z +
      A (hyperplaneTail 2 z) + z 0 * B (hyperplaneTail 2 z)}
  have hV : V ∈ nhds 0 := hEinto.and (hparameter.and (hGidentity.and hFidentity))
  have hpersist := eventually_exists_prepared_zero_mem_nhds
    (fun p ↦ H (parameterPoint p)) (fun p ↦ A (parameterPoint p))
    (fun p ↦ B (parameterPoint p)) hHpair hApair hBpair hAzero
    (restriction_eq_neg_square_eventually h H hH hhrep hhres)
    hplusFunction hminusFunction V hV
  filter_upwards [hpersist] with tau htau
  obtain ⟨z, hz, hztau, hHzero, hABzero⟩ := htau
  have hpoint : parameterPoint (tau, z 2) = hyperplaneTail 2 z := by
    rw [← hztau]
    ext i
    fin_cases i <;> rfl
  rw [hpoint] at hHzero hABzero
  refine ⟨E z, hz.1, hz.2.1.trans hztau, hz.2.2.1.trans hHzero, ?_⟩
  rw [hz.2.2.2, hHzero, zero_mul, zero_add]
  exact hABzero

@[expose] def swapParameter (z : Source 3) : Source 3 := ![z 1, z 0, z 2]

theorem swapParameter_analyticAt : AnalyticAt ℂ swapParameter 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) 1).analyticAt 0
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) 0).analyticAt 0
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) 2).analyticAt 0

private theorem swapParameter_zero : swapParameter (0 : Source 3) = 0 := by
  ext i
  fin_cases i <;> rfl

private theorem swapParameter_involutive (z : Source 3) : swapParameter (swapParameter z) = z := by
  ext i
  fin_cases i <;> rfl

private theorem swapParameter_hyperplane (z : Source 2) :
    swapParameter (hyperplaneInclusion 2 z) = specialFunction z := by
  ext i
  fin_cases i <;> rfl

/-- Equality on the special fibre gives an analytic multiple of the
parameter, by convergent Hadamard division. -/
theorem exists_crossing_parameter_factor
    (G : Source 3 → ℂ) (hG : AnalyticAt ℂ G 0)
    (hspecial : ∀ᶠ z in nhds (0 : Source 2), G (specialFunction z) = z 0 ^ 2 - z 1 ^ 2) :
    ∃ D : Germ 3,
      ofFunction G hG = coordinate 0 ^ 2 - coordinate 2 ^ 2 + coordinate 1 * D := by
  let difference : Source 3 → ℂ := fun z ↦ G z - (z 0 ^ 2 - z 2 ^ 2)
  have hdifference : AnalyticAt ℂ difference 0 := hG.sub
    ((((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) 0).analyticAt 0).pow 2).sub
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 ↦ ℂ) 2).analyticAt 0).pow 2))
  have hswapped : AnalyticAt ℂ (difference ∘ swapParameter) 0 :=
    hdifference.comp_of_eq swapParameter_analyticAt swapParameter_zero
  have hzero : (difference ∘ swapParameter) ∘ hyperplaneInclusion 2 =ᶠ[nhds 0] fun _ ↦ 0 := by
    filter_upwards [hspecial] with z hz
    change difference (swapParameter (hyperplaneInclusion 2 z)) = 0
    rw [swapParameter_hyperplane]
    change G (specialFunction z) - (z 0 ^ 2 - z 1 ^ 2) = 0
    exact sub_eq_zero.mpr hz
  obtain ⟨Q, hQ, hfactor⟩ :=
    Germ.AnalyticAt.exists_eventuallyEq_coordinate_mul_of_restrict_eq_zero hswapped hzero
  have hQswap : AnalyticAt ℂ (Q ∘ swapParameter) 0 :=
    hQ.comp_of_eq swapParameter_analyticAt swapParameter_zero
  refine ⟨ofFunction (Q ∘ swapParameter) hQswap, ?_⟩
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  have ht : Tendsto swapParameter (nhds 0) (nhds 0) := by
    simpa only [swapParameter_zero] using swapParameter_analyticAt.continuousAt.tendsto
  filter_upwards [ht.eventually hfactor] with z hz
  change difference (swapParameter (swapParameter z)) =
    (swapParameter z) 0 * Q (swapParameter z) at hz
  rw [swapParameter_involutive] at hz
  change G z = z 0 ^ 2 - z 2 ^ 2 + z 1 * Q (swapParameter z)
  change G z - (z 0 ^ 2 - z 2 ^ 2) = z 1 * Q (swapParameter z) at hz
  linear_combination hz

private theorem branchGerm_pullback_ne_zero_of_not_eventually_zero
    (F : Source 3 → ℂ) (hF : AnalyticAt ℂ F 0) (s : ℂ)
    (hne : ¬ ∀ᶠ x in nhds 0, F ![s * x, 0, x] = 0) :
    (branchGerm s).pullbackRingHom (ofFunction F hF) ≠ 0 := by
  intro hzero
  apply hne
  rw [branchGerm, PointedMapGerm.pullbackRingHom_comp] at hzero
  have heq := Filter.Germ.coe_eq.mp (congrArg Subtype.val hzero)
  change ∀ᶠ z in nhds (0 : Source 1), F (specialFunction (lineFunction s z)) = 0 at heq
  let scalarPoint : ℂ → Source 1 := fun x _ ↦ x
  have ht : Tendsto scalarPoint (nhds 0) (nhds 0) :=
    (continuous_pi fun _ ↦ continuous_id).continuousAt.tendsto
  filter_upwards [ht.eventually heq] with x hx
  exact hx

/-- Analytic quadratic-crossing persistence from the original special-fibre
equation and its two nonzero branch restrictions. No prepared coefficient,
resultant, transformed restriction, or multivariable persistence hypothesis
is assumed. The parameter is coordinate `1` in `(Y,tau,x)`. -/
theorem eventually_exists_quadraticCrossingZero_mem_nhds
    (G F : Source 3 → ℂ) (hG : AnalyticAt ℂ G 0) (hF : AnalyticAt ℂ F 0)
    (hspecial : ∀ᶠ z in nhds (0 : Source 2), G (specialFunction z) = z 0 ^ 2 - z 1 ^ 2)
    (hFzero : F 0 = 0)
    (hplus : ¬ ∀ᶠ x in nhds 0, F ![x, 0, x] = 0)
    (hminus : ¬ ∀ᶠ x in nhds 0, F ![-x, 0, x] = 0)
    (U : Set (Source 3)) (hU : U ∈ nhds 0) :
    ∀ᶠ tau in nhds 0, ∃ z : Source 3,
      z ∈ U ∧ z 1 = tau ∧ G z = 0 ∧ F z = 0 := by
  obtain ⟨D, hD⟩ := exists_crossing_parameter_factor G hG hspecial
  apply eventually_exists_crossing_zero_mem_nhds_of_coordinate_factor G F hG hF D hD hFzero
    ?_ ?_ U hU
  · apply branchGerm_pullback_ne_zero_of_not_eventually_zero F hF 1
    simpa only [one_mul] using hplus
  · apply branchGerm_pullback_ne_zero_of_not_eventually_zero F hF (-1)
    simpa only [neg_one_mul] using hminus

end OnLeConjecture.Analytic.QuadraticCrossing
