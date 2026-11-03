/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CyclicCoverDescent
public import OnLeConjecture.Analytic.DiagonalCoordinates
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The cyclic-cover relation and independence of analytic remainders

Power substitution is injective on analytic plane germs. Distinct residue
characters then separate the terms of an analytic remainder in the last
cover coordinate. The final kernel equality explicitly retains analytic
division for an arbitrary three-variable dividend as a hypothesis.
-/

public section

open Filter
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic.CyclicCover

/-- Equality after simultaneous positive power substitution implies
equality on a neighborhood, even without analyticity. -/
theorem eventuallyEq_of_comp_powerPairFunction (r : ℕ) (hr : 0 < r)
    {f g : Source 2 → ℂ}
    (hfg : (f ∘ powerPairFunction r) =ᶠ[nhds 0] (g ∘ powerPairFunction r)) :
    f =ᶠ[nhds 0] g := by
  rcases Metric.eventually_nhds_iff.mp hfg with ⟨ε, hε, hball⟩
  apply Filter.Eventually.mono (Metric.ball_mem_nhds (0 : Source 2) (pow_pos hε r))
  intro z hz
  have hzNorm : ‖z‖ < ε ^ r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hzCoord : ∀ i, ‖z i‖ < ε ^ r :=
    (pi_norm_lt_iff (pow_pos hε r)).mp hzNorm
  choose w hw using fun i => IsAlgClosed.exists_pow_nat_eq (z i) hr
  have hwNorm : ‖w‖ < ε := by
    apply (pi_norm_lt_iff hε).mpr
    intro i
    apply lt_of_pow_lt_pow_left₀ r hε.le
    rw [← norm_pow, hw]
    exact hzCoord i
  have hwBall : w ∈ Metric.ball (0 : Source 2) ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using hwNorm
  have hpowers : powerPairFunction r w = z := funext hw
  simpa only [Function.comp_apply, hpowers] using hball hwBall

/-- Simultaneous positive power substitution is injective on analytic
plane germs. -/
theorem powerPairGerm_pullback_injective (r : ℕ) (hr : 0 < r) :
    Function.Injective (powerPairGerm r hr).pullbackRingHom := by
  intro f g hfg
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  change IsAnalyticGerm f at hf
  change IsAnalyticGerm g at hg
  induction f using Filter.Germ.inductionOn with
  | _ f =>
      induction g using Filter.Germ.inductionOn with
      | _ g =>
          rw [isAnalyticGerm_ofFun] at hf hg
          change Germ.compPointed (Germ.ofFunction f hf) (powerPairGerm r hr) =
            Germ.compPointed (Germ.ofFunction g hg) (powerPairGerm r hr) at hfg
          rw [powerPairGerm, Germ.compPointed_ofFunction,
            Germ.compPointed_ofFunction] at hfg
          apply Subtype.ext
          apply Filter.Germ.coe_eq.mpr
          apply eventuallyEq_of_comp_powerPairFunction r hr
          exact Filter.Germ.coe_eq.mp (congrArg Subtype.val hfg)

/-- A vanishing sum of distinct residue eigenvectors has every term zero.
-/
theorem eq_zero_of_sum_residue_eigenvectors_eq_zero
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    (r : ℕ) (hr : 0 < r) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (T : Module.End ℂ A) (q : Fin r → A)
    (hcharacter : ∀ i, T (q i) = ζ ^ i.1 • q i)
    (hsum : ∑ i, q i = 0) : ∀ i, q i = 0 := by
  classical
  intro j
  let S : Module.End ℂ A := (ζ ^ j.1)⁻¹ • T
  let p : Fin r → Fin r → A := fun i k => if k = j then q i else 0
  have hdecomposition : (0 : A) = ∑ i, ∑ k, p i k := by
    simpa [p] using hsum.symm
  have hpcharacter (i k : Fin r) :
      S (p i k) = (ζ ^ i.1 / ζ ^ k.1) • p i k := by
    by_cases hkj : k = j
    · subst k
      simp only [S, p, if_pos rfl, LinearMap.smul_apply, hcharacter,
        smul_smul, div_eq_mul_inv, mul_comm]
    · simp [p, hkj]
  have hdiagonal := invariant_sum_eq_diagonal r hr ζ hζ S p 0
    hdecomposition hpcharacter (map_zero S)
  simpa [p] using hdiagonal.symm

/-- Scaling only the first source coordinate. -/
@[expose] noncomputable def firstScalingFunction (ζ : ℂ) (z : Source 2) :
    Source 2 := fun i => (if i = 0 then ζ else 1) * z i

theorem firstScalingFunction_analyticAt (ζ : ℂ) :
    AnalyticAt ℂ (firstScalingFunction ζ) 0 := by
  apply AnalyticAt.pi
  intro i
  exact analyticAt_const.mul
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).analyticAt 0)

theorem firstScalingFunction_zero (ζ : ℂ) :
    firstScalingFunction ζ (0 : Source 2) = 0 := by
  funext i
  simp [firstScalingFunction]

/-- The pointed germ scaling only the first coordinate. -/
@[expose] noncomputable def firstScalingGerm (ζ : ℂ) : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (firstScalingFunction ζ)
    (firstScalingFunction_analyticAt ζ) (firstScalingFunction_zero ζ)

@[expose] noncomputable def firstScalingAlgHom (ζ : ℂ) : Germ 2 →ₐ[ℂ] Germ 2 where
  toRingHom := (firstScalingGerm ζ).pullbackRingHom
  commutes' c := (firstScalingGerm ζ).pullback_constRingHom c

@[simp]
theorem firstScalingAlgHom_coordinate (ζ : ℂ) (i : Fin 2) :
    firstScalingAlgHom ζ (Germ.coordinate i) =
      Germ.constRingHom 2 (if i = 0 then ζ else 1) * Germ.coordinate i := by
  change (firstScalingGerm ζ).pullbackRingHom (Germ.coordinate i) = _
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rw [show (firstScalingGerm ζ).1 = MapGerm.ofFunction (firstScalingFunction ζ)
    (firstScalingFunction_analyticAt ζ) from rfl, MapGerm.component_ofFunction]
  rfl

theorem powerPair_comp_firstScaling (r : ℕ) (hr : 0 < r) (ζ : ℂ)
    (hζ : ζ ^ r = 1) :
    (powerPairGerm r hr).comp (firstScalingGerm ζ) = powerPairGerm r hr := by
  simp only [powerPairGerm, firstScalingGerm, PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  funext i
  change ((if i = 0 then ζ else 1) * z i) ^ r = z i ^ r
  rw [mul_pow]
  split_ifs <;> simp [hζ]

theorem firstScalingAlgHom_powerPair_pullback (r : ℕ) (hr : 0 < r) (ζ : ℂ)
    (hζ : ζ ^ r = 1) (a : Germ 2) :
    firstScalingAlgHom ζ ((powerPairGerm r hr).pullbackRingHom a) =
      (powerPairGerm r hr).pullbackRingHom a := by
  change ((firstScalingGerm ζ).pullbackRingHom.comp
    (powerPairGerm r hr).pullbackRingHom) a = _
  rw [← PointedMapGerm.pullbackRingHom_comp, powerPair_comp_firstScaling r hr ζ hζ]

/-- Analytic coefficients in distinct diagonal residues are independent
after pullback by the cyclic cover. -/
theorem diagonal_remainder_coefficients_eq_zero
    (r : ℕ) (hr : 0 < r) (a : Fin r → Germ 2)
    (hzero : ∑ i, (powerPairGerm r hr).pullbackRingHom (a i) *
      (Germ.coordinate (0 : Fin 2) * Germ.coordinate (1 : Fin 2)) ^ i.1 = 0) :
    ∀ i, a i = 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / r)
  have hζ : IsPrimitiveRoot ζ r := Complex.isPrimitiveRoot_exp r hr.ne'
  let q : Fin r → Germ 2 := fun i =>
    (powerPairGerm r hr).pullbackRingHom (a i) *
      (Germ.coordinate (0 : Fin 2) * Germ.coordinate (1 : Fin 2)) ^ i.1
  have hcharacter (i : Fin r) :
      (firstScalingAlgHom ζ).toLinearMap (q i) = ζ ^ i.1 • q i := by
    change firstScalingAlgHom ζ
      ((powerPairGerm r hr).pullbackRingHom (a i) *
        (Germ.coordinate (0 : Fin 2) * Germ.coordinate (1 : Fin 2)) ^ i.1) = _
    rw [map_mul, map_pow, map_mul,
      firstScalingAlgHom_powerPair_pullback r hr ζ hζ.pow_eq_one,
      firstScalingAlgHom_coordinate, firstScalingAlgHom_coordinate]
    simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false,
      map_one, one_mul, Algebra.smul_def]
    change (powerPairGerm r hr).pullbackRingHom (a i) *
        (Germ.constRingHom 2 ζ * Germ.coordinate 0 * Germ.coordinate 1) ^ i.1 =
      Germ.constRingHom 2 (ζ ^ i.1) *
        ((powerPairGerm r hr).pullbackRingHom (a i) *
          (Germ.coordinate 0 * Germ.coordinate 1) ^ i.1)
    rw [map_pow, mul_pow, mul_pow, mul_pow]
    ring
  have hq := eq_zero_of_sum_residue_eigenvectors_eq_zero r hr ζ hζ
    (firstScalingAlgHom ζ).toLinearMap q hcharacter hzero
  intro i
  have hmonomial :
      (Germ.coordinate (0 : Fin 2) * Germ.coordinate (1 : Fin 2)) ^ i.1 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (Germ.coordinate_ne_zero _) (Germ.coordinate_ne_zero _))
  have hpullback : (powerPairGerm r hr).pullbackRingHom (a i) = 0 :=
    (mul_eq_zero.mp (hq i)).resolve_right hmonomial
  exact powerPairGerm_pullback_injective r hr (hpullback.trans (map_zero _).symm)

/-- The hypersurface equation in the three cover coordinates. -/
@[expose] noncomputable def relationGerm (r : ℕ) : Germ 3 :=
  Germ.coordinate (0 : Fin 3) * Germ.coordinate (1 : Fin 3) -
    Germ.coordinate (2 : Fin 3) ^ r

@[simp]
theorem coverGerm_pullback_first (r : ℕ) (hr : 0 < r) :
    (coverGerm r hr).pullbackRingHom (Germ.coordinate (0 : Fin 3)) =
      Germ.coordinate (0 : Fin 2) ^ r := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rw [show (coverGerm r hr).1 = MapGerm.ofFunction (coverFunction r)
    (coverFunction_analyticAt r) from rfl, MapGerm.component_ofFunction]
  rfl

@[simp]
theorem coverGerm_pullback_second (r : ℕ) (hr : 0 < r) :
    (coverGerm r hr).pullbackRingHom (Germ.coordinate (1 : Fin 3)) =
      Germ.coordinate (1 : Fin 2) ^ r := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rw [show (coverGerm r hr).1 = MapGerm.ofFunction (coverFunction r)
    (coverFunction_analyticAt r) from rfl, MapGerm.component_ofFunction]
  rfl

@[simp]
theorem coverGerm_pullback_relation (r : ℕ) (hr : 0 < r) :
    (coverGerm r hr).pullbackRingHom (relationGerm r) = 0 := by
  simp only [relationGerm, map_sub, map_mul, map_pow,
    coverGerm_pullback_first, coverGerm_pullback_second,
    coverGerm_pullback_last, mul_pow, sub_self]

/-- Every analytic multiple of the hypersurface equation vanishes after
pullback. -/
theorem span_relation_le_ker_coverGerm_pullback (r : ℕ) (hr : 0 < r) :
    Ideal.span {relationGerm r} ≤ RingHom.ker (coverGerm r hr).pullbackRingHom := by
  rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  exact coverGerm_pullback_relation r hr

/-- Once analytic division in the last coordinate is available for an
arbitrary three-variable dividend, the cyclic-cover kernel is exactly the
principal ideal generated by its hypersurface equation. -/
theorem ker_coverGerm_pullback_eq_span_of_analytic_division
    (r : ℕ) (hr : 0 < r)
    (hdivision : ∀ f : Germ 3, ∃ q : Germ 3, ∃ a : Fin r → Germ 2,
      f = relationGerm r * q + ∑ i,
        projectionGerm.pullbackRingHom (a i) * Germ.coordinate (2 : Fin 3) ^ i.1) :
    RingHom.ker (coverGerm r hr).pullbackRingHom = Ideal.span {relationGerm r} := by
  apply le_antisymm
  · intro f hf
    obtain ⟨q, a, hdivision⟩ := hdivision f
    have hzero := congrArg (coverGerm r hr).pullbackRingHom hdivision
    rw [RingHom.mem_ker] at hf
    simp only [hf, map_add, map_mul, coverGerm_pullback_relation,
      zero_mul, zero_add, map_sum, map_pow, coverGerm_pullback_last,
      coverGerm_pullback_projection] at hzero
    have ha := diagonal_remainder_coefficients_eq_zero r hr a hzero.symm
    have hfq : f = relationGerm r * q := by
      simpa only [ha, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
        using hdivision
    rw [hfq]
    exact Ideal.mul_mem_right q (Ideal.span {relationGerm r})
      (Ideal.subset_span (Set.mem_singleton (relationGerm r)))
  · exact span_relation_le_ker_coverGerm_pullback r hr

end OnLeConjecture.Analytic.CyclicCover
