/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Hyperplane
public import OnLeConjecture.Analytic.Inverse
public import OnLeConjecture.Analytic.PullbackEquivalence
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Division by a smooth analytic germ

This file proves the order one case of analytic Weierstrass division. A germ
whose derivative in the first coordinate direction is nonzero can be made
the first coordinate by an analytic change of variables. Its principal
quotient is therefore the analytic germ ring on the corresponding
hyperplane.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Replace the first coordinate of a point by the value of a scalar
function and leave the remaining coordinates unchanged. -/
@[expose] noncomputable def firstCoordinateReplacement {n : ℕ}
    (f : Source (n + 1) → ℂ) : Source (n + 1) → Source (n + 1) :=
  fun z i ↦ Fin.cases (f z) (fun j ↦ z j.succ) i

@[simp]
theorem firstCoordinateReplacement_apply_zero {n : ℕ}
    (f : Source (n + 1) → ℂ) (z : Source (n + 1)) :
    firstCoordinateReplacement f z 0 = f z := by
  simp [firstCoordinateReplacement]

@[simp]
theorem firstCoordinateReplacement_apply_succ {n : ℕ}
    (f : Source (n + 1) → ℂ) (z : Source (n + 1)) (i : Fin n) :
    firstCoordinateReplacement f z i.succ = z i.succ := by
  simp [firstCoordinateReplacement]

/-- Replacing the first coordinate by an analytic function is analytic. -/
theorem firstCoordinateReplacement_analyticAt {n : ℕ}
    {f : Source (n + 1) → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (firstCoordinateReplacement f) 0 := by
  apply AnalyticAt.pi
  intro i
  induction i using Fin.cases with
  | zero =>
      simpa only [firstCoordinateReplacement_apply_zero] using hf
  | succ i =>
      change AnalyticAt ℂ (fun z : Source (n + 1) ↦ z i.succ) 0
      exact (ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Fin (n + 1) ↦ ℂ) i.succ).analyticAt 0

@[simp]
theorem firstCoordinateReplacement_zero {n : ℕ}
    {f : Source (n + 1) → ℂ} (hf0 : f 0 = 0) :
    firstCoordinateReplacement f 0 = 0 := by
  ext i
  induction i using Fin.cases with
  | zero => simp [hf0]
  | succ i => simp

/-- The differential of first coordinate replacement. -/
theorem fderiv_firstCoordinateReplacement_apply {n : ℕ}
    {f : Source (n + 1) → ℂ} (hf : DifferentiableAt ℂ f 0)
    (v : Source (n + 1)) (i : Fin (n + 1)) :
    fderiv ℂ (firstCoordinateReplacement f) 0 v i =
      Fin.cases (fderiv ℂ f 0 v) (fun j ↦ v j.succ) i := by
  rw [fderiv_pi]
  · induction i using Fin.cases with
    | zero => rfl
    | succ i =>
        change fderiv ℂ (fun z : Source (n + 1) ↦ z i.succ) 0 v =
          v i.succ
        change fderiv ℂ
          (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : Fin (n + 1) ↦ ℂ) i.succ) 0 v = v i.succ
        rw [ContinuousLinearMap.fderiv]
        rfl
  · intro j
    induction j using Fin.cases with
    | zero => exact hf
    | succ j =>
        change DifferentiableAt ℂ (fun z : Source (n + 1) ↦ z j.succ) 0
        exact (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin (n + 1) ↦ ℂ) j.succ).differentiableAt

/-- The differential of first coordinate replacement is injective when the
first directional derivative of the replacement function is nonzero. -/
theorem fderiv_firstCoordinateReplacement_injective {n : ℕ}
    {f : Source (n + 1) → ℂ} (hf : DifferentiableAt ℂ f 0)
    (hregular : fderiv ℂ f 0 (firstCoordinateVector n) ≠ 0) :
    Function.Injective (fderiv ℂ (firstCoordinateReplacement f) 0) := by
  apply (injective_iff_map_eq_zero
    (fderiv ℂ (firstCoordinateReplacement f) 0)).mpr
  intro v hv
  have htail (i : Fin n) : v i.succ = 0 := by
    have hi := congrFun hv i.succ
    rw [fderiv_firstCoordinateReplacement_apply hf] at hi
    simpa using hi
  have hfirst : fderiv ℂ f 0 v = 0 := by
    have h0 := congrFun hv (0 : Fin (n + 1))
    rw [fderiv_firstCoordinateReplacement_apply hf] at h0
    simpa using h0
  have hv : v = v 0 • firstCoordinateVector n := by
    ext i
    induction i using Fin.cases with
    | zero => simp
    | succ i => simp [htail i]
  rw [hv, map_smul, smul_eq_mul, mul_eq_zero] at hfirst
  have hv0 : v 0 = 0 := hfirst.resolve_right hregular
  rw [hv, hv0, zero_smul]

/-- A germ regular of order one in the first coordinate can be made the
first coordinate by an analytic change of variables. -/
theorem exists_equiv_pullback_coordinate_eq_of_firstDerivative_ne_zero
    {n : ℕ} (g : Germ (n + 1)) (hg : g ∈ Germ.maximalIdeal (n + 1))
    (hregular : Germ.differential g (firstCoordinateVector n) ≠ 0) :
    ∃ e : PointedEquivGerm (n + 1),
      e.pullbackAlgEquiv (Germ.coordinate (0 : Fin (n + 1))) = g := by
  rcases g with ⟨g, hgan⟩
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hgan
      have hf0 : f 0 = 0 := by
        rw [Germ.mem_maximalIdeal_iff] at hg
        change Filter.Germ.value (f : FunctionGerm (n + 1)) = 0 at hg
        simpa only [Filter.Germ.value_ofFun] using hg
      change fderiv ℂ f 0 (firstCoordinateVector n) ≠ 0 at hregular
      let F : Source (n + 1) → Source (n + 1) :=
        firstCoordinateReplacement f
      have hF : AnalyticAt ℂ F 0 :=
        firstCoordinateReplacement_analyticAt hgan
      have hF0 : F 0 = 0 := firstCoordinateReplacement_zero hf0
      let p : PointedMapGerm (n + 1) (n + 1) :=
        PointedMapGerm.ofFunction F hF hF0
      have hinjective : Function.Injective p.differential := by
        change Function.Injective (fderiv ℂ F 0)
        exact fderiv_firstCoordinateReplacement_injective
          hgan.differentiableAt hregular
      have hbijective : Function.Bijective p.differential :=
        ⟨hinjective, LinearMap.surjective_of_injective hinjective⟩
      rcases p.exists_pointedEquivGerm_of_differential_bijective
          hbijective with ⟨e, he⟩
      refine ⟨e, ?_⟩
      rw [PointedEquivGerm.pullbackAlgEquiv_apply,
        PointedEquivGerm.pullbackRingEquiv_apply, he,
        PointedMapGerm.pullback_coordinate]
      apply Subtype.ext
      change ((MapGerm.ofFunction F hF).component 0).1 = _
      rw [MapGerm.component_ofFunction]
      rfl

/-- Restriction to the hypersurface obtained from the first coordinate
hyperplane by an analytic equivalence. -/
@[expose] noncomputable def smoothRestriction {n : ℕ}
    (e : PointedEquivGerm (n + 1)) : Germ (n + 1) →ₐ[ℂ] Germ n :=
  (Germ.hyperplaneRestrictionAlgHom n).comp
    e.pullbackAlgEquiv.symm.toAlgHom

@[simp]
theorem smoothRestriction_apply {n : ℕ}
    (e : PointedEquivGerm (n + 1)) (q : Germ (n + 1)) :
    Germ.smoothRestriction e q =
      Germ.hyperplaneRestriction n (e.pullbackAlgEquiv.symm q) :=
  rfl

/-- Smooth restriction is surjective. -/
theorem smoothRestriction_surjective {n : ℕ}
    (e : PointedEquivGerm (n + 1)) :
    Function.Surjective (Germ.smoothRestriction e) := by
  intro q
  obtain ⟨r, hr⟩ := Germ.hyperplaneRestrictionAlgHom_surjective n q
  refine ⟨e.pullbackAlgEquiv r, ?_⟩
  rw [Germ.smoothRestriction_apply, e.pullbackAlgEquiv.symm_apply_apply]
  exact hr

/-- The kernel of smooth restriction is generated by the transformed first
coordinate. -/
theorem ker_smoothRestriction_eq_span {n : ℕ}
    (e : PointedEquivGerm (n + 1)) :
    RingHom.ker (Germ.smoothRestriction e) =
      Ideal.span {e.pullbackAlgEquiv
        (Germ.coordinate (0 : Fin (n + 1)))} := by
  ext q
  rw [RingHom.mem_ker]
  change Germ.hyperplaneRestriction n (e.pullbackAlgEquiv.symm q) = 0 ↔ _
  rw [← RingHom.mem_ker,
    Germ.ker_hyperplaneRestriction_eq_span_coordinate_zero]
  simp only [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨e.pullbackAlgEquiv a, ?_⟩
    calc
      q = e.pullbackAlgEquiv (e.pullbackAlgEquiv.symm q) :=
        (e.pullbackAlgEquiv.apply_symm_apply q).symm
      _ = e.pullbackAlgEquiv
          (Germ.coordinate (0 : Fin (n + 1)) * a) := by rw [ha]
      _ = e.pullbackAlgEquiv (Germ.coordinate (0 : Fin (n + 1))) *
          e.pullbackAlgEquiv a := map_mul _ _ _
  · rintro ⟨a, ha⟩
    refine ⟨e.pullbackAlgEquiv.symm a, ?_⟩
    calc
      e.pullbackAlgEquiv.symm q =
          e.pullbackAlgEquiv.symm
            (e.pullbackAlgEquiv
              (Germ.coordinate (0 : Fin (n + 1))) * a) := by rw [ha]
      _ = Germ.coordinate (0 : Fin (n + 1)) *
          e.pullbackAlgEquiv.symm a := by
        rw [map_mul, e.pullbackAlgEquiv.symm_apply_apply]

/-- The quotient by a germ obtained from the first coordinate through an
analytic equivalence is the germ ring on a hyperplane. -/
noncomputable def smoothQuotientAlgEquiv {n : ℕ}
    (e : PointedEquivGerm (n + 1)) :
    (Germ (n + 1) ⧸
        Ideal.span {e.pullbackAlgEquiv
          (Germ.coordinate (0 : Fin (n + 1)))}) ≃ₐ[ℂ]
      Germ n :=
  (Ideal.quotientEquivAlgOfEq ℂ
      (Germ.ker_smoothRestriction_eq_span e).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Germ.smoothRestriction e)
      (Germ.smoothRestriction_surjective e))

@[simp]
theorem smoothQuotientAlgEquiv_mk {n : ℕ}
    (e : PointedEquivGerm (n + 1)) (q : Germ (n + 1)) :
    Germ.smoothQuotientAlgEquiv e
        (Ideal.Quotient.mk
          (Ideal.span {e.pullbackAlgEquiv
            (Germ.coordinate (0 : Fin (n + 1)))}) q) =
      Germ.smoothRestriction e q := by
  rw [Germ.smoothQuotientAlgEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- Order one analytic Weierstrass division. Every germ is a unique sum of
a multiple of the transformed coordinate and the pullback of a germ that is
constant in the first coordinate. -/
theorem exists_unique_smooth_division {n : ℕ}
    (e : PointedEquivGerm (n + 1)) (f : Germ (n + 1)) :
    ∃! qr : Germ (n + 1) × Germ n,
      f = e.pullbackAlgEquiv
          (Germ.coordinate (0 : Fin (n + 1))) * qr.1 +
        e.pullbackAlgEquiv (Germ.hyperplaneExtension n qr.2) := by
  let f' : Germ (n + 1) := e.pullbackAlgEquiv.symm f
  let r : Germ n := Germ.hyperplaneRestriction n f'
  have hdifference :
      f' - Germ.hyperplaneExtension n r ∈
        RingHom.ker (Germ.hyperplaneRestriction n) := by
    rw [RingHom.mem_ker, map_sub]
    change Germ.hyperplaneRestriction n f' -
      Germ.hyperplaneRestriction n (Germ.hyperplaneExtension n r) = 0
    have hext : Germ.hyperplaneRestriction n
        (Germ.hyperplaneExtension n r) = r := by
      simpa using DFunLike.congr_fun
        (Germ.hyperplaneRestriction_comp_extension n) r
    rw [hext]
    simp [r]
  rw [Germ.ker_hyperplaneRestriction_eq_span_coordinate_zero,
    Ideal.mem_span_singleton] at hdifference
  rcases hdifference with ⟨q, hq⟩
  refine ⟨⟨e.pullbackAlgEquiv q, r⟩, ?_, ?_⟩
  · change f = e.pullbackAlgEquiv
        (Germ.coordinate (0 : Fin (n + 1))) *
          e.pullbackAlgEquiv q +
        e.pullbackAlgEquiv (Germ.hyperplaneExtension n r)
    calc
      f = e.pullbackAlgEquiv f' :=
        (e.pullbackAlgEquiv.apply_symm_apply f).symm
      _ = e.pullbackAlgEquiv
          (Germ.coordinate (0 : Fin (n + 1)) * q +
            Germ.hyperplaneExtension n r) := by
        congr 1
        exact (sub_eq_iff_eq_add.mp hq)
      _ = e.pullbackAlgEquiv
          (Germ.coordinate (0 : Fin (n + 1))) *
            e.pullbackAlgEquiv q +
          e.pullbackAlgEquiv (Germ.hyperplaneExtension n r) := by
        rw [map_add, map_mul]
  · intro qr hqr
    rcases qr with ⟨q', r'⟩
    have htransformed := congrArg e.pullbackAlgEquiv.symm hqr
    simp only [map_add, map_mul,
      e.pullbackAlgEquiv.symm_apply_apply] at htransformed
    have hremainder := congrArg (Germ.hyperplaneRestriction n) htransformed
    simp only [map_add, map_mul,
      Germ.hyperplaneRestriction_coordinate_zero, zero_mul, zero_add] at hremainder
    have hext : Germ.hyperplaneRestriction n
        (Germ.hyperplaneExtension n r') = r' := by
      simpa using DFunLike.congr_fun
        (Germ.hyperplaneRestriction_comp_extension n) r'
    rw [hext] at hremainder
    have hr' : r' = r := by
      change r = r' at hremainder
      exact hremainder.symm
    rw [hr'] at htransformed
    have hqeq : e.pullbackAlgEquiv.symm q' = q := by
      have hcoordinate : Germ.coordinate (0 : Fin (n + 1)) *
            e.pullbackAlgEquiv.symm q' =
          Germ.coordinate (0 : Fin (n + 1)) * q := by
        calc
          Germ.coordinate (0 : Fin (n + 1)) *
                e.pullbackAlgEquiv.symm q' =
              f' - Germ.hyperplaneExtension n r :=
            (eq_sub_iff_add_eq.mpr htransformed.symm)
          _ = Germ.coordinate (0 : Fin (n + 1)) * q := hq
      have hcoordinateNe :
          Germ.coordinate (0 : Fin (n + 1)) ≠ 0 := by
        intro hzero
        have hd := congrArg Germ.differential hzero
        have happ := congrArg
          (fun L : Source (n + 1) →L[ℂ] ℂ ↦
            L (firstCoordinateVector n)) hd
        simp [firstCoordinateVector] at happ
      exact mul_left_cancel₀ hcoordinateNe hcoordinate
    have hq' : q' = e.pullbackAlgEquiv q := by
      calc
        q' = e.pullbackAlgEquiv (e.pullbackAlgEquiv.symm q') :=
          (e.pullbackAlgEquiv.apply_symm_apply q').symm
        _ = e.pullbackAlgEquiv q := by rw [hqeq]
    exact Prod.ext hq' hr'

/-- Division by a germ that is regular in the first coordinate direction.
The remainder is an analytic germ on the smooth hypersurface defined by the
divisor. -/
theorem exists_equiv_and_unique_division_of_firstDerivative_ne_zero
    {n : ℕ} (g : Germ (n + 1)) (hg : g ∈ Germ.maximalIdeal (n + 1))
    (hregular : Germ.differential g (firstCoordinateVector n) ≠ 0) :
    ∃ e : PointedEquivGerm (n + 1),
      e.pullbackAlgEquiv (Germ.coordinate (0 : Fin (n + 1))) = g ∧
        ∀ f : Germ (n + 1), ∃! qr : Germ (n + 1) × Germ n,
          f = g * qr.1 +
            e.pullbackAlgEquiv (Germ.hyperplaneExtension n qr.2) := by
  obtain ⟨e, he⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_of_firstDerivative_ne_zero
      g hg hregular
  refine ⟨e, he, ?_⟩
  intro f
  simpa only [he] using Germ.exists_unique_smooth_division e f

/-- The principal quotient by a germ regular in the first coordinate
direction is isomorphic to the analytic germ ring in one fewer variable. -/
theorem nonempty_quotientAlgEquiv_of_firstDerivative_ne_zero
    {n : ℕ} (g : Germ (n + 1)) (hg : g ∈ Germ.maximalIdeal (n + 1))
    (hregular : Germ.differential g (firstCoordinateVector n) ≠ 0) :
    Nonempty
      ((Germ (n + 1) ⧸ Ideal.span {g}) ≃ₐ[ℂ] Germ n) := by
  obtain ⟨e, he⟩ :=
    Germ.exists_equiv_pullback_coordinate_eq_of_firstDerivative_ne_zero
      g hg hregular
  have hquotient := Germ.smoothQuotientAlgEquiv e
  rw [he] at hquotient
  exact ⟨hquotient⟩

end Germ

end OnLeConjecture.Analytic
