/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AdicSeparated
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Taylor series of complex analytic germs

This file constructs the Taylor series of an analytic germ in one variable as
a formal power series. Restriction to every complex line then gives an
injective algebra homomorphism from the ring of analytic germs in any finite
dimension to a family of formal power series.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- The canonical continuous linear equivalence between `Source 1` and `ℂ`. -/
@[expose] noncomputable def oneVariableEquiv : Source 1 ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ)

/-- A function on `Source 1`, written as a function on `ℂ`. -/
@[expose] noncomputable def oneVariableRepresentative
    (f : Source 1 → ℂ) : ℂ → ℂ :=
  f ∘ Germ.oneVariableEquiv.symm

@[simp]
theorem oneVariableRepresentative_apply (f : Source 1 → ℂ) (z : ℂ) :
    Germ.oneVariableRepresentative f z =
      f (Germ.oneVariableEquiv.symm z) :=
  rfl

/-- Eventual equality at the origin is preserved when a representative is
written as a function on `ℂ`. -/
theorem oneVariableRepresentative_eventuallyEq {f g : Source 1 → ℂ}
    (hfg : f =ᶠ[𝓝 0] g) :
    Germ.oneVariableRepresentative f =ᶠ[𝓝 0]
      Germ.oneVariableRepresentative g := by
  have ht : Tendsto Germ.oneVariableEquiv.symm
      (𝓝 (0 : ℂ)) (𝓝 (0 : Source 1)) := by
    rw [← map_zero Germ.oneVariableEquiv.symm]
    exact Germ.oneVariableEquiv.symm.continuous.continuousAt
  exact hfg.comp_tendsto ht

/-- Analyticity at the origin is preserved when a representative is written
as a function on `ℂ`. -/
theorem oneVariableRepresentative_analyticAt {f : Source 1 → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (Germ.oneVariableRepresentative f) 0 := by
  have hf' : AnalyticAt ℂ f (Germ.oneVariableEquiv.symm 0) := by
    simpa using hf
  exact hf'.comp (Germ.oneVariableEquiv.symm.analyticAt 0)

/-- The formal Taylor series of a complex function at the origin. Its
coefficients are the iterated derivatives divided by the corresponding
factorials. -/
@[expose] noncomputable def functionTaylorSeries (f : ℂ → ℂ) :
    PowerSeries ℂ :=
  PowerSeries.mk fun k ↦
    (k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0

@[simp]
theorem functionTaylorSeries_coeff (f : ℂ → ℂ) (k : ℕ) :
    PowerSeries.coeff k (Germ.functionTaylorSeries f) =
      (k.factorial : ℂ)⁻¹ * iteratedDeriv k f 0 := by
  simp [Germ.functionTaylorSeries]

/-- The formal Taylor series preserves addition for functions analytic at the
origin. -/
theorem functionTaylorSeries_add {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    Germ.functionTaylorSeries (f + g) =
      Germ.functionTaylorSeries f + Germ.functionTaylorSeries g := by
  ext k
  simp [Germ.functionTaylorSeries_coeff,
    iteratedDeriv_add hf.contDiffAt hg.contDiffAt, mul_add]

/-- The formal Taylor series preserves multiplication for functions analytic
at the origin. -/
theorem functionTaylorSeries_mul {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    Germ.functionTaylorSeries (f * g) =
      Germ.functionTaylorSeries f * Germ.functionTaylorSeries g := by
  ext k
  simp only [Germ.functionTaylorSeries_coeff,
    iteratedDeriv_mul hf.contDiffAt hg.contDiffAt, Finset.mul_sum,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Nat.cast_choose _ (by grind)]
  field_simp [Nat.factorial_ne_zero]

/-- The Taylor series of the zero function is zero. -/
@[simp]
theorem functionTaylorSeries_zero :
    Germ.functionTaylorSeries (fun _ : ℂ ↦ 0) = 0 := by
  ext k
  simp [Germ.functionTaylorSeries_coeff]

/-- The Taylor series of the constant function one is one. -/
@[simp]
theorem functionTaylorSeries_one :
    Germ.functionTaylorSeries (fun _ : ℂ ↦ 1) = 1 := by
  ext k
  have hderiv : iteratedDeriv k (fun _ : ℂ ↦ 1) 0 =
      if k = 0 then (1 : ℂ) else 0 := by
    simpa [ite_apply] using
      (iteratedDeriv_const (𝕜 := ℂ) (F := ℂ) (c := (1 : ℂ))
        (n := k) (x := (0 : ℂ)))
  by_cases hk : k = 0
  · subst k
    simp [Germ.functionTaylorSeries_coeff, hderiv]
  · rw [PowerSeries.coeff_one]
    simp [Germ.functionTaylorSeries_coeff, hderiv, hk]

/-- The Taylor series of a constant function is the corresponding constant
formal power series. -/
theorem functionTaylorSeries_const (c : ℂ) :
    Germ.functionTaylorSeries (fun _ : ℂ ↦ c) = PowerSeries.C c := by
  ext k
  have hderiv : iteratedDeriv k (fun _ : ℂ ↦ c) 0 =
      if k = 0 then c else (0 : ℂ) := by
    simpa [ite_apply] using
      (iteratedDeriv_const (𝕜 := ℂ) (F := ℂ) (c := c)
        (n := k) (x := (0 : ℂ)))
  by_cases hk : k = 0
  · subst k
    simp [Germ.functionTaylorSeries_coeff, hderiv]
  · rw [PowerSeries.coeff_C_of_ne_zero hk]
    simp [Germ.functionTaylorSeries_coeff, hderiv, hk]

/-- An analytic function has zero formal Taylor series exactly when it
vanishes in a neighborhood of the origin. -/
theorem functionTaylorSeries_eq_zero_iff {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) :
    Germ.functionTaylorSeries f = 0 ↔ ∀ᶠ z in 𝓝 0, f z = 0 := by
  rcases hf with ⟨p, hp⟩
  constructor
  · intro hseries
    rw [hp.locally_zero_iff]
    apply FormalMultilinearSeries.ext
    intro k
    apply FormalMultilinearSeries.coeff_eq_zero.mp
    have hcoeff := congrArg (PowerSeries.coeff k) hseries
    have hderiv : iteratedDeriv k f 0 = 0 := by
      simpa [Germ.functionTaylorSeries_coeff,
        Nat.factorial_ne_zero] using hcoeff
    rcases hp with ⟨r, hr⟩
    have hfactorial := hr.factorial_smul (1 : ℂ) k
    have hzero : k.factorial • p.coeff k = 0 := by
      change k.factorial • p.coeff k = iteratedDeriv k f 0 at hfactorial
      exact hfactorial.trans hderiv
    simpa [Nat.factorial_ne_zero] using hzero
  · intro hzero
    ext k
    have hderiv : iteratedDeriv k f 0 = 0 := by
      calc
        iteratedDeriv k f 0 = iteratedDeriv k (0 : ℂ → ℂ) 0 :=
          Filter.EventuallyEq.iteratedDeriv_eq k hzero
        _ = 0 := by simp
    simp [Germ.functionTaylorSeries_coeff, hderiv]

/-- The formal Taylor series of an analytic germ in one variable. -/
@[expose] noncomputable def oneVariableTaylorSeries (q : Germ 1) :
    PowerSeries ℂ :=
  q.1.liftOn
    (fun f ↦ Germ.functionTaylorSeries
      (Germ.oneVariableRepresentative f))
    fun f g hfg ↦ by
      apply PowerSeries.ext
      intro k
      simp only [Germ.functionTaylorSeries_coeff]
      congr 1
      exact Filter.EventuallyEq.iteratedDeriv_eq k
        (Germ.oneVariableRepresentative_eventuallyEq hfg)

@[simp]
theorem oneVariableTaylorSeries_ofFunction (f : Source 1 → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    Germ.oneVariableTaylorSeries (Germ.ofFunction f hf) =
      Germ.functionTaylorSeries (Germ.oneVariableRepresentative f) :=
  rfl

/-- The Taylor series of a one variable analytic germ is zero exactly when
the germ is zero. -/
theorem oneVariableTaylorSeries_eq_zero_iff {q : Germ 1} :
    Germ.oneVariableTaylorSeries q = 0 ↔ q = 0 := by
  rcases q with ⟨q, hq⟩
  change IsAnalyticGerm q at hq
  induction q using Filter.Germ.inductionOn with
  | _ f =>
      have hf : AnalyticAt ℂ f 0 :=
        (isAnalyticGerm_ofFun f).mp hq
      have hfOne := Germ.oneVariableRepresentative_analyticAt hf
      rw [show
        Germ.oneVariableTaylorSeries
            (⟨(f : FunctionGerm 1), hq⟩ : Germ 1) =
          Germ.functionTaylorSeries
            (Germ.oneVariableRepresentative f) from rfl]
      rw [Germ.functionTaylorSeries_eq_zero_iff hfOne]
      constructor
      · intro hzero
        apply Subtype.ext
        apply Filter.Germ.coe_eq.mpr
        have ht : Tendsto Germ.oneVariableEquiv
            (𝓝 (0 : Source 1)) (𝓝 (0 : ℂ)) := by
          rw [← map_zero Germ.oneVariableEquiv]
          exact Germ.oneVariableEquiv.continuous.continuousAt
        have hsource := ht.eventually hzero
        filter_upwards [hsource] with z hz
        simpa [Germ.oneVariableRepresentative] using hz
      · intro hzero
        have hvalue := congrArg Subtype.val hzero
        change (f : FunctionGerm 1) = 0 at hvalue
        have hsource : f =ᶠ[𝓝 0] 0 := Filter.Germ.coe_eq.mp hvalue
        have ht : Tendsto Germ.oneVariableEquiv.symm
            (𝓝 (0 : ℂ)) (𝓝 (0 : Source 1)) := by
          rw [← map_zero Germ.oneVariableEquiv.symm]
          exact Germ.oneVariableEquiv.symm.continuous.continuousAt
        have hone := ht.eventually hsource
        filter_upwards [hone] with z hz
        simpa [Germ.oneVariableRepresentative] using hz

/-- The Taylor series ring homomorphism for analytic germs in one variable. -/
@[expose] noncomputable def oneVariableTaylorRingHom :
    Germ 1 →+* PowerSeries ℂ where
  toFun := Germ.oneVariableTaylorSeries
  map_zero' := by
    rw [Germ.oneVariableTaylorSeries_eq_zero_iff]
  map_one' := by
    change Germ.oneVariableTaylorSeries
        (Germ.ofFunction (fun _ : Source 1 ↦ (1 : ℂ)) analyticAt_const) = 1
    rw [Germ.oneVariableTaylorSeries_ofFunction]
    have hone : Germ.oneVariableRepresentative
        (fun _ : Source 1 ↦ (1 : ℂ)) = fun _ : ℂ ↦ 1 := by
      funext z
      rfl
    rw [hone]
    exact Germ.functionTaylorSeries_one
  map_add' q r := by
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    change IsAnalyticGerm q at hq
    change IsAnalyticGerm r at hr
    induction q using Filter.Germ.inductionOn with
    | _ f =>
      induction r using Filter.Germ.inductionOn with
      | _ g =>
        have hf : AnalyticAt ℂ f 0 :=
          (isAnalyticGerm_ofFun f).mp hq
        have hg : AnalyticAt ℂ g 0 :=
          (isAnalyticGerm_ofFun g).mp hr
        have hfOne := Germ.oneVariableRepresentative_analyticAt hf
        have hgOne := Germ.oneVariableRepresentative_analyticAt hg
        change Germ.functionTaylorSeries
            (Germ.oneVariableRepresentative (f + g)) =
          Germ.functionTaylorSeries (Germ.oneVariableRepresentative f) +
            Germ.functionTaylorSeries (Germ.oneVariableRepresentative g)
        have hadd : Germ.oneVariableRepresentative (f + g) =
            Germ.oneVariableRepresentative f +
              Germ.oneVariableRepresentative g := by
          funext z
          rfl
        rw [hadd]
        exact Germ.functionTaylorSeries_add hfOne hgOne
  map_mul' q r := by
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    change IsAnalyticGerm q at hq
    change IsAnalyticGerm r at hr
    induction q using Filter.Germ.inductionOn with
    | _ f =>
      induction r using Filter.Germ.inductionOn with
      | _ g =>
        have hf : AnalyticAt ℂ f 0 :=
          (isAnalyticGerm_ofFun f).mp hq
        have hg : AnalyticAt ℂ g 0 :=
          (isAnalyticGerm_ofFun g).mp hr
        have hfOne := Germ.oneVariableRepresentative_analyticAt hf
        have hgOne := Germ.oneVariableRepresentative_analyticAt hg
        change Germ.functionTaylorSeries
            (Germ.oneVariableRepresentative (f * g)) =
          Germ.functionTaylorSeries (Germ.oneVariableRepresentative f) *
            Germ.functionTaylorSeries (Germ.oneVariableRepresentative g)
        have hmul : Germ.oneVariableRepresentative (f * g) =
            Germ.oneVariableRepresentative f *
              Germ.oneVariableRepresentative g := by
          funext z
          rfl
        rw [hmul]
        exact Germ.functionTaylorSeries_mul hfOne hgOne

@[simp]
theorem oneVariableTaylorRingHom_apply (q : Germ 1) :
    Germ.oneVariableTaylorRingHom q =
      Germ.oneVariableTaylorSeries q :=
  rfl

/-- The Taylor series ring homomorphism in one variable is injective. -/
theorem oneVariableTaylorRingHom_injective :
    Function.Injective Germ.oneVariableTaylorRingHom := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro q hq
  exact Germ.oneVariableTaylorSeries_eq_zero_iff.mp hq

/-- The Taylor series algebra homomorphism for analytic germs in one
variable. -/
@[expose] noncomputable def oneVariableTaylorAlgHom :
    Germ 1 →ₐ[ℂ] PowerSeries ℂ where
  __ := Germ.oneVariableTaylorRingHom
  commutes' c := by
    change Germ.oneVariableTaylorSeries (Germ.constRingHom 1 c) =
      algebraMap ℂ (PowerSeries ℂ) c
    change Germ.oneVariableTaylorSeries
        (Germ.ofFunction (fun _ : Source 1 ↦ c) analyticAt_const) =
      PowerSeries.C c
    rw [Germ.oneVariableTaylorSeries_ofFunction]
    have hconst : Germ.oneVariableRepresentative
        (fun _ : Source 1 ↦ c) = fun _ : ℂ ↦ c := by
      funext z
      rfl
    rw [hconst]
    exact Germ.functionTaylorSeries_const c

@[simp]
theorem oneVariableTaylorAlgHom_apply (q : Germ 1) :
    Germ.oneVariableTaylorAlgHom q =
      Germ.oneVariableTaylorSeries q :=
  rfl

/-- The Taylor series algebra homomorphism in one variable is injective. -/
theorem oneVariableTaylorAlgHom_injective :
    Function.Injective Germ.oneVariableTaylorAlgHom :=
  Germ.oneVariableTaylorRingHom_injective

/-- Restriction to a complex line, as an algebra homomorphism. -/
@[expose] noncomputable def lineRestrictionAlgHom {n : ℕ}
    (v : Source n) : Germ n →ₐ[ℂ] Germ 1 where
  __ := Germ.lineRestriction v
  commutes' c := by
    exact (Germ.lineGerm v).pullback_constRingHom c

@[simp]
theorem lineRestrictionAlgHom_apply {n : ℕ} (v : Source n)
    (q : Germ n) :
    Germ.lineRestrictionAlgHom v q = Germ.lineRestriction v q :=
  rfl

/-- The family of Taylor series obtained by restricting an analytic germ to
every complex line through the origin. -/
@[expose] noncomputable def radialTaylorAlgHom (n : ℕ) :
    Germ n →ₐ[ℂ] (Source n → PowerSeries ℂ) where
  toFun q v := Germ.oneVariableTaylorAlgHom
    (Germ.lineRestrictionAlgHom v q)
  map_zero' := by
    funext v
    change Germ.oneVariableTaylorAlgHom
      (Germ.lineRestriction v 0) = 0
    rw [map_zero, map_zero]
  map_one' := by
    funext v
    change Germ.oneVariableTaylorAlgHom
      (Germ.lineRestriction v 1) = 1
    rw [map_one, map_one]
  map_add' q r := by
    funext v
    change Germ.oneVariableTaylorAlgHom
      (Germ.lineRestriction v (q + r)) =
        Germ.oneVariableTaylorAlgHom (Germ.lineRestriction v q) +
          Germ.oneVariableTaylorAlgHom (Germ.lineRestriction v r)
    rw [map_add, map_add]
  map_mul' q r := by
    funext v
    change Germ.oneVariableTaylorAlgHom
      (Germ.lineRestriction v (q * r)) =
        Germ.oneVariableTaylorAlgHom (Germ.lineRestriction v q) *
          Germ.oneVariableTaylorAlgHom (Germ.lineRestriction v r)
    rw [map_mul, map_mul]
  commutes' c := by
    funext v
    exact (Germ.oneVariableTaylorAlgHom.comp
      (Germ.lineRestrictionAlgHom v)).commutes c

@[simp]
theorem radialTaylorAlgHom_apply (n : ℕ) (q : Germ n)
    (v : Source n) :
    Germ.radialTaylorAlgHom n q v =
      Germ.oneVariableTaylorSeries (Germ.lineRestriction v q) :=
  rfl

/-- On a function representative, the coefficients of the radial Taylor
series are its normalized directional derivatives. -/
theorem radialTaylorAlgHom_coeff_ofFunction {n : ℕ}
    (f : Source n → ℂ) (hf : AnalyticAt ℂ f 0)
    (k : ℕ) (v : Source n) :
    PowerSeries.coeff k
        (Germ.radialTaylorAlgHom n (Germ.ofFunction f hf) v) =
      (k.factorial : ℂ)⁻¹ *
        iteratedDeriv k (fun z : ℂ ↦ f (z • v)) 0 := by
  rw [Germ.radialTaylorAlgHom_apply,
    Germ.lineRestriction_ofFunction,
    Germ.oneVariableTaylorSeries_ofFunction,
    Germ.functionTaylorSeries_coeff]
  congr 2

/-- Taylor series on all complex lines determine an analytic germ. -/
theorem radialTaylorAlgHom_injective (n : ℕ) :
    Function.Injective (Germ.radialTaylorAlgHom n) := by
  intro f g hfg
  apply sub_eq_zero.mp
  by_contra hsub
  obtain ⟨v, hv⟩ := Germ.exists_lineRestriction_ne_zero hsub
  have hline : Germ.lineRestriction v f = Germ.lineRestriction v g :=
    Germ.oneVariableTaylorAlgHom_injective (congrFun hfg v)
  apply hv
  rw [map_sub, hline, sub_self]

end Germ

end OnLeConjecture.Analytic
