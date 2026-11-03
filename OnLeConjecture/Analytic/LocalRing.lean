/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Germ
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Topology.Germ

/-!
# The local ring of complex analytic germs

This file defines evaluation at the origin on complex analytic germs. Its
kernel is the maximal ideal of germs that vanish at the origin. An analytic
germ is a unit exactly when its value at the origin is nonzero. Consequently,
the ring of analytic germs is a local ring.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Evaluation at the origin is a ring homomorphism on analytic germs. -/
@[expose] noncomputable def valueRingHom (n : ℕ) : Germ n →+* ℂ :=
  Filter.Germ.valueRingHom.comp (analyticGermSubring n).subtype

@[simp]
theorem valueRingHom_ofFunction {n : ℕ} (f : Source n → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    valueRingHom n (Germ.ofFunction f hf) = f 0 := by
  change Filter.Germ.value (f : FunctionGerm n) = f 0
  exact Filter.Germ.value_ofFun f 0

@[simp]
theorem valueRingHom_const (n : ℕ) (c : ℂ) :
    valueRingHom n (Germ.constRingHom n c) = c := by
  change Filter.Germ.value
      ((fun _ : Source n ↦ c) : FunctionGerm n) = c
  exact Filter.Germ.value_ofFun (fun _ : Source n ↦ c) 0

/-- Evaluation at the origin is surjective because constant germs are
analytic. -/
theorem valueRingHom_surjective (n : ℕ) :
    Function.Surjective (valueRingHom n) := by
  intro c
  exact ⟨Germ.constRingHom n c, valueRingHom_const n c⟩

/-- The ideal of analytic germs that vanish at the origin. -/
@[expose] noncomputable def maximalIdeal (n : ℕ) : Ideal (Germ n) :=
  RingHom.ker (valueRingHom n)

@[simp]
theorem mem_maximalIdeal_iff {n : ℕ} {g : Germ n} :
    g ∈ maximalIdeal n ↔ valueRingHom n g = 0 :=
  RingHom.mem_ker

/-- The kernel of evaluation at the origin is a maximal ideal. -/
theorem maximalIdeal_isMaximal (n : ℕ) :
    (maximalIdeal n).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (valueRingHom n)
    (valueRingHom_surjective n)

/-- An analytic germ with nonzero value at the origin is a unit. -/
theorem isUnit_of_valueRingHom_ne_zero {n : ℕ} {g : Germ n}
    (hg : valueRingHom n g ≠ 0) : IsUnit g := by
  rcases g with ⟨g, hgan⟩
  change IsAnalyticGerm g at hgan
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      have hf : AnalyticAt ℂ f 0 :=
        (isAnalyticGerm_ofFun f).mp hgan
      have hf0 : f 0 ≠ 0 := by
        change Filter.Germ.value (f : FunctionGerm n) ≠ 0 at hg
        simpa only [Filter.Germ.value_ofFun] using hg
      refine isUnit_iff_exists_inv.mpr
        ⟨⟨(f⁻¹ : FunctionGerm n),
          (isAnalyticGerm_ofFun f⁻¹).mpr (hf.inv hf0)⟩, ?_⟩
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact (hf.continuousAt.eventually_ne hf0).mono fun z hz ↦ by
        simp [hz]

/-- Evaluation at the origin of a unit is nonzero. -/
theorem valueRingHom_ne_zero_of_isUnit {n : ℕ} {g : Germ n}
    (hg : IsUnit g) : valueRingHom n g ≠ 0 :=
  isUnit_iff_ne_zero.mp (hg.map (valueRingHom n))

/-- A complex analytic germ is a unit exactly when it does not vanish at the
origin. -/
theorem isUnit_iff_valueRingHom_ne_zero {n : ℕ} {g : Germ n} :
    IsUnit g ↔ valueRingHom n g ≠ 0 :=
  ⟨valueRingHom_ne_zero_of_isUnit, isUnit_of_valueRingHom_ne_zero⟩

/-- The ring of complex analytic germs at the origin is local. -/
noncomputable instance instIsLocalRing (n : ℕ) : IsLocalRing (Germ n) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun g ↦ by
    by_cases hg : valueRingHom n g = 0
    · right
      apply isUnit_of_valueRingHom_ne_zero
      simp [hg]
    · left
      exact isUnit_of_valueRingHom_ne_zero hg

end Germ

end OnLeConjecture.Analytic
