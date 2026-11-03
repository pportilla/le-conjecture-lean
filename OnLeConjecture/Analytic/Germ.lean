/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Order.Filter.Germ.Basic

/-!
# Complex analytic germs at the origin

This file defines the ring of scalar complex analytic germs at the origin of
`ℂⁿ`. It uses the existing quotient of functions by eventual equality and the
predicate `AnalyticAt` from mathlib.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- The source vector space for germs in `n` variables. -/
abbrev Source (n : ℕ) := Fin n → ℂ

/-- The ambient ring of germs of complex valued functions at the origin. -/
abbrev FunctionGerm (n : ℕ) :=
  Filter.Germ (𝓝 (0 : Source n)) ℂ

/-- A function germ is analytic when any representative is analytic at the
origin. Eventual equality makes this predicate independent of the chosen
representative. -/
def IsAnalyticGerm {n : ℕ} (g : FunctionGerm n) : Prop :=
  g.liftOn (fun f ↦ AnalyticAt ℂ f 0) fun _f _h hfh ↦
    propext (analyticAt_congr hfh)

@[simp]
theorem isAnalyticGerm_ofFun {n : ℕ} (f : Source n → ℂ) :
    IsAnalyticGerm (f : FunctionGerm n) ↔ AnalyticAt ℂ f 0 :=
  Iff.rfl

/-- The analytic function germs form a subring of all function germs. -/
@[expose] def analyticGermSubring (n : ℕ) : Subring (FunctionGerm n) where
  carrier := {g | IsAnalyticGerm g}
  zero_mem' := by
    change AnalyticAt ℂ (fun _ : Source n ↦ (0 : ℂ)) 0
    exact analyticAt_const
  one_mem' := by
    change AnalyticAt ℂ (fun _ : Source n ↦ (1 : ℂ)) 0
    exact analyticAt_const
  add_mem' := by
    intro f g hf hg
    induction f using Filter.Germ.inductionOn with
    | _ f =>
      induction g using Filter.Germ.inductionOn with
      | _ g =>
        change AnalyticAt ℂ f 0 at hf
        change AnalyticAt ℂ g 0 at hg
        change AnalyticAt ℂ (fun x ↦ f x + g x) 0
        exact hf.add hg
  neg_mem' := by
    intro f hf
    induction f using Filter.Germ.inductionOn with
    | _ f =>
      change AnalyticAt ℂ f 0 at hf
      change AnalyticAt ℂ (fun x ↦ -f x) 0
      exact hf.neg
  mul_mem' := by
    intro f g hf hg
    induction f using Filter.Germ.inductionOn with
    | _ f =>
      induction g using Filter.Germ.inductionOn with
      | _ g =>
        change AnalyticAt ℂ f 0 at hf
        change AnalyticAt ℂ g 0 at hg
        change AnalyticAt ℂ (fun x ↦ f x * g x) 0
        exact hf.mul hg

@[simp]
theorem mem_analyticGermSubring {n : ℕ} {g : FunctionGerm n} :
    g ∈ analyticGermSubring n ↔ IsAnalyticGerm g :=
  Iff.rfl

/-- The ring of scalar complex analytic germs at the origin of `ℂⁿ`. -/
abbrev Germ (n : ℕ) := analyticGermSubring n

/-- An analytic function defines an analytic germ. -/
@[expose] noncomputable def Germ.ofFunction {n : ℕ}
    (f : Source n → ℂ) (hf : AnalyticAt ℂ f 0) :
    Germ n :=
  ⟨(f : FunctionGerm n), (isAnalyticGerm_ofFun f).mpr hf⟩

@[simp]
theorem Germ.coe_ofFunction {n : ℕ} (f : Source n → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    ((Germ.ofFunction f hf : Germ n) : FunctionGerm n) =
      (f : FunctionGerm n) :=
  rfl

/-- Eventually equal analytic functions determine the same analytic germ. -/
theorem Germ.ofFunction_eq_of_eventuallyEq {n : ℕ}
    {f g : Source n → ℂ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (hfg : f =ᶠ[𝓝 0] g) :
    Germ.ofFunction f hf = Germ.ofFunction g hg := by
  apply Subtype.ext
  exact hfg.germ_eq

/-- The germ of the `i`th coordinate function. -/
@[expose] noncomputable def Germ.coordinate {n : ℕ} (i : Fin n) : Germ n :=
  Germ.ofFunction (fun z : Source n ↦ z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0)

@[simp]
theorem Germ.coe_coordinate {n : ℕ} (i : Fin n) :
    ((Germ.coordinate i : Germ n) : FunctionGerm n) =
      ((fun z : Source n ↦ z i) : FunctionGerm n) :=
  rfl

/-- Constant analytic germs form a ring homomorphism from `ℂ`. -/
@[expose] noncomputable def Germ.constRingHom (n : ℕ) : ℂ →+* Germ n where
  toFun c := Germ.ofFunction (fun _ : Source n ↦ c) analyticAt_const
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem Germ.coe_constRingHom (n : ℕ) (c : ℂ) :
    (((Germ.constRingHom n) c : Germ n) : FunctionGerm n) =
      ((fun _ : Source n ↦ c) : FunctionGerm n) :=
  rfl

noncomputable instance Germ.instAlgebra (n : ℕ) : Algebra ℂ (Germ n) :=
  (Germ.constRingHom n).toAlgebra

end OnLeConjecture.Analytic
