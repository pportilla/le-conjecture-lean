/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Germ
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.Germ

/-!
# Germs of complex analytic maps

This file defines analytic map germs between finite dimensional complex vector
spaces, their differential at the origin, and the proposition asserted by
Lê's conjecture in dimensions two and three.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- The ambient type of function germs from `ℂⁿ` to `ℂᵐ`. -/
abbrev FunctionMapGerm (n m : ℕ) :=
  Filter.Germ (𝓝 (0 : Source n)) (Source m)

/-- Analyticity of a map germ at the origin. -/
def IsAnalyticMapGerm {n m : ℕ} (g : FunctionMapGerm n m) : Prop :=
  g.liftOn (fun f ↦ AnalyticAt ℂ f 0) fun _f _h hfh ↦
    propext (analyticAt_congr hfh)

@[simp]
theorem isAnalyticMapGerm_ofFun {n m : ℕ} (f : Source n → Source m) :
    IsAnalyticMapGerm (f : FunctionMapGerm n m) ↔ AnalyticAt ℂ f 0 :=
  Iff.rfl

/-- A complex analytic map germ from `ℂⁿ` to `ℂᵐ`. -/
abbrev MapGerm (n m : ℕ) :=
  {g : FunctionMapGerm n m // IsAnalyticMapGerm g}

/-- An analytic map defines an analytic map germ. -/
@[expose] noncomputable def MapGerm.ofFunction {n m : ℕ}
    (f : Source n → Source m) (hf : AnalyticAt ℂ f 0) : MapGerm n m :=
  ⟨(f : FunctionMapGerm n m), (isAnalyticMapGerm_ofFun f).2 hf⟩

/-- The differential of a map germ at the origin. Eventual equality of
representatives makes the definition independent of the representative. -/
@[expose] noncomputable def MapGerm.differential {n m : ℕ} (g : MapGerm n m) :
    Source n →L[ℂ] Source m :=
  g.1.liftOn (fun f ↦ fderiv ℂ f 0) fun _f _h hfh ↦
    hfh.fderiv_eq

@[simp]
theorem MapGerm.differential_ofFunction {n m : ℕ}
    (f : Source n → Source m) (hf : AnalyticAt ℂ f 0) :
    (MapGerm.ofFunction f hf).differential = fderiv ℂ f 0 :=
  rfl

/-- The value of a map germ at the origin. -/
@[expose] noncomputable def MapGerm.valueAtOrigin {n m : ℕ} (g : MapGerm n m) :
    Source m :=
  g.1.value

@[simp]
theorem MapGerm.valueAtOrigin_ofFunction {n m : ℕ}
    (f : Source n → Source m) (hf : AnalyticAt ℂ f 0) :
    (MapGerm.ofFunction f hf).valueAtOrigin = f 0 :=
  rfl

/-- An analytic germ that maps the origin to the origin. -/
abbrev PointedMapGerm (n m : ℕ) :=
  {g : MapGerm n m // g.valueAtOrigin = 0}

/-- An analytic function that vanishes at the origin defines a pointed map
germ. -/
@[expose] noncomputable def PointedMapGerm.ofFunction {n m : ℕ}
    (f : Source n → Source m) (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    PointedMapGerm n m :=
  ⟨MapGerm.ofFunction f hf, by simpa using h0⟩

/-- The differential of a pointed map germ at the origin. -/
@[expose] noncomputable def PointedMapGerm.differential {n m : ℕ}
    (g : PointedMapGerm n m) : Source n →L[ℂ] Source m :=
  g.1.differential

@[simp]
theorem PointedMapGerm.differential_ofFunction {n m : ℕ}
    (f : Source n → Source m) (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    (PointedMapGerm.ofFunction f hf h0).differential = fderiv ℂ f 0 :=
  rfl

/-- A map germ has an injective representative when some representative is
injective on a neighborhood of the origin. -/
@[expose] def PointedMapGerm.HasInjectiveRepresentative {n m : ℕ}
    (g : PointedMapGerm n m) : Prop :=
  ∃ (f : Source n → Source m) (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0),
    g = PointedMapGerm.ofFunction f hf h0 ∧
      ∃ s ∈ 𝓝 (0 : Source n), Set.InjOn f s

/-- The formal statement of Lê's conjecture for maps from `ℂ²` to `ℂ³`. -/
@[expose] def LeConjecture : Prop :=
  ∀ g : PointedMapGerm 2 3,
    g.HasInjectiveRepresentative → g.differential ≠ 0

end OnLeConjecture.Analytic
