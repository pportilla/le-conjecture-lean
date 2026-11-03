/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.AnalyticCoordinateEndomorphism

/-!
# Cancellation of an injective analytic germ

An injective analytic germ cancels on the left between pointed maps from
any source dimension, including two curve parametrizations.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

open Filter Set
open scoped Topology

theorem HasInjectiveRepresentative.comp_left_cancel
    {l n m : ℕ} {f : PointedMapGerm n m} (hf : f.HasInjectiveRepresentative)
    {a b : PointedMapGerm l n} (heq : f.comp a = f.comp b) : a = b := by
  obtain ⟨F, hF, hF0, hf, s, hs, hFinj⟩ := hf
  obtain ⟨A, hA, hA0, ha⟩ := a.exists_ofFunction
  obtain ⟨B, hB, hB0, hb⟩ := b.exists_ofFunction
  have hfunctions :
      ((F ∘ A : Source l → Source m) : FunctionMapGerm l m) =
        (F ∘ B : Source l → Source m) := by
    have h := congrArg (fun q : PointedMapGerm l m => q.1.1) heq
    rw [hf, ha, hb, comp_ofFunction, comp_ofFunction] at h
    exact h
  have hFAFB : ∀ᶠ z in nhds (0 : Source l), F (A z) = F (B z) :=
    Filter.Germ.coe_eq.mp hfunctions
  have hAmem : ∀ᶠ z in nhds (0 : Source l), A z ∈ s :=
    hA.continuousAt (by simpa only [hA0] using hs)
  have hBmem : ∀ᶠ z in nhds (0 : Source l), B z ∈ s :=
    hB.continuousAt (by simpa only [hB0] using hs)
  have hAB : A =ᶠ[nhds (0 : Source l)] B := by
    filter_upwards [hFAFB, hAmem, hBmem] with z heq hAz hBz
    exact hFinj hAz hBz heq
  rw [ha, hb]
  apply Subtype.ext
  apply Subtype.ext
  exact Filter.Germ.coe_eq.mpr hAB

end OnLeConjecture.Analytic.PointedMapGerm
