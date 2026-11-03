/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Composition
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Equivalences of pointed analytic map germs

This file defines invertible pointed analytic self maps and right left
equivalence of pointed analytic map germs. It proves that right left
equivalence preserves vanishing of the differential.
-/

public section

namespace OnLeConjecture.Analytic

/-- An invertible pointed analytic self map germ. -/
structure PointedEquivGerm (n : ℕ) where
  forward : PointedMapGerm n n
  inverse : PointedMapGerm n n
  forward_inverse : forward.comp inverse = PointedMapGerm.identity n
  inverse_forward : inverse.comp forward = PointedMapGerm.identity n

namespace PointedEquivGerm

/-- The inverse equivalence. -/
@[expose] def symm {n : ℕ} (e : PointedEquivGerm n) :
    PointedEquivGerm n where
  forward := e.inverse
  inverse := e.forward
  forward_inverse := e.inverse_forward
  inverse_forward := e.forward_inverse

/-- The differentials of the forward and inverse germs compose to the
identity in this order. -/
theorem differential_forward_inverse {n : ℕ} (e : PointedEquivGerm n) :
    e.forward.differential ∘L e.inverse.differential =
      ContinuousLinearMap.id ℂ (Source n) := by
  have h := congrArg PointedMapGerm.differential e.forward_inverse
  simpa only [PointedMapGerm.differential_comp,
    PointedMapGerm.differential_identity] using h

/-- The differentials of the inverse and forward germs compose to the
identity in this order. -/
theorem differential_inverse_forward {n : ℕ} (e : PointedEquivGerm n) :
    e.inverse.differential ∘L e.forward.differential =
      ContinuousLinearMap.id ℂ (Source n) := by
  have h := congrArg PointedMapGerm.differential e.inverse_forward
  simpa only [PointedMapGerm.differential_comp,
    PointedMapGerm.differential_identity] using h

end PointedEquivGerm

/-- Right left equivalence of pointed analytic map germs. -/
@[expose] def PointedMapGerm.RightLeftEquivalent {n m : ℕ}
    (f g : PointedMapGerm n m) : Prop :=
  ∃ (source : PointedEquivGerm n) (target : PointedEquivGerm m),
    g = target.forward.comp (f.comp source.forward)

/-- Right left equivalence is symmetric. -/
theorem PointedMapGerm.RightLeftEquivalent.symm {n m : ℕ}
    {f g : PointedMapGerm n m} (hfg : f.RightLeftEquivalent g) :
    g.RightLeftEquivalent f := by
  rcases hfg with ⟨source, target, hfg⟩
  refine ⟨source.symm, target.symm, ?_⟩
  rw [hfg]
  symm
  calc
    target.inverse.comp
        ((target.forward.comp (f.comp source.forward)).comp source.inverse) =
      target.inverse.comp
        (target.forward.comp
          ((f.comp source.forward).comp source.inverse)) := by
            rw [PointedMapGerm.comp_assoc]
    _ = target.inverse.comp
        (target.forward.comp
          (f.comp (source.forward.comp source.inverse))) := by
            rw [PointedMapGerm.comp_assoc]
    _ = target.inverse.comp (target.forward.comp f) := by
            rw [source.forward_inverse, PointedMapGerm.comp_identity]
    _ = (target.inverse.comp target.forward).comp f := by
            rw [PointedMapGerm.comp_assoc]
    _ = f := by
            rw [target.inverse_forward, PointedMapGerm.identity_comp]

/-- Right left equivalent pointed analytic map germs have simultaneously
zero or nonzero differential. -/
theorem PointedMapGerm.rightLeftEquivalent_differential_eq_zero_iff
    {n m : ℕ} {f g : PointedMapGerm n m}
    (hfg : f.RightLeftEquivalent g) :
    g.differential = 0 ↔ f.differential = 0 := by
  rcases hfg with ⟨source, target, rfl⟩
  constructor
  · intro hzero
    have hcomposition :
        target.forward.differential ∘L
            (f.differential ∘L source.forward.differential) = 0 := by
      simpa only [PointedMapGerm.differential_comp] using hzero
    calc
      f.differential =
          (ContinuousLinearMap.id ℂ (Source m)) ∘L f.differential ∘L
            (ContinuousLinearMap.id ℂ (Source n)) := by
              rw [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
      _ = (target.inverse.differential ∘L target.forward.differential) ∘L
            f.differential ∘L
              (source.forward.differential ∘L source.inverse.differential) := by
              rw [target.differential_inverse_forward,
                source.differential_forward_inverse]
      _ = target.inverse.differential ∘L
            (target.forward.differential ∘L
              (f.differential ∘L source.forward.differential)) ∘L
                source.inverse.differential := by
              simp only [ContinuousLinearMap.comp_assoc]
      _ = 0 := by
        rw [hcomposition]
        apply ContinuousLinearMap.ext
        intro v
        simp
  · intro hzero
    rw [PointedMapGerm.differential_comp,
      PointedMapGerm.differential_comp, hzero]
    apply ContinuousLinearMap.ext
    intro v
    simp

end OnLeConjecture.Analytic
