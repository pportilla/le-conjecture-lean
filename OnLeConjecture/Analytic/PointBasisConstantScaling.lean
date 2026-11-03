/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeakTransformIdealData

/-!
# Constant rescaling of a recorded member

A nonzero constant changes neither the orders nor the strict-transform
charts of a member. The weak generators and their completeness remain
unchanged.
-/

public section

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace AnalyticPointBasis

@[expose] noncomputable def scaleMember {N : ℕ} (c : AnalyticPointBasis N)
    (a : ℂ) (ha : a ≠ 0) : AnalyticPointBasis N :=
  { c with
    germ := fun p => constRingHom 2 a * c.germ p
    germ_mem := fun p => (maximalIdeal 2 ^ c.multiplicity p).mul_mem_left _ (c.germ_mem p)
    germ_not_mem_succ := fun p hp => by
      apply c.germ_not_mem_succ p
      have h := (maximalIdeal 2 ^ (c.multiplicity p + 1)).mul_mem_left
        (constRingHom 2 a⁻¹) hp
      simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul] using h
    transform_identity := fun p hp => by
      simp only [map_mul, PointedMapGerm.pullback_constRingHom, c.transform_identity p hp]
      ring }

end AnalyticPointBasis

namespace WeakTransformIdealData

@[expose] noncomputable def scaleMember {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*}
    (d : WeakTransformIdealData c ι) (a : ℂ) (ha : a ≠ 0) :
    WeakTransformIdealData (c.scaleMember a ha) ι where
  generators := d.generators
  generator_mem_pow := d.generator_mem_pow
  generic_member_mem p := (Ideal.span (Set.range (d.generators p))).mul_mem_left _
    (d.generic_member_mem p)
  transform_identity := d.transform_identity

theorem finiteWeakBasepointCompleteness_scaleMember
    {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*}
    (d : WeakTransformIdealData c ι) (a : ℂ) (ha : a ≠ 0)
    (hcomplete : FiniteWeakBasepointCompleteness d) :
    FiniteWeakBasepointCompleteness (d.scaleMember a ha) := by
  constructor
  exact hcomplete.realizes_common_zero

end WeakTransformIdealData

end OnLeConjecture.Analytic
