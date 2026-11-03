/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ImageRingDimension
public import OnLeConjecture.External.TauCeti.KrullDimensionQuotient

/-!
# Height of the ideal defining a finite plane image in three-space

The target analytic local ring has dimension three, and the quotient by
the pullback kernel has dimension two. The general inequality between
height and quotient dimension bounds the kernel's height by one. The
kernel is a nonzero prime ideal in a domain, so its height equals one.
No factoriality assumption is required for this conclusion.
-/

public section

namespace OnLeConjecture

/-- A nonzero prime in a three-dimensional domain with two-dimensional
quotient has height one. -/
theorem height_eq_one_of_dim_three_quotient_dim_two
    {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (hp : p ≠ ⊥) (hdim : ringKrullDim R = (3 : ℕ∞))
    (hquot : ringKrullDim (R ⧸ p) = (2 : ℕ∞)) : p.height = 1 := by
  have h := Ideal.height_add_ringKrullDim_quotient_le p
  rw [hdim, hquot] at h
  have hupper : p.height ≤ 1 := by
    have h' : (p.height : WithBot ℕ∞) + (2 : ℕ) ≤ (1 : WithBot ℕ∞) + (2 : ℕ) := by
      norm_num at h ⊢
      exact h
    exact WithBot.coe_le_coe.mp (ENat.WithBot.add_le_add_natCast_right_iff.mp h')
  have hlower : 1 ≤ p.height := by
    apply Order.one_le_iff_ne_zero.mpr
    intro hz
    exact hp (Ideal.height_eq_zero_iff_eq_bot.mp hz)
  exact le_antisymm hupper hlower

namespace Analytic.PointedMapGerm

/-- The pullback kernel of a finite plane germ into three-space has height
one in the actual target ring of analytic germs. -/
theorem pullback_kernel_height_eq_one_of_finite
    (g : PointedMapGerm 2 3) (hfinite : g.IsFiniteAtOrigin) :
    (RingHom.ker g.pullbackRingHom).height = 1 := by
  let := g.pullback_kernel_isPrime
  apply height_eq_one_of_dim_three_quotient_dim_two
  · exact g.pullback_kernel_ne_bot_of_finite_of_two_lt hfinite (by decide)
  · simpa using Germ.ringKrullDim_all 3
  · rw [g.quotientKernelEquivImageRing.ringKrullDim]
    exact g.imageRing_ringKrullDim_eq_two_of_finite hfinite

/-- Local injectivity supplies finiteness, hence height one for the
vanishing ideal of the plane image in three-space. -/
theorem pullback_kernel_height_eq_one_of_injective
    (g : PointedMapGerm 2 3) (hinjective : g.HasInjectiveRepresentative) :
    (RingHom.ker g.pullbackRingHom).height = 1 :=
  g.pullback_kernel_height_eq_one_of_finite (g.injective_isFiniteAtOrigin_two hinjective)

end Analytic.PointedMapGerm

end OnLeConjecture
