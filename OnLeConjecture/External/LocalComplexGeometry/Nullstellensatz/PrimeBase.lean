/-
Vendored from BochaoKong/nullstellensatz, commit
029697242294aea7989bf5d391199696a43490df, retrieved 2026-10-29.
Original source: LocalComplexGeometry/Nullstellensatz/PrimeBase.lean
https://github.com/BochaoKong/nullstellensatz/tree/029697242294aea7989bf5d391199696a43490df
Licensed under Apache 2.0. See the retained LICENSE in this source directory.
-/
module

public import OnLeConjecture.External.LocalComplexGeometry.Germs.Ring
public import OnLeConjecture.External.LocalComplexGeometry.Nullstellensatz.RadicalReduction

@[expose] public section

/-!
# The zero-dimensional prime case

The analytic Nullstellensatz induction starts in complex dimension zero.  The
germ ring there is canonically `ℂ`, so its only prime ideal is zero; the zero
ideal has the full neighborhood as its zero-set germ.
-/

namespace LocalComplexGeometry

noncomputable section

/-- Every prime ideal of the zero-dimensional holomorphic germ ring is zero. -/
theorem holomorphicGerm_zero_prime_eq_bot
    (P : Ideal (HolomorphicGerm 0)) (hP : P.IsPrime) :
    P = ⊥ := by
  apply le_antisymm
  · intro f hf
    by_contra hf0
    have he0 : holomorphicGermZeroEquiv f ≠ 0 :=
      fun h ↦ hf0 (holomorphicGermZeroEquiv.injective (h.trans (map_zero _).symm))
    have heunit : IsUnit (holomorphicGermZeroEquiv f) :=
      isUnit_iff_ne_zero.mpr he0
    have hfunit : IsUnit f :=
      (MulEquiv.isUnit_map holomorphicGermZeroEquiv).mp heunit
    let : P.IsPrime := hP
    exact (Ideal.notMem_of_isUnit P hfunit) hf
  · exact bot_le

/-- The prime zero-set theorem in complex dimension zero. -/
theorem primeZeroSetProperty_zero : PrimeZeroSetProperty 0 := by
  intro P hP
  rw [holomorphicGerm_zero_prime_eq_bot P hP,
    idealZeroSetGerm_bot, vanishingIdeal_top]

end

end LocalComplexGeometry
