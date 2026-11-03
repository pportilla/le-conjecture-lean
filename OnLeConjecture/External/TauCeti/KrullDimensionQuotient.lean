/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Height and quotient dimension

This is a minimal excerpt from `TauCeti/RingTheory/KrullDimension/Quotient.lean`
at commit `eb4dd2412a1cd62f73128361bfd3cb422df32e37`, retrieved 2026-10-29.
The source Git blob is `4f067b44ab87aef2f66f3193d6c5831468ee3dca`:
https://github.com/TauCetiProject/TauCeti/blob/eb4dd2412a1cd62f73128361bfd3cb422df32e37/TauCeti/RingTheory/KrullDimension/Quotient.lean

Only the two algebraic dimension lemmas required here are included. The
original declarations and proofs are retained, with imports reduced to
their Mathlib dependencies. The Apache 2.0 license is in this directory.
-/

public section

namespace PrimeSpectrum

variable {R : Type*} [CommRing R]

/-- The coheight of a point `p` of `Spec R` is the Krull dimension of `R ⧸ p`. -/
theorem coheight_eq_ringKrullDim_quotient (p : PrimeSpectrum R) :
    (Order.coheight p : WithBot ℕ∞) = ringKrullDim (R ⧸ p.asIdeal) := by
  have : Set.Ici p = zeroLocus (p.asIdeal : Set R) := by
    ext x
    rw [Set.mem_Ici, mem_zeroLocus, SetLike.coe_subset_coe, asIdeal_le_asIdeal]
  rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient, this]

end PrimeSpectrum

namespace Ideal

variable {R : Type*} [CommRing R]

/-- For a prime `p` of a commutative ring `R`, `ht p + dim (R ⧸ p) ≤ dim R`. -/
theorem height_add_ringKrullDim_quotient_le (p : Ideal R) [p.IsPrime] :
    p.height + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, ‹_›⟩
  have : Nonempty (PrimeSpectrum R) := ⟨P⟩
  rw [P.height_eq_orderHeight, ← P.coheight_eq_ringKrullDim_quotient, ringKrullDim,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  exact_mod_cast le_iSup (fun a : PrimeSpectrum R ↦ Order.height a + Order.coheight a) P

end Ideal
