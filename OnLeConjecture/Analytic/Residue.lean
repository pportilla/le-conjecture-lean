/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Coordinates
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The residue field of the analytic germ ring

Evaluation at the origin identifies the residue field of the analytic local
ring with the complex numbers.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- The explicitly defined ideal of germs that vanish at the origin is the
maximal ideal supplied by the local ring instance. -/
theorem maximalIdeal_eq_isLocalRing (n : ℕ) :
    Germ.maximalIdeal n = IsLocalRing.maximalIdeal (Germ n) :=
  IsLocalRing.eq_maximalIdeal (Germ.maximalIdeal_isMaximal n)

/-- Evaluation at the origin identifies the residue field with `ℂ`. -/
noncomputable def residueFieldEquiv (n : ℕ) :
    IsLocalRing.ResidueField (Germ n) ≃+* ℂ :=
  (Ideal.quotEquivOfEq
      (IsLocalRing.ker_eq_maximalIdeal (Germ.valueRingHom n)
        (Germ.valueRingHom_surjective n)).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (Germ.valueRingHom_surjective n))

@[simp]
theorem residueFieldEquiv_residue (n : ℕ) (g : Germ n) :
    Germ.residueFieldEquiv n (IsLocalRing.residue (Germ n) g) =
      Germ.valueRingHom n g := by
  change
    Germ.residueFieldEquiv n
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Germ n)) g) =
      Germ.valueRingHom n g
  rw [Germ.residueFieldEquiv]
  change
    (RingHom.quotientKerEquivOfSurjective
      (Germ.valueRingHom_surjective n))
        ((Ideal.quotEquivOfEq
          (IsLocalRing.ker_eq_maximalIdeal (Germ.valueRingHom n)
            (Germ.valueRingHom_surjective n)).symm)
            (Ideal.Quotient.mk
              (IsLocalRing.maximalIdeal (Germ n)) g)) =
      Germ.valueRingHom n g
  rw [Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- The residue field equivalence respects the scalar embeddings of `ℂ`. -/
noncomputable def residueFieldAlgEquiv (n : ℕ) :
    IsLocalRing.ResidueField (Germ n) ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofRingEquiv (f := Germ.residueFieldEquiv n) (by
    intro c
    change Germ.residueFieldEquiv n
        (IsLocalRing.residue (Germ n) (Germ.constRingHom n c)) = c
    rw [Germ.residueFieldEquiv_residue, Germ.valueRingHom_const])

end Germ

end OnLeConjecture.Analytic
