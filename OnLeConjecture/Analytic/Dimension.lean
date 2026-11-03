/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.Cotangent
public import OnLeConjecture.Analytic.Hyperplane
public import OnLeConjecture.Analytic.OneVariableOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Dimension of the analytic germ ring

The coordinate classes give the exact embedding dimension of the analytic
local ring. Coordinate hyperplane restriction gives the lower bound for its
Krull dimension. Consequently, Noetherianity alone implies that the ring has
Krull dimension `n` and is regular.

The rings in zero and one variables are proved Noetherian without an extra
hypothesis.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

namespace Germ

/-- Evaluation at the origin is injective for germs in zero variables. -/
theorem valueRingHom_injective_zero :
    Function.Injective (Germ.valueRingHom 0) := by
  intro f g hfg
  rcases f with ⟨f, hf⟩
  rcases g with ⟨g, hg⟩
  induction f using Filter.Germ.inductionOn with
  | _ f =>
    induction g using Filter.Germ.inductionOn with
    | _ g =>
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      have hzero : f 0 = g 0 := by
        change Filter.Germ.value (f : FunctionGerm 0) =
          Filter.Germ.value (g : FunctionGerm 0) at hfg
        simpa only [Filter.Germ.value_ofFun] using hfg
      filter_upwards [] with z
      simpa only [Subsingleton.elim z 0] using hzero

/-- Evaluation identifies germs in zero variables with the complex numbers. -/
noncomputable def zeroVariablesRingEquiv : Germ 0 ≃+* ℂ :=
  RingEquiv.ofBijective (Germ.valueRingHom 0)
    ⟨Germ.valueRingHom_injective_zero,
      Germ.valueRingHom_surjective 0⟩

/-- Each coordinate germ is nonzero. -/
theorem coordinate_ne_zero {n : ℕ} (i : Fin n) :
    Germ.coordinate i ≠ 0 := by
  intro h
  have hd := congrArg Germ.differential h
  have happ := congrArg
    (fun L : Source n →L[ℂ] ℂ ↦ L (Pi.single i 1)) hd
  simp at happ

/-- The maximal ideal has embedding dimension `n`. -/
theorem spanFinrank_maximalIdeal (n : ℕ) :
    (IsLocalRing.maximalIdeal (Germ n)).spanFinrank = n := by
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg]
  · exact Germ.finrank_residueCotangentSpace n
  · rw [← Germ.maximalIdeal_eq_isLocalRing]
    rw [← Germ.span_range_coordinate_eq_maximalIdeal]
    exact Submodule.fg_span (Set.finite_range Germ.coordinate)

/-- Restriction to a coordinate hyperplane raises the Krull dimension by at
least one. -/
theorem ringKrullDim_succ_le (n : ℕ) :
    ringKrullDim (Germ n) + 1 ≤ ringKrullDim (Germ (n + 1)) := by
  apply ringKrullDim_succ_le_of_surjective
    (Germ.hyperplaneRestriction n)
    (Germ.hyperplaneRestriction_surjective n)
    (mem_nonZeroDivisors_of_ne_zero
      (Germ.coordinate_ne_zero (0 : Fin (n + 1))))
  exact Germ.hyperplaneRestriction_coordinate_zero n

/-- The number of variables is a lower bound for the Krull dimension. -/
theorem natCast_le_ringKrullDim (n : ℕ) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (Germ n) := by
  induction n with
  | zero =>
      exact ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
      calc
        ((n + 1 : ℕ) : WithBot ℕ∞) =
            (n : WithBot ℕ∞) + 1 := by norm_num
        _ ≤ ringKrullDim (Germ n) + 1 := by
          simpa only [add_comm] using add_le_add_right ih 1
        _ ≤ ringKrullDim (Germ (n + 1)) := Germ.ringKrullDim_succ_le n

/-- A Noetherian analytic germ ring has Krull dimension equal to its number
of variables. -/
theorem ringKrullDim_eq_natCast (n : ℕ) [IsNoetherianRing (Germ n)] :
    ringKrullDim (Germ n) = (n : WithBot ℕ∞) := by
  apply le_antisymm
  · calc
      ringKrullDim (Germ n) ≤
          (IsLocalRing.maximalIdeal (Germ n)).spanFinrank :=
        ringKrullDim_le_spanFinrank_maximalIdeal (Germ n)
      _ = n := by
        exact_mod_cast Germ.spanFinrank_maximalIdeal n
  · exact Germ.natCast_le_ringKrullDim n

/-- A Noetherian analytic germ ring is regular. -/
theorem isRegularLocalRing_of_isNoetherianRing (n : ℕ)
    [IsNoetherianRing (Germ n)] : IsRegularLocalRing (Germ n) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [Germ.spanFinrank_maximalIdeal, Germ.ringKrullDim_eq_natCast]

/-- The analytic germ ring in zero variables is Noetherian. -/
noncomputable instance instIsNoetherianRingZero :
    IsNoetherianRing (Germ 0) :=
  isNoetherianRing_of_ringEquiv ℂ Germ.zeroVariablesRingEquiv.symm

/-- The analytic germ ring in zero variables is regular. -/
noncomputable instance instIsRegularLocalRingZero :
    IsRegularLocalRing (Germ 0) :=
  Germ.isRegularLocalRing_of_isNoetherianRing 0

/-- The analytic germ ring in one variable is Noetherian. -/
noncomputable instance instIsNoetherianRingOne :
    IsNoetherianRing (Germ 1) := inferInstance

/-- The analytic germ ring in one variable is regular. -/
noncomputable instance instIsRegularLocalRingOne :
    IsRegularLocalRing (Germ 1) :=
  Germ.isRegularLocalRing_of_isNoetherianRing 1

end Germ

end OnLeConjecture.Analytic
