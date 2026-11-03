/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LinearCoordinates
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Permuting target coordinates

A linear target coordinate change can move any selected component of a map
germ to the first coordinate.
-/

public section

namespace OnLeConjecture.Analytic

open Filter
open scoped Topology

/-- A component of a composite pointed map is the pullback of the
corresponding outer component. -/
theorem PointedMapGerm.component_comp_general {l n m : ℕ}
    (g : PointedMapGerm n m) (f : PointedMapGerm l n)
    (j : Fin m) :
    (g.comp f).1.component j =
      f.pullbackRingHom (g.1.component j) := by
  calc
    (g.comp f).1.component j =
        (g.comp f).pullbackRingHom (Germ.coordinate j) :=
      ((g.comp f).pullback_coordinate j).symm
    _ = (f.pullbackRingHom.comp g.pullbackRingHom)
        (Germ.coordinate j) := by
      rw [PointedMapGerm.pullbackRingHom_comp]
    _ = f.pullbackRingHom (g.1.component j) := by
      change f.pullbackRingHom
        (g.pullbackRingHom (Germ.coordinate j)) =
          f.pullbackRingHom (g.1.component j)
      rw [g.pullback_coordinate]

/-- The continuous linear equivalence that swaps coordinates zero and `i`. -/
@[expose]
noncomputable def coordinateSwapEquiv {n : ℕ} (i : Fin (n + 1)) :
    Source (n + 1) ≃L[ℂ] Source (n + 1) :=
  ContinuousLinearEquiv.piCongrLeft ℂ
    (fun _ : Fin (n + 1) ↦ ℂ) (Equiv.swap 0 i)

@[simp]
theorem coordinateSwapEquiv_apply_zero {n : ℕ}
    (i : Fin (n + 1)) (z : Source (n + 1)) :
    coordinateSwapEquiv i z 0 = z i := by
  have h := Equiv.piCongrLeft_apply_apply
    (fun _ : Fin (n + 1) ↦ ℂ) (Equiv.swap 0 i) z i
  change (Equiv.piCongrLeft
    (fun _ : Fin (n + 1) ↦ ℂ) (Equiv.swap 0 i)) z 0 = z i
  simpa using h

/-- The pointed analytic germ of the coordinate swap. -/
@[expose]
noncomputable def coordinateSwapPointedEquiv {n : ℕ}
    (i : Fin (n + 1)) : PointedEquivGerm (n + 1) :=
  Germ.pointedEquivGermOfContinuousLinearEquiv (coordinateSwapEquiv i)

/-- The first component of the coordinate swap is coordinate `i`. -/
theorem coordinateSwapPointedEquiv_component_zero {n : ℕ}
    (i : Fin (n + 1)) :
    (coordinateSwapPointedEquiv i).forward.1.component 0 =
      Germ.coordinate i := by
  simp only [coordinateSwapPointedEquiv,
    Germ.pointedEquivGermOfContinuousLinearEquiv]
  apply Subtype.ext
  change ((MapGerm.ofFunction (coordinateSwapEquiv i)
    ((coordinateSwapEquiv i).analyticAt 0)).component 0).1 =
      (Germ.coordinate i).1
  rw [MapGerm.component_ofFunction, Germ.coe_coordinate]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦
    coordinateSwapEquiv_apply_zero i z

/-- Swapping target coordinates moves component `i` of a pointed map germ
to component zero. -/
theorem coordinateSwap_comp_component_zero {l n : ℕ}
    (i : Fin (n + 1)) (g : PointedMapGerm l (n + 1)) :
    ((coordinateSwapPointedEquiv i).forward.comp g).1.component 0 =
      g.1.component i := by
  rw [PointedMapGerm.component_comp_general,
    coordinateSwapPointedEquiv_component_zero,
    g.pullback_coordinate]

/-- If one component of a plane map germ is nonzero, source and target linear
changes make the first component regular in the first source coordinate. -/
theorem PointedMapGerm.exists_rightLeft_firstComponent_regular
    {n : ℕ} (g : PointedMapGerm 2 (n + 1)) (i : Fin (n + 1))
    (hi : g.1.component i ≠ 0) :
    ∃ source : PointedEquivGerm 2,
      ∃ target : PointedEquivGerm (n + 1), ∃ d : ℕ,
        Germ.IsRegularInFirstCoordinateOfOrder
          ((target.forward.comp
            (g.comp source.forward)).1.component 0) d := by
  obtain ⟨source, d, hregular⟩ :=
    Germ.exists_linear_equiv_regularInFirstCoordinate hi
  let target : PointedEquivGerm (n + 1) :=
    coordinateSwapPointedEquiv i
  refine ⟨source, target, d, ?_⟩
  have hinner :
      (g.comp source.forward).1.component i =
        source.forward.pullbackRingHom (g.1.component i) :=
    g.component_comp_general source.forward i
  have houter :
      (target.forward.comp (g.comp source.forward)).1.component 0 =
        (g.comp source.forward).1.component i := by
    exact coordinateSwap_comp_component_zero i
      (g.comp source.forward)
  rw [houter, hinner]
  exact hregular

/-- A map germ with a nonzero component is right left equivalent to one whose
first component is regular in the first source coordinate. -/
theorem PointedMapGerm.exists_rightLeftEquivalent_firstComponent_regular
    {n : ℕ} (g : PointedMapGerm 2 (n + 1)) (i : Fin (n + 1))
    (hi : g.1.component i ≠ 0) :
    ∃ h : PointedMapGerm 2 (n + 1), ∃ d : ℕ,
      g.RightLeftEquivalent h ∧
        Germ.IsRegularInFirstCoordinateOfOrder
          (h.1.component 0) d := by
  obtain ⟨source, target, d, hregular⟩ :=
    g.exists_rightLeft_firstComponent_regular i hi
  let h : PointedMapGerm 2 (n + 1) :=
    target.forward.comp (g.comp source.forward)
  refine ⟨h, d, ?_, hregular⟩
  exact ⟨source, target, rfl⟩

end OnLeConjecture.Analytic
