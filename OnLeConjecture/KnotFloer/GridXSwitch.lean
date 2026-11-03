/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullMarkingIndependence
public import OnLeConjecture.KnotFloer.GridFullLaurentSpectral
public import OnLeConjecture.KnotFloer.BifilteredShift
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Commutation.Grading.Basic

/-!
# The filtered map for an adjacent X-marking switch

Switching the X markings in two cyclically adjacent columns while retaining
the O markings leaves the full differential and its Maslov grading unchanged.
The identity on Laurent chains shifts the Alexander filtration by at most
one half. This provides an elementary filtered map for a proposed sequence
of band moves. Its realization by a smooth band and preservation of the
normalized knot class require separate geometric and normalization results.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ} {G H : GridDiagram n}

/-- The X-Maslov grading depends only on the X markings. -/
theorem maslovX_eq_of_X_eq (h : G.X = H.X) (x : GridState n) :
    G.maslovXℤ x = H.maslovXℤ x := by
  simp only [GridDiagram.maslovXℤ_def, GridDiagram.XSet_def, h]

/-- Exact X-Maslov change under a switch of adjacent X markings. -/
theorem maslovX_adjacent_X_switch {a : Fin n} (ha : a ≠ finRotate n a)
    (hX : H.X = G.X.swapColumns a (finRotate n a)) (x : GridState n) :
    H.maslovXℤ x = G.maslovXℤ x +
      if x (finRotate n a) ∈
        Grid.cIco (finRotate n (G.X a)) (finRotate n (G.X (finRotate n a)))
      then 1 else -1 := by
  have h := G.swapMarkings.maslovOℤ_swapColumns_finRotate ha x
  rw [← GridDiagram.swapColumns_swapMarkings] at h
  simp only [GridDiagram.maslovOℤ_swapMarkings, GridDiagram.swapMarkings_O] at h
  rw [maslovX_eq_of_X_eq (G := H) (H := G.swapColumns a (finRotate n a))
    (by simpa only [GridDiagram.swapColumns_X] using hX)]
  exact h

/-- An adjacent X switch changes every Alexander grading by at most one half. -/
theorem alexander_adjacent_X_switch_bounds {a : Fin n} (ha : a ≠ finRotate n a)
    (hO : G.O = H.O) (hX : H.X = G.X.swapColumns a (finRotate n a))
    (x : GridState n) :
    G.alexander x - 1 / 2 ≤ H.alexander x ∧
      H.alexander x ≤ G.alexander x + 1 / 2 := by
  have hM := maslovX_adjacent_X_switch ha hX x
  have hMO := maslovO_eq_of_O_eq hO x
  simp only [GridDiagram.alexander_def, GridDiagram.maslovO_eq_intCast,
    GridDiagram.maslovX_eq_intCast, hMO]
  split_ifs at hM <;>
    have hMQ := congrArg (fun z : ℤ => (z : ℚ)) hM <;>
    push_cast at hMQ <;> constructor <;> linarith

/-- The native marking isomorphism is the identity on underlying Laurent chains. -/
theorem laurentMaslovChainEquiv_markingIso (R : Type*) [CommRing R] [CharP R 2]
    (hO : G.O = H.O) (m : ℤ) (c : (laurentMaslovComplex G R).X m) :
    (laurentMaslovChainEquiv H R m ((laurentMaslovMarkingIso R hO).hom.f m c) :
      LaurentChain R n) = (laurentMaslovChainEquiv G R m c : LaurentChain R n) := by
  rfl

/-- The actual native chain map for an adjacent X switch has shifts `(0,1/2)`. -/
theorem laurentMaslovMarkingIso_adjacent_X_switch_shifts
    (R : Type*) [CommRing R] [CharP R 2] {a : Fin n}
    (ha : a ≠ finRotate n a) (hO : G.O = H.O)
    (hX : H.X = G.X.swapColumns a (finRotate n a)) :
    (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R)
      (laurentMaslovMarkingIso R hO).hom 0 (1 / 2) := by
  intro p q m c hc x k hk
  change k ∈ ((laurentMaslovChainEquiv G R m c : LaurentChain R n) x).coeff.support at hk
  obtain ⟨hp, hq⟩ := hc x k hk
  have hA : (H.alexander x : ℝ) ≤ (G.alexander x : ℝ) + 1 / 2 := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (alexander_adjacent_X_switch_bounds ha hO hX x).2
  exact ⟨by simpa using hp, by linarith⟩

end OnLeConjecture.KnotFloer.GridFull
