/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti); see THIRD_PARTY_NOTICES.md.
Authors: The Tau Ceti contributors, Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentSpectral
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.SmallGrid.Gradings
public import OnLeConjecture.External.TauCeti.KnotTheory.Grid.Rectangle.Count

/-!
# The full differential of the standard two-by-two grid

The two rectangles from the identity state to the transposition state each cover one O
marking. The reverse rectangles each cover one X marking and no O marking. Thus the two
polynomial matrix entries are `V₀ + V₁` and `1 + 1`. After specializing both O variables to
the same Laurent variable in characteristic two, the full differential vanishes.

The concrete rectangle construction adapts
`TauCeti/KnotTheory/Grid/SmallGrid/SimplyBlocked/Differential.lean` at commit
`eb4dd2412a1cd62f73128361bfd3cb422df32e37`, under Apache 2.0. The full rectangle counts here
include the X-containing reverse rectangles excluded from that upstream differential.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory HomologicalComplex GridRectangleBetween

/-- The lower-left O square as an oriented rectangle between the two states. -/
noncomputable def twoByTwoORectangle :
    GridRectangleBetween GridState.twoByTwoId GridState.twoByTwoSwap where
  left := 0
  right := 1
  left_ne_right := by decide
  map_left := by simp
  map_right := by simp
  map_of_ne c hc₀ hc₁ := by fin_cases c <;> simp_all

/-- The upper-left X square as a rectangle in the reverse direction. -/
noncomputable def twoByTwoXRectangle :
    GridRectangleBetween GridState.twoByTwoSwap GridState.twoByTwoId where
  left := 0
  right := 1
  left_ne_right := by decide
  map_left := by simp
  map_right := by simp
  map_of_ne c hc₀ hc₁ := by fin_cases c <;> simp_all

private theorem twoByTwoORectangle_OColumns :
    GridDiagram.twoByTwo.OColumns twoByTwoORectangle.toGridRectangle = {0} := by
  ext c
  fin_cases c <;>
    simp [GridDiagram.mem_OColumns, bottom_def, top_def,
      twoByTwoORectangle, Grid.mem_cIco]

private theorem twoByTwoORectangle_swap_OColumns :
    GridDiagram.twoByTwo.OColumns twoByTwoORectangle.swapSides.toGridRectangle = {1} := by
  ext c
  fin_cases c <;>
    simp [GridDiagram.mem_OColumns, bottom_def, top_def,
      twoByTwoORectangle, Grid.mem_cIco]

private theorem twoByTwoXRectangle_OColumns :
    GridDiagram.twoByTwo.OColumns twoByTwoXRectangle.toGridRectangle = ∅ := by
  ext c
  fin_cases c <;>
    simp [GridDiagram.mem_OColumns, bottom_def, top_def,
      twoByTwoXRectangle, Grid.mem_cIco]

private theorem twoByTwoXRectangle_swap_OColumns :
    GridDiagram.twoByTwo.OColumns twoByTwoXRectangle.swapSides.toGridRectangle = ∅ := by
  ext c
  fin_cases c <;>
    simp [GridDiagram.mem_OColumns, bottom_def, top_def,
      twoByTwoXRectangle, Grid.mem_cIco]

variable (R : Type*) [CommSemiring R]

/-- The two forward rectangles carry the two different O variables. -/
theorem coefficient_twoByTwo_id_swap :
    coefficient GridDiagram.twoByTwo R GridState.twoByTwoId GridState.twoByTwoSwap =
      MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1 := by
  classical
  rw [coefficient, emptyRectangles_eq_univ_of_le_two (by decide),
    twoByTwoORectangle.univ_eq_pair]
  simp only [Finset.sum_pair (swapSides_ne_self _).symm, OMonomial_eq_monomial_oExponent, oExponent,
    twoByTwoORectangle_OColumns, twoByTwoORectangle_swap_OColumns, Finset.sum_singleton]
  rfl

/-- The two reverse rectangles contain X markings and have O weight one. -/
theorem coefficient_twoByTwo_swap_id :
    coefficient GridDiagram.twoByTwo R GridState.twoByTwoSwap GridState.twoByTwoId = 1 + 1 := by
  classical
  rw [coefficient, emptyRectangles_eq_univ_of_le_two (by decide),
    twoByTwoXRectangle.univ_eq_pair]
  simp only [Finset.sum_pair (swapSides_ne_self _).symm, OMonomial_eq_monomial_oExponent, oExponent,
    twoByTwoXRectangle_OColumns, twoByTwoXRectangle_swap_OColumns, Finset.sum_empty]
  simp

/-- A state has no rectangle to itself, hence the corresponding diagonal coefficient is zero. -/
theorem coefficient_self {n : ℕ} (G : GridDiagram n) (x : GridState n) :
    coefficient G R x x = 0 := by
  simp [coefficient, emptyRectangles_self]

variable [CharP R 2]

/-- Every polynomial chain has differential supported on the X-state with coefficient
its O-state coefficient times `V₀ + V₁`. -/
theorem differential_twoByTwo_apply (c : GridChainMinus R 2) :
    differential GridDiagram.twoByTwo R c = Finsupp.single GridState.twoByTwoSwap
      (c GridState.twoByTwoId * (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1)) := by
  classical
  have hu : (Finset.univ : Finset (GridState 2)) =
      {GridState.twoByTwoId, GridState.twoByTwoSwap} := by
    ext x
    simpa using GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x
  ext y
  rw [differential_apply_apply, Finsupp.sum_fintype _ _ fun _ => zero_mul _, hu,
    Finset.sum_pair GridState.twoByTwoId_ne_twoByTwoSwap]
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap y with rfl | rfl
  · simp only [coefficient_self, coefficient_twoByTwo_swap_id, CharTwo.add_self_eq_zero,
      mul_zero, Finsupp.single_eq_of_ne GridState.twoByTwoId_ne_twoByTwoSwap]
  · simp [coefficient_twoByTwo_id_swap, coefficient_self]

/-- Both off-diagonal Laurent entries cancel after identifying the O variables. -/
theorem laurentCoefficient_twoByTwo_eq_zero (x y : GridState 2) :
    laurentCoefficient GridDiagram.twoByTwo R x y = 0 := by
  rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap x with rfl | rfl <;>
    rcases GridState.eq_twoByTwoId_or_eq_twoByTwoSwap y with rfl | rfl
  · simp [laurentCoefficient, coefficient_self]
  · rw [laurentCoefficient, coefficient_twoByTwo_id_swap, map_add,
      laurentSpecialization_X, laurentSpecialization_X]
    ext k
    exact CharTwo.add_self_eq_zero _
  · rw [laurentCoefficient, coefficient_twoByTwo_swap_id, map_add, map_one]
    ext k
    exact CharTwo.add_self_eq_zero _
  · simp [laurentCoefficient, coefficient_self]

/-- The full all-O-collapsed Laurent differential of the two-by-two grid is zero. -/
theorem laurentDifferential_twoByTwo_eq_zero :
    laurentDifferential GridDiagram.twoByTwo R = 0 := by
  ext c y
  simp [laurentCoefficient_twoByTwo_eq_zero]

end OnLeConjecture.KnotFloer.GridFull
