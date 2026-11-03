/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentMapBounds
public import OnLeConjecture.KnotFloer.GridXSwitch

/-!
# The diagonal maps of an adjacent O switch

Let `G` and `H` be grid diagrams of size `n` with the same X markings, where the O markings of
`H` are those of `G` with the columns `a` and `a + 1` (cyclically) exchanged. For a state `x`
let `e(x) ∈ {0, 1}` be the indicator that the row `x (a + 1)` lies in the cyclic interval from
`O(a) + 1` to `O(a + 1)` (both rows read in `G`). This is the O switch of Section 4 of the
written proof of Statement E (`statement_E_complete_proof.tex`, Lemma `nativeOSaddleIncidence`),
where for `r = O(a) < s = O(a + 1)` the indicator is `𝟙{r < x(a + 1) ≤ s}`.

The main results are the following.

* `maslovOℤ_oSwitch`: `M_O^H(x) = M_O^G(x) + 2 e(x) - 1`.
* `oSwitch_card_OColumns`: for every empty rectangle `q` from `x` to `y`, the O counts satisfy
  `n_O^H(q) + e(x) = n_O^G(q) + e(y)`.
* `laurentDifferential_comp_oSwitchMap`: the Laurent-linear map `F(x) = T^{e(x)} x` is a chain
  map from the native Laurent complex of `G` to that of `H`.
* `oSwitchMap_mem_maslovPiece`: `F` lowers the Maslov degree by one.
* `oSwitchMap_mem_bifiltrationLevel`: `F` has filtration shifts `(0, -1/2)`.
* `oSwitchMap_comp_oSwitchMap`: the reverse switch `F'`, which is the O switch from `H` to `G`,
  satisfies `F' F = T` and `F F' = T`, with `F'(x) = T^{1 - e(x)} x`.

The maps here are Laurent-linear maps of the underlying Laurent chain modules. Their graded
restrictions are `oSwitchGraded`. The derivative maps and the canonical-class pairing of the
written proof are not treated in this file.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ}

/-! ### The switch indicator and the Maslov change -/

/-- The O-switch indicator of a state for the columns `a` and `a + 1` of `G`: it is one exactly
when the row of the state in column `a + 1` lies in the cyclic interval from `G.O a + 1` to
`G.O (a + 1)`. -/
def oSwitchIndicator (G : GridDiagram n) (a : Fin n) (x : GridState n) : ℤ :=
  if x (finRotate n a) ∈ Grid.cIco (finRotate n (G.O a)) (finRotate n (G.O (finRotate n a)))
  then 1 else 0

theorem oSwitchIndicator_nonneg (G : GridDiagram n) (a : Fin n) (x : GridState n) :
    0 ≤ oSwitchIndicator G a x := by
  unfold oSwitchIndicator
  split_ifs <;> norm_num

theorem oSwitchIndicator_le_one (G : GridDiagram n) (a : Fin n) (x : GridState n) :
    oSwitchIndicator G a x ≤ 1 := by
  unfold oSwitchIndicator
  split_ifs <;> norm_num

variable {G H : GridDiagram n} {a : Fin n}

/-- Exact change of the O-Maslov grading under an adjacent O switch. -/
theorem maslovOℤ_oSwitch (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (x : GridState n) :
    H.maslovOℤ x = G.maslovOℤ x + 2 * oSwitchIndicator G a x - 1 := by
  have h := G.maslovOℤ_swapColumns_finRotate ha x
  rw [maslovO_eq_of_O_eq (G := H) (H := G.swapColumns a (finRotate n a))
    (by rw [GridDiagram.swapColumns_O, hO]), h]
  unfold oSwitchIndicator
  split_ifs <;> ring

/-- The O switch from `H` back to `G` has the complementary indicator. -/
theorem oSwitchIndicator_reverse (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (x : GridState n) :
    oSwitchIndicator H a x = 1 - oSwitchIndicator G a x := by
  have hGO : G.O a ≠ G.O (finRotate n a) := fun h => ha (G.O.toPerm.injective h)
  have hrot : finRotate n (G.O a) ≠ finRotate n (G.O (finRotate n a)) :=
    fun h => hGO ((finRotate n).injective h)
  have hHa : H.O a = G.O (finRotate n a) := by
    rw [hO, GridState.swapColumns_apply, Equiv.swap_apply_left]
  have hHb : H.O (finRotate n a) = G.O a := by
    rw [hO, GridState.swapColumns_apply, Equiv.swap_apply_right]
  unfold oSwitchIndicator
  rw [hHa, hHb]
  by_cases hx : x (finRotate n a) ∈
      Grid.cIco (finRotate n (G.O a)) (finRotate n (G.O (finRotate n a)))
  · have hx' : x (finRotate n a) ∉
        Grid.cIco (finRotate n (G.O (finRotate n a))) (finRotate n (G.O a)) := by
      intro h'
      exact (Grid.notMem_cIco_iff_mem_cIco_swap hrot).mpr h' hx
    rw [if_pos hx, if_neg hx']
    norm_num
  · have hx' : x (finRotate n a) ∈
        Grid.cIco (finRotate n (G.O (finRotate n a))) (finRotate n (G.O a)) :=
      (Grid.notMem_cIco_iff_mem_cIco_swap hrot).mp hx
    rw [if_neg hx, if_pos hx']
    norm_num

/-- Exchanging the O markings back recovers `G`. -/
theorem oSwitch_reverse_O (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    G.O = H.O.swapColumns a (finRotate n a) := by
  rw [hO]
  ext c
  simp only [GridState.swapColumns_apply, Equiv.swap_apply_self]

/-- The rectangle identity of the O switch: for every empty rectangle from `x` to `y`, the O
counts in `G` and `H` differ by the change of the indicator. -/
theorem oSwitch_card_OColumns (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) {x y : GridState n}
    (r : GridRectangleBetween x y) (hr : r.IsEmpty) :
    ((H.OColumns r.toGridRectangle).card : ℤ) + oSwitchIndicator G a x =
      ((G.OColumns r.toGridRectangle).card : ℤ) + oSwitchIndicator G a y := by
  have hG := laurentMaslovDegree_add_card_OColumns G r hr 0
  have hH := laurentMaslovDegree_add_card_OColumns H r hr 0
  simp only [laurentMaslovDegree, zero_add, mul_zero, sub_zero] at hG hH
  rw [maslovOℤ_oSwitch ha hO x, maslovOℤ_oSwitch ha hO y] at hH
  linarith

/-! ### Laurent-linear diagonal maps -/

variable (R : Type*) [CommRing R]

/-- The Laurent-linear map multiplying each state `x` by `T ^ (e x)`. -/
def laurentDiagonalMap (e : GridState n → ℤ) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  Finsupp.lsum (LaurentPolynomial R) fun x : GridState n =>
    (LinearMap.id : LaurentPolynomial R →ₗ[LaurentPolynomial R] LaurentPolynomial R).smulRight
      (Finsupp.single x (LaurentPolynomial.T (e x)))

theorem laurentDiagonalMap_single (e : GridState n → ℤ) (x : GridState n)
    (p : LaurentPolynomial R) :
    laurentDiagonalMap R e (single x p) = single x (p * LaurentPolynomial.T (e x)) := by
  rw [laurentDiagonalMap, Finsupp.lsum_single]
  simp [LinearMap.smulRight_apply, Finsupp.smul_single]

theorem laurentDiagonalMap_apply (e : GridState n → ℤ) (c : LaurentChain R n)
    (y : GridState n) :
    laurentDiagonalMap R e c y = c y * LaurentPolynomial.T (e y) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply, zero_mul]
  | add c d hc hd => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hc, hd, add_mul]
  | single x p =>
    rw [laurentDiagonalMap_single, Finsupp.single_apply, Finsupp.single_apply]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hxy, if_neg hxy, zero_mul]

/-- Diagonal maps compose by adding exponents. -/
theorem laurentDiagonalMap_comp (e e' : GridState n → ℤ) :
    laurentDiagonalMap R e' ∘ₗ laurentDiagonalMap R e =
      laurentDiagonalMap R (fun x => e x + e' x) := by
  refine LinearMap.ext fun c => Finsupp.ext fun y => ?_
  simp only [LinearMap.comp_apply, laurentDiagonalMap_apply, mul_assoc,
    ← LaurentPolynomial.T_add]

/-- A constant diagonal exponent is multiplication by a power of `T`. -/
theorem laurentDiagonalMap_const (k : ℤ) (c : LaurentChain R n) :
    laurentDiagonalMap R (fun _ => k) c = (LaurentPolynomial.T k : LaurentPolynomial R) • c := by
  refine Finsupp.ext fun y => ?_
  rw [laurentDiagonalMap_apply, Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-! ### The O-switch map -/

/-- The O-switch map `x ↦ T^{e(x)} x` for the columns `a` and `a + 1` of `G`. -/
def oSwitchMap (G : GridDiagram n) (a : Fin n) :
    LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n :=
  laurentDiagonalMap R (oSwitchIndicator G a)

theorem oSwitchMap_single (x : GridState n) :
    oSwitchMap R G a (single x 1) = single x (LaurentPolynomial.T (oSwitchIndicator G a x)) := by
  rw [oSwitchMap, laurentDiagonalMap_single, one_mul]

/-- Coefficient identity behind the chain property of the O-switch map. -/
theorem laurentCoefficient_oSwitch (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (x y : GridState n) :
    LaurentPolynomial.T (oSwitchIndicator G a x) * laurentCoefficient H R x y =
      laurentCoefficient G R x y * LaurentPolynomial.T (oSwitchIndicator G a y) := by
  rw [laurentCoefficient_eq, laurentCoefficient_eq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
  congr 1
  have h := oSwitch_card_OColumns ha hO r ((GridRectangleBetween.mem_emptyRectangles r).mp hr)
  linarith

/-- The O-switch map is a chain map between the native Laurent complexes. -/
theorem laurentDifferential_comp_oSwitchMap (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    laurentDifferential H R ∘ₗ oSwitchMap R G a = oSwitchMap R G a ∘ₗ laurentDifferential G R := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  refine Finsupp.ext fun y => ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have hs : (single x (LaurentPolynomial.T (oSwitchIndicator G a x)) : LaurentChain R n) =
      (LaurentPolynomial.T (oSwitchIndicator G a x) : LaurentPolynomial R) • single x 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [oSwitchMap, laurentDiagonalMap_apply, laurentDiagonalMap_single, one_mul, hs,
    map_smul, Finsupp.smul_apply, smul_eq_mul,
    laurentDifferential_single, laurentDifferential_single, laurentOnGenerator_apply,
    laurentOnGenerator_apply]
  exact laurentCoefficient_oSwitch R ha hO x y

/-- The O-switch map lowers the Maslov degree by one. -/
theorem oSwitchMap_mem_maslovPiece (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) {m : ℤ} {c : LaurentChain R n}
    (hc : c ∈ laurentMaslovPiece G R m) :
    oSwitchMap R G a c ∈ laurentMaslovPiece H R (m - 1) := by
  have h := laurentMap_mem_maslovPiece G H (oSwitchMap R G a) (-1) ?_ hc
  · simpa [sub_eq_add_neg] using h
  intro x y k hk
  rw [oSwitchMap_single] at hk
  by_cases hxy : x = y
  · subst hxy
    rw [Finsupp.single_eq_same] at hk
    have hk' : k = oSwitchIndicator G a x := by
      change k ∈ (Finsupp.single (oSwitchIndicator G a x) (1 : R)).support at hk
      exact Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    rw [hk', maslovOℤ_oSwitch ha hO x]
    ring
  · rw [Finsupp.single_apply, if_neg hxy] at hk
    simp at hk

/-- Alexander change of an adjacent O switch with fixed X markings. -/
theorem alexander_oSwitch (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) (x : GridState n) :
    H.alexander x = G.alexander x + oSwitchIndicator G a x - 1 / 2 := by
  have hM := maslovOℤ_oSwitch ha hO x
  have hMX : H.maslovXℤ x = G.maslovXℤ x := maslovX_eq_of_X_eq hX x
  simp only [GridDiagram.alexander_def, GridDiagram.maslovO_eq_intCast,
    GridDiagram.maslovX_eq_intCast, hMX]
  have hMQ := congrArg (fun z : ℤ => (z : ℚ)) hM
  push_cast at hMQ
  rw [hMQ]
  ring

/-- The O-switch map has filtration shifts `(0, -1/2)`. -/
theorem oSwitchMap_mem_bifiltrationLevel (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (hX : H.X = G.X) {u v : ℝ}
    {c : LaurentChain R n} (hc : c ∈ laurentBifiltrationLevel G R u v) :
    oSwitchMap R G a c ∈ laurentBifiltrationLevel H R u (v - 1 / 2) := by
  have h := laurentMap_mem_bifiltrationLevel G H (oSwitchMap R G a) (-1 / 2) ?_ hc
  · convert h using 2
    push_cast
    ring
  intro x y k hk
  rw [oSwitchMap_single] at hk
  by_cases hxy : x = y
  · subst hxy
    rw [Finsupp.single_eq_same] at hk
    have hk' : k = oSwitchIndicator G a x := by
      change k ∈ (Finsupp.single (oSwitchIndicator G a x) (1 : R)).support at hk
      exact Finset.mem_singleton.mp (Finsupp.support_single_subset hk)
    subst hk'
    refine ⟨?_, ?_⟩
    · have := oSwitchIndicator_nonneg G a x
      have : (0 : ℚ) ≤ (oSwitchIndicator G a x : ℚ) := by exact_mod_cast this
      linarith
    · rw [alexander_oSwitch ha hO hX x]
      linarith
  · rw [Finsupp.single_apply, if_neg hxy] at hk
    simp at hk

/-- The reverse O switch composed with the O switch is multiplication by `T`. -/
theorem oSwitchMap_comp_oSwitchMap (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    oSwitchMap R H a ∘ₗ oSwitchMap R G a =
      (LaurentPolynomial.T 1 : LaurentPolynomial R) •
        (LinearMap.id : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n) := by
  apply LinearMap.ext
  intro c
  rw [oSwitchMap, oSwitchMap, laurentDiagonalMap_comp]
  have he : (fun x => oSwitchIndicator G a x + oSwitchIndicator H a x) = fun _ => (1 : ℤ) := by
    funext x
    rw [oSwitchIndicator_reverse ha hO x]
    ring
  rw [he, laurentDiagonalMap_const]
  rfl

/-- The O switch composed with the reverse O switch is multiplication by `T`. -/
theorem oSwitchMap_comp_oSwitchMap_reverse (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) :
    oSwitchMap R G a ∘ₗ oSwitchMap R H a =
      (LaurentPolynomial.T 1 : LaurentPolynomial R) •
        (LinearMap.id : LaurentChain R n →ₗ[LaurentPolynomial R] LaurentChain R n) := by
  apply LinearMap.ext
  intro c
  rw [oSwitchMap, oSwitchMap, laurentDiagonalMap_comp]
  have he : (fun x => oSwitchIndicator H a x + oSwitchIndicator G a x) = fun _ => (1 : ℤ) := by
    funext x
    rw [oSwitchIndicator_reverse ha hO x]
    ring
  rw [he, laurentDiagonalMap_const]
  rfl

/-! ### Graded restriction -/

/-- The O-switch map restricted to a Maslov piece, with values one degree lower. -/
def oSwitchGraded (ha : a ≠ finRotate n a) (hO : H.O = G.O.swapColumns a (finRotate n a))
    (m : ℤ) : laurentMaslovPiece G R m →ₗ[R] laurentMaslovPiece H R (m - 1) :=
  ((oSwitchMap R G a).restrictScalars R).restrict fun _ hc => oSwitchMap_mem_maslovPiece R ha hO hc

@[simp]
theorem coe_oSwitchGraded (ha : a ≠ finRotate n a)
    (hO : H.O = G.O.swapColumns a (finRotate n a)) (m : ℤ) (c : laurentMaslovPiece G R m) :
    (oSwitchGraded R ha hO m c : LaurentChain R n) = oSwitchMap R G a c := rfl

end OnLeConjecture.KnotFloer.GridFull
