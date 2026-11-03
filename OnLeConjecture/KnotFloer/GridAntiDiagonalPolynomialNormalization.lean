/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationNativeOldPolynomial
public import OnLeConjecture.KnotFloer.GridAntiDiagonalNativeClass

/-!
# Polynomial homology normalization for the auxiliary anti-diagonal grids

The explicit stabilization sequence and the computed two-by-two base determine
the polynomial homology image in degree zero. The same sequence proves that
all positive-degree polynomial images vanish.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti CategoryTheory HomologicalComplex

variable (R : Type*) [CommRing R] [CharP R 2]

/-- Positive polynomial homology has zero image in the computed two-by-two model. -/
theorem twoByTwo_polynomialHomologyImage_eq_bot (a : Fin 2) (m : ℤ) (hm : 0 < m) :
    polynomialHomologyImage R GridDiagram.twoByTwo a m = ⊥ := by
  apply le_antisymm _ bot_le
  rintro ξ ⟨η, rfl⟩
  rw [twoByTwo_oneVariable_homology_eq_zero R a m hm η, map_zero]
  exact Submodule.zero_mem _

/-- Every positive-degree polynomial homology image in the auxiliary sequence vanishes. -/
theorem antiDiagonalAuxiliary_polynomialHomologyImage_eq_bot
    (n : ℕ) (a : Fin (n + 2)) (m : ℤ) (hm : 0 < m) :
    polynomialHomologyImage R (antiDiagonalAuxiliaryGrid n) a m = ⊥ := by
  induction n generalizing m with
  | zero =>
    rw [← antiDiagonalAuxiliaryBaseIso_polynomialImage R 0 a m,
      twoByTwo_polynomialHomologyImage_eq_bot R 0 m hm, Submodule.map_bot]
  | succ n ih =>
    apply le_antisymm _ bot_le
    intro ξ hξ
    let z : polynomialHomologyImage R (antiDiagonalAuxiliaryGrid (n + 1)) a m := ⟨ξ, hξ⟩
    let e := stabilizationNativeOldPolynomialHomologyImageEquiv R
      (antiDiagonalAuxiliaryGrid n) (Fin.last (n + 1)) 0 a m
    have hz : e z = 0 := by
      apply Prod.ext <;> apply Subtype.ext
      · exact (ih 0 m hm).le (e z).1.property
      · exact (ih 0 (m + 1) (by omega)).le (e z).2.property
    have hz0 : z = 0 := e.injective (hz.trans e.map_zero.symm)
    exact congrArg Subtype.val hz0

/-- The polynomial image in the base model is the coefficient ring. -/
def twoByTwoPolynomialImageZeroEquiv (a : Fin 2) :
    polynomialHomologyImage R GridDiagram.twoByTwo a 0 ≃ₗ[R] R where
  toFun ξ := twoByTwoLaurentMaslovZeroHomologyEquiv R ξ.val
  invFun r := ⟨(twoByTwoLaurentMaslovZeroHomologyEquiv R).symm r, by
    rw [twoByTwo_polynomialHomologyImage_eq_top]
    trivial⟩
  left_inv ξ := Subtype.ext ((twoByTwoLaurentMaslovZeroHomologyEquiv R).symm_apply_apply ξ.val)
  right_inv r := (twoByTwoLaurentMaslovZeroHomologyEquiv R).apply_symm_apply r
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

/-- The degree-one image contributes a zero factor at every auxiliary stabilization. -/
def antiDiagonalAuxiliaryPolynomialImageDropPositive (n : ℕ) (a : Fin (n + 2)) :
    (polynomialHomologyImage R (antiDiagonalAuxiliaryGrid n) a 0 ×
        polynomialHomologyImage R (antiDiagonalAuxiliaryGrid n) a 1) ≃ₗ[R]
      polynomialHomologyImage R (antiDiagonalAuxiliaryGrid n) a 0 where
  toFun := Prod.fst
  invFun ξ := (ξ, 0)
  left_inv ξ := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact ((antiDiagonalAuxiliary_polynomialHomologyImage_eq_bot R n a 1 (by decide)).le
        ξ.2.property).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual degree-zero polynomial homology image of every auxiliary grid is R. -/
def antiDiagonalAuxiliaryPolynomialImageZeroEquiv :
    (n : ℕ) → (a : Fin (n + 2)) →
      polynomialHomologyImage R (antiDiagonalAuxiliaryGrid n) a 0 ≃ₗ[R] R
  | 0, a => (antiDiagonalAuxiliaryBasePolynomialImageEquiv R 0 a 0).symm.trans
      (twoByTwoPolynomialImageZeroEquiv R 0)
  | n + 1, a =>
    (stabilizationNativeOldPolynomialHomologyImageEquiv R
      (antiDiagonalAuxiliaryGrid n) (Fin.last (n + 1)) 0 a 0).trans
      ((antiDiagonalAuxiliaryPolynomialImageDropPositive R n 0).trans
        (antiDiagonalAuxiliaryPolynomialImageZeroEquiv n 0))

/-- The actual stabilization projection followed by the old first summand. -/
def antiDiagonalAuxiliaryNativeOldProjection (n : ℕ) :
    laurentMaslovComplex (antiDiagonalAuxiliaryGrid (n + 1)) R ⟶
      laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R :=
  (stabilizationNativeOldHomotopyEquiv R (antiDiagonalAuxiliaryGrid n)
    (Fin.last (n + 1))).hom ≫
      shiftedDoubleFst (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R)

/-- The native projection retains the tracked X-state chain in the old first summand. -/
theorem antiDiagonalAuxiliaryNativeOldProjection_chain (n : ℕ) :
    (antiDiagonalAuxiliaryNativeOldProjection R n).f 0
      (antiDiagonalAuxiliaryNativeChain (n + 1) R) = antiDiagonalAuxiliaryNativeChain n R := by
  apply (laurentMaslovChainEquiv (antiDiagonalAuxiliaryGrid n) R 0).injective
  apply Subtype.ext
  exact (congrArg Prod.fst (antiDiagonalAuxiliaryNativeProjection_apply n R)).trans
    (antiDiagonalAuxiliaryNativeChain_apply n R).symm

/-- The same projection maps the selected cycle to the selected old cycle. -/
theorem antiDiagonalAuxiliaryNativeOldProjection_cycle (n : ℕ) :
    cyclesMap (antiDiagonalAuxiliaryNativeOldProjection R n) 0
      (antiDiagonalAuxiliaryNativeCycle (n + 1) R) = antiDiagonalAuxiliaryNativeCycle n R := by
  apply (ModuleCat.mono_iff_injective
    ((laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).iCycles 0)).mp inferInstance
  have h := congrArg (fun f :
      (laurentMaslovComplex (antiDiagonalAuxiliaryGrid (n + 1)) R).cycles 0 ⟶
        (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).X 0 =>
      f (antiDiagonalAuxiliaryNativeCycle (n + 1) R))
    (cyclesMap_i (antiDiagonalAuxiliaryNativeOldProjection R n) 0)
  change (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).iCycles 0
      (cyclesMap (antiDiagonalAuxiliaryNativeOldProjection R n) 0
        (antiDiagonalAuxiliaryNativeCycle (n + 1) R)) =
    (antiDiagonalAuxiliaryNativeOldProjection R n).f 0
      ((laurentMaslovComplex (antiDiagonalAuxiliaryGrid (n + 1)) R).iCycles 0
        (antiDiagonalAuxiliaryNativeCycle (n + 1) R)) at h
  rw [h]
  have hinc (k : ℕ) :
      (laurentMaslovComplex (antiDiagonalAuxiliaryGrid k) R).iCycles 0
        (antiDiagonalAuxiliaryNativeCycle k R) = antiDiagonalAuxiliaryNativeChain k R := by
    apply (laurentMaslovChainEquiv (antiDiagonalAuxiliaryGrid k) R 0).injective
    apply Subtype.ext
    exact (antiDiagonalAuxiliaryNativeCycle_apply k R).trans
      (antiDiagonalAuxiliaryNativeChain_apply k R).symm
  rw [hinc, hinc]
  exact antiDiagonalAuxiliaryNativeOldProjection_chain R n

/-- The actual native homology map takes the tracked new class to the tracked old class. -/
theorem antiDiagonalAuxiliaryNativeOldProjection_class (n : ℕ) :
    homologyMap (antiDiagonalAuxiliaryNativeOldProjection R n) 0
      (antiDiagonalAuxiliaryNativeClass (n + 1) R) = antiDiagonalAuxiliaryNativeClass n R := by
  have h := congrArg (fun f :
      (laurentMaslovComplex (antiDiagonalAuxiliaryGrid (n + 1)) R).cycles 0 ⟶
        (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).homology 0 =>
      f (antiDiagonalAuxiliaryNativeCycle (n + 1) R))
    (homologyπ_naturality (antiDiagonalAuxiliaryNativeOldProjection R n) 0)
  change homologyMap (antiDiagonalAuxiliaryNativeOldProjection R n) 0
      ((laurentMaslovComplex (antiDiagonalAuxiliaryGrid (n + 1)) R).homologyπ 0
        (antiDiagonalAuxiliaryNativeCycle (n + 1) R)) =
    (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).homologyπ 0
      (cyclesMap (antiDiagonalAuxiliaryNativeOldProjection R n) 0
        (antiDiagonalAuxiliaryNativeCycle (n + 1) R)) at h
  exact h.trans (congrArg ((laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) R).homologyπ 0)
    (antiDiagonalAuxiliaryNativeOldProjection_cycle R n))

/-- The explicit auxiliary X-state class survives in Laurent homology in every size. -/
theorem antiDiagonalAuxiliaryNativeClass_ne_zero (n : ℕ) [Nontrivial R] :
    antiDiagonalAuxiliaryNativeClass n R ≠ 0 := by
  induction n with
  | zero => exact antiDiagonalAuxiliaryNativeClass_zero_ne_zero R
  | succ n ih =>
    intro h
    apply ih
    rw [← antiDiagonalAuxiliaryNativeOldProjection_class R n, h, map_zero]

/-- Over the two-element field, the tracked class is the unique nonzero polynomial-image class. -/
theorem antiDiagonalAuxiliaryNativeClass_unique (n : ℕ) (a : Fin (n + 2))
    (ξ : (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) (ZMod 2)).homology 0)
    (hmem : ξ ∈ polynomialHomologyImage (ZMod 2) (antiDiagonalAuxiliaryGrid n) a 0)
    (hne : ξ ≠ 0) : ξ = antiDiagonalAuxiliaryNativeClass n (ZMod 2) := by
  let e := antiDiagonalAuxiliaryPolynomialImageZeroEquiv (ZMod 2) n a
  let z : polynomialHomologyImage (ZMod 2) (antiDiagonalAuxiliaryGrid n) a 0 := ⟨ξ, hmem⟩
  let c : polynomialHomologyImage (ZMod 2) (antiDiagonalAuxiliaryGrid n) a 0 :=
    ⟨antiDiagonalAuxiliaryNativeClass n (ZMod 2),
      antiDiagonalAuxiliaryNativeClass_mem_polynomialImage n (ZMod 2) a⟩
  have hz : e z ≠ 0 := by
    intro h
    exact hne (congrArg Subtype.val (e.injective (h.trans e.map_zero.symm)))
  have hc : e c ≠ 0 := by
    intro h
    exact antiDiagonalAuxiliaryNativeClass_ne_zero (ZMod 2) n
      (congrArg Subtype.val (e.injective (h.trans e.map_zero.symm)))
  have hcases (r : ZMod 2) : r = 0 ∨ r = 1 := by
    fin_cases r
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact congrArg Subtype.val (e.injective
    (((hcases (e z)).resolve_left hz).trans ((hcases (e c)).resolve_left hc).symm))

/-- Existence and uniqueness refer to the actual polynomial image inside native Laurent homology. -/
theorem existsUnique_antiDiagonalAuxiliary_nonzero_polynomialHomologyImage
    (n : ℕ) (a : Fin (n + 2)) :
    ∃! ξ : (laurentMaslovComplex (antiDiagonalAuxiliaryGrid n) (ZMod 2)).homology 0,
      ξ ≠ 0 ∧ ξ ∈ polynomialHomologyImage (ZMod 2) (antiDiagonalAuxiliaryGrid n) a 0 := by
  refine ⟨antiDiagonalAuxiliaryNativeClass n (ZMod 2),
    ⟨antiDiagonalAuxiliaryNativeClass_ne_zero (ZMod 2) n,
      antiDiagonalAuxiliaryNativeClass_mem_polynomialImage n (ZMod 2) a⟩, ?_⟩
  intro ξ hξ
  exact antiDiagonalAuxiliaryNativeClass_unique n a ξ hξ.2 hξ.1

end OnLeConjecture.KnotFloer.GridFull
