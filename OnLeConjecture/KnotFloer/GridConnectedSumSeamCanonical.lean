/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTensorDifferential
public import OnLeConjecture.KnotFloer.GridCanonicalTensorClass
public import OnLeConjecture.KnotFloer.GridLaurentTensorNativeCertificate

/-!
# Canonical class transport under the explicit seam parity identity

The finite parity identity is an explicit hypothesis of the native
comparison. Under that identity, the constructed filtered inclusion
carries the nonzero polynomial pure tensor class to the unique nonzero
polynomial-image class of the seam. No parity theorem, connected-sum
realization, or Künneth theorem is claimed here.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti TensorProduct CategoryTheory HomologicalComplex
variable {n m : ℕ} {K : Type*} [Field K] [CharP K 2]
variable (G : GridDiagram (n + 1)) (H : GridDiagram (m + 1))
  (hG : G.X (Fin.last n) = Fin.last n) (hH : H.X 0 = 0) (hO : H.O (Fin.last m) = 0)

/-- The explicit tensor basis equivalence restricted to the proved equal degree submodules. -/
def seamTensorMaslovPieceEquiv (d : ℤ) :
    laurentTensorMaslovPiece (K := K) G H d ≃ₗ[K] seamRetainedMaslovPiece G H hG hH K d where
  toFun c := ⟨seamTensorCoordinatesEquiv K c.val,
    seamTensorCoordinatesEquiv_mem_maslov G H hG hH hO c.property⟩
  invFun c := ⟨(seamTensorCoordinatesEquiv K).symm c.val,
    seamTensorCoordinatesEquiv_symm_mem_maslov G H hG hH hO c.property⟩
  left_inv c := Subtype.ext ((seamTensorCoordinatesEquiv K).symm_apply_apply c.val)
  right_inv c := Subtype.ext ((seamTensorCoordinatesEquiv K).apply_symm_apply c.val)
  map_add' c e := Subtype.ext ((seamTensorCoordinatesEquiv K).map_add c.val e.val)
  map_smul' a c := Subtype.ext
    (((seamTensorCoordinatesEquiv K).restrictScalars K).map_smul a c.val)

variable (hpar : ∀ p q : SeamRetainedIndex n m,
    laurentEvalOne (seamRetainedDifferential G H hG hH K (Pi.single p 1) q) =
      (if p.2 = q.2 then ((GridRectangleBetween.emptyRectangles p.1 q.1).card : K) else 0) +
        if p.1 = q.1 then ((GridRectangleBetween.emptyRectangles p.2 q.2).card : K) else 0)

/-- The native tensor and retained complexes are isomorphic under exactly the parity identity. -/
def seamTensorNativeIso :
    laurentTensorMaslovComplex (K := K) G H ≅ seamRetainedMaslovComplex K G H hG hH hO :=
  HomologicalComplex.Hom.isoOfComponents
    (fun d => (seamTensorMaslovPieceEquiv G H hG hH hO d).toModuleIso) (by
      intro i j hij
      rw [ComplexShape.down_Rel] at hij
      subst i
      rw [seamRetainedMaslovComplex_d]
      simp only [laurentTensorMaslovComplex, ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      have hh := LinearMap.congr_fun
        ((seamTensorCoordinates_intertwines_iff_evalOne G H hG hH hO).mpr hpar) c.val
      change seamRetainedDifferential G H hG hH K (seamTensorCoordinatesEquiv K c.val) =
        seamTensorCoordinatesEquiv K (laurentTensorDifferential G H c.val)
      exact hh)

/-- The full native seam complex is equivalent to the balanced tensor under the parity identity. -/
def seamNativeTensorHomotopyEquiv :
    HomotopyEquiv (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) K)
      (laurentTensorMaslovComplex (K := K) G H) :=
  (seamNativeHomotopyEquiv K G H hG hH hO).trans
    (HomotopyEquiv.ofIso (seamTensorNativeIso G H hG hH hO hpar).symm)

/-- The native tensor inclusion is the actual corrected inclusion after the tensor basis map. -/
theorem seamNativeTensorHomotopyEquiv_inv_apply (d : ℤ)
    (c : (laurentTensorMaslovComplex (K := K) G H).X d) :
    (laurentMaslovChainEquiv (connectedSumSeamGrid G H hG hH) K d
      ((seamNativeTensorHomotopyEquiv G H hG hH hO hpar).inv.f d c) :
        LaurentChain K (n + m + 1)) =
      (seamFullContraction G H hG hH K).incl
        (seamTensorCoordinatesEquiv K (laurentTensorMaslovChainEquiv G H d c)) := rfl

/-- The tensor projection is the corrected projection followed by the inverse basis map. -/
theorem seamNativeTensorHomotopyEquiv_hom_apply (d : ℤ)
    (c : (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) K).X d) :
    (laurentTensorMaslovChainEquiv G H d
      ((seamNativeTensorHomotopyEquiv G H hG hH hO hpar).hom.f d c) :
        LaurentChain K (n + 1) ⊗[LaurentPolynomial K] LaurentChain K (m + 1)) =
      (seamTensorCoordinatesEquiv K).symm ((seamFullContraction G H hG hH K).proj
        (laurentMaslovChainEquiv (connectedSumSeamGrid G H hG hH) K d c)) := rfl

/-- The native inclusion has zero shift in both convolved filtration coordinates. -/
theorem seamNativeTensorHomotopyEquiv_inv_shifts :
    (laurentTensorMaslovBifiltration (K := K) G H).Shifts
      (laurentMaslovBifiltration (connectedSumSeamGrid G H hG hH) K)
      (seamNativeTensorHomotopyEquiv G H hG hH hO hpar).inv 0 0 := by
  intro u v d c hc
  change (laurentMaslovChainEquiv _ K d
    ((seamNativeTensorHomotopyEquiv G H hG hH hO hpar).inv.f d c) :
      LaurentChain K (n + m + 1)) ∈ laurentBifiltrationLevel _ K (u + 0) (v + 0)
  rw [seamNativeTensorHomotopyEquiv_inv_apply, add_zero, add_zero]
  exact seamFullContraction_incl_mem_bifiltration_of_last_O G H hG hH hO K
    (seamTensorCoordinatesEquiv_mem_bifiltration G H hG hH hO hc)

/-- The native projection has zero shift in both convolved filtration coordinates. -/
theorem seamNativeTensorHomotopyEquiv_hom_shifts :
    (laurentMaslovBifiltration (connectedSumSeamGrid G H hG hH) K).Shifts
      (laurentTensorMaslovBifiltration (K := K) G H)
      (seamNativeTensorHomotopyEquiv G H hG hH hO hpar).hom 0 0 := by
  intro u v d c hc
  change (laurentTensorMaslovChainEquiv G H d
    ((seamNativeTensorHomotopyEquiv G H hG hH hO hpar).hom.f d c) :
      LaurentChain K (n + 1) ⊗[LaurentPolynomial K] LaurentChain K (m + 1)) ∈
        laurentTensorBifiltrationLevel G H (u + 0) (v + 0)
  rw [seamNativeTensorHomotopyEquiv_hom_apply, add_zero, add_zero]
  exact seamTensorCoordinatesEquiv_symm_mem_bifiltration G H hG hH hO
    (seamFullContraction_proj_mem_bifiltration_of_last_O G H hG hH hO K hc)



section Canonical
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The binary pure tensor class of the already constructed normalized polynomial cycles. -/
def gridCanonicalBinaryTensorClass (hn : 2 ≤ n + 1) (hm : 2 ≤ m + 1) :
    (laurentTensorMaslovComplex (K := ZMod 2) G H).homology 0 :=
  laurentTensorNativeClass G H (gridCanonicalCycle G hn) (gridCanonicalCycle H hm)

/-- The binary selected tensor class is nonzero by the existing scalar dual construction. -/
theorem gridCanonicalBinaryTensorClass_ne_zero (hn : 2 ≤ n + 1) (hm : 2 ≤ m + 1) :
    gridCanonicalBinaryTensorClass G H hn hm ≠ 0 := by
  exact laurentTensorNativeClass_ne_zero G H (gridCanonicalClass G hn)
    (gridCanonicalClass H hm) 0 0 0 le_rfl (by norm_num)
    (by simpa using gridCanonicalClass_spectralThreshold_zero G hn)
    (by simpa using gridCanonicalClass_spectralThreshold_zero H hm)
    (gridCanonicalCycle G hn) (gridCanonicalCycle H hm)
    (gridCanonicalCycle_class G hn) (gridCanonicalCycle_class H hm)

private theorem canonicalCycle_first_zero {l : ℕ} (J : GridDiagram l) (hl : 2 ≤ l) :
    (laurentMaslovChainEquiv J (ZMod 2) 0
      ((laurentMaslovComplex J (ZMod 2)).iCycles 0 (gridCanonicalCycle J hl)) :
        LaurentChain (ZMod 2) l) ∈
      laurentBifiltrationLevel J (ZMod 2) 0 (maslovCoordinateBound J 0) := by
  have hh := laurentMaslovBifiltration_bound J (ZMod 2) 0
    ((laurentMaslovComplex J (ZMod 2)).iCycles 0 (gridCanonicalCycle J hl))
  intro x k hk
  refine ⟨?_, (hh x k hk).2⟩
  have hn := gridCanonicalCycle_nonnegative J hl x k hk
  exact neg_nonpos.mpr (by exact_mod_cast hn)

/-- The selected tensor cycle has first filtration bound zero. -/
theorem gridCanonicalBinaryTensorCycle_first_zero (hn : 2 ≤ n + 1) (hm : 2 ≤ m + 1) :
    laurentTensorNativeChain G H (gridCanonicalCycle G hn) (gridCanonicalCycle H hm) ∈
      (laurentTensorMaslovBifiltration (K := ZMod 2) G H).level 0
        (maslovCoordinateBound G 0 + maslovCoordinateBound H 0) 0 := by
  change (laurentTensorMaslovChainEquiv G H 0
    (laurentTensorNativeChain G H (gridCanonicalCycle G hn) (gridCanonicalCycle H hm)) :
      LaurentChain (ZMod 2) (n + 1) ⊗[LaurentPolynomial (ZMod 2)]
        LaurentChain (ZMod 2) (m + 1)) ∈
    laurentTensorBifiltrationLevel G H 0 (maslovCoordinateBound G 0 + maslovCoordinateBound H 0)
  simp only [laurentTensorNativeChain, LinearEquiv.apply_symm_apply]
  exact Submodule.subset_span ⟨0, maslovCoordinateBound G 0, 0, maslovCoordinateBound H 0,
    _, _, canonicalCycle_first_zero G hn, canonicalCycle_first_zero H hm, by norm_num, le_rfl, rfl⟩

variable (hpar₂ : ∀ p q : SeamRetainedIndex n m,
    laurentEvalOne (seamRetainedDifferential G H hG hH (ZMod 2) (Pi.single p 1) q) =
      (if p.2 = q.2 then ((GridRectangleBetween.emptyRectangles p.1 q.1).card : ZMod 2) else 0) +
        if p.1 = q.1 then ((GridRectangleBetween.emptyRectangles p.2 q.2).card : ZMod 2) else 0)

/-- The actual tensor inclusion carries the selected pure tensor class into the polynomial image. -/
theorem seamNativeTensor_inv_canonical_mem_polynomialImage
    (hn : 2 ≤ n + 1) (hm : 2 ≤ m + 1) (a : Fin (n + m + 1)) :
    homologyMap (seamNativeTensorHomotopyEquiv G H hG hH hO hpar₂).inv 0
        (gridCanonicalBinaryTensorClass G H hn hm) ∈
      polynomialHomologyImage (ZMod 2) (connectedSumSeamGrid G H hG hH) a 0 := by
  let φ := (seamNativeTensorHomotopyEquiv G H hG hH hO hpar₂).inv
  let c := laurentTensorNativeCycle G H (gridCanonicalCycle G hn) (gridCanonicalCycle H hm)
  apply (mem_polynomialHomologyImage_iff_exists_cycle (ZMod 2)
    (connectedSumSeamGrid G H hG hH) a 0 _).mpr
  refine ⟨cyclesMap φ 0 c, ?_, ?_⟩
  · have hi := seamNativeTensorHomotopyEquiv_inv_shifts G H hG hH hO hpar₂
      0 (maslovCoordinateBound G 0 + maslovCoordinateBound H 0) 0
      (laurentTensorNativeChain G H (gridCanonicalCycle G hn) (gridCanonicalCycle H hm))
      (gridCanonicalBinaryTensorCycle_first_zero G H hn hm)
    have he := congrArg (fun f : (laurentTensorMaslovComplex (K := ZMod 2) G H).cycles 0 ⟶
        (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) (ZMod 2)).X 0 => f c)
      (cyclesMap_i φ 0)
    change (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) (ZMod 2)).iCycles 0
      (cyclesMap φ 0 c) = φ.f 0 ((laurentTensorMaslovComplex (K := ZMod 2) G H).iCycles 0 c) at he
    dsimp only [c] at he
    rw [laurentTensorNativeCycle_iCycles] at he
    intro x k hk
    rw [he] at hk
    have hh := (hi x k hk).1
    simp only [add_zero] at hh
    have hkr : (0 : ℝ) ≤ (k : ℝ) := neg_nonpos.mp hh
    exact_mod_cast hkr
  · have he := congrArg
      (fun f : (laurentTensorMaslovComplex (K := ZMod 2) G H).cycles 0 ⟶
        (laurentMaslovComplex (connectedSumSeamGrid G H hG hH) (ZMod 2)).homology 0 => f c)
      (homologyπ_naturality φ 0)
    exact he.symm

/-- The filtered inclusion sends the nonzero pure tensor class to the seam's canonical class. -/
theorem seamNativeTensor_inv_canonicalClass (hn : 2 ≤ n + 1) (hm : 2 ≤ m + 1) :
    homologyMap (seamNativeTensorHomotopyEquiv G H hG hH hO hpar₂).inv 0
      (gridCanonicalBinaryTensorClass G H hn hm) =
        gridCanonicalClass (connectedSumSeamGrid G H hG hH) (by omega) := by
  apply gridCanonicalClass_unique _ (by omega) ⟨0, by omega⟩
  · exact seamNativeTensor_inv_canonical_mem_polynomialImage G H hG hH hO hpar₂ hn hm _
  · let e := seamNativeTensorHomotopyEquiv G H hG hH hO hpar₂
    exact (map_ne_zero_iff _ (e.symm.toHomologyIso 0).toLinearEquiv.injective).mpr
      (gridCanonicalBinaryTensorClass_ne_zero G H hn hm)

/-- The actual projection sends the seam's canonical class to the selected pure tensor class. -/
theorem seamNativeTensor_hom_canonicalClass (hn : 2 ≤ n + 1) (hm : 2 ≤ m + 1) :
    homologyMap (seamNativeTensorHomotopyEquiv G H hG hH hO hpar₂).hom 0
      (gridCanonicalClass (connectedSumSeamGrid G H hG hH) (by omega)) =
        gridCanonicalBinaryTensorClass G H hn hm := by
  rw [← seamNativeTensor_inv_canonicalClass G H hG hH hO hpar₂ hn hm]
  let e := seamNativeTensorHomotopyEquiv G H hG hH hO hpar₂
  exact (e.toHomologyIso 0).toLinearEquiv.apply_symm_apply _

include hO hpar₂ in
/-- The normalized seam and selected tensor thresholds agree under the same parity input. -/
theorem seamNativeTensor_canonical_spectralThreshold
    (hn : 2 ≤ n + 1) (hm : 2 ≤ m + 1) (t : ℝ) :
    ((laurentTensorMaslovBifiltration (K := ZMod 2) G H).weighted t).spectralThreshold 0
      (gridCanonicalBinaryTensorClass G H hn hm) =
        RealFiltration.spectralThreshold
          ((laurentMaslovBifiltration (connectedSumSeamGrid G H hG hH) (ZMod 2)).weighted t)
          0 (gridCanonicalClass (connectedSumSeamGrid G H hG hH) (by omega)) := by
  rw [← seamNativeTensor_hom_canonicalClass G H hG hH hO hpar₂ hn hm]
  exact Bifiltration.weighted_spectralThreshold_eq_of_homotopyEquiv
    (seamNativeTensorHomotopyEquiv G H hG hH hO hpar₂)
    (Bifiltration.shifts_zero_zero_iff.mp
      (seamNativeTensorHomotopyEquiv_hom_shifts G H hG hH hO hpar₂))
    (Bifiltration.shifts_zero_zero_iff.mp
      (seamNativeTensorHomotopyEquiv_inv_shifts G H hG hH hO hpar₂)) 0 _ t

end Canonical
end OnLeConjecture.KnotFloer.GridFull
