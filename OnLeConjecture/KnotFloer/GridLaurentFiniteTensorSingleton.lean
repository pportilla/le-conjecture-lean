/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridCanonicalTensorClass
public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorUnit
public import OnLeConjecture.KnotFloer.GridLaurentTensorMaslov

/-!
# Chain maps induced on Maslov pieces, and the singleton finite tensor

The native grid, binary tensor and finite tensor complexes are all built from
homogeneous submodules of an underlying module. A linear map of underlying
modules that preserves the homogeneous submodules and commutes with the
underlying differentials induces a chain map. If it also maps each filtration
level into the level with the same bounds, the chain map has shifts `(0,0)`.

For a singleton index type, Mathlib's equivalence
`PiTensorProduct.subsingletonEquiv` induces an isomorphism between the native
complex of the sole grid and the finite tensor complex. Both directions have
shifts `(0,0)`, and the isomorphism carries the normalized class of the grid to
the canonical finite tensor class (M005, alias M611).
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti PiTensorProduct TensorProduct CategoryTheory HomologicalComplex

section PieceMaps

/-- A chain complex whose chain groups are identified with homogeneous submodules of one
underlying module, whose differential is induced by one underlying linear map, and whose
bifiltration is induced by one family of underlying submodules. -/
structure PieceComplexData (K : Type*) [Field K] (C : ChainComplex (ModuleCat K) ℤ)
    (M : Type*) [AddCommGroup M] [Module K M] where
  /-- The homogeneous submodule in each degree. -/
  piece : ℤ → Submodule K M
  /-- The identification of each chain group with its homogeneous submodule. -/
  equiv : ∀ r, C.X r ≃ₗ[K] piece r
  /-- The underlying differential. -/
  d : M →ₗ[K] M
  equiv_d : ∀ r x, (equiv r (C.d (r + 1) r x) : M) = d (equiv (r + 1) x)
  /-- The bifiltration of the chain complex. -/
  bifiltration : Bifiltration C
  /-- The underlying filtration levels. -/
  level : ℝ → ℝ → Submodule K M
  mem_level : ∀ a b r x, x ∈ bifiltration.level a b r ↔ (equiv r x : M) ∈ level a b

namespace PieceComplexData

variable {K : Type*} [Field K]
variable {M N L : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup L] [Module K L]
variable {C D E : ChainComplex (ModuleCat K) ℤ}
variable (A : PieceComplexData K C M) (B : PieceComplexData K D N) (B' : PieceComplexData K E L)

/-- The chain map induced by a linear map of underlying modules that preserves the
homogeneous submodules and commutes with the underlying differentials. -/
def hom (f : M →ₗ[K] N) (hf : ∀ r x, x ∈ A.piece r → f x ∈ B.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x)) : C ⟶ D :=
  ChainComplex.ofHom (fun r => ModuleCat.ofHom
      ((B.equiv r).symm.toLinearMap ∘ₗ f.restrict (hf r) ∘ₗ (A.equiv r).toLinearMap)) (by
    intro r
    ext x
    apply (B.equiv r).injective
    apply Subtype.ext
    change (B.equiv r (D.d (r + 1) r ((B.equiv (r + 1)).symm ⟨f (A.equiv (r + 1) x), _⟩)) : N) =
      ((B.equiv r ((B.equiv r).symm ⟨f (A.equiv r (C.d (r + 1) r x)), _⟩)) : N)
    rw [B.equiv_d, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change B.d (f (A.equiv (r + 1) x)) = f (A.equiv r (C.d (r + 1) r x))
    rw [A.equiv_d, hfd])

/-- The induced chain map is the given linear map on underlying elements. -/
theorem hom_apply (f : M →ₗ[K] N) (hf : ∀ r x, x ∈ A.piece r → f x ∈ B.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x)) (r : ℤ) (x : C.X r) :
    (B.equiv r ((A.hom B f hf hfd).f r x) : N) = f (A.equiv r x) := by
  change (B.equiv r ((B.equiv r).symm ⟨f (A.equiv r x), _⟩) : N) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Composition of underlying maps induces composition of chain maps. -/
theorem hom_comp (f : M →ₗ[K] N) (hf : ∀ r x, x ∈ A.piece r → f x ∈ B.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x)) (g : N →ₗ[K] L)
    (hg : ∀ r x, x ∈ B.piece r → g x ∈ B'.piece r) (hgd : ∀ x, g (B.d x) = B'.d (g x)) :
    A.hom B f hf hfd ≫ B.hom B' g hg hgd =
      A.hom B' (g ∘ₗ f) (fun r x hx => hg r _ (hf r x hx)) (fun x => by
        simp only [LinearMap.comp_apply, hfd, hgd]) := by
  ext r : 1
  ext x
  apply (B'.equiv r).injective
  apply Subtype.ext
  rw [HomologicalComplex.comp_f, ModuleCat.comp_apply, hom_apply, hom_apply, hom_apply]
  rfl

/-- The isomorphism induced by a linear equivalence of underlying modules that preserves
and reflects the homogeneous submodules and commutes with the underlying differentials. -/
def iso (f : M ≃ₗ[K] N) (hf : ∀ r x, f x ∈ B.piece r ↔ x ∈ A.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x)) : C ≅ D where
  hom := A.hom B f.toLinearMap (fun r x hx => (hf r x).mpr hx) hfd
  inv := B.hom A f.symm.toLinearMap
    (fun r x hx => (hf r (f.symm x)).mp (by simpa using hx)) (fun x => by
      apply f.injective
      simp [hfd])
  hom_inv_id := by
    ext r : 1
    ext x
    apply (A.equiv r).injective
    apply Subtype.ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.comp_apply,
      ModuleCat.id_apply, hom_apply, hom_apply]
    simp
  inv_hom_id := by
    ext r : 1
    ext x
    apply (B.equiv r).injective
    apply Subtype.ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.comp_apply,
      ModuleCat.id_apply, hom_apply, hom_apply]
    simp

theorem iso_hom (f : M ≃ₗ[K] N) (hf : ∀ r x, f x ∈ B.piece r ↔ x ∈ A.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x)) :
    (A.iso B f hf hfd).hom = A.hom B f.toLinearMap (fun r x hx => (hf r x).mpr hx) hfd := rfl

theorem iso_hom_apply (f : M ≃ₗ[K] N) (hf : ∀ r x, f x ∈ B.piece r ↔ x ∈ A.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x)) (r : ℤ) (x : C.X r) :
    (B.equiv r ((A.iso B f hf hfd).hom.f r x) : N) = f (A.equiv r x) :=
  hom_apply A B f.toLinearMap (fun r x hx => (hf r x).mpr hx) hfd r x

theorem iso_inv_apply (f : M ≃ₗ[K] N) (hf : ∀ r x, f x ∈ B.piece r ↔ x ∈ A.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x)) (r : ℤ) (y : D.X r) :
    (A.equiv r ((A.iso B f hf hfd).inv.f r y) : M) = f.symm (B.equiv r y) :=
  hom_apply B A f.symm.toLinearMap
    (fun r x hx => (hf r (f.symm x)).mp (by simpa using hx)) (fun x => by
      apply f.injective
      simp [hfd]) r y

/-- Level preservation of the underlying map gives shifts `(0,0)` for the induced map. -/
theorem hom_shifts (f : M →ₗ[K] N) (hf : ∀ r x, x ∈ A.piece r → f x ∈ B.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x)) (hL : ∀ a b x, x ∈ A.level a b → f x ∈ B.level a b) :
    A.bifiltration.Shifts B.bifiltration (A.hom B f hf hfd) 0 0 := by
  intro a b r x hx
  rw [add_zero, add_zero, B.mem_level, hom_apply]
  exact hL a b _ ((A.mem_level a b r x).mp hx)

theorem iso_hom_shifts (f : M ≃ₗ[K] N) (hf : ∀ r x, f x ∈ B.piece r ↔ x ∈ A.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x)) (hL : ∀ a b x, x ∈ A.level a b → f x ∈ B.level a b) :
    A.bifiltration.Shifts B.bifiltration (A.iso B f hf hfd).hom 0 0 :=
  hom_shifts A B f.toLinearMap (fun r x hx => (hf r x).mpr hx) hfd hL

theorem iso_inv_shifts (f : M ≃ₗ[K] N) (hf : ∀ r x, f x ∈ B.piece r ↔ x ∈ A.piece r)
    (hfd : ∀ x, f (A.d x) = B.d (f x))
    (hL : ∀ a b y, y ∈ B.level a b → f.symm y ∈ A.level a b) :
    B.bifiltration.Shifts A.bifiltration (A.iso B f hf hfd).inv 0 0 :=
  hom_shifts B A f.symm.toLinearMap
    (fun r x hx => (hf r (f.symm x)).mp (by simpa using hx)) (fun x => by
      apply f.injective
      simp [hfd]) hL

end PieceComplexData

variable {K : Type*} [Field K] [CharP K 2]

/-- The native grid complex as a complex of homogeneous Laurent chains. -/
def laurentGridPieceData {n : ℕ} (G : GridDiagram n) :
    PieceComplexData K (laurentMaslovComplex G K) (LaurentChain K n) where
  piece := laurentMaslovPiece G K
  equiv := laurentMaslovChainEquiv G K
  d := (laurentDifferential G K).restrictScalars K
  equiv_d := laurentMaslovChainEquiv_d G K
  bifiltration := laurentMaslovBifiltration G K
  level := laurentBifiltrationLevel G K
  mem_level _ _ _ _ := Iff.rfl

/-- The native finite tensor complex as a complex of homogeneous finite tensors. -/
def laurentFinitePieceData {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (G : ∀ i, GridDiagram (n i)) :
    PieceComplexData K (laurentFiniteMaslovComplex (K := K) G)
      (LaurentFiniteTensor (K := K) (n := n)) where
  piece := laurentFiniteMaslovPiece G
  equiv := laurentFiniteMaslovChainEquiv G
  d := (laurentFiniteDifferential G).restrictScalars K
  equiv_d := laurentFiniteMaslovChainEquiv_d G
  bifiltration := laurentFiniteMaslovBifiltration G
  level := laurentFiniteBifiltrationLevel G
  mem_level _ _ _ _ := Iff.rfl

/-- The native binary tensor complex as a complex of homogeneous binary tensors. -/
def laurentTensorPieceData {n m : ℕ} (G : GridDiagram n) (H : GridDiagram m) :
    PieceComplexData K (laurentTensorMaslovComplex (K := K) G H)
      (LaurentChain K n ⊗[LaurentPolynomial K] LaurentChain K m) where
  piece := laurentTensorMaslovPiece G H
  equiv := laurentTensorMaslovChainEquiv G H
  d := (laurentTensorDifferential (K := K) G H).restrictScalars K
  equiv_d := laurentTensorMaslovChainEquiv_d G H
  bifiltration := laurentTensorMaslovBifiltration G H
  level := laurentTensorBifiltrationLevel G H
  mem_level _ _ _ _ := Iff.rfl

end PieceMaps

/-- Equal degree-zero cycles after a chain map give equal homology classes. -/
theorem homologyMap_homologyπ_eq_of_iCycles {K : Type*} [Field K]
    {C D : ChainComplex (ModuleCat K) ℤ} (φ : C ⟶ D) (c : C.cycles 0) (c' : D.cycles 0)
    (h : φ.f 0 (C.iCycles 0 c) = D.iCycles 0 c') :
    homologyMap φ 0 (C.homologyπ 0 c) = D.homologyπ 0 c' := by
  have hc : cyclesMap φ 0 c = c' := by
    apply (ModuleCat.mono_iff_injective (D.iCycles 0)).mp inferInstance
    have he := congrArg (fun g : C.cycles 0 ⟶ D.X 0 => g c) (cyclesMap_i φ 0)
    exact he.trans h
  have hn := congrArg (fun g : C.cycles 0 ⟶ D.homology 0 => g c) (homologyπ_naturality φ 0)
  exact hn.trans (congrArg (D.homologyπ 0) hc)

section Singleton

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι] (i₀ : ι)
variable {K : Type*} [Field K] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i))

omit [DecidableEq ι] in
private theorem sum_subsingleton_eq {α : Type*} [AddCommMonoid α] (f : ι → α) :
    ∑ i, f i = f i₀ :=
  Fintype.sum_subsingleton f i₀

omit [Fintype ι] in
/-- The inverse singleton tensor equivalence on a chain is a pure tensor. -/
theorem subsingletonEquiv_symm_eq_tprod (c : LaurentChain K (n i₀)) :
    (PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
        (s := fun i => LaurentChain K (n i)) i₀).symm c =
      tprod (LaurentPolynomial K) (Function.update (0 : ∀ i, LaurentChain K (n i)) i₀ c) := by
  rw [LinearEquiv.symm_apply_eq, subsingletonEquiv_apply_tprod, Function.update_self]

omit [Fintype ι] in
private theorem update_zero_subsingleton {β : ι → Type*} [∀ i, Zero (β i)] (c : β i₀) (i : ι)
    (P : ∀ i, β i → Prop) (hP : P i₀ c) :
    P i (Function.update (0 : ∀ i, β i) i₀ c i) := by
  obtain rfl := Subsingleton.elim i₀ i
  simpa using hP

omit [DecidableEq ι] in
/-- The singleton tensor equivalence preserves and reflects every Maslov piece. -/
theorem subsingletonEquiv_symm_mem_maslovPiece_iff (r : ℤ) (c : LaurentChain K (n i₀)) :
    (PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
        (s := fun i => LaurentChain K (n i)) i₀).symm c ∈ laurentFiniteMaslovPiece G r ↔
      c ∈ laurentMaslovPiece (G i₀) K r := by
  classical
  set e := PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
    (s := fun i => LaurentChain K (n i)) i₀
  constructor
  · intro h
    have hc : e (e.symm c) = c := e.apply_symm_apply c
    rw [← hc]
    generalize e.symm c = z at h
    induction h using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, p, x, hx, hr, rfl⟩ := hz
      rw [map_smul, subsingletonEquiv_apply_tprod]
      rw [sum_subsingleton_eq i₀] at hr
      rw [← hr]
      exact laurentMonomial_smul_mem_maslovPiece (G i₀) j 1 (hx i₀)
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
    | smul a z _ hz =>
      change ((e.toLinearMap.restrictScalars K) (a • z)) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a hz
  · intro hc
    rw [subsingletonEquiv_symm_eq_tprod]
    apply Submodule.subset_span
    refine ⟨0, fun _ => r, Function.update 0 i₀ c, fun i => ?_, ?_, by simp⟩
    · exact update_zero_subsingleton i₀ c i
        (fun i x => x ∈ laurentMaslovPiece (G i) K r) hc
    · simp [sum_subsingleton_eq i₀]

omit [DecidableEq ι] in
/-- The singleton tensor equivalence preserves and reflects every filtration level. -/
theorem subsingletonEquiv_symm_mem_bifiltrationLevel_iff (a b : ℝ) (c : LaurentChain K (n i₀)) :
    (PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
        (s := fun i => LaurentChain K (n i)) i₀).symm c ∈ laurentFiniteBifiltrationLevel G a b ↔
      c ∈ laurentBifiltrationLevel (G i₀) K a b := by
  classical
  set e := PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
    (s := fun i => LaurentChain K (n i)) i₀
  constructor
  · intro h
    have hc : e (e.symm c) = c := e.apply_symm_apply c
    rw [← hc]
    generalize e.symm c = z at h
    induction h using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, u, v, x, hx, hA, hB, rfl⟩ := hz
      rw [map_smul, subsingletonEquiv_apply_tprod]
      rw [sum_subsingleton_eq i₀] at hA hB
      exact laurentBifiltrationLevel_mono (G i₀) K hA hB
        (T_smul_mem_laurentBifiltrationLevel (G i₀) K j _ (hx i₀))
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
    | smul a z _ hz =>
      change ((e.toLinearMap.restrictScalars K) (a • z)) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a hz
  · intro hc
    rw [subsingletonEquiv_symm_eq_tprod]
    apply Submodule.subset_span
    refine ⟨0, fun _ => a, fun _ => b, Function.update 0 i₀ c, fun i => ?_, ?_, ?_, by simp⟩
    · exact update_zero_subsingleton i₀ c i
        (fun i x => x ∈ laurentBifiltrationLevel (G i) K a b) hc
    · simp [sum_subsingleton_eq i₀]
    · simp [sum_subsingleton_eq i₀]

/-- The singleton tensor equivalence intertwines the grid and tensor differentials. -/
theorem subsingletonEquiv_symm_differential (c : LaurentChain K (n i₀)) :
    (PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
        (s := fun i => LaurentChain K (n i)) i₀).symm (laurentDifferential (G i₀) K c) =
      laurentFiniteDifferential G
        ((PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
          (s := fun i => LaurentChain K (n i)) i₀).symm c) := by
  set e := PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
    (s := fun i => LaurentChain K (n i)) i₀
  apply e.injective
  rw [laurentFiniteDifferential_subsingleton G i₀, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- The inverse singleton tensor equivalence, as a linear equivalence over the coefficients. -/
def laurentFiniteSubsingletonEquiv :
    LaurentChain K (n i₀) ≃ₗ[K] LaurentFiniteTensor (K := K) (n := n) :=
  (PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
    (s := fun i => LaurentChain K (n i)) i₀).symm.restrictScalars K

omit [Fintype ι] [DecidableEq ι] in
theorem laurentFiniteSubsingletonEquiv_apply (c : LaurentChain K (n i₀)) :
    laurentFiniteSubsingletonEquiv (K := K) (n := n) i₀ c =
      (PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
        (s := fun i => LaurentChain K (n i)) i₀).symm c := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem laurentFiniteSubsingletonEquiv_symm_apply (z : LaurentFiniteTensor (K := K) (n := n)) :
    (laurentFiniteSubsingletonEquiv (K := K) (n := n) i₀).symm z =
      PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
        (s := fun i => LaurentChain K (n i)) i₀ z := rfl

variable [CharP K 2]

/-- The native complex of the sole grid is isomorphic to the singleton finite tensor. -/
def laurentFiniteMaslovSubsingletonIso :
    laurentMaslovComplex (G i₀) K ≅ laurentFiniteMaslovComplex (K := K) G :=
  (laurentGridPieceData (G i₀)).iso (laurentFinitePieceData G)
    (laurentFiniteSubsingletonEquiv i₀)
    (fun r c => subsingletonEquiv_symm_mem_maslovPiece_iff i₀ G r c)
    (fun c => subsingletonEquiv_symm_differential i₀ G c)

/-- On underlying chains, the singleton isomorphism is the inverse Mathlib equivalence. -/
theorem laurentFiniteMaslovSubsingletonIso_hom_apply (r : ℤ)
    (c : (laurentMaslovComplex (G i₀) K).X r) :
    (laurentFiniteMaslovChainEquiv G r ((laurentFiniteMaslovSubsingletonIso i₀ G).hom.f r c) :
        LaurentFiniteTensor (K := K) (n := n)) =
      (PiTensorProduct.subsingletonEquiv (R := LaurentPolynomial K)
        (s := fun i => LaurentChain K (n i)) i₀).symm
          (laurentMaslovChainEquiv (G i₀) K r c : LaurentChain K (n i₀)) :=
  PieceComplexData.iso_hom_apply _ _ _ _ _ r c

/-- The singleton isomorphism has shifts `(0,0)`. -/
theorem laurentFiniteMaslovSubsingletonIso_hom_shifts :
    (laurentMaslovBifiltration (G i₀) K).Shifts (laurentFiniteMaslovBifiltration G)
      (laurentFiniteMaslovSubsingletonIso i₀ G).hom 0 0 :=
  PieceComplexData.iso_hom_shifts (laurentGridPieceData (G i₀)) (laurentFinitePieceData G) _ _ _
    (fun a b c hc => (subsingletonEquiv_symm_mem_bifiltrationLevel_iff i₀ G a b c).mpr hc)

/-- The inverse singleton isomorphism has shifts `(0,0)`. -/
theorem laurentFiniteMaslovSubsingletonIso_inv_shifts :
    (laurentFiniteMaslovBifiltration G).Shifts (laurentMaslovBifiltration (G i₀) K)
      (laurentFiniteMaslovSubsingletonIso i₀ G).inv 0 0 :=
  PieceComplexData.iso_inv_shifts (laurentGridPieceData (G i₀)) (laurentFinitePieceData G) _ _ _
    (fun a b z hz => (subsingletonEquiv_symm_mem_bifiltrationLevel_iff i₀ G a b _).mp (by
      rw [laurentFiniteSubsingletonEquiv_symm_apply, LinearEquiv.symm_apply_apply]
      exact hz))

end Singleton

section SingletonCanonical

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι] (i₀ : ι)
variable {sizes : ι → ℕ} (D : ∀ i, GridDiagram (sizes i)) (hD : ∀ i, 2 ≤ sizes i)

/-- The singleton isomorphism carries the selected native chain to the finite native chain. -/
theorem laurentFiniteMaslovSubsingletonIso_hom_canonicalCycle :
    (laurentFiniteMaslovSubsingletonIso (K := ZMod 2) i₀ D).hom.f 0
        ((laurentMaslovComplex (D i₀) (ZMod 2)).iCycles 0 (gridCanonicalCycle (D i₀) (hD i₀))) =
      (laurentFiniteMaslovComplex (K := ZMod 2) D).iCycles 0
        (laurentFiniteNativeCycle D (fun i => gridCanonicalCycle (D i) (hD i))) := by
  rw [laurentFiniteNativeCycle_iCycles]
  apply (laurentFiniteMaslovChainEquiv D 0).injective
  apply Subtype.ext
  rw [laurentFiniteMaslovSubsingletonIso_hom_apply, subsingletonEquiv_symm_eq_tprod]
  simp only [laurentFiniteNativeChain, LinearEquiv.apply_symm_apply]
  congr 1
  funext i
  obtain rfl := Subsingleton.elim i₀ i
  simp

/-- The singleton isomorphism carries the normalized class to the canonical tensor class. -/
theorem laurentFiniteMaslovSubsingletonIso_hom_canonicalClass :
    homologyMap (laurentFiniteMaslovSubsingletonIso (K := ZMod 2) i₀ D).hom 0
        (gridCanonicalClass (D i₀) (hD i₀)) =
      gridCanonicalFiniteTensorClass D hD := by
  rw [← gridCanonicalCycle_class]
  exact homologyMap_homologyπ_eq_of_iCycles _ _ _
    (laurentFiniteMaslovSubsingletonIso_hom_canonicalCycle i₀ D hD)

/-- The inverse singleton isomorphism carries the canonical tensor class to the
normalized class. -/
theorem laurentFiniteMaslovSubsingletonIso_inv_canonicalClass :
    homologyMap (laurentFiniteMaslovSubsingletonIso (K := ZMod 2) i₀ D).inv 0
        (gridCanonicalFiniteTensorClass D hD) =
      gridCanonicalClass (D i₀) (hD i₀) := by
  rw [← laurentFiniteMaslovSubsingletonIso_hom_canonicalClass i₀ D hD,
    ← ModuleCat.comp_apply, ← homologyMap_comp, Iso.hom_inv_id, homologyMap_id]
  rfl

end SingletonCanonical

end OnLeConjecture.KnotFloer.GridFull
