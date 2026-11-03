/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridLaurentFiniteTensorFiltration

/-! # Native Maslov degrees of the finite balanced tensor product -/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti PiTensorProduct CategoryTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [Field K] {n : ι → ℕ} (G : ∀ i, GridDiagram (n i))

/-- Homogeneous finite tensors, including the Laurent powers of the empty tensor unit. -/
def laurentFiniteMaslovPiece (r : ℤ) :
    Submodule K (LaurentFiniteTensor (K := K) (n := n)) :=
  Submodule.span K {z | ∃ j : ℤ, ∃ p : ι → ℤ, ∃ x : ∀ i, LaurentChain K (n i),
    (∀ i, x i ∈ laurentMaslovPiece (G i) K (p i)) ∧ (∑ i, p i) - 2 * j = r ∧
      z = (LaurentPolynomial.T j : LaurentPolynomial K) • tprod (LaurentPolynomial K) x}

/-- The additive group on each degree, induced by the coefficient field. -/
instance laurentFiniteMaslovPieceAddCommGroup (r : ℤ) :
    AddCommGroup (laurentFiniteMaslovPiece (K := K) G r) :=
  Module.addCommMonoidToAddCommGroup K

/-- The differential lowers the sum Maslov degree by one. -/
theorem laurentFiniteDifferential_mem_maslovPiece {r : ℤ}
    {z : LaurentFiniteTensor (K := K) (n := n)} (hz : z ∈ laurentFiniteMaslovPiece G r) :
    laurentFiniteDifferential G z ∈ laurentFiniteMaslovPiece G (r - 1) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, p, x, hx, hr, rfl⟩ := hz
    rw [map_smul, laurentFiniteDifferential_tprod, Finset.smul_sum]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.subset_span
    refine ⟨j, Function.update p i (p i - 1), _, ?_, ?_, rfl⟩
    · intro k
      by_cases h : k = i
      · subst k
        simpa using laurentDifferential_mem_maslovPiece (G i) (hx i)
      · simpa [h] using hx k
    · have hs := Finset.sum_update_of_mem (Finset.mem_univ i) p (p i)
      rw [Function.update_eq_self] at hs
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      omega
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul a z _ hz =>
    change ((laurentFiniteDifferential G).restrictScalars K) (a • z) ∈ _
    rw [map_smul]
    exact Submodule.smul_mem _ a hz

/-- The differential restricted between consecutive finite tensor degrees. -/
def laurentFiniteGradedDifferential (r : ℤ) :
    laurentFiniteMaslovPiece (K := K) G (r + 1) →ₗ[K] laurentFiniteMaslovPiece (K := K) G r where
  toFun z := ⟨laurentFiniteDifferential G z, by
    simpa only [add_sub_cancel_right] using laurentFiniteDifferential_mem_maslovPiece G z.property⟩
  map_add' z w := Subtype.ext (map_add (laurentFiniteDifferential G)
    (z : LaurentFiniteTensor (K := K) (n := n)) (w : LaurentFiniteTensor (K := K) (n := n)))
  map_smul' a z := Subtype.ext (((laurentFiniteDifferential G).restrictScalars K).map_smul a
    (z : LaurentFiniteTensor (K := K) (n := n)))

variable [CharP K 2]

/-- The native finite Laurent tensor complex. -/
def laurentFiniteMaslovComplex : ChainComplex (ModuleCat K) ℤ :=
  ChainComplex.of (fun r => ModuleCat.of K (laurentFiniteMaslovPiece (K := K) G r))
    (fun r => ModuleCat.ofHom (laurentFiniteGradedDifferential G r)) (fun r => by
      ext z
      exact laurentFiniteDifferential_sq_eq_zero G
        (z : LaurentFiniteTensor (K := K) (n := n)))

/-- Identify a native chain group with its homogeneous submodule. -/
def laurentFiniteMaslovChainEquiv (r : ℤ) :
    (laurentFiniteMaslovComplex (K := K) G).X r ≃ₗ[K] laurentFiniteMaslovPiece (K := K) G r :=
  (eqToIso (show (laurentFiniteMaslovComplex (K := K) G).X r =
    ModuleCat.of K (laurentFiniteMaslovPiece (K := K) G r) from rfl)).toLinearEquiv

/-- The native differential agrees with the finite sum of factor differentials. -/
theorem laurentFiniteMaslovChainEquiv_d (r : ℤ)
    (z : (laurentFiniteMaslovComplex (K := K) G).X (r + 1)) :
    (laurentFiniteMaslovChainEquiv G r
      ((laurentFiniteMaslovComplex (K := K) G).d (r + 1) r z) :
        LaurentFiniteTensor (K := K) (n := n)) =
      laurentFiniteDifferential G (laurentFiniteMaslovChainEquiv G (r + 1) z) := by
  simp only [laurentFiniteMaslovComplex, ChainComplex.of_d]
  rfl

/-- The outgoing degree-zero differential on the underlying finite tensor. -/
theorem laurentFiniteMaslovChainEquiv_d_zero (z : (laurentFiniteMaslovComplex (K := K) G).X 0) :
    (laurentFiniteMaslovChainEquiv G (-1)
      ((laurentFiniteMaslovComplex (K := K) G).d 0 (-1) z) :
        LaurentFiniteTensor (K := K) (n := n)) =
      laurentFiniteDifferential G (laurentFiniteMaslovChainEquiv G 0 z) := by
  have h : (0 : ℤ) = -1 + 1 := by omega
  revert z
  rw [h]
  intro z
  exact laurentFiniteMaslovChainEquiv_d (K := K) G (-1) z

/-- The native coordinatewise convolved bifiltration. -/
def laurentFiniteMaslovBifiltration : Bifiltration (laurentFiniteMaslovComplex (K := K) G) where
  level A B r := (laurentFiniteBifiltrationLevel G A B).comap
    ((laurentFiniteMaslovPiece (K := K) G r).subtype.comp
      (laurentFiniteMaslovChainEquiv G r).toLinearMap)
  mono r _ _ _ _ hA hB := Submodule.comap_mono (Submodule.span_mono (by
    rintro z ⟨j, a, b, x, hx, ha, hb, hz⟩
    exact ⟨j, a, b, x, hx, ha.trans hA, hb.trans hB, hz⟩))
  differential_mem A B i j z hz := by
    by_cases hij : j + 1 = i
    · subst i
      change (laurentFiniteMaslovChainEquiv G j
        ((laurentFiniteMaslovComplex (K := K) G).d (j + 1) j z) :
          LaurentFiniteTensor (K := K) (n := n)) ∈ laurentFiniteBifiltrationLevel G A B
      rw [laurentFiniteMaslovChainEquiv_d]
      exact laurentFiniteDifferential_mem_bifiltrationLevel G A B hz
    · rw [(laurentFiniteMaslovComplex (K := K) G).shape i j
        (by simpa only [ComplexShape.down_Rel] using hij)]
      exact Submodule.zero_mem _

/-- A native weighted-level bound also holds on the underlying finite tensor. -/
theorem native_weighted_mem_laurentFiniteWeightedLevel (t : ℝ) (r : ℤ)
    {s : ℝ} {z : (laurentFiniteMaslovComplex (K := K) G).X r}
    (hz : z ∈ ((laurentFiniteMaslovBifiltration G).weighted t).level s r) :
    (laurentFiniteMaslovChainEquiv G r z : LaurentFiniteTensor (K := K) (n := n)) ∈
      laurentFiniteWeightedLevel G t s := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨A, B, hz, hs⟩ := hz
    exact Submodule.subset_span ⟨A, B, hz, hs⟩
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]; exact Submodule.zero_mem _
  | add z w _ _ hz hw => simpa using Submodule.add_mem _ hz hw
  | smul a z _ hz => simpa using Submodule.smul_mem _ a hz

end OnLeConjecture.KnotFloer.GridFull
