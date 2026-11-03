/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.NilpotentGermEvaluation

/-!
# Two coordinate projections and nilpotent evaluation

The two projections from the product of source coordinate spaces induce
inclusions of germ rings. Two homomorphisms into a complex algebra that
annihilate maximal-ideal powers extend jointly to the product germ ring.
The extension is constructed by evaluation of finite polynomial jets.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.Analytic

namespace PointedMapGerm

/-- The linear selection of a tuple of source coordinates. -/
def coordinateSelectionLinear {n m : ℕ} (s : Fin m → Fin n) : Source n →L[ℂ] Source m :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (s i))

/-- The pointed germ selecting a tuple of source coordinates. -/
def coordinateSelection {n m : ℕ} (s : Fin m → Fin n) : PointedMapGerm n m :=
  .ofFunction (coordinateSelectionLinear s)
    ((coordinateSelectionLinear s).analyticAt 0) (map_zero _)

@[simp]
theorem coordinateSelection_pullback_coordinate {n m : ℕ} (s : Fin m → Fin n) (i : Fin m) :
    (coordinateSelection s).pullbackRingHom (Germ.coordinate i) = Germ.coordinate (s i) := by
  rw [pullback_coordinate]
  rfl

/-- The first projection from a product of coordinate spaces. -/
def firstProjection (n m : ℕ) : PointedMapGerm (n + m) n :=
  coordinateSelection (Fin.castAdd m)

/-- The second projection from a product of coordinate spaces. -/
def secondProjection (n m : ℕ) : PointedMapGerm (n + m) m :=
  coordinateSelection (Fin.natAdd n)

/-- Pullback as a complex algebra homomorphism. -/
def scalarPullback {n m : ℕ} (g : PointedMapGerm n m) : Germ m →ₐ[ℂ] Germ n :=
  { __ := g.pullbackRingHom
    commutes' := g.pullback_constRingHom }

@[simp]
theorem scalarPullback_apply {n m : ℕ} (g : PointedMapGerm n m) (f : Germ m) :
    g.scalarPullback f = g.pullbackRingHom f := rfl

/-- Scalar pullback preserves every maximal-ideal power. -/
theorem scalarPullback_maximalIdeal_pow_le {n m : ℕ} (g : PointedMapGerm n m) (N : ℕ) :
    Germ.maximalIdeal m ^ N ≤ Ideal.comap g.scalarPullback (Germ.maximalIdeal n ^ N) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  apply pow_le_pow_left'
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  exact g.pullback_mem_maximalIdeal hf

end PointedMapGerm

namespace Germ

/-- Homomorphisms annihilating maximal-ideal powers extend to a joint
evaluation on the product of their source coordinate spaces. -/
theorem exists_joint_nilpotent_evaluation
    {R : Type*} [CommRing R] [Algebra ℂ R] {n m : ℕ}
    (φ : Germ n →ₐ[ℂ] R) (ψ : Germ m →ₐ[ℂ] R)
    (hφ : ∃ N, maximalIdeal n ^ N ≤ RingHom.ker φ)
    (hψ : ∃ N, maximalIdeal m ^ N ≤ RingHom.ker ψ) :
    ∃ (χ : Germ (n + m) →ₐ[ℂ] R) (N : ℕ),
      maximalIdeal (n + m) ^ N ≤ RingHom.ker χ ∧
      χ.comp (PointedMapGerm.firstProjection n m).scalarPullback = φ ∧
      χ.comp (PointedMapGerm.secondProjection n m).scalarPullback = ψ := by
  let x : Fin (n + m) → R :=
    Fin.addCases (fun i ↦ φ (coordinate i)) (fun i ↦ ψ (coordinate i))
  have hx : ∀ i, IsNilpotent (x i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      obtain ⟨N, hN⟩ := hφ
      refine ⟨N, ?_⟩
      simp only [x, Fin.addCases_left]
      rw [← map_pow]
      exact hN (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal j) N)
    · intro j
      obtain ⟨N, hN⟩ := hψ
      refine ⟨N, ?_⟩
      simp only [x, Fin.addCases_right]
      rw [← map_pow]
      exact hN (Ideal.pow_mem_pow (coordinate_mem_maximalIdeal j) N)
  obtain ⟨χ, N, hN, hχ⟩ := exists_evaluation_of_isNilpotent x hx
  refine ⟨χ, N, hN, ?_, ?_⟩
  · refine algHom_ext_of_exists_maximalIdeal_pow_le_ker _ φ ?_ hφ ?_
    · exact ⟨N, fun f hf ↦ hN
        ((PointedMapGerm.firstProjection n m).scalarPullback_maximalIdeal_pow_le N hf)⟩
    · intro i
      change χ ((PointedMapGerm.coordinateSelection (Fin.castAdd m)).pullbackRingHom
        (coordinate i)) = _
      rw [PointedMapGerm.coordinateSelection_pullback_coordinate]
      simpa [x] using hχ (Fin.castAdd m i)
  · refine algHom_ext_of_exists_maximalIdeal_pow_le_ker _ ψ ?_ hψ ?_
    · exact ⟨N, fun f hf ↦ hN
        ((PointedMapGerm.secondProjection n m).scalarPullback_maximalIdeal_pow_le N hf)⟩
    · intro i
      change χ ((PointedMapGerm.coordinateSelection (Fin.natAdd n)).pullbackRingHom
        (coordinate i)) = _
      rw [PointedMapGerm.coordinateSelection_pullback_coordinate]
      simpa [x] using hχ (Fin.natAdd n i)

end Germ

end OnLeConjecture.Analytic
