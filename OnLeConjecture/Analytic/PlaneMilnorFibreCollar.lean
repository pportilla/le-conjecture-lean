/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneMilnorFibre
public import OnLeConjecture.Analytic.PlaneMilnorPolydisc
public import OnLeConjecture.DifferentialTopology.CompactSupportEvolution
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Collars of Milnor fibres and of polydisc fibres

Let `φ : ℝ → E → E` be jointly continuous with `φ 0 = id`, let `Y ⊆ X ⊆ E`, and let
`T` be a nonnegative function, continuous on `X` and vanishing on `Y`. If the trajectory of every
`x ∈ X` stays in `X` up to time `T x` and lies in `Y` at time `T x`, then
`h (τ, x) = φ (τ T x) x` is a deformation retraction of `X` onto `Y`. In particular the
inclusion `Y → X` is a homotopy equivalence (`exists_homotopyEquiv_of_flow`). The special case
of a function `ψ` with `ψ (φ t x) = ψ x - t` along the collar `a ≤ ψ ≤ b` is
`exists_homotopyEquiv_of_flow_level`.

We apply this construction to two families of fibres of a function `H : Source 2 → ℂ`.

* **Ball collar.** Write `w = (-∂₁ f, ∂₀ f)` for the kernel vector of the equation `f` on the
  Euclidean plane. Where the equation together with the squared norm is a submersion, the
  Hermitian product `⟨z, w⟩` does not vanish and the field `V₀ = -w / (2 ⟨z, w⟩)` satisfies
  `df (V₀) = 0` and `d ‖·‖² (V₀) = -1`. The product of `V₀` with a smooth cutoff function is a
  compactly supported `C¹` field, and its flow retracts the Milnor fibre of radius `ε` onto the
  Milnor fibre of radius `ε₁` (`milnorFibre_collar_of_transverse`, `exists_milnorFibre_collar`).
* **Polydisc collar.** Where the fibre partial derivative `∂₀ H` does not vanish, the field
  `V₀ = (∂₁ H · z₁ / ∂₀ H, -z₁)` satisfies `dH (V₀) = 0` and contracts the base coordinate `z₁`
  radially. The flow of its product with a cutoff function retracts the polydisc fibre with base
  radius `η₁` onto the polydisc fibre with base radius `η₂`. The fibre coordinate cannot leave
  the polydisc, by an intermediate value argument (`polydiscFibre_collar`).
-/

@[expose] public noncomputable section

open Filter Metric Set Function
open scoped Topology ContDiff NNReal Manifold ComplexConjugate

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- **Collar along a flow.** Let `φ : ℝ → E → E` be jointly continuous with `φ 0 = id`, and
let `Y ⊆ X`. Suppose that `T` is a nonnegative function, continuous on `X` and vanishing on `Y`,
such that the trajectory of every `x ∈ X` stays in `X` up to time `T x` and lies in `Y` at
time `T x`. Then the inclusion `Y → X` is a homotopy equivalence. -/
theorem exists_homotopyEquiv_of_flow {E : Type*} [TopologicalSpace E] (φ : ℝ → E → E)
    (hφ : Continuous fun p : ℝ × E => φ p.1 p.2) (hφ0 : ∀ x, φ 0 x = x)
    {X Y : Set E} (hYX : Y ⊆ X) (T : E → ℝ) (hT : ContinuousOn T X)
    (hT0 : ∀ x ∈ X, 0 ≤ T x) (hTY : ∀ x ∈ Y, T x = 0)
    (hmaps : ∀ x ∈ X, ∀ t, 0 ≤ t → t ≤ T x → φ t x ∈ X)
    (hend : ∀ x ∈ X, φ (T x) x ∈ Y) :
    ∃ e : ContinuousMap.HomotopyEquiv Y X, ∀ y, (e.toFun y : E) = y := by
  have hTX : Continuous fun x : X => T x := continuousOn_iff_continuous_domRestrict.mp hT
  let i : C(Y, X) := ⟨Set.inclusion hYX, continuous_inclusion hYX⟩
  let r : C(X, Y) := ⟨fun x => ⟨φ (T x) x, hend x x.2⟩,
    (hφ.comp (hTX.prodMk continuous_subtype_val)).subtype_mk _⟩
  have hri : r.comp i = ContinuousMap.id Y := by
    ext y
    change φ (T y) y = y
    rw [hTY y y.2, hφ0]
  have hmem : ∀ p : unitInterval × X, φ ((p.1 : ℝ) * T p.2) p.2 ∈ X := fun p =>
    hmaps p.2 p.2.2 _ (mul_nonneg p.1.2.1 (hT0 _ p.2.2))
      (mul_le_of_le_one_left (hT0 _ p.2.2) p.1.2.2)
  let F : ContinuousMap.Homotopy (ContinuousMap.id X) (i.comp r) :=
    { toFun := fun p => ⟨φ ((p.1 : ℝ) * T p.2) p.2, hmem p⟩
      continuous_toFun := by
        refine (hφ.comp (Continuous.prodMk ?_ ?_)).subtype_mk _
        · exact (continuous_subtype_val.comp continuous_fst).mul (hTX.comp continuous_snd)
        · exact continuous_subtype_val.comp continuous_snd
      map_zero_left := fun x => by
        apply Subtype.ext
        change φ (0 * T x) x = x
        rw [zero_mul, hφ0]
      map_one_left := fun x => by
        apply Subtype.ext
        change φ (1 * T x) x = φ (T x) x
        rw [one_mul] }
  refine ⟨⟨i, r, ?_, ⟨F.symm⟩⟩, fun y => rfl⟩
  rw [hri]

/-- **Collar along a level function.** Let `φ : ℝ → E → E` be jointly continuous with
`φ 0 = id`, let `Z` be a set, and let `ψ` be continuous on `Z`. Suppose that for `x ∈ Z` with
`a ≤ ψ x ≤ b` and `0 ≤ t ≤ ψ x - a` the point `φ t x` lies in `Z` and `ψ (φ t x) = ψ x - t`.
Then the inclusion of `{x ∈ Z | ψ x ≤ a}` into `{x ∈ Z | ψ x ≤ b}` is a homotopy
equivalence. -/
theorem exists_homotopyEquiv_of_flow_level {E : Type*} [TopologicalSpace E] (φ : ℝ → E → E)
    (hφ : Continuous fun p : ℝ × E => φ p.1 p.2) (hφ0 : ∀ x, φ 0 x = x) (Z : Set E)
    (ψ : E → ℝ) (hψ : ContinuousOn ψ Z) {a b : ℝ} (hab : a ≤ b)
    (hflow : ∀ x ∈ Z, a ≤ ψ x → ψ x ≤ b → ∀ t, 0 ≤ t → t ≤ ψ x - a →
      φ t x ∈ Z ∧ ψ (φ t x) = ψ x - t) :
    ∃ e : ContinuousMap.HomotopyEquiv {x | x ∈ Z ∧ ψ x ≤ a} {x | x ∈ Z ∧ ψ x ≤ b},
      ∀ y, (e.toFun y : E) = y := by
  refine exists_homotopyEquiv_of_flow φ hφ hφ0 (fun x hx => ⟨hx.1, hx.2.trans hab⟩)
    (fun x => max 0 (ψ x - a))
    ((ContinuousOn.sup continuousOn_const (hψ.sub continuousOn_const)).mono fun x hx => hx.1)
    (fun x _ => le_max_left _ _)
    (fun x hx => max_eq_left (sub_nonpos.mpr hx.2)) ?_ ?_
  · intro x hx t ht htT
    by_cases hxa : ψ x ≤ a
    · have ht0 : t = 0 := le_antisymm (htT.trans_eq (max_eq_left (sub_nonpos.mpr hxa))) ht
      rw [ht0, hφ0]
      exact hx
    push Not at hxa
    have hT : max 0 (ψ x - a) = ψ x - a := max_eq_right (sub_nonneg.mpr hxa.le)
    obtain ⟨hZ, hψt⟩ := hflow x hx.1 hxa.le hx.2 t ht (hT ▸ htT)
    exact ⟨hZ, by rw [hψt]; linarith [hx.2]⟩
  · intro x hx
    by_cases hxa : ψ x ≤ a
    · rw [max_eq_left (sub_nonpos.mpr hxa), hφ0]
      exact ⟨hx.1, hxa⟩
    push Not at hxa
    rw [max_eq_right (sub_nonneg.mpr hxa.le)]
    obtain ⟨hZ, hψt⟩ := hflow x hx.1 hxa.le hx.2 _ (sub_nonneg.mpr hxa.le) le_rfl
    exact ⟨hZ, by rw [hψt]; linarith⟩

section Flow

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth cutoff function with values in `[0, 1]`, equal to one on a compact set and with
compact topological support inside a given open neighbourhood of it. -/
theorem exists_contDiff_cutoff [FiniteDimensional ℝ F] {K U : Set F} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : F → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ, hχ, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, F) (n := ⊤) isOpen_interior hK.isClosed hKL
  have htsupp : tsupport χ ⊆ L := by
    rw [tsupport, hsupp]
    exact closure_minimal interior_subset hLc.isClosed
  exact ⟨χ, contMDiff_iff_contDiff.mp hχ, hLc.of_isClosed_subset (isClosed_tsupport _) htsupp,
    htsupp.trans hLU, fun x => hrange (mem_range_self x), fun x hx => (hone x).mp hx⟩

/-- Multiplying a field by a cutoff function preserves `C^n` regularity as soon as the field is
`C^n` near every point of the topological support of the cutoff. -/
theorem contDiff_smul_of_tsupport {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : WithTop ℕ∞} {χ : F → ℝ} {V : F → G} (hχ : ContDiff ℝ n χ)
    (hV : ∀ x ∈ tsupport χ, ContDiffAt ℝ n V x) :
    ContDiff ℝ n fun x => χ x • V x := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hV x hx)
  · have h0 : (fun y => χ y • V y) =ᶠ[𝓝 x] fun _ => (0 : G) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- A compactly supported `C¹` autonomous field has a globally Lipschitz clock suspension. -/
theorem exists_lipschitz_autonomousSuspension {V : F → F} (hV : ContDiff ℝ 1 V)
    (hc : HasCompactSupport V) :
    ∃ C, LipschitzWith C (TauCeti.timeDependentSuspension fun _ : ℝ => V) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hV one_ne_zero
  exact ⟨_, (LipschitzWith.const (1 : ℝ)).prodMk (hC.comp LipschitzWith.prod_snd)⟩

variable [CompleteSpace F]

/-- A trajectory of an autonomous field that meets a zero of the field is constant. -/
theorem timeDependentFlow_autonomous_eq_self {V : F → F} {C : ℝ≥0}
    (hV : LipschitzWith C (TauCeti.timeDependentSuspension fun _ : ℝ => V)) {x : F} {t₀ : ℝ}
    (h0 : V (TauCeti.timeDependentFlow (fun _ => V) hV 0 t₀ x) = 0) (t : ℝ) :
    TauCeti.timeDependentFlow (fun _ => V) hV 0 t x = x := by
  set p := TauCeti.timeDependentFlow (fun _ => V) hV 0 t₀ x with hp
  have hfix : ∀ u, TauCeti.timeDependentFlow (fun _ => V) hV t₀ u p = p := fun u =>
    DifferentialTopology.timeDependentEvolution_eq_of_forall_zero (fun _ => V) hV
      (fun _ => h0) t₀ u
  have hx : p = x := by
    have h := TauCeti.timeDependentFlow_trans (fun _ => V) hV 0 t₀ 0 x
    rw [← hp, hfix, TauCeti.timeDependentFlow_self] at h
    exact h
  have h := TauCeti.timeDependentFlow_trans (fun _ => V) hV 0 t₀ t x
  rw [← hp, hfix] at h
  rw [← h, hx]

/-- A function whose derivative annihilates an autonomous field wherever the field does not
vanish is constant along every trajectory. -/
theorem apply_timeDependentFlow_autonomous {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {V : F → F} {C : ℝ≥0}
    (hV : LipschitzWith C (TauCeti.timeDependentSuspension fun _ : ℝ => V)) (f : F → G)
    (hf : ∀ z, V z ≠ 0 → ∃ L : F →L[ℝ] G, HasFDerivAt f L z ∧ L (V z) = 0) (t : ℝ) (x : F) :
    f (TauCeti.timeDependentFlow (fun _ => V) hV 0 t x) = f x := by
  by_cases h : ∃ t₀, V (TauCeti.timeDependentFlow (fun _ => V) hV 0 t₀ x) = 0
  · obtain ⟨t₀, h0⟩ := h
    rw [timeDependentFlow_autonomous_eq_self hV h0]
  · push Not at h
    have hd : ∀ u, HasDerivAt (fun u => f (TauCeti.timeDependentFlow (fun _ => V) hV 0 u x))
        0 u := by
      intro u
      obtain ⟨L, hL, hLV⟩ := hf _ (h u)
      have := hL.comp_hasDerivAt u (TauCeti.hasDerivAt_timeDependentFlow (fun _ => V) hV 0 u x)
      rwa [hLV] at this
    have hc := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t 0
    simpa only [TauCeti.timeDependentFlow_self] using hc

end Flow

section Ball

/-- The vector `(-∂₁ f, ∂₀ f)` built from the complex partial derivatives of a function on the
Euclidean plane. It lies in the kernel of the complex differential of `f`. -/
def euclideanKernelVector (f : EuclideanSpace ℂ (Fin 2) → ℂ) (z : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Fin 2) :=
  (-fderiv ℂ f z (EuclideanSpace.single 1 1)) • EuclideanSpace.single 0 1 +
    fderiv ℂ f z (EuclideanSpace.single 0 1) • EuclideanSpace.single 1 1

/-- The Hermitian product `⟨z, w⟩` of the position vector with the kernel vector `w`. -/
def euclideanKernelPairing (f : EuclideanSpace ℂ (Fin 2) → ℂ) (z : EuclideanSpace ℂ (Fin 2)) :
    ℂ :=
  inner ℂ z (euclideanKernelVector f z)

/-- The field `-w / (2 ⟨z, w⟩)`, where `w` is the kernel vector. Where the pairing does not
vanish, it lies in the kernel of the differential of `f` and decreases the squared norm at unit
speed. -/
def euclideanRadialField (f : EuclideanSpace ℂ (Fin 2) → ℂ) (z : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Fin 2) :=
  (-(2 * euclideanKernelPairing f z)⁻¹) • euclideanKernelVector f z

/-- On the Euclidean plane, the real inner product is the real part of the Hermitian one. -/
theorem real_inner_euclidean (z v : EuclideanSpace ℂ (Fin 2)) :
    inner ℝ z v = (inner ℂ z v).re := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, Complex.inner]

/-- The kernel vector lies in the kernel of the complex differential. -/
theorem fderiv_euclideanKernelVector (f : EuclideanSpace ℂ (Fin 2) → ℂ)
    (z : EuclideanSpace ℂ (Fin 2)) : fderiv ℂ f z (euclideanKernelVector f z) = 0 := by
  simp only [euclideanKernelVector, map_add, map_smul, smul_eq_mul]
  ring

/-- The radial field lies in the kernel of the complex differential. -/
theorem fderiv_euclideanRadialField (f : EuclideanSpace ℂ (Fin 2) → ℂ)
    (z : EuclideanSpace ℂ (Fin 2)) : fderiv ℂ f z (euclideanRadialField f z) = 0 := by
  rw [euclideanRadialField, map_smul, fderiv_euclideanKernelVector, smul_zero]

/-- Where the pairing does not vanish, the radial field decreases the squared norm at unit
speed. -/
theorem two_mul_inner_euclideanRadialField {f : EuclideanSpace ℂ (Fin 2) → ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (hz : euclideanKernelPairing f z ≠ 0) :
    2 * inner ℝ z (euclideanRadialField f z) = -1 := by
  rw [real_inner_euclidean, euclideanRadialField, inner_smul_right,
    ← euclideanKernelPairing]
  have h : -(2 * euclideanKernelPairing f z)⁻¹ * euclideanKernelPairing f z = -(1 / 2) := by
    field_simp
  rw [h]
  norm_num

/-- If the function together with the squared norm is a submersion at `z`, then the pairing
of `z` with the kernel vector does not vanish. -/
theorem euclideanKernelPairing_ne_zero {f : EuclideanSpace ℂ (Fin 2) → ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} (hf : DifferentiableAt ℂ f z)
    (hs : Surjective (fderiv ℝ (fun z => (f z, ‖z‖ ^ 2)) z)) :
    euclideanKernelPairing f z ≠ 0 := by
  intro hD
  have hP : HasFDerivAt (fun z => (f z, ‖z‖ ^ 2))
      (((fderiv ℂ f z).restrictScalars ℝ).prod (2 • innerSL ℝ z)) z :=
    (hf.hasFDerivAt.restrictScalars ℝ).prodMk (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  rw [hP.fderiv] at hs
  obtain ⟨u, hu⟩ := hs (1, 0)
  obtain ⟨v, hv⟩ := hs (0, 1)
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_restrictScalars',
    smul_apply, innerSL_apply_apply, Prod.mk.injEq, nsmul_eq_mul,
    Nat.cast_ofNat] at hu hv
  set a := fderiv ℂ f z (EuclideanSpace.single 0 1)
  set b := fderiv ℂ f z (EuclideanSpace.single 1 1)
  have hL : ∀ w : EuclideanSpace ℂ (Fin 2), fderiv ℂ f z w = w 0 * a + w 1 * b := by
    intro w
    have hw : w = w 0 • EuclideanSpace.single 0 1 + w 1 • EuclideanSpace.single 1 1 := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [hw]
    simp only [map_add, map_smul, smul_eq_mul, a, b]
  have hinner : inner ℂ z v = conj (z 0) * v 0 + conj (z 1) * v 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  have hD' : -b * conj (z 0) + a * conj (z 1) = 0 := by
    simpa [euclideanKernelPairing, euclideanKernelVector, inner_add_right, inner_smul_right,
      EuclideanSpace.inner_single_right, a, b] using hD
  have hv0 : v 0 * a + v 1 * b = 0 := by rw [← hL]; exact hv.1
  have hP0 : inner ℂ z v ≠ 0 := by
    intro h
    have h2 := hv.2
    rw [real_inner_euclidean, h] at h2
    simp at h2
  have ha : a * inner ℂ z v = 0 := by
    rw [hinner]
    linear_combination conj (z 0) * hv0 + v 1 * hD'
  have hb : b * inner ℂ z v = 0 := by
    rw [hinner]
    linear_combination conj (z 1) * hv0 - v 0 * hD'
  have ha0 : a = 0 := (mul_eq_zero.mp ha).resolve_right hP0
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right hP0
  have hu1 := hu.1
  rw [hL, ha0, hb0] at hu1
  simp at hu1

/-- The kernel vector is smooth at every point where the function is analytic. -/
theorem contDiffAt_euclideanKernelVector {f : EuclideanSpace ℂ (Fin 2) → ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} {n : WithTop ℕ∞} (hf : AnalyticAt ℂ f z) :
    ContDiffAt ℝ n (euclideanKernelVector f) z := by
  have hd : ∀ v : EuclideanSpace ℂ (Fin 2), ContDiffAt ℝ n (fun z => fderiv ℂ f z v) z :=
    fun v => (hf.fderiv.contDiffAt.clm_apply contDiffAt_const).restrict_scalars ℝ
  exact ((hd _).neg.smul contDiffAt_const).add ((hd _).smul contDiffAt_const)

/-- The pairing is smooth at every point where the function is analytic. -/
theorem contDiffAt_euclideanKernelPairing {f : EuclideanSpace ℂ (Fin 2) → ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} {n : WithTop ℕ∞} (hf : AnalyticAt ℂ f z) :
    ContDiffAt ℝ n (euclideanKernelPairing f) z :=
  contDiffAt_id.inner ℂ (contDiffAt_euclideanKernelVector hf)

/-- The radial field is smooth at every point where the function is analytic and the pairing
does not vanish. -/
theorem contDiffAt_euclideanRadialField {f : EuclideanSpace ℂ (Fin 2) → ℂ}
    {z : EuclideanSpace ℂ (Fin 2)} {n : WithTop ℕ∞} (hf : AnalyticAt ℂ f z)
    (hz : euclideanKernelPairing f z ≠ 0) :
    ContDiffAt ℝ n (euclideanRadialField f) z :=
  ((contDiffAt_const.mul (contDiffAt_euclideanKernelPairing hf)).inv
    (mul_ne_zero two_ne_zero hz)).neg.smul (contDiffAt_euclideanKernelVector hf)

end Ball

section BallCollar

/-- **Ball collar.** Suppose that the equation is analytic on the closed ball of radius `ε` and
that the equation together with the squared norm is a submersion at every point of the closed
annulus `ε₁ ≤ ‖z‖ ≤ ε` at which the equation has modulus less than `c`. Then, for every level
`s` with `‖s‖ < c`, the inclusion of the Milnor fibre of radius `ε₁` into the Milnor fibre of
radius `ε` is a homotopy equivalence. -/
theorem milnorFibre_collar_of_transverse (H : Source 2 → ℂ) {ε ε₁ c : ℝ} (hε₁ : 0 ≤ ε₁)
    (hε₁ε : ε₁ ≤ ε)
    (han : ∀ z : EuclideanSpace ℂ (Fin 2), ‖z‖ ≤ ε → AnalyticAt ℂ (euclideanEquation H) z)
    (htr : ∀ z : EuclideanSpace ℂ (Fin 2), ε₁ ≤ ‖z‖ → ‖z‖ ≤ ε →
      ‖euclideanEquation H z‖ < c → Surjective (fderiv ℝ (radialPair H) z))
    (s : ℂ) (hs : ‖s‖ < c) :
    ∃ e : ContinuousMap.HomotopyEquiv (milnorFibre H ε₁ s) (milnorFibre H ε s),
      ∀ z, ((e.toFun z : milnorFibre H ε s) : EuclideanSpace ℂ (Fin 2)) = z := by
  set E := euclideanEquation H with hEdef
  let U : Set (EuclideanSpace ℂ (Fin 2)) :=
    {z | AnalyticAt ℂ E z} ∩ euclideanKernelPairing E ⁻¹' {0}ᶜ
  have hUo : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_analyticAt ℂ E) isOpen_compl_singleton
    intro z hz
    exact (contDiffAt_euclideanKernelPairing (n := 0) hz).continuousAt.continuousWithinAt
  let K : Set (EuclideanSpace ℂ (Fin 2)) :=
    (closedBall 0 ε ∩ E ⁻¹' {s}) ∩ {z | ε₁ ≤ ‖z‖}
  have hKc : IsCompact K := by
    have hEc : ContinuousOn E (closedBall 0 ε) := fun z hz =>
      (han z (mem_closedBall_zero_iff.mp hz)).continuousAt.continuousWithinAt
    refine (isCompact_closedBall 0 ε).of_isClosed_subset ?_
      (inter_subset_left.trans inter_subset_left)
    exact (hEc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton).inter
      (isClosed_le continuous_const continuous_norm)
  have hKU : K ⊆ U := by
    rintro z ⟨⟨hzε, hzs⟩, hz₁⟩
    have hzε' : ‖z‖ ≤ ε := mem_closedBall_zero_iff.mp hzε
    have hzs' : E z = s := hzs
    refine ⟨han z hzε', euclideanKernelPairing_ne_zero (han z hzε').differentiableAt ?_⟩
    exact htr z hz₁ hzε' (by rw [hzs']; exact hs)
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχK⟩ := exists_contDiff_cutoff hKc hUo hKU
  let V : EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) :=
    fun z => χ z • euclideanRadialField E z
  have hV : ContDiff ℝ 1 V :=
    contDiff_smul_of_tsupport (hχ.of_le (by exact_mod_cast le_top))
      (fun z hz => contDiffAt_euclideanRadialField (hχU hz).1 (hχU hz).2)
  have hVc : HasCompactSupport V := hχc.smul_right
  obtain ⟨C, hC⟩ := exists_lipschitz_autonomousSuspension hV hVc
  let φ : ℝ → EuclideanSpace ℂ (Fin 2) → EuclideanSpace ℂ (Fin 2) :=
    fun t x => TauCeti.timeDependentFlow (fun _ => V) hC 0 t x
  have hφc : Continuous fun p : ℝ × EuclideanSpace ℂ (Fin 2) => φ p.1 p.2 :=
    (TauCeti.continuous_timeDependentFlow _ hC).comp
      (by fun_prop : Continuous fun p : ℝ × EuclideanSpace ℂ (Fin 2) => (((0 : ℝ), p.1), p.2))
  have hφ0 : ∀ x, φ 0 x = x := fun x => TauCeti.timeDependentFlow_self _ hC 0 x
  -- the equation is constant along trajectories
  have hEφ : ∀ t x, E (φ t x) = E x := by
    intro t x
    refine apply_timeDependentFlow_autonomous hC E (fun z hz => ?_) t x
    have hχz : χ z ≠ 0 := fun h0 => hz (by simp [V, h0])
    have hzU := hχU (subset_tsupport _ hχz)
    refine ⟨(fderiv ℂ E z).restrictScalars ℝ,
      hzU.1.differentiableAt.hasFDerivAt.restrictScalars ℝ, ?_⟩
    simp [V, fderiv_euclideanRadialField]
  -- the squared norm decreases at rate `χ`
  have hVr : ∀ z, 2 * inner ℝ z (V z) = -χ z := by
    intro z
    by_cases hχz : χ z = 0
    · simp [V, hχz]
    · have hzU := hχU (subset_tsupport _ hχz)
      rw [real_inner_smul_right, mul_left_comm, two_mul_inner_euclideanRadialField hzU.2,
        mul_neg_one]
  have hN : ∀ x t, HasDerivAt (fun t => ‖φ t x‖ ^ 2) (-χ (φ t x)) t := by
    intro x t
    have h := (TauCeti.hasDerivAt_timeDependentFlow (fun _ => V) hC 0 t x).norm_sq
    rwa [hVr] at h
  have hanti : ∀ x, Antitone fun t => ‖φ t x‖ ^ 2 := fun x =>
    antitone_of_deriv_nonpos (fun t => (hN x t).differentiableAt)
      (fun t => by rw [(hN x t).deriv]; linarith [(hχ01 (φ t x)).1])
  have hN' : ∀ x t, HasDerivAt (fun t => ‖φ t x‖ ^ 2 + t) (-χ (φ t x) + 1) t :=
    fun x t => (hN x t).add (hasDerivAt_id' t)
  have hmono : ∀ x, Monotone fun t => ‖φ t x‖ ^ 2 + t := fun x =>
    monotone_of_deriv_nonneg (fun t => (hN' x t).differentiableAt)
      (fun t => by rw [(hN' x t).deriv]; linarith [(hχ01 (φ t x)).2])
  have hnorm_le : ∀ x, ∀ t, 0 ≤ t → ‖φ t x‖ ≤ ‖x‖ := by
    intro x t ht
    have h := hanti x ht
    simp only [hφ0] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  -- the collar time
  let T : EuclideanSpace ℂ (Fin 2) → ℝ := fun x => max 0 (‖x‖ ^ 2 - ε₁ ^ 2)
  refine exists_homotopyEquiv_of_flow φ hφc hφ0 (milnorFibre_mono H hε₁ε s) T
    (Continuous.continuousOn (by fun_prop)) (fun x _ => le_max_left _ _) ?_ ?_ ?_
  · intro x hx
    exact max_eq_left (sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg _) hx.1 2))
  · intro x hx t ht _
    exact ⟨(hnorm_le x t ht).trans hx.1, (hEφ t x).trans hx.2⟩
  · intro x hx
    by_cases hx₁ : ‖x‖ ≤ ε₁
    · have hT : T x = 0 := max_eq_left (sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg _) hx₁ 2))
      rw [hT, hφ0]
      exact ⟨hx₁, hx.2⟩
    push Not at hx₁
    have hTx : T x = ‖x‖ ^ 2 - ε₁ ^ 2 :=
      max_eq_right (sub_nonneg.mpr (pow_le_pow_left₀ hε₁ hx₁.le 2))
    have hK : ∀ t ∈ Icc 0 (T x), φ t x ∈ K := by
      rintro t ⟨ht0, htT⟩
      refine ⟨⟨mem_closedBall_zero_iff.mpr ((hnorm_le x t ht0).trans hx.1), ?_⟩, ?_⟩
      · exact (hEφ t x).trans hx.2
      · have h := hmono x ht0
        simp only [hφ0, add_zero] at h
        have h2 : ε₁ ^ 2 ≤ ‖φ t x‖ ^ 2 := by linarith
        exact (pow_le_pow_iff_left₀ hε₁ (norm_nonneg _) two_ne_zero).mp h2
    have hd : ∀ t ∈ Icc 0 (T x), HasDerivAt (fun t => ‖φ t x‖ ^ 2 + t) 0 t := by
      intro t ht
      have h := hN' x t
      rwa [hχK _ (hK t ht), neg_add_cancel] at h
    have hconst := constant_of_has_deriv_right_zero
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (T x)
      ⟨le_max_left _ _, le_rfl⟩
    simp only [hφ0, add_zero] at hconst
    have h2 : ‖φ (T x) x‖ ^ 2 = ε₁ ^ 2 := by linarith
    refine ⟨?_, (hEφ _ x).trans hx.2⟩
    exact ((pow_left_inj₀ (norm_nonneg _) hε₁ two_ne_zero).mp h2).le

/-- **Collar of the Milnor fibre.** For every sufficiently small radius `ε` and every inner
radius `0 < ε₁ < ε` there is `δ > 0` such that, for every level `s` with `‖s‖ < δ`, the
inclusion of the Milnor fibre of radius `ε₁` over `s` into the Milnor fibre of radius `ε` over
`s` is a homotopy equivalence. -/
theorem exists_milnorFibre_collar (H : Source 2 → ℂ) (hH : AnalyticAt ℂ H 0) (hH0 : H 0 = 0)
    (hsq : Squarefree (ofFunction H hH)) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ ε₁, 0 < ε₁ → ε₁ < ε → ∃ δ > 0, ∀ s : ℂ, ‖s‖ < δ →
      ∃ e : ContinuousMap.HomotopyEquiv (milnorFibre H ε₁ s) (milnorFibre H ε s),
        ∀ z, ((e.toFun z : milnorFibre H ε s) : EuclideanSpace ℂ (Fin 2)) = z := by
  obtain ⟨ε₀, hε₀, han, htr⟩ := exists_radial_transverse_neighbourhood H hH hH0 hsq
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ ε₁ hε₁ hε₁ε => ?_⟩
  obtain ⟨c, hc, hsurj⟩ := htr ε hε hεε₀ ε₁ hε₁ hε₁ε.le
  refine ⟨c, hc, fun s hs => ?_⟩
  exact milnorFibre_collar_of_transverse H hε₁.le hε₁ε.le
    (fun z hz => (han z (by linarith)).1) hsurj s hs

end BallCollar

section PolydiscCollar

/-- The field `(∂₁H · z₁ / ∂₀H, -z₁)` on `ℂ²`. Where the fibre partial derivative does not
vanish, it lies in the kernel of the differential of `H` and contracts the base coordinate
radially at unit logarithmic speed. -/
def polydiscRadialField (H : Source 2 → ℂ) (z : Source 2) : Source 2 :=
  ![basePartial H z * z 1 / fibrePartial H z, -z 1]

/-- The base component of the polydisc field is `-z₁`. -/
theorem polydiscRadialField_one (H : Source 2 → ℂ) (z : Source 2) :
    polydiscRadialField H z 1 = -z 1 := by
  simp [polydiscRadialField]

/-- Where the fibre partial derivative does not vanish, the polydisc field lies in the kernel of
the complex differential. -/
theorem fderiv_polydiscRadialField {H : Source 2 → ℂ} {z : Source 2}
    (hz : fibrePartial H z ≠ 0) : fderiv ℂ H z (polydiscRadialField H z) = 0 := by
  have hv : polydiscRadialField H z =
      (basePartial H z * z 1 / fibrePartial H z) • Pi.single 0 1 + (-z 1) • Pi.single 1 1 := by
    ext i
    fin_cases i <;> simp [polydiscRadialField]
  rw [hv, map_add, map_smul, map_smul]
  change basePartial H z * z 1 / fibrePartial H z * fibrePartial H z +
    -z 1 * basePartial H z = 0
  field_simp
  ring

/-- The polydisc field is smooth at every point where `H` is analytic and the fibre partial
derivative does not vanish. -/
theorem contDiffAt_polydiscRadialField {H : Source 2 → ℂ} {z : Source 2} {n : WithTop ℕ∞}
    (hH : AnalyticAt ℂ H z) (hz : fibrePartial H z ≠ 0) :
    ContDiffAt ℝ n (polydiscRadialField H) z := by
  have hd : ∀ v : Source 2, ContDiffAt ℂ n (fun z => fderiv ℂ H z v) z :=
    fun v => hH.fderiv.contDiffAt.clm_apply contDiffAt_const
  refine ContDiffAt.restrict_scalars ℝ (𝕜' := ℂ) ?_
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · simp only [polydiscRadialField, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact ((hd _).mul (contDiff_apply ℂ ℂ 1).contDiffAt).div (hd _) hz
  · simp only [polydiscRadialField, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    exact (contDiff_apply ℂ ℂ 1).contDiffAt.neg

-- The positivity hypothesis `hc` follows from `hs` and is kept for the required interface.
set_option linter.unusedVariables false in
/-- **Polydisc collar.** Suppose that `H` is analytic on the polydisc
`{squareNorm (z 1) ≤ η₁, ‖z 0‖ ≤ ρ}`, that its fibre partial derivative does not vanish where
`η₂ ≤ squareNorm (z 1)` and `‖H z‖ ≤ c`, and that every point of the polydisc with `‖H z‖ ≤ c`
satisfies `‖z 0‖ < ρ'` for some `ρ' < ρ`. Then, for every level `s` with `‖s‖ < c`, the inclusion
of the polydisc fibre with base radius `η₂` into the polydisc fibre with base radius `η₁` is a
homotopy equivalence. -/
theorem polydiscFibre_collar (H : Source 2 → ℂ) {η₁ η₂ ρ ρ' c : ℝ}
    (hη₂ : 0 < η₂) (hη : η₂ < η₁) (hρ' : ρ' < ρ) (hc : 0 < c)
    (han : ∀ z : Source 2, squareNorm (z 1) ≤ η₁ → ‖z 0‖ ≤ ρ → AnalyticAt ℂ H z)
    (hpolar : ∀ z : Source 2, η₂ ≤ squareNorm (z 1) → squareNorm (z 1) ≤ η₁ → ‖z 0‖ ≤ ρ →
      ‖H z‖ ≤ c → fibrePartial H z ≠ 0)
    (hroot : ∀ z : Source 2, squareNorm (z 1) ≤ η₁ → ‖z 0‖ ≤ ρ → ‖H z‖ ≤ c → ‖z 0‖ < ρ')
    (s : ℂ) (hs : ‖s‖ < c) :
    ∃ e : ContinuousMap.HomotopyEquiv (polydiscFibre H η₂ ρ s) (polydiscFibre H η₁ ρ s),
      ∀ z, ((e.toFun z : polydiscFibre H η₁ ρ s) : Source 2) = z := by
  let U : Set (Source 2) := {z | AnalyticAt ℂ H z} ∩ fibrePartial H ⁻¹' {0}ᶜ
  have hUo : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_ (isOpen_analyticAt ℂ H) isOpen_compl_singleton
    intro z hz
    exact (hz.fderiv.continuousAt.clm_apply continuousAt_const).continuousWithinAt
  let A : Set (Source 2) := {z | squareNorm (z 1) ≤ η₁} ∩ {z | ‖z 0‖ ≤ ρ}
  have hAc : IsClosed A :=
    (isClosed_le (continuous_squareNorm.comp (continuous_apply 1)) continuous_const).inter
      (isClosed_le (continuous_norm.comp (continuous_apply 0)) continuous_const)
  let K : Set (Source 2) := (A ∩ H ⁻¹' {s}) ∩ {z | η₂ ≤ squareNorm (z 1)}
  have hKc : IsCompact K := by
    have hHc : ContinuousOn H A := fun z hz => (han z hz.1 hz.2).continuousAt.continuousWithinAt
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (hHc.preimage_isClosed_of_isClosed hAc isClosed_singleton).inter
        (isClosed_le continuous_const (continuous_squareNorm.comp (continuous_apply 1)))
    · refine (isBounded_iff_forall_norm_le.mpr ⟨max ρ (2 * η₁), fun z hz => ?_⟩)
      refine (pi_norm_le_iff_of_nonneg (le_max_of_le_right (by linarith))).mpr
        (Fin.forall_fin_two.mpr ⟨le_max_of_le_left hz.1.1.2, le_max_of_le_right ?_⟩)
      have h1 : squareNorm (z 1) ≤ η₁ := hz.1.1.1
      linarith [norm_le_two_mul_squareNorm (z 1)]
  have hKU : K ⊆ U := by
    rintro z ⟨⟨⟨hz1, hz0⟩, hzs⟩, hz2⟩
    have hzs' : H z = s := hzs
    exact ⟨han z hz1 hz0, hpolar z hz2 hz1 hz0 (by rw [hzs']; exact hs.le)⟩
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχK⟩ := exists_contDiff_cutoff hKc hUo hKU
  let V : Source 2 → Source 2 := fun z => χ z • polydiscRadialField H z
  have hV : ContDiff ℝ 1 V :=
    contDiff_smul_of_tsupport (hχ.of_le (by exact_mod_cast le_top))
      (fun z hz => contDiffAt_polydiscRadialField (hχU hz).1 (hχU hz).2)
  have hVc : HasCompactSupport V := hχc.smul_right
  obtain ⟨C, hC⟩ := exists_lipschitz_autonomousSuspension hV hVc
  let φ : ℝ → Source 2 → Source 2 := fun t x => TauCeti.timeDependentFlow (fun _ => V) hC 0 t x
  have hφc : Continuous fun p : ℝ × Source 2 => φ p.1 p.2 :=
    (TauCeti.continuous_timeDependentFlow _ hC).comp
      (by fun_prop : Continuous fun p : ℝ × Source 2 => (((0 : ℝ), p.1), p.2))
  have hφ0 : ∀ x, φ 0 x = x := fun x => TauCeti.timeDependentFlow_self _ hC 0 x
  -- the equation is constant along trajectories
  have hHφ : ∀ t x, H (φ t x) = H x := by
    intro t x
    refine apply_timeDependentFlow_autonomous hC H (fun z hz => ?_) t x
    have hχz : χ z ≠ 0 := fun h0 => hz (by simp [V, h0])
    have hzU := hχU (subset_tsupport _ hχz)
    refine ⟨(fderiv ℂ H z).restrictScalars ℝ,
      hzU.1.differentiableAt.hasFDerivAt.restrictScalars ℝ, ?_⟩
    simp [V, fderiv_polydiscRadialField hzU.2]
  -- the base coordinate is contracted at rate `χ`
  have hbase : ∀ x t, HasDerivAt (fun t => φ t x 1) (-(χ (φ t x) : ℂ) * φ t x 1) t := by
    intro x t
    have h := hasDerivAt_pi.mp (TauCeti.hasDerivAt_timeDependentFlow (fun _ => V) hC 0 t x) 1
    have hV1 : ∀ z, V z 1 = -(χ z : ℂ) * z 1 := by
      intro z
      simp [V, polydiscRadialField_one, Complex.real_smul]
    exact h.congr_deriv (hV1 _)
  have hχφ : ∀ x, Continuous fun u => χ (φ u x) := fun x =>
    hχ.continuous.comp (hφc.comp (by fun_prop : Continuous fun u : ℝ => (u, x)))
  let m : Source 2 → ℝ → ℝ := fun x t => ∫ u in (0 : ℝ)..t, χ (φ u x)
  have hm : ∀ x t, HasDerivAt (m x) (χ (φ t x)) t := fun x t =>
    ((hχφ x).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hm0 : ∀ x, m x 0 = 0 := fun x => intervalIntegral.integral_same
  have hm_nonneg : ∀ x t, 0 ≤ t → 0 ≤ m x t := by
    intro x t ht
    have hmono : Monotone (m x) := monotone_of_deriv_nonneg (fun t => (hm x t).differentiableAt)
      (fun t => by rw [(hm x t).deriv]; exact (hχ01 _).1)
    simpa [hm0] using hmono ht
  have hm' : ∀ x t, HasDerivAt (fun t => m x t - t) (χ (φ t x) - 1) t :=
    fun x t => (hm x t).sub (hasDerivAt_id' t)
  have hm_le : ∀ x t, 0 ≤ t → m x t ≤ t := by
    intro x t ht
    have hanti : Antitone fun t => m x t - t :=
      antitone_of_deriv_nonpos (fun t => (hm' x t).differentiableAt)
        (fun t => by rw [(hm' x t).deriv]; linarith [(hχ01 (φ t x)).2])
    have h := hanti ht
    simp only [hm0, sub_zero] at h
    linarith
  -- explicit solution for the base coordinate
  have hsol : ∀ x t, φ t x 1 = (Real.exp (-m x t) : ℂ) * x 1 := by
    intro x t
    have hq : ∀ u, HasDerivAt (fun u => (Real.exp (m x u) : ℂ) * φ u x 1) 0 u := by
      intro u
      have he := ((hm x u).exp).ofReal_comp
      refine (he.mul (hbase x u)).congr_deriv ?_
      push_cast
      ring
    have hc := is_const_of_deriv_eq_zero (fun u => (hq u).differentiableAt)
      (fun u => (hq u).deriv) t 0
    simp only [hm0, Real.exp_zero, Complex.ofReal_one, one_mul, hφ0] at hc
    rw [← hc, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      Complex.ofReal_one, one_mul]
  have hsq : ∀ x t, squareNorm (φ t x 1) = Real.exp (-m x t) * squareNorm (x 1) := by
    intro x t
    rw [hsol, squareNorm_smul_of_nonneg (Real.exp_pos _).le]
  have hsq_le : ∀ x t, 0 ≤ t → squareNorm (φ t x 1) ≤ squareNorm (x 1) := by
    intro x t ht
    rw [hsq]
    exact mul_le_of_le_one_left (squareNorm_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hm_nonneg x t ht)))
  -- the fibre coordinate stays inside the polydisc
  have hfibre : ∀ x ∈ polydiscFibre H η₁ ρ s, ∀ t, 0 ≤ t → ‖φ t x 0‖ ≤ ρ := by
    intro x hx t ht
    by_contra hlt
    push Not at hlt
    have hx0 : ‖x 0‖ < ρ' := hroot x hx.1 hx.2.1 (by rw [hx.2.2]; exact hs.le)
    have hcont : ContinuousOn (fun u => ‖φ u x 0‖) (Icc 0 t) :=
      (continuous_norm.comp ((continuous_apply 0).comp
        (hφc.comp (by fun_prop : Continuous fun u : ℝ => (u, x))))).continuousOn
    obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc ht hcont
      ⟨by simp only [hφ0]; exact hx0.le, (hρ'.trans hlt).le⟩
    have hu' : ‖φ u x 0‖ = ρ' := hu'
    have hu1 : squareNorm (φ u x 1) ≤ η₁ := (hsq_le x u hu.1).trans hx.1
    have hHu : ‖H (φ u x)‖ ≤ c := by rw [hHφ, hx.2.2]; exact hs.le
    have h := hroot (φ u x) hu1 (by rw [hu']; exact hρ'.le) hHu
    rw [hu'] at h
    exact lt_irrefl _ h
  -- the collar time
  let T : Source 2 → ℝ := fun x => Real.log (max η₂ (squareNorm (x 1))) - Real.log η₂
  have hTc : Continuous T :=
    ((continuous_const.max (continuous_squareNorm.comp (continuous_apply 1))).log
      (fun x => (hη₂.trans_le (le_max_left _ _)).ne')).sub continuous_const
  refine exists_homotopyEquiv_of_flow φ hφc hφ0 (polydiscFibre_mono H hη.le ρ s) T
    hTc.continuousOn (fun x _ => sub_nonneg.mpr (Real.log_le_log hη₂ (le_max_left _ _)))
    ?_ ?_ ?_
  · intro x hx
    simp only [T, max_eq_left hx.1, sub_self]
  · intro x hx t ht _
    exact ⟨(hsq_le x t ht).trans hx.1, hfibre x hx t ht, (hHφ t x).trans hx.2.2⟩
  · intro x hx
    by_cases hx₂ : squareNorm (x 1) ≤ η₂
    · have hT : T x = 0 := by simp only [T, max_eq_left hx₂, sub_self]
      rw [hT, hφ0]
      exact ⟨hx₂, hx.2.1, hx.2.2⟩
    push Not at hx₂
    have hpos : 0 < squareNorm (x 1) := hη₂.trans hx₂
    have hTx : T x = Real.log (squareNorm (x 1)) - Real.log η₂ := by
      simp only [T, max_eq_right hx₂.le]
    have hexpT : Real.exp (-T x) * squareNorm (x 1) = η₂ := by
      rw [hTx, neg_sub, Real.exp_sub, Real.exp_log hη₂, Real.exp_log hpos]
      field_simp
    have hK : ∀ t ∈ Icc 0 (T x), φ t x ∈ K := by
      rintro t ⟨ht0, htT⟩
      refine ⟨⟨⟨(hsq_le x t ht0).trans hx.1, hfibre x hx t ht0⟩, (hHφ t x).trans hx.2.2⟩, ?_⟩
      change η₂ ≤ squareNorm (φ t x 1)
      rw [hsq, ← hexpT]
      gcongr
      linarith [hm_le x t ht0]
    have hd : ∀ t ∈ Icc 0 (T x), HasDerivAt (fun t => m x t - t) 0 t := by
      intro t ht
      have h := hm' x t
      rwa [hχK _ (hK t ht), sub_self] at h
    have hconst := constant_of_has_deriv_right_zero
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (T x)
      ⟨sub_nonneg.mpr (Real.log_le_log hη₂ (le_max_left _ _)), le_rfl⟩
    simp only [hm0, sub_zero] at hconst
    have hmT : m x (T x) = T x := by linarith
    refine ⟨?_, hfibre x hx _ (hTx ▸ sub_nonneg.mpr (Real.log_le_log hη₂ hx₂.le)),
      (hHφ _ x).trans hx.2.2⟩
    change squareNorm (φ (T x) x 1) ≤ η₂
    rw [hsq, hmT, hexpT]

end PolydiscCollar

end OnLeConjecture.Analytic
