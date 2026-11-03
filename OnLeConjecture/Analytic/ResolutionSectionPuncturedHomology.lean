/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ResolutionSectionExteriorHypotheses
public import OnLeConjecture.DifferentialTopology.DiscreteHomotopyModel
public import OnLeConjecture.DifferentialTopology.RationalMayerVietorisComplement
public import Mathlib.Analysis.Complex.Convex

/-!
# Rational homology of the punctured section

Let `K` be a subset of the level set `{f = s}` of a function `f : ℂ² → ℂ`, and let
`D j`, `j ∈ ι`, be finitely many coordinate disks (`PlaneLevelCoordinateDisk f s`) whose
closed disks lie in `K` and are pairwise disjoint. If `K` has curve homology with Euler
characteristic `χ`, then `K \ ⋃ j, (D j).openDisk` has curve homology with Euler
characteristic `χ − #ι` (`hasCurveRatHomology_diff_iUnion_openDisk`). Applied to the
target cut and the coordinate disks of a level `L` with `L.ExteriorHypotheses D ε`, this
computes the rational homology of the punctured section `L.diskExterior D ε`
(`ResolutionSectionLevel.ExteriorHypotheses.hasCurveRatHomology_diskExterior`).

Write `r_j` for the radius of `D j`, `ψ_j` for its parametrization and `w_j` for its
chart coordinate. The proof covers `K` by the relatively open sets
`U = K \ ⋃ j, ψ_j(closedBall 0 (r_j / 2))` and `V = ⋃ j, (D j).openDisk`.

* `V` is a disjoint union of `#ι` open disks, so it has the homology of `#ι` points.
* `U ∩ V` is the disjoint union of the annuli `ψ_j {r_j / 2 < ‖w‖ < r_j}`. Each
  annulus is covered by the slit annuli `{w ∉ (-∞, 0]}` and `{w ∉ [0, ∞)}`, which are
  homeomorphic to convex rectangles through `Complex.exp`. Their intersection is the
  disjoint union of the upper and the lower half annulus. The Mayer–Vietoris count
  gives `U ∩ V` curve homology with Euler characteristic `#ι + #ι − 2 #ι = 0`.
* The Mayer–Vietoris count for one open piece gives `U` curve homology with Euler
  characteristic `χ + 0 − #ι`.
* The punctured set `E = K \ ⋃ j, (D j).openDisk` is a deformation retract of `U`.
  The homotopy fixes `E` and pushes `ψ_j(w)` with `r_j / 2 < ‖w‖ ≤ r_j` to
  `ψ_j(((1 − t) + t r_j / ‖w‖) w)`.
-/

@[expose] public noncomputable section

open Set Metric Function
open scoped Topology Real unitInterval

namespace OnLeConjecture.DifferentialTopology

/-- Let `Y` be a subset of a topological space `Z`, covered by finitely many pairwise
disjoint subsets `C c = Y ∩ O c` with `O c` open in `Z`, each of which is a
contractible space. Then `Y` has the rational homology of `#κ` points. -/
theorem hasDiscreteRatHomology_of_disjoint_contractible_subsets {Z : Type}
    [TopologicalSpace Z] {κ : Type} [Fintype κ] {Y : Set Z} (C O : κ → Set Z)
    (hO : ∀ c, IsOpen (O c)) (hC : ∀ c, C c = Y ∩ O c) (hdisj : Pairwise (Disjoint on C))
    (hcover : Y ⊆ ⋃ c, C c) (hcontr : ∀ c, ContractibleSpace ↥(C c)) :
    HasDiscreteRatHomology ↥Y (Fintype.card κ) := by
  let e := Fintype.equivFin κ
  let C' : Fin (Fintype.card κ) → Set Y := fun i => Subtype.val ⁻¹' C (e.symm i)
  have hCY : ∀ c, C c ⊆ Y := fun c => (hC c) ▸ inter_subset_left
  obtain ⟨h⟩ := nonempty_homotopyEquiv_fin_of_disjoint_contractible C'
    (fun i => isOpen_preimage_val_of_eq_inter (hO _) (hC _))
    (fun i j hij => (hdisj (e.symm.injective.ne hij)).preimage _)
    (eq_univ_of_forall fun y => by
      obtain ⟨c, hc⟩ := mem_iUnion.1 (hcover y.2)
      exact mem_iUnion.2 ⟨e c, by simpa [C'] using hc⟩)
    (fun i => have := hcontr (e.symm i)
      (homeomorphSubtypePreimageVal (hCY (e.symm i))).contractibleSpace)
  exact hasDiscreteRatHomology_of_homotopyEquiv_fin h

end OnLeConjecture.DifferentialTopology

namespace OnLeConjecture.Analytic

open OnLeConjecture.DifferentialTopology

section ComplexModels

/-- The open annulus `{u ∈ ℂ | r / 2 < ‖u‖ < r}`. -/
def coordinateAnnulus (r : ℝ) : Set ℂ := {u | r / 2 < ‖u‖ ∧ ‖u‖ < r}

/-- The annulus `coordinateAnnulus r` without the nonpositive real axis. -/
def slitAnnulus (r : ℝ) : Set ℂ := coordinateAnnulus r ∩ Complex.slitPlane

/-- The annulus `coordinateAnnulus r` without the nonnegative real axis. -/
def negSlitAnnulus (r : ℝ) : Set ℂ := {u | -u ∈ slitAnnulus r}

/-- The points of `coordinateAnnulus r` with positive imaginary part. -/
def upperAnnulus (r : ℝ) : Set ℂ := coordinateAnnulus r ∩ {u | 0 < u.im}

/-- The points of `coordinateAnnulus r` with negative imaginary part. -/
def lowerAnnulus (r : ℝ) : Set ℂ := {u | -u ∈ upperAnnulus r}

/-- The open rectangle with real parts in `(a, b)` and imaginary parts in `(c, d)`. -/
def complexRect (a b c d : ℝ) : Set ℂ := {z | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

variable {r : ℝ}

theorem mem_coordinateAnnulus {u : ℂ} :
    u ∈ coordinateAnnulus r ↔ r / 2 < ‖u‖ ∧ ‖u‖ < r :=
  Iff.rfl

theorem neg_mem_coordinateAnnulus {u : ℂ} :
    -u ∈ coordinateAnnulus r ↔ u ∈ coordinateAnnulus r := by
  simp only [mem_coordinateAnnulus, norm_neg]

theorem isOpen_coordinateAnnulus (r : ℝ) : IsOpen (coordinateAnnulus r) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem coordinateAnnulus_subset_ball (r : ℝ) : coordinateAnnulus r ⊆ ball 0 r :=
  fun _ hu => mem_ball_zero_iff.2 hu.2

theorem norm_pos_of_mem_coordinateAnnulus {u : ℂ} (hu : u ∈ coordinateAnnulus r) :
    0 < ‖u‖ := by
  have := hu.1
  have := hu.2
  linarith [norm_nonneg u]

theorem slitAnnulus_subset (r : ℝ) : slitAnnulus r ⊆ coordinateAnnulus r :=
  inter_subset_left

theorem negSlitAnnulus_subset (r : ℝ) : negSlitAnnulus r ⊆ coordinateAnnulus r :=
  fun _ hu => neg_mem_coordinateAnnulus.1 hu.1

theorem upperAnnulus_subset (r : ℝ) : upperAnnulus r ⊆ coordinateAnnulus r :=
  inter_subset_left

theorem lowerAnnulus_subset (r : ℝ) : lowerAnnulus r ⊆ coordinateAnnulus r :=
  fun _ hu => neg_mem_coordinateAnnulus.1 hu.1

theorem isOpen_slitAnnulus (r : ℝ) : IsOpen (slitAnnulus r) :=
  (isOpen_coordinateAnnulus r).inter Complex.isOpen_slitPlane

theorem isOpen_negSlitAnnulus (r : ℝ) : IsOpen (negSlitAnnulus r) :=
  (isOpen_slitAnnulus r).preimage continuous_neg

theorem isOpen_upperAnnulus (r : ℝ) : IsOpen (upperAnnulus r) :=
  (isOpen_coordinateAnnulus r).inter (isOpen_lt continuous_const Complex.continuous_im)

theorem isOpen_lowerAnnulus (r : ℝ) : IsOpen (lowerAnnulus r) :=
  (isOpen_upperAnnulus r).preimage continuous_neg

/-- Every point of the annulus lies in one of the two slit annuli. -/
theorem coordinateAnnulus_subset_union (r : ℝ) :
    coordinateAnnulus r ⊆ slitAnnulus r ∪ negSlitAnnulus r := by
  intro u hu
  have hu0 : u ≠ 0 := norm_pos_iff.1 (norm_pos_of_mem_coordinateAnnulus hu)
  by_cases him : u.im = 0
  · rcases lt_or_gt_of_ne (fun hre : u.re = 0 => hu0 (Complex.ext hre him)) with hre | hre
    · refine Or.inr ⟨neg_mem_coordinateAnnulus.2 hu, ?_⟩
      exact Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hre))
    · exact Or.inl ⟨hu, Complex.mem_slitPlane_iff.2 (Or.inl hre)⟩
  · exact Or.inl ⟨hu, Complex.mem_slitPlane_iff.2 (Or.inr him)⟩

/-- The two slit annuli meet in the union of the upper and the lower half annulus. -/
theorem slitAnnulus_inter_negSlitAnnulus (r : ℝ) :
    slitAnnulus r ∩ negSlitAnnulus r = upperAnnulus r ∪ lowerAnnulus r := by
  ext u
  simp only [slitAnnulus, negSlitAnnulus, upperAnnulus, lowerAnnulus, mem_inter_iff,
    mem_union, mem_ofPred_eq, neg_mem_coordinateAnnulus, Complex.mem_slitPlane_iff,
    Complex.neg_re, Complex.neg_im]
  constructor
  · rintro ⟨⟨hu, h₁⟩, -, h₂⟩
    rcases lt_trichotomy u.im 0 with h | h | h
    · exact Or.inr ⟨hu, by linarith⟩
    · rcases h₁ with h₁ | h₁
      · rcases h₂ with h₂ | h₂
        · linarith
        · exact absurd (by rw [h, neg_zero]) h₂
      · exact absurd h h₁
    · exact Or.inl ⟨hu, h⟩
  · rintro (⟨hu, h⟩ | ⟨hu, h⟩)
    · exact ⟨⟨hu, Or.inr h.ne'⟩, hu, Or.inr (by linarith)⟩
    · exact ⟨⟨hu, Or.inr (by linarith)⟩, hu, Or.inr h.ne'⟩

theorem disjoint_upperAnnulus_lowerAnnulus (r : ℝ) :
    Disjoint (upperAnnulus r) (lowerAnnulus r) := by
  rw [Set.disjoint_left]
  rintro u ⟨-, h₁⟩ ⟨-, h₂⟩
  simp only [mem_ofPred_eq, Complex.neg_im] at h₁ h₂
  linarith

theorem convex_complexRect (a b c d : ℝ) : Convex ℝ (complexRect a b c d) := by
  have : complexRect a b c d =
      ({z : ℂ | a < z.re} ∩ {z | z.re < b}) ∩ ({z | c < z.im} ∩ {z | z.im < d}) := by
    ext z
    simp [complexRect, and_assoc]
  rw [this]
  exact ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).inter
    ((convex_halfSpace_im_gt c).inter (convex_halfSpace_im_lt d))

theorem nonempty_complexRect {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    (complexRect a b c d).Nonempty := by
  refine ⟨⟨(a + b) / 2, (c + d) / 2⟩, ?_⟩
  change a < (a + b) / 2 ∧ (a + b) / 2 < b ∧ c < (c + d) / 2 ∧ (c + d) / 2 < d
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The image under `Complex.exp` of a nonempty convex subset of the strip
`-π < Im z < π` is a contractible space. -/
theorem contractibleSpace_exp_image {S : Set ℂ} (hS : S ⊆ {z : ℂ | z.im ∈ Ioo (-π) π})
    (hconv : Convex ℝ S) (hne : S.Nonempty) : ContractibleSpace ↥(Complex.exp '' S) := by
  obtain ⟨x, hx⟩ := hne
  exact contractibleSpace_of_homeomorph_starConvex
    (Complex.expOpenPartialHomeomorph.homeomorphOfImageSubsetSource hS rfl).symm
    (hconv.starConvex hx) ⟨x, hx⟩

theorem exp_mem_coordinateAnnulus (hr : 0 < r) {z : ℂ} (h₁ : Real.log (r / 2) < z.re)
    (h₂ : z.re < Real.log r) : Complex.exp z ∈ coordinateAnnulus r := by
  rw [mem_coordinateAnnulus, Complex.norm_exp]
  exact ⟨(Real.log_lt_iff_lt_exp (by positivity)).1 h₁, (Real.lt_log_iff_exp_lt hr).1 h₂⟩

theorem log_re_mem_of_mem_coordinateAnnulus {u : ℂ} (hu : u ∈ coordinateAnnulus r) :
    Real.log (r / 2) < (Complex.log u).re ∧ (Complex.log u).re < Real.log r := by
  have hr : 0 < r / 2 := by
    have := hu.1
    have := hu.2
    linarith [norm_nonneg u]
  rw [Complex.log_re]
  exact ⟨Real.log_lt_log hr hu.1, Real.log_lt_log (norm_pos_of_mem_coordinateAnnulus hu) hu.2⟩

theorem slitAnnulus_eq_exp_image (hr : 0 < r) :
    slitAnnulus r = Complex.exp '' complexRect (Real.log (r / 2)) (Real.log r) (-π) π := by
  ext w
  constructor
  · rintro ⟨hw, hws⟩
    have hlog := log_re_mem_of_mem_coordinateAnnulus hw
    refine ⟨Complex.log w, ⟨hlog.1, hlog.2, ?_, ?_⟩,
      Complex.exp_log (Complex.slitPlane_ne_zero hws)⟩
    · rw [Complex.log_im]
      exact Complex.neg_pi_lt_arg w
    · rw [Complex.log_im]
      exact (Complex.arg_le_pi w).lt_of_ne (Complex.slitPlane_arg_ne_pi hws)
  · rintro ⟨z, ⟨h₁, h₂, h₃, h₄⟩, rfl⟩
    exact ⟨exp_mem_coordinateAnnulus hr h₁ h₂,
      Complex.expOpenPartialHomeomorph.map_source ⟨h₃, h₄⟩⟩

theorem upperAnnulus_eq_exp_image (hr : 0 < r) :
    upperAnnulus r = Complex.exp '' complexRect (Real.log (r / 2)) (Real.log r) 0 π := by
  ext w
  constructor
  · rintro ⟨hw, him⟩
    have him' : 0 < w.im := him
    have hw0 : w ≠ 0 := norm_pos_iff.1 (norm_pos_of_mem_coordinateAnnulus hw)
    have hlog := log_re_mem_of_mem_coordinateAnnulus hw
    refine ⟨Complex.log w, ⟨hlog.1, hlog.2, ?_, ?_⟩, Complex.exp_log hw0⟩
    · rw [Complex.log_im]
      refine (Complex.arg_nonneg_iff.2 him'.le).lt_of_ne fun h => ?_
      exact him'.ne' (Complex.arg_eq_zero_iff.1 h.symm).2
    · rw [Complex.log_im]
      exact Complex.arg_lt_pi_iff.2 (Or.inr him'.ne')
  · rintro ⟨z, ⟨h₁, h₂, h₃, h₄⟩, rfl⟩
    refine ⟨exp_mem_coordinateAnnulus hr h₁ h₂, ?_⟩
    change 0 < (Complex.exp z).im
    rw [Complex.exp_im]
    exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h₃ h₄)

/-- The set of complex numbers whose negatives lie in `S` is homeomorphic to `S`. -/
def negPreimageHomeomorph (S : Set ℂ) : ↥{u : ℂ | -u ∈ S} ≃ₜ ↥S where
  toFun u := ⟨-u.1, u.2⟩
  invFun v := ⟨-v.1, by
    change - -v.1 ∈ S
    rw [neg_neg]
    exact v.2⟩
  left_inv u := Subtype.ext (neg_neg u.1)
  right_inv v := Subtype.ext (neg_neg v.1)
  continuous_toFun := (continuous_subtype_val.neg).subtype_mk _
  continuous_invFun := (continuous_subtype_val.neg).subtype_mk _

theorem contractibleSpace_slitAnnulus (hr : 0 < r) : ContractibleSpace ↥(slitAnnulus r) := by
  rw [slitAnnulus_eq_exp_image hr]
  refine contractibleSpace_exp_image (fun z hz => ⟨hz.2.2.1, hz.2.2.2⟩) (convex_complexRect _ _ _ _)
    (nonempty_complexRect (Real.log_lt_log (by positivity) (half_lt_self hr)) ?_)
  linarith [Real.pi_pos]

theorem contractibleSpace_upperAnnulus (hr : 0 < r) : ContractibleSpace ↥(upperAnnulus r) := by
  rw [upperAnnulus_eq_exp_image hr]
  exact contractibleSpace_exp_image
    (fun z hz => ⟨by linarith [Real.pi_pos, hz.2.2.1], hz.2.2.2⟩) (convex_complexRect _ _ _ _)
    (nonempty_complexRect (Real.log_lt_log (by positivity) (half_lt_self hr)) Real.pi_pos)

theorem contractibleSpace_negSlitAnnulus (hr : 0 < r) :
    ContractibleSpace ↥(negSlitAnnulus r) :=
  have := contractibleSpace_slitAnnulus hr
  (negPreimageHomeomorph (slitAnnulus r)).contractibleSpace

theorem contractibleSpace_lowerAnnulus (hr : 0 < r) : ContractibleSpace ↥(lowerAnnulus r) :=
  have := contractibleSpace_upperAnnulus hr
  (negPreimageHomeomorph (upperAnnulus r)).contractibleSpace

end ComplexModels

namespace PlaneLevelCoordinateDisk

variable {f : CollarPlane → ℂ} {s : ℂ} {z : CollarPlane} (D : PlaneLevelCoordinateDisk f s z)

/-- The coordinate `w = coordinate (x − z)` of a point `x` of the plane in the chart of
the disk `D`. -/
def chart (x : CollarPlane) : ℂ := D.coordinate (x - z)

theorem continuous_chart : Continuous D.chart :=
  D.coordinate.continuous.comp (continuous_id.sub continuous_const)

theorem chart_ψ {u : ℂ} (hu : u ∈ D.W) : D.chart (D.ψ u) = u :=
  D.left_inverse u hu

theorem ball_subset_W : ball (0 : ℂ) D.radius ⊆ D.W :=
  ball_subset_closedBall.trans D.closedBall_subset

theorem image_subset_level {S : Set ℂ} (hS : S ⊆ D.W) : D.ψ '' S ⊆ {w | f w = s} := by
  rintro _ ⟨u, hu, rfl⟩
  exact D.level_eq u (hS hu)

theorem chart_mem_of_mem_image {S : Set ℂ} (hS : S ⊆ D.W) {x : CollarPlane}
    (hx : x ∈ D.ψ '' S) : D.chart x ∈ S := by
  obtain ⟨u, hu, rfl⟩ := hx
  rw [D.chart_ψ (hS hu)]
  exact hu

theorem ψ_chart_of_mem_image {S : Set ℂ} (hS : S ⊆ D.W) {x : CollarPlane}
    (hx : x ∈ D.ψ '' S) : D.ψ (D.chart x) = x := by
  obtain ⟨u, hu, rfl⟩ := hx
  rw [D.chart_ψ (hS hu)]

/-- The parametrization `ψ` of the disk `D` maps a subset `S` of its domain
homeomorphically onto its image. -/
def imageHomeomorph {S : Set ℂ} (hS : S ⊆ D.W) : S ≃ₜ D.ψ '' S where
  toFun u := ⟨D.ψ u, mem_image_of_mem _ u.2⟩
  invFun w := ⟨D.chart w, D.chart_mem_of_mem_image hS w.2⟩
  left_inv u := Subtype.ext (D.chart_ψ (hS u.2))
  right_inv w := Subtype.ext (D.ψ_chart_of_mem_image hS w.2)
  continuous_toFun := (D.analytic.continuousOn.mono hS).domRestrict.subtype_mk _
  continuous_invFun := (D.continuous_chart.comp continuous_subtype_val).subtype_mk _

/-- A point of the level lies in the open disk if and only if it lies in the ambient open
set of `D`. -/
theorem mem_openDisk_iff {x : CollarPlane} (hx : f x = s) :
    x ∈ D.openDisk ↔ x ∈ D.ambientOpen := by
  change x ∈ D.ψ '' ball 0 D.radius ↔ _
  rw [D.open_image_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩

/-- Let `S` be a subset of the open coordinate ball of `D` and let `Y` be a subset of the
level containing `ψ(S)`. Then `ψ(S)` is the intersection of `Y` with the open set of
points of `D.ambientOpen` whose chart coordinate lies in `S`. -/
theorem image_eq_inter_preimage {S : Set ℂ} (hS : S ⊆ ball 0 D.radius)
    {Y : Set CollarPlane} (hY : Y ⊆ {w | f w = s}) (hSY : D.ψ '' S ⊆ Y) :
    D.ψ '' S = Y ∩ (D.ambientOpen ∩ D.chart ⁻¹' S) := by
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨hSY ⟨u, hu, rfl⟩, ?_, ?_⟩
    · exact (D.mem_openDisk_iff (D.level_eq u (D.ball_subset_W (hS hu)))).1 ⟨u, hS hu, rfl⟩
    · change D.chart (D.ψ u) ∈ S
      rw [D.chart_ψ (D.ball_subset_W (hS hu))]
      exact hu
  · rintro x ⟨hxY, hxO, hxS⟩
    obtain ⟨u, hu, rfl⟩ := (D.mem_openDisk_iff (hY hxY)).2 hxO
    rw [mem_preimage, D.chart_ψ (D.ball_subset_W hu)] at hxS
    exact ⟨u, hxS, rfl⟩

theorem isOpen_ambientOpen_inter_chart_preimage {S : Set ℂ} (hS : IsOpen S) :
    IsOpen (D.ambientOpen ∩ D.chart ⁻¹' S) :=
  D.isOpen_ambientOpen.inter (hS.preimage D.continuous_chart)

/-- The point `ψ(chart x)` of a point `x` of the closed disk is `x`, and its chart
coordinate has norm at most the radius. -/
theorem chart_of_mem_closedDisk {x : CollarPlane} (hx : x ∈ D.closedDisk) :
    ‖D.chart x‖ ≤ D.radius ∧ D.ψ (D.chart x) = x := by
  obtain ⟨u, hu, rfl⟩ := hx
  rw [D.chart_ψ (D.closedBall_subset hu)]
  exact ⟨mem_closedBall_zero_iff.1 hu, rfl⟩

/-- The radial push in the coordinate disk `D` at time `t`. It sends a point `x` with
chart coordinate `w` to `ψ(((1 − t) + t r / ‖w‖) w)`, where `r` is the radius of `D`. -/
def radialPush (t : ℝ) (x : CollarPlane) : CollarPlane :=
  D.ψ ((1 - t + t * (D.radius / ‖D.chart x‖)) • D.chart x)

end PlaneLevelCoordinateDisk

/-- Let `0 < ‖u‖ ≤ r` and `0 ≤ t ≤ 1`. Then the vector `((1 − t) + t r / ‖u‖) u` has norm
`(1 − t) ‖u‖ + t r`. -/
theorem norm_radialScale {r t : ℝ} {u : ℂ} (hu : 0 < ‖u‖) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hr : 0 ≤ r) :
    ‖(1 - t + t * (r / ‖u‖)) • u‖ = (1 - t) * ‖u‖ + t * r := by
  have hc : 0 ≤ 1 - t + t * (r / ‖u‖) :=
    add_nonneg (by linarith) (mul_nonneg ht₀ (div_nonneg hr hu.le))
  rw [norm_smul, Real.norm_of_nonneg hc]
  field_simp

section DiskFamily

variable {ι : Type} {f : CollarPlane → ℂ} {s : ℂ} {z : ι → CollarPlane}
  (D : ∀ j, PlaneLevelCoordinateDisk f s (z j))

/-- The union of the images `ψ_{q c}(T c)` of subsets `T c` of the coordinate planes of
the disks `D (q c)`. -/
def diskPieces {κ : Type} (q : κ → ι) (T : κ → Set ℂ) : Set CollarPlane :=
  ⋃ c, (D (q c)).ψ '' T c

/-- The union of the images of the closed coordinate balls of half radius. -/
def halfDisks : Set CollarPlane :=
  ⋃ j, (D j).ψ '' closedBall 0 ((D j).radius / 2)

variable {D}

theorem diskPieces_mono {κ : Type} {q : κ → ι} {T T' : κ → Set ℂ} (h : ∀ c, T c ⊆ T' c) :
    diskPieces D q T ⊆ diskPieces D q T' :=
  iUnion_mono fun c => image_mono (h c)

theorem diskPieces_subset_level {κ : Type} {q : κ → ι} {T : κ → Set ℂ}
    (hT : ∀ c, T c ⊆ (D (q c)).W) : diskPieces D q T ⊆ {w | f w = s} :=
  iUnion_subset fun c => (D (q c)).image_subset_level (hT c)

/-- Two points of the closed disks with the same image lie in the same disk. -/
theorem index_eq_of_ψ_eq (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    {j k : ι} {u v : ℂ} (hu : u ∈ closedBall 0 (D j).radius)
    (hv : v ∈ closedBall 0 (D k).radius) (h : (D j).ψ u = (D k).ψ v) : j = k := by
  by_contra hjk
  refine disjoint_left.1 (hdisj hjk) ⟨u, hu, rfl⟩ ?_
  rw [h]
  exact ⟨v, hv, rfl⟩

theorem disjoint_ψ_image (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    {j k : ι} {S T : Set ℂ} (hS : S ⊆ closedBall 0 (D j).radius)
    (hT : T ⊆ closedBall 0 (D k).radius) (h : j = k → Disjoint S T) :
    Disjoint ((D j).ψ '' S) ((D k).ψ '' T) := by
  rw [Set.disjoint_left]
  rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
  obtain rfl := index_eq_of_ψ_eq hdisj (hS hu) (hT hv) he.symm
  obtain rfl := (D j).injOn ((D j).closedBall_subset (hT hv)) ((D j).closedBall_subset (hS hu)) he
  exact Set.disjoint_left.1 (h rfl) hu hv

/-- If all pieces lie in the open coordinate balls and their union lies in a subset `Y` of
the level, then the union is the intersection of `Y` with an open subset of the plane. -/
theorem diskPieces_eq_inter {κ : Type} {q : κ → ι} {T : κ → Set ℂ}
    (hT : ∀ c, T c ⊆ ball 0 (D (q c)).radius) {Y : Set CollarPlane}
    (hY : Y ⊆ {w | f w = s}) (hPY : diskPieces D q T ⊆ Y) :
    diskPieces D q T = Y ∩ ⋃ c, ((D (q c)).ambientOpen ∩ (D (q c)).chart ⁻¹' T c) := by
  rw [inter_iUnion]
  refine iUnion_congr fun c => ?_
  exact (D (q c)).image_eq_inter_preimage (hT c) hY
    ((subset_iUnion (fun c => (D (q c)).ψ '' T c) c).trans hPY)

theorem isOpen_diskPiecesOpen {κ : Type} {q : κ → ι} {T : κ → Set ℂ}
    (hT : ∀ c, IsOpen (T c)) :
    IsOpen (⋃ c, ((D (q c)).ambientOpen ∩ (D (q c)).chart ⁻¹' T c)) :=
  isOpen_iUnion fun c => (D (q c)).isOpen_ambientOpen_inter_chart_preimage (hT c)

/-- Finitely many pairwise disjoint open contractible pieces in pairwise disjoint disks
give the rational homology of as many points as there are pieces. -/
theorem hasDiscreteRatHomology_diskPieces
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    {κ : Type} [Fintype κ] {q : κ → ι} {T : κ → Set ℂ}
    (hT : ∀ c, T c ⊆ ball 0 (D (q c)).radius) (hTo : ∀ c, IsOpen (T c))
    (hTd : ∀ c c', c ≠ c' → q c = q c' → Disjoint (T c) (T c'))
    (hTc : ∀ c, ContractibleSpace (T c)) :
    HasDiscreteRatHomology ↥(diskPieces D q T) (Fintype.card κ) := by
  have hlevel := diskPieces_subset_level (D := D) (q := q) (T := T)
    fun c => (hT c).trans (D (q c)).ball_subset_W
  refine hasDiscreteRatHomology_of_disjoint_contractible_subsets
    (fun c => (D (q c)).ψ '' T c) (fun c => (D (q c)).ambientOpen ∩ (D (q c)).chart ⁻¹' T c)
    (fun c => (D (q c)).isOpen_ambientOpen_inter_chart_preimage (hTo c))
    (fun c => (D (q c)).image_eq_inter_preimage (hT c) hlevel
      (subset_iUnion (fun c => (D (q c)).ψ '' T c) c)) ?_ (fun _ hx => hx) ?_
  · intro c c' hcc'
    exact disjoint_ψ_image hdisj ((hT c).trans ball_subset_closedBall)
      ((hT c').trans ball_subset_closedBall) (hTd c c' hcc')
  · intro c
    have := hTc c
    exact ((D (q c)).imageHomeomorph ((hT c).trans (D (q c)).ball_subset_W)).symm.contractibleSpace

/-- The union of pieces over all disks meets a second such union in the union of the
pointwise intersections. -/
theorem diskPieces_inter (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    {T T' : ι → Set ℂ} (hT : ∀ j, T j ⊆ closedBall 0 (D j).radius)
    (hT' : ∀ j, T' j ⊆ closedBall 0 (D j).radius) :
    diskPieces D id T ∩ diskPieces D id T' = diskPieces D id fun j => T j ∩ T' j := by
  ext x
  simp only [diskPieces, mem_inter_iff, mem_iUnion, mem_image, id]
  constructor
  · rintro ⟨⟨j, u, hu, rfl⟩, ⟨k, v, hv, he⟩⟩
    obtain rfl := index_eq_of_ψ_eq hdisj (hT j hu) (hT' k hv) he.symm
    obtain rfl := (D j).injOn ((D j).closedBall_subset (hT' j hv))
      ((D j).closedBall_subset (hT j hu)) he
    exact ⟨j, v, ⟨hu, hv⟩, rfl⟩
  · rintro ⟨j, u, ⟨hu, hu'⟩, rfl⟩
    exact ⟨⟨j, u, hu, rfl⟩, ⟨j, u, hu', rfl⟩⟩

end DiskFamily

section DiskFamilyHomology

variable {ι : Type} {f : CollarPlane → ℂ} {s : ℂ} {z : ι → CollarPlane}
  {D : ∀ j, PlaneLevelCoordinateDisk f s (z j)}

/-- The union of the open disks has the rational homology of `#ι` points. -/
theorem hasDiscreteRatHomology_openDisks [Fintype ι]
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk) :
    HasDiscreteRatHomology ↥(diskPieces D id fun j => ball 0 (D j).radius) (Fintype.card ι) :=
  hasDiscreteRatHomology_diskPieces hdisj (fun _ => subset_rfl) (fun _ => isOpen_ball)
    (fun _ _ h h' => absurd h' h)
    (fun j => (convex_ball (0 : ℂ) _).contractibleSpace ⟨0, mem_ball_self (D j).radius_pos⟩)

/-- The union of the annuli `ψ_j {r_j / 2 < ‖w‖ < r_j}` has curve homology with Euler
characteristic zero. -/
theorem hasCurveRatHomology_annulusPieces [Finite ι]
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk) :
    HasCurveRatHomology ↥(diskPieces D id fun j => coordinateAnnulus (D j).radius) 0 := by
  have := Fintype.ofFinite ι
  have hann : ∀ j, coordinateAnnulus (D j).radius ⊆ ball 0 (D j).radius :=
    fun j => coordinateAnnulus_subset_ball _
  have hY : (diskPieces D id fun j => coordinateAnnulus (D j).radius) ⊆ {w | f w = s} :=
    diskPieces_subset_level fun j => (hann j).trans (D j).ball_subset_W
  have hPp := diskPieces_eq_inter (q := id) (T := fun j => slitAnnulus (D j).radius)
    (fun j => (slitAnnulus_subset _).trans (hann j)) hY
    (diskPieces_mono fun j => slitAnnulus_subset _)
  have hPm := diskPieces_eq_inter (q := id) (T := fun j => negSlitAnnulus (D j).radius)
    (fun j => (negSlitAnnulus_subset _).trans (hann j)) hY
    (diskPieces_mono fun j => negSlitAnnulus_subset _)
  have hcover : (diskPieces D id fun j => coordinateAnnulus (D j).radius) ⊆
      (diskPieces D id fun j => slitAnnulus (D j).radius) ∪
        diskPieces D id fun j => negSlitAnnulus (D j).radius := by
    refine iUnion_subset fun j => ?_
    rintro _ ⟨u, hu, rfl⟩
    rcases coordinateAnnulus_subset_union _ hu with h | h
    · exact Or.inl (mem_iUnion.2 ⟨j, u, h, rfl⟩)
    · exact Or.inr (mem_iUnion.2 ⟨j, u, h, rfl⟩)
  have hp : HasDiscreteRatHomology ↥(diskPieces D id fun j => slitAnnulus (D j).radius)
      (Fintype.card ι) :=
    hasDiscreteRatHomology_diskPieces hdisj (fun j => (slitAnnulus_subset _).trans (hann j))
      (fun _ => isOpen_slitAnnulus _) (fun _ _ h h' => absurd h' h)
      (fun j => contractibleSpace_slitAnnulus (D j).radius_pos)
  have hm : HasDiscreteRatHomology ↥(diskPieces D id fun j => negSlitAnnulus (D j).radius)
      (Fintype.card ι) :=
    hasDiscreteRatHomology_diskPieces hdisj (fun j => (negSlitAnnulus_subset _).trans (hann j))
      (fun _ => isOpen_negSlitAnnulus _) (fun _ _ h h' => absurd h' h)
      (fun j => contractibleSpace_negSlitAnnulus (D j).radius_pos)
  have hcl : ∀ j, coordinateAnnulus (D j).radius ⊆ closedBall 0 (D j).radius :=
    fun j => (hann j).trans ball_subset_closedBall
  have hinter : (diskPieces D id fun j => slitAnnulus (D j).radius) ∩
      (diskPieces D id fun j => negSlitAnnulus (D j).radius) =
      diskPieces D (Sum.elim id id)
        (Sum.elim (fun j => upperAnnulus (D j).radius) fun j => lowerAnnulus (D j).radius) := by
    rw [diskPieces_inter hdisj (fun j => (slitAnnulus_subset _).trans (hcl j))
      (fun j => (negSlitAnnulus_subset _).trans (hcl j))]
    ext x
    simp only [diskPieces, slitAnnulus_inter_negSlitAnnulus, image_union, mem_iUnion,
      mem_union, Sum.exists, Sum.elim_inl, Sum.elim_inr, id]
    exact exists_or
  have hpm : HasDiscreteRatHomology
      ↥((diskPieces D id fun j => slitAnnulus (D j).radius) ∩
        (diskPieces D id fun j => negSlitAnnulus (D j).radius)) (Fintype.card (ι ⊕ ι)) := by
    rw [hinter]
    refine hasDiscreteRatHomology_diskPieces hdisj ?_ ?_ ?_ ?_
    · rintro (j | j)
      · exact (upperAnnulus_subset _).trans (hann j)
      · exact (lowerAnnulus_subset _).trans (hann j)
    · rintro (j | j)
      · exact isOpen_upperAnnulus _
      · exact isOpen_lowerAnnulus _
    · rintro (j | j) (k | k) hne heq
      · exact absurd (congrArg Sum.inl heq) hne
      · exact disjoint_upperAnnulus_lowerAnnulus _ |>.mono_right (by
          simp only [Sum.elim_inl, Sum.elim_inr, id] at heq ⊢
          subst heq
          exact subset_rfl)
      · simp only [Sum.elim_inl, Sum.elim_inr, id] at heq ⊢
        subst heq
        exact (disjoint_upperAnnulus_lowerAnnulus _).symm
      · exact absurd (congrArg Sum.inr heq) hne
    · rintro (j | j)
      · exact contractibleSpace_upperAnnulus (D j).radius_pos
      · exact contractibleSpace_lowerAnnulus (D j).radius_pos
  have h := HasCurveRatHomology.mayerVietoris_subset (isOpen_diskPiecesOpen fun _ =>
      isOpen_slitAnnulus _) (isOpen_diskPiecesOpen fun _ => isOpen_negSlitAnnulus _) hPp hPm
    hcover hp.toCurve hm.toCurve hpm
  rwa [Fintype.card_sum, Nat.cast_add, sub_self] at h

end DiskFamilyHomology

section OuterPart

variable {ι : Type} {f : CollarPlane → ℂ} {s : ℂ} {z : ι → CollarPlane}
  {D : ∀ j, PlaneLevelCoordinateDisk f s (z j)} {K : Set CollarPlane}

theorem half_closedBall_subset_ball {r : ℝ} (hr : 0 < r) :
    closedBall (0 : ℂ) (r / 2) ⊆ ball 0 r :=
  closedBall_subset_ball (half_lt_self hr)

theorem isClosed_halfDisks [Finite ι] : IsClosed (halfDisks D) :=
  isClosed_iUnion_of_finite fun j => ((isCompact_closedBall (0 : ℂ) _).image_of_continuousOn
    ((D j).analytic.continuousOn.mono ((half_closedBall_subset_ball (D j).radius_pos).trans
      (D j).ball_subset_W))).isClosed

/-- A point `ψ_j(v)` with `r_j / 2 < ‖v‖ ≤ r_j` lies in `K` and outside all half disks. -/
theorem ψ_mem_diff_halfDisks
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    (hDK : ∀ j, (D j).closedDisk ⊆ K) {j : ι} {v : ℂ} (hv₁ : (D j).radius / 2 < ‖v‖)
    (hv₂ : ‖v‖ ≤ (D j).radius) : (D j).ψ v ∈ K \ halfDisks D := by
  have hvc : v ∈ closedBall 0 (D j).radius := mem_closedBall_zero_iff.2 hv₂
  refine ⟨hDK j ⟨v, hvc, rfl⟩, fun h => ?_⟩
  obtain ⟨k, w, hw, he⟩ := mem_iUnion.1 h
  have hwc : w ∈ closedBall 0 (D k).radius :=
    (half_closedBall_subset_ball (D k).radius_pos).trans ball_subset_closedBall hw
  obtain rfl := index_eq_of_ψ_eq hdisj hwc hvc he
  obtain rfl := (D k).injOn ((D k).closedBall_subset hwc) ((D k).closedBall_subset hvc) he
  exact absurd (mem_closedBall_zero_iff.1 hw) (not_le.2 hv₁)

/-- A point `ψ_j(v)` with `‖v‖ = r_j` lies in `K` and outside all open disks. -/
theorem ψ_mem_diff_openDisks
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    (hDK : ∀ j, (D j).closedDisk ⊆ K) {j : ι} {v : ℂ} (hv : ‖v‖ = (D j).radius) :
    (D j).ψ v ∈ K \ ⋃ k, (D k).openDisk := by
  have hvc : v ∈ closedBall 0 (D j).radius := mem_closedBall_zero_iff.2 hv.le
  refine ⟨hDK j ⟨v, hvc, rfl⟩, fun h => ?_⟩
  obtain ⟨k, w, hw, he⟩ := mem_iUnion.1 h
  have hwc : w ∈ closedBall 0 (D k).radius := ball_subset_closedBall hw
  obtain rfl := index_eq_of_ψ_eq hdisj hwc hvc he
  obtain rfl := (D k).injOn ((D k).closedBall_subset hwc) ((D k).closedBall_subset hvc) he
  exact absurd (mem_ball_zero_iff.1 hw) (not_lt.2 hv.ge)

theorem diff_openDisks_subset_diff_halfDisks :
    K \ ⋃ k, (D k).openDisk ⊆ K \ halfDisks D := by
  refine sdiff_subset_sdiff_right (iUnion_mono fun j => ?_)
  exact image_mono (half_closedBall_subset_ball (D j).radius_pos)

/-- The part of `K` outside the half disks meets the union of the open disks in the union
of the annuli. -/
theorem diff_halfDisks_inter_openDisks
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    (hDK : ∀ j, (D j).closedDisk ⊆ K) :
    (K \ halfDisks D) ∩ (diskPieces D id fun j => ball 0 (D j).radius) =
      diskPieces D id fun j => coordinateAnnulus (D j).radius := by
  apply Subset.antisymm
  · rintro x ⟨⟨-, hxS⟩, hxV⟩
    obtain ⟨j, u, hu, rfl⟩ := mem_iUnion.1 hxV
    refine mem_iUnion.2 ⟨j, u, ⟨?_, mem_ball_zero_iff.1 hu⟩, rfl⟩
    by_contra hle
    exact hxS (mem_iUnion.2 ⟨j, u, mem_closedBall_zero_iff.2 (not_lt.1 hle), rfl⟩)
  · intro x hx
    obtain ⟨j, u, hu, rfl⟩ := mem_iUnion.1 hx
    exact ⟨ψ_mem_diff_halfDisks hdisj hDK hu.1 hu.2.le,
      mem_iUnion.2 ⟨j, u, coordinateAnnulus_subset_ball _ hu, rfl⟩⟩

/-- If `K` has curve homology with Euler characteristic `χ`, then the part of `K` outside
the half disks has curve homology with Euler characteristic `χ − #ι`. -/
theorem hasCurveRatHomology_diff_halfDisks [Fintype ι]
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    (hK : K ⊆ {w | f w = s}) (hDK : ∀ j, (D j).closedDisk ⊆ K) {χ : ℤ}
    (hKh : HasCurveRatHomology K χ) :
    HasCurveRatHomology ↥(K \ halfDisks D) (χ - Fintype.card ι) := by
  have hVK : (diskPieces D id fun j => ball 0 (D j).radius) ⊆ K :=
    iUnion_subset fun j => (image_mono ball_subset_closedBall).trans (hDK j)
  have hV := diskPieces_eq_inter (q := id) (T := fun j => ball 0 (D j).radius)
    (fun _ => subset_rfl) hK hVK
  have hcover : K ⊆ (K \ halfDisks D) ∪ diskPieces D id fun j => ball 0 (D j).radius := by
    intro x hx
    by_cases hxS : x ∈ halfDisks D
    · obtain ⟨j, u, hu, rfl⟩ := mem_iUnion.1 hxS
      exact Or.inr (mem_iUnion.2 ⟨j, u, half_closedBall_subset_ball (D j).radius_pos hu, rfl⟩)
    · exact Or.inl ⟨hx, hxS⟩
  have hUV : HasCurveRatHomology
      ↥((K \ halfDisks D) ∩ diskPieces D id fun j => ball 0 (D j).radius) 0 := by
    rw [diff_halfDisks_inter_openDisks hdisj hDK]
    exact hasCurveRatHomology_annulusPieces hdisj
  have h := HasCurveRatHomology.of_mayerVietoris_complement_subset isClosed_halfDisks.isOpen_compl
    (isOpen_diskPiecesOpen fun _ => isOpen_ball) (sdiff_eq K _) hV hcover hKh
    (hasDiscreteRatHomology_openDisks hdisj).toCurve hUV
  rwa [add_zero] at h

end OuterPart

namespace PlaneLevelCoordinateDisk

variable {f : CollarPlane → ℂ} {s : ℂ} {z : CollarPlane} (D : PlaneLevelCoordinateDisk f s z)

theorem openDisk_subset_ambientOpen : D.openDisk ⊆ D.ambientOpen := by
  intro x hx
  change x ∈ D.ψ '' ball 0 D.radius at hx
  rw [D.open_image_eq] at hx
  exact hx.1

/-- A point of the closed disk outside the open disk has chart coordinate of norm equal
to the radius. -/
theorem chart_of_mem_closedDisk_of_not_mem_openDisk {x : CollarPlane} (hx : x ∈ D.closedDisk)
    (hxo : x ∉ D.openDisk) : ‖D.chart x‖ = D.radius ∧ D.ψ (D.chart x) = x := by
  obtain ⟨hle, hψ⟩ := D.chart_of_mem_closedDisk hx
  exact ⟨le_antisymm hle (not_lt.1 fun h => hxo ⟨_, mem_ball_zero_iff.2 h, hψ⟩), hψ⟩

theorem radialPush_zero {x : CollarPlane} (hψ : D.ψ (D.chart x) = x) : D.radialPush 0 x = x := by
  rw [radialPush, sub_zero, zero_mul, add_zero, one_smul, hψ]

/-- The radial push fixes every point whose chart coordinate has norm equal to the radius. -/
theorem radialPush_of_norm_eq {x : CollarPlane} (hn : ‖D.chart x‖ = D.radius)
    (hψ : D.ψ (D.chart x) = x) (t : ℝ) : D.radialPush t x = x := by
  rw [radialPush, hn, div_self D.radius_pos.ne', mul_one, sub_add_cancel, one_smul, hψ]

end PlaneLevelCoordinateDisk

section Retraction

variable {ι : Type} {f : CollarPlane → ℂ} {s : ℂ} {z : ι → CollarPlane}
  {D : ∀ j, PlaneLevelCoordinateDisk f s (z j)} {K : Set CollarPlane}

/-- A point of `K` outside the half disks that lies in the closed disk `D j` has chart
coordinate `w` with `r_j / 2 < ‖w‖ ≤ r_j`. -/
theorem chart_of_mem_diff_halfDisks {j : ι} {x : CollarPlane} (hx : x ∈ K \ halfDisks D)
    (hxj : x ∈ (D j).closedDisk) :
    (D j).radius / 2 < ‖(D j).chart x‖ ∧ ‖(D j).chart x‖ ≤ (D j).radius ∧
      (D j).ψ ((D j).chart x) = x := by
  obtain ⟨hle, hψ⟩ := (D j).chart_of_mem_closedDisk hxj
  refine ⟨?_, hle, hψ⟩
  by_contra h
  exact hx.2 (mem_iUnion.2 ⟨j, (D j).chart x, mem_closedBall_zero_iff.2 (not_lt.1 h), hψ⟩)

theorem radialPush_mem_diff_halfDisks
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    (hDK : ∀ j, (D j).closedDisk ⊆ K) {j : ι} {x : CollarPlane} (hx : x ∈ K \ halfDisks D)
    (hxj : x ∈ (D j).closedDisk) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (D j).radialPush t x ∈ K \ halfDisks D := by
  obtain ⟨h₁, h₂, -⟩ := chart_of_mem_diff_halfDisks hx hxj
  have hpos : 0 < ‖(D j).chart x‖ := (half_pos (D j).radius_pos).trans h₁
  have hn := norm_radialScale hpos ht₀ ht₁ (D j).radius_pos.le
  refine ψ_mem_diff_halfDisks hdisj hDK ?_ ?_ <;> rw [hn] <;> nlinarith

theorem radialPush_one_mem_diff_openDisks
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    (hDK : ∀ j, (D j).closedDisk ⊆ K) {j : ι} {x : CollarPlane} (hx : x ∈ K \ halfDisks D)
    (hxj : x ∈ (D j).closedDisk) :
    (D j).radialPush 1 x ∈ K \ ⋃ k, (D k).openDisk := by
  obtain ⟨h₁, -, -⟩ := chart_of_mem_diff_halfDisks hx hxj
  have hpos : 0 < ‖(D j).chart x‖ := (half_pos (D j).radius_pos).trans h₁
  refine ψ_mem_diff_openDisks hdisj hDK ?_
  rw [norm_radialScale hpos zero_le_one le_rfl (D j).radius_pos.le]
  ring

/-- The set `K \ ⋃ j, (D j).openDisk` is homotopy equivalent to the part of `K` outside
the half disks. The homotopy fixes `K \ ⋃ j, (D j).openDisk` and pushes each point
`ψ_j(w)` with `r_j / 2 < ‖w‖ ≤ r_j` radially to the circle `‖w‖ = r_j`. -/
theorem nonempty_homotopyEquiv_diff_openDisks [Finite ι]
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    (hK : K ⊆ {w | f w = s}) (hDK : ∀ j, (D j).closedDisk ⊆ K) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(K \ ⋃ j, (D j).openDisk) ↥(K \ halfDisks D)) := by
  classical
  have hEU : K \ ⋃ j, (D j).openDisk ⊆ K \ halfDisks D := diff_openDisks_subset_diff_halfDisks
  let g : unitInterval × ↥(K \ halfDisks D) → CollarPlane := fun p =>
    if h : ∃ j, (p.2 : CollarPlane) ∈ (D j).openDisk then
      (D (Classical.choose h)).radialPush p.1 p.2 else p.2
  have hg_push : ∀ (p : unitInterval × ↥(K \ halfDisks D)) (j : ι),
      (p.2 : CollarPlane) ∈ (D j).closedDisk → g p = (D j).radialPush p.1 p.2 := by
    intro p j hj
    simp only [g]
    split_ifs with h
    · have hk : Classical.choose h = j := by
        by_contra hne
        exact disjoint_left.1 (hdisj hne)
          ((D _).openDisk_subset_closedDisk (Classical.choose_spec h)) hj
      rw [hk]
    · obtain ⟨hn, hψ⟩ := (D j).chart_of_mem_closedDisk_of_not_mem_openDisk hj
        fun h' => h ⟨j, h'⟩
      exact ((D j).radialPush_of_norm_eq hn hψ _).symm
  have hg_self : ∀ p : unitInterval × ↥(K \ halfDisks D),
      (p.2 : CollarPlane) ∉ ⋃ j, (D j).openDisk → g p = p.2 := by
    intro p hp
    simp only [g]
    rw [dif_neg]
    rintro ⟨j, hj⟩
    exact hp (mem_iUnion.2 ⟨j, hj⟩)
  have hsnd : Continuous fun p : unitInterval × ↥(K \ halfDisks D) => (p.2 : CollarPlane) :=
    continuous_subtype_val.comp continuous_snd
  have hpush_cont : ∀ j, ContinuousOn
      (fun p : unitInterval × ↥(K \ halfDisks D) => (D j).radialPush p.1 p.2)
      ((fun p : unitInterval × ↥(K \ halfDisks D) => (p.2 : CollarPlane)) ⁻¹'
        (D j).closedDisk) := by
    intro j
    have hc : Continuous fun p : unitInterval × ↥(K \ halfDisks D) => (D j).chart p.2 :=
      (D j).continuous_chart.comp hsnd
    have ht : Continuous fun p : unitInterval × ↥(K \ halfDisks D) => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hinner : ContinuousOn (fun p : unitInterval × ↥(K \ halfDisks D) =>
        (1 - (p.1 : ℝ) + p.1 * ((D j).radius / ‖(D j).chart p.2‖)) • (D j).chart p.2)
        ((fun p : unitInterval × ↥(K \ halfDisks D) => (p.2 : CollarPlane)) ⁻¹'
          (D j).closedDisk) := by
      have hcoef : ContinuousOn (fun p : unitInterval × ↥(K \ halfDisks D) =>
          1 - (p.1 : ℝ) + p.1 * ((D j).radius / ‖(D j).chart p.2‖))
          ((fun p : unitInterval × ↥(K \ halfDisks D) => (p.2 : CollarPlane)) ⁻¹'
            (D j).closedDisk) := by
        refine (continuous_const.sub ht).continuousOn.add
          (ht.continuousOn.mul (continuousOn_const.div hc.norm.continuousOn ?_))
        intro p hp
        exact ((half_pos (D j).radius_pos).trans (chart_of_mem_diff_halfDisks p.2.2 hp).1).ne'
      exact hcoef.smul hc.continuousOn
    have hmaps : MapsTo (fun p : unitInterval × ↥(K \ halfDisks D) =>
        (1 - (p.1 : ℝ) + p.1 * ((D j).radius / ‖(D j).chart p.2‖)) • (D j).chart p.2)
        ((fun p : unitInterval × ↥(K \ halfDisks D) => (p.2 : CollarPlane)) ⁻¹'
          (D j).closedDisk) (D j).W := by
      intro p hp
      obtain ⟨h₁, h₂, -⟩ := chart_of_mem_diff_halfDisks p.2.2 hp
      have hpos : 0 < ‖(D j).chart p.2‖ := (half_pos (D j).radius_pos).trans h₁
      apply (D j).closedBall_subset
      rw [mem_closedBall_zero_iff, norm_radialScale hpos p.1.2.1 p.1.2.2 (D j).radius_pos.le]
      nlinarith [p.1.2.1, p.1.2.2]
    exact (D j).analytic.continuousOn.comp hinner hmaps
  have hg_cont : Continuous g := by
    let F : Option ι → Set (unitInterval × ↥(K \ halfDisks D)) := fun o =>
      o.elim ((fun p => (p.2 : CollarPlane)) ⁻¹' (⋃ j, (D j).ambientOpen)ᶜ)
        fun j => (fun p => (p.2 : CollarPlane)) ⁻¹' (D j).closedDisk
    refine LocallyFinite.continuous (f := F) (locallyFinite_of_finite F) ?_ ?_ ?_
    · refine eq_univ_of_forall fun p => ?_
      by_cases hp : (p.2 : CollarPlane) ∈ ⋃ j, (D j).ambientOpen
      · obtain ⟨j, hj⟩ := mem_iUnion.1 hp
        have hlev : f p.2 = s := hK p.2.2.1
        exact mem_iUnion.2 ⟨some j,
          (D j).openDisk_subset_closedDisk (((D j).mem_openDisk_iff hlev).2 hj)⟩
      · exact mem_iUnion.2 ⟨none, hp⟩
    · rintro (_ | j)
      · exact (isOpen_iUnion fun j => (D j).isOpen_ambientOpen).isClosed_compl.preimage hsnd
      · exact (D j).isCompact_closedDisk.isClosed.preimage hsnd
    · rintro (_ | j)
      · refine hsnd.continuousOn.congr fun p hp => hg_self p fun h => hp ?_
        obtain ⟨j, hj⟩ := mem_iUnion.1 h
        exact mem_iUnion.2 ⟨j, (D j).openDisk_subset_ambientOpen hj⟩
      · exact (hpush_cont j).congr fun p hp => hg_push p j hp
  have hg_mem : ∀ p, g p ∈ K \ halfDisks D := by
    intro p
    by_cases hp : (p.2 : CollarPlane) ∈ ⋃ j, (D j).openDisk
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hp
      rw [hg_push p j ((D j).openDisk_subset_closedDisk hj)]
      exact radialPush_mem_diff_halfDisks hdisj hDK p.2.2 ((D j).openDisk_subset_closedDisk hj)
        p.1.2.1 p.1.2.2
    · rw [hg_self p hp]
      exact p.2.2
  have hg_one : ∀ x : ↥(K \ halfDisks D), g (1, x) ∈ K \ ⋃ j, (D j).openDisk := by
    intro x
    by_cases hx : (x : CollarPlane) ∈ ⋃ j, (D j).openDisk
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      rw [hg_push (1, x) j ((D j).openDisk_subset_closedDisk hj)]
      exact radialPush_one_mem_diff_openDisks hdisj hDK x.2 ((D j).openDisk_subset_closedDisk hj)
    · rw [hg_self (1, x) hx]
      exact ⟨x.2.1, hx⟩
  have hg_zero : ∀ x : ↥(K \ halfDisks D), g (0, x) = x := by
    intro x
    by_cases hx : (x : CollarPlane) ∈ ⋃ j, (D j).openDisk
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      have hxj := (D j).openDisk_subset_closedDisk hj
      rw [hg_push (0, x) j hxj]
      exact (D j).radialPush_zero (chart_of_mem_diff_halfDisks x.2 hxj).2.2
    · exact hg_self (0, x) hx
  let incl : C(↥(K \ ⋃ j, (D j).openDisk), ↥(K \ halfDisks D)) :=
    ⟨fun x => ⟨x, hEU x.2⟩, continuous_subtype_val.subtype_mk _⟩
  let ρ : C(↥(K \ halfDisks D), ↥(K \ ⋃ j, (D j).openDisk)) :=
    ⟨fun x => ⟨g (1, x), hg_one x⟩,
      (hg_cont.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  have hρi : ρ.comp incl = ContinuousMap.id _ :=
    ContinuousMap.ext fun x => Subtype.ext (hg_self (1, ⟨x, hEU x.2⟩) x.2.2)
  let H : ContinuousMap.Homotopy (ContinuousMap.id ↥(K \ halfDisks D)) (incl.comp ρ) :=
    { toFun := fun p => ⟨g p, hg_mem p⟩
      continuous_toFun := hg_cont.subtype_mk _
      map_zero_left := fun x => Subtype.ext (hg_zero x)
      map_one_left := fun _ => rfl }
  exact ⟨{ toFun := incl
           invFun := ρ
           left_inv := by rw [hρi]
           right_inv := ⟨H.symm⟩ }⟩

/-- **Homology of the complement of finitely many disks.** Let `K` be a subset of the
level `{f = s}`, and let `D j`, `j ∈ ι`, be finitely many coordinate disks of this level
whose closed disks lie in `K` and are pairwise disjoint. If `K` has curve homology with
Euler characteristic `χ`, then `K \ ⋃ j, (D j).openDisk` has curve homology with Euler
characteristic `χ − #ι`. -/
theorem hasCurveRatHomology_diff_iUnion_openDisk [Fintype ι]
    (hdisj : Pairwise fun j k => Disjoint (D j).closedDisk (D k).closedDisk)
    (hK : K ⊆ {w | f w = s}) (hDK : ∀ j, (D j).closedDisk ⊆ K) {χ : ℤ}
    (hKh : HasCurveRatHomology K χ) :
    HasCurveRatHomology ↥(K \ ⋃ j, (D j).openDisk) (χ - Fintype.card ι) := by
  obtain ⟨e⟩ := nonempty_homotopyEquiv_diff_openDisks hdisj hK hDK
  exact (hasCurveRatHomology_diff_halfDisks hdisj hK hDK hKh).of_homotopyEquiv e

end Retraction

open OnLeConjecture.Analytic.Germ

namespace ResolutionSectionLevel.ExteriorHypotheses

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative} {A : ResolutionSectionAssembly g hd hi}
  {L : ResolutionSectionLevel A} {D : (j : L.points) → L.PointCoordinateDisk j} {ε : ℝ}

/-- The target cut lies in the level of the source equation. -/
theorem cut_subset_level (_hL : L.ExteriorHypotheses D ε) :
    targetSectionCut A.H L.radius ε L.parameter ⊆
      {w | euclideanEquation (fun x => A.H x 0) w = L.parameter} :=
  fun _ hz => hz.1.2

/-- **Rational homology of the punctured section.** The punctured section
`L.diskExterior D ε` has curve homology with Euler characteristic `1 − μ − N`, where `μ`
is the Milnor number of the source equation and `N` is the number of critical points of
the level. -/
theorem hasCurveRatHomology_diskExterior (hL : L.ExteriorHypotheses D ε) :
    HasCurveRatHomology ↥(L.diskExterior D ε)
      (1 - (A.sourceMilnorNumber : ℤ) - (L.points.card : ℤ)) := by
  have h := hasCurveRatHomology_diff_iUnion_openDisk hL.disjoint hL.cut_subset_level
    hL.closedDisk_subset_cut hL.cut_homology
  rwa [Fintype.card_coe] at h

/-- If the punctured section `L.diskExterior D ε` is connected in rational homology, then
its first rational homology has dimension `μ + N`, where `μ` is the Milnor number of the
source equation and `N` is the number of critical points of the level. -/
theorem finrank_ratH_one_diskExterior (hL : L.ExteriorHypotheses D ε)
    (h0 : Module.finrank ℚ (ratH ↥(L.diskExterior D ε) 0) = 1) :
    Module.finrank ℚ (ratH ↥(L.diskExterior D ε) 1) = A.sourceMilnorNumber + L.points.card := by
  have h := hL.hasCurveRatHomology_diskExterior.euler
  rw [h0] at h
  omega

end ResolutionSectionLevel.ExteriorHypotheses

end OnLeConjecture.Analytic
