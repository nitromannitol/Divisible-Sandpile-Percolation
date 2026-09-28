import Sandpile.Support.ContRiemann
import Sandpile.Support.ContMeshIntegral

/-!
# The Mesh Point and Riemann-Sum Convergence

The mesh point of `ℝ^d` for the mesh `R^{-1}ℤ^d`, which is the space half of the
Riemann-sum argument of `sandpile.tex:4724-4729`.

The exact identity `Sandpile.Support.sum_double_cellMass_eq` writes the double
space sum of `prop:weighted-membrane-limit` as the double integral of the kernel
read at the mesh points of the two integration variables; this file supplies the
mesh point itself, its measurability, the bound `‖meshPoint R u - u‖ ≤ √d / R`
and the resulting convergence to the identity, which is what turns that double
integral into the double integral of the Brownian heat kernel once the times are
bounded away from zero and the kernel is uniformly continuous there.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- The point of the mesh `R^{-1}ℤ^d` that a point of space falls into. -/
noncomputable def meshPoint (R : ℝ) (u : Space d) : Space d :=
  WithLp.toLp 2 (fun i : Fin d => ((⌊R * u i⌋ : ℤ) : ℝ) / R)

/-- The `i`-th coordinate of the mesh point, unfolded from `meshPoint`'s
definition as a `WithLp` term. -/
theorem meshPoint_apply (R : ℝ) (u : Space d) (i : Fin d) :
    meshPoint R u i = ((⌊R * u i⌋ : ℤ) : ℝ) / R := rfl

/-- Rounding to the mesh is measurable. -/
theorem measurable_meshPoint (R : ℝ) : Measurable (meshPoint (d := d) R) := by
  have h1 : Measurable (fun u : Space d => (fun i : Fin d => ((⌊R * u i⌋ : ℤ) : ℝ) / R)) :=
    measurable_pi_lambda _ fun i =>
      (Measurable.of_discrete.comp (measurable_coord R i)).div_const R
  exact (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp h1

/-- The mesh point is within `√d / R` of the point. -/
theorem norm_meshPoint_sub_le {R : ℝ} (hR : 0 < R) (u : Space d) :
    ‖meshPoint R u - u‖ ≤ Real.sqrt d / R := by
  have hcoord : ∀ i : Fin d, |(meshPoint R u - u) i| ≤ 1 / R := by
    intro i
    have : (meshPoint R u - u) i = ((⌊R * u i⌋ : ℤ) : ℝ) / R - u i := rfl
    rw [this]
    exact abs_floor_div_sub_le hR (u i)
  have hsq : ∑ i : Fin d, ((meshPoint R u - u) i) ^ 2 ≤ (d : ℝ) * (1 / R) ^ 2 := by
    calc ∑ i : Fin d, ((meshPoint R u - u) i) ^ 2
        ≤ ∑ _i : Fin d, (1 / R) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := hcoord i
          nlinarith [abs_nonneg ((meshPoint R u - u) i), sq_abs ((meshPoint R u - u) i)]
      _ = (d : ℝ) * (1 / R) ^ 2 := by simp [Finset.sum_const]
  have hnorm : ‖meshPoint R u - u‖ = Real.sqrt (∑ i : Fin d, ((meshPoint R u - u) i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hrhs : Real.sqrt ((d : ℝ) * (1 / R) ^ 2) = Real.sqrt d / R := by
    rw [Real.sqrt_mul hd0, Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / R)]
    field_simp
  calc Real.sqrt (∑ i : Fin d, ((meshPoint R u - u) i) ^ 2)
      ≤ Real.sqrt ((d : ℝ) * (1 / R) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt d / R := hrhs

/-- The mesh point converges to the point as the mesh refines. -/
theorem tendsto_meshPoint (u : Space d) :
    Tendsto (fun R : ℝ => meshPoint R u) atTop (𝓝 u) := by
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (?_ : Tendsto (fun R : ℝ => Real.sqrt d / R) atTop (𝓝 0))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_meshPoint_sub_le hR u
  · exact tendsto_const_nhds.div_atTop tendsto_id

/-- Reading any function at the mesh point of space is measurable: the mesh point
factors through the lattice site, which is a discrete space. -/
theorem measurable_meshPoint_comp (R : ℝ) (G : Space d → ℝ) :
    Measurable (fun u : Space d => G (meshPoint R u)) := by
  have h : (fun u : Space d => G (meshPoint R u))
      = (fun x : Sandpile.Site d =>
          G (WithLp.toLp 2 (fun i : Fin d => ((x i : ℤ) : ℝ) / R)))
        ∘ (fun (u : Space d) (i : Fin d) => ⌊R * u i⌋) := rfl
  rw [h]
  refine Measurable.of_discrete.comp ?_
  exact measurable_pi_lambda _ fun i => measurable_coord R i

/-- **The double space sums converge to the double space integral.**  The kernel
is read at the mesh points of the two integration variables; when it is bounded
and continuous, which the Brownian heat kernel is at times bounded away from
zero, dominated convergence gives the limit. -/
theorem tendsto_integral2_meshPoint (φ : Space d → ℝ) (hint : Integrable φ)
    (K : Space d → Space d → ℝ) (hK : Continuous fun p : Space d × Space d => K p.1 p.2)
    (C : ℝ) (hC : ∀ x y, |K x y| ≤ C) :
    Tendsto (fun R : ℝ =>
        ∫ u : Space d, (∫ v : Space d, K (meshPoint R u) (meshPoint R v) * φ v) * φ u)
      atTop (𝓝 (∫ u : Space d, (∫ v : Space d, K u v * φ v) * φ u)) := by
  have habs : Integrable (fun v : Space d => |φ v|) := hint.abs
  have hCint : Integrable (fun v : Space d => C * |φ v|) := habs.const_mul C
  -- integrability of every inner integrand
  have hintg : ∀ (x : Space d) (P : Space d → Space d),
      Measurable P → Integrable (fun v : Space d => K x (P v) * φ v) := by
    intro x P hP
    refine hint.bdd_mul (c := C) ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact ((hK.comp ((continuous_const.prodMk continuous_id))).measurable.comp
        hP).aestronglyMeasurable
    · simpa using hC x (P v)
  have hinnerbd : ∀ (x : Space d) (P : Space d → Space d), Measurable P →
      |∫ v : Space d, K x (P v) * φ v| ≤ C * ∫ v : Space d, |φ v| := by
    intro x P hP
    calc |∫ v : Space d, K x (P v) * φ v|
        ≤ ∫ v : Space d, |K x (P v) * φ v| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ v : Space d, C * |φ v| := by
          refine MeasureTheory.integral_mono ((hintg x P hP).abs) hCint fun v => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hC x (P v)) (abs_nonneg (φ v))
      _ = C * ∫ v : Space d, |φ v| := MeasureTheory.integral_const_mul C _
  have hmeshmeas : ∀ R : ℝ, Measurable (meshPoint (d := d) R) := measurable_meshPoint
  have hinner : ∀ u : Space d,
      Tendsto (fun R : ℝ => ∫ v : Space d, K (meshPoint R u) (meshPoint R v) * φ v) atTop
        (𝓝 (∫ v : Space d, K u v * φ v)) := by
    intro u
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun v => C * |φ v|)
      (Filter.Eventually.of_forall fun R => (hintg (meshPoint R u) (meshPoint R)
        (hmeshmeas R)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun v => ?_)
      hCint (Filter.Eventually.of_forall fun v => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hC _ _) (abs_nonneg (φ v))
    · have hpair : Tendsto (fun R : ℝ => ((meshPoint R u, meshPoint R v) : Space d × Space d))
          atTop (𝓝 (u, v)) := (tendsto_meshPoint u).prodMk_nhds (tendsto_meshPoint v)
      exact ((hK.tendsto (u, v)).comp hpair).mul tendsto_const_nhds
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun u => (C * ∫ v : Space d, |φ v|) * |φ u|)
    (Filter.Eventually.of_forall fun R => ?_)
    (Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun u => ?_)
    (habs.const_mul (C * ∫ v : Space d, |φ v|))
    (Filter.Eventually.of_forall fun u => (hinner u).mul tendsto_const_nhds)
  · exact ((measurable_meshPoint_comp R
      (fun x => ∫ v : Space d, K x (meshPoint R v) * φ v)).aestronglyMeasurable).mul
      hint.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (hinnerbd (meshPoint R u) (meshPoint R) (hmeshmeas R)) (abs_nonneg (φ u))

end Sandpile.Support
