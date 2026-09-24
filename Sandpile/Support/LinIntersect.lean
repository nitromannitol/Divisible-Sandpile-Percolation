/-
The intersection count of two walks, and its first moment.

`lem:dgt4-linearization-from-survival` uses at `sandpile.tex:5695-5709` the two
intersection moments of `ssec:green-estimates`, for

  "$\mathcal I(X,Y)\coloneqq\sum_{r,h\geq0}\one_{\{X_r=Y_h\}}$",

the number of intersections of two independent walks.  The first of them
(`eq:dgt4-intersection-first-moment`, `sandpile.tex:1312-1317`) is the identity

  "$\mathbf E_x\mathbf E_y\sum_{i,j\geq0}\one_{\{X_i=Y_j\}}
      = \sum_{z\in\Z^d}G(x,z)G(y,z)$",

which the paper attributes to Tonelli's theorem, together with the bound
`≤ C(1+|x-y|)^{4-d}` of `Sandpile.External.GreenBoundsHigh`.  That identity is
proved here.  The second moment is the cited input
`Sandpile.External.IntersectionSecondMoment`.

Everything is in `ℝ≥0∞`: the count is a `tsum` of indicators there, so an
infinite count is `⊤` rather than a junk zero, and the expectations are lower
integrals, which need no integrability hypothesis.  The route is the
factorization of the count through the local times,
`I(X,Y) = ∑_z L_X(z) L_Y(z)`, which turns the double walk average into a product
of two one-walk averages and needs no product measure on a common space.
-/
import Sandpile.External.IntersectionSecondMoment
import Sandpile.Support.ExitGreen
import Sandpile.Support.LinReturn

open MeasureTheory
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The local time `L_X(z) = ∑_{i≥0} 1{X_i = z}` of a path at a site, in
`ℝ≥0∞`. -/
noncomputable def localTime (z : Site d) (X : ℕ → Site d) : ℝ≥0∞ :=
  ∑' i : ℕ, (if X i = z then (1 : ℝ≥0∞) else 0)

/-- The intersection count factors through the local times:
`I(X,Y) = ∑_z L_X(z) L_Y(z)`. -/
theorem interCount_eq_tsum_localTime (X Y : ℕ → Site d) :
    Sandpile.External.interCount X Y = ∑' z : Site d, localTime z X * localTime z Y := by
  classical
  have hind : ∀ p : ℕ × ℕ,
      Set.indicator {q : ℕ × ℕ | X q.1 = Y q.2} (fun _ => (1 : ℝ≥0∞)) p
        = (if X p.1 = Y p.2 then (1 : ℝ≥0∞) else 0) := by
    intro p
    by_cases h : X p.1 = Y p.2
    · rw [Set.indicator_of_mem (by simpa using h), if_pos h]
    · rw [Set.indicator_of_notMem (by simpa using h), if_neg h]
  have hmul : ∀ z : Site d, localTime z X * localTime z Y
      = ∑' i : ℕ, ∑' j : ℕ,
          ((if X i = z then (1 : ℝ≥0∞) else 0) * (if Y j = z then (1 : ℝ≥0∞) else 0)) := by
    intro z
    rw [localTime, localTime, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [← ENNReal.tsum_mul_left]
  have hpoint : ∀ i j : ℕ,
      (∑' z : Site d, (if X i = z then (1 : ℝ≥0∞) else 0) * (if Y j = z then (1 : ℝ≥0∞) else 0))
        = (if X i = Y j then (1 : ℝ≥0∞) else 0) := by
    intro i j
    rw [tsum_eq_single (X i) (by
      intro z hz
      rw [if_neg (fun h => hz h.symm), zero_mul])]
    by_cases h : X i = Y j
    · rw [if_pos h, if_pos rfl, if_pos h.symm, one_mul]
    · rw [if_neg h, if_pos rfl, if_neg (fun hh => h hh.symm), mul_zero]
  calc Sandpile.External.interCount X Y
      = ∑' p : ℕ × ℕ, (if X p.1 = Y p.2 then (1 : ℝ≥0∞) else 0) := by
        rw [Sandpile.External.interCount]
        exact tsum_congr hind
    _ = ∑' i : ℕ, ∑' j : ℕ, (if X i = Y j then (1 : ℝ≥0∞) else 0) := ENNReal.tsum_prod'
    _ = ∑' i : ℕ, ∑' j : ℕ, ∑' z : Site d,
          ((if X i = z then (1 : ℝ≥0∞) else 0) * (if Y j = z then (1 : ℝ≥0∞) else 0)) :=
        tsum_congr fun i => tsum_congr fun j => (hpoint i j).symm
    _ = ∑' i : ℕ, ∑' z : Site d, ∑' j : ℕ,
          ((if X i = z then (1 : ℝ≥0∞) else 0) * (if Y j = z then (1 : ℝ≥0∞) else 0)) :=
        tsum_congr fun i => ENNReal.tsum_comm
    _ = ∑' z : Site d, ∑' i : ℕ, ∑' j : ℕ,
          ((if X i = z then (1 : ℝ≥0∞) else 0) * (if Y j = z then (1 : ℝ≥0∞) else 0)) :=
        ENNReal.tsum_comm
    _ = ∑' z : Site d, localTime z X * localTime z Y := (tsum_congr hmul).symm

/-- The cylinder `{X_i = z}` is measurable. -/
theorem measurableSet_path_eq (i : ℕ) (z : Site d) :
    MeasurableSet {X : ℕ → Site d | X i = z} := by
  have hpre : {X : ℕ → Site d | X i = z} = (fun X : ℕ → Site d => X i) ⁻¹' {z} := rfl
  rw [hpre]
  exact measurable_pi_apply i (measurableSet_singleton z)

theorem indicator_path_eq (i : ℕ) (z : Site d) :
    (fun X : ℕ → Site d => (if X i = z then (1 : ℝ≥0∞) else 0))
      = Set.indicator {X : ℕ → Site d | X i = z} (fun _ => (1 : ℝ≥0∞)) := by
  classical
  funext X
  by_cases h : X i = z
  · rw [if_pos h, Set.indicator_of_mem (by simpa using h)]
  · rw [if_neg h, Set.indicator_of_notMem (by simpa using h)]

/-- The local time at a site is a measurable function of the path. -/
theorem measurable_localTime (z : Site d) :
    Measurable (fun X : ℕ → Site d => localTime z X) := by
  classical
  refine Measurable.tsum fun i => ?_
  rw [indicator_path_eq i z]
  exact measurable_const.indicator (measurableSet_path_eq i z)

/-- The law of the walk at a fixed time is the heat kernel. -/
theorem walkLaw_apply_site [NeZero d] (hd : 1 ≤ d) (x : Site d) (n : ℕ) (z : Site d) :
    (walkLaw d x) {X : ℕ → Site d | X n = z} = ENNReal.ofReal (heatKernel d n x z) := by
  classical
  have hC := measure_walk_mem_finset (d := d) hd x n {z}
  simp only [Finset.mem_singleton, Finset.sum_singleton] at hC
  have hne : (walkLaw d x) {X : ℕ → Site d | X n = z} ≠ ⊤ := measure_ne_top _ _
  rw [← hC, measureReal_def, ENNReal.ofReal_toReal hne]

/-- The mean local time of the walk is the Green function:
`E_x L_X(z) = G(x,z)`. -/
theorem lintegral_localTime [NeZero d] (hd : 3 ≤ d) (x z : Site d) :
    ∫⁻ X, localTime z X ∂(walkLaw d x) = ENNReal.ofReal (green d x z) := by
  classical
  have hmeas : ∀ i : ℕ,
      AEMeasurable (fun X : ℕ → Site d => (if X i = z then (1 : ℝ≥0∞) else 0)) (walkLaw d x) := by
    intro i
    rw [indicator_path_eq i z]
    exact (measurable_const.indicator (measurableSet_path_eq i z)).aemeasurable
  have hstep : ∀ i : ℕ,
      ∫⁻ X, (if X i = z then (1 : ℝ≥0∞) else 0) ∂(walkLaw d x)
        = ENNReal.ofReal (heatKernel d i x z) := by
    intro i
    rw [indicator_path_eq i z, lintegral_indicator_const (measurableSet_path_eq i z),
      one_mul, walkLaw_apply_site (by omega) x i z]
  calc ∫⁻ X, localTime z X ∂(walkLaw d x)
      = ∑' i : ℕ, ∫⁻ X, (if X i = z then (1 : ℝ≥0∞) else 0) ∂(walkLaw d x) := by
        simp only [localTime]
        exact lintegral_tsum hmeas
    _ = ∑' i : ℕ, ENNReal.ofReal (heatKernel d i x z) := tsum_congr hstep
    _ = ENNReal.ofReal (green d x z) := by
        rw [green]
        exact (ENNReal.ofReal_tsum_of_nonneg (fun i => heatKernel_nonneg i x z)
          (summable_heatKernel_transient hd x z)).symm

/-- **The first intersection estimate, `eq:dgt4-intersection-first-moment`, in
the walk vocabulary.**  The expected number of intersections of two independent
walks started at `x` and `y` is `∑_z G(x,z)G(y,z)`.  This is the paper's Tonelli
identity at `sandpile.tex:1312-1317`. -/
theorem lintegral_interCount [NeZero d] (hd : 3 ≤ d) (x y : Site d) :
    ∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ∂(walkLaw d y) ∂(walkLaw d x)
      = ∑' z : Site d, ENNReal.ofReal (green d x z) * ENNReal.ofReal (green d y z) := by
  classical
  have hinner : ∀ X : ℕ → Site d,
      ∫⁻ Y, Sandpile.External.interCount X Y ∂(walkLaw d y)
        = ∑' z : Site d, localTime z X * ENNReal.ofReal (green d y z) := by
    intro X
    calc ∫⁻ Y, Sandpile.External.interCount X Y ∂(walkLaw d y)
        = ∫⁻ Y, ∑' z : Site d, localTime z X * localTime z Y ∂(walkLaw d y) := by
          exact lintegral_congr fun Y => interCount_eq_tsum_localTime X Y
      _ = ∑' z : Site d, ∫⁻ Y, localTime z X * localTime z Y ∂(walkLaw d y) :=
          lintegral_tsum fun z =>
            ((measurable_localTime z).const_mul (localTime z X)).aemeasurable
      _ = ∑' z : Site d, localTime z X * ∫⁻ Y, localTime z Y ∂(walkLaw d y) :=
          tsum_congr fun z => lintegral_const_mul _ (measurable_localTime z)
      _ = ∑' z : Site d, localTime z X * ENNReal.ofReal (green d y z) :=
          tsum_congr fun z => by rw [lintegral_localTime hd y z]
  calc ∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ∂(walkLaw d y) ∂(walkLaw d x)
      = ∫⁻ X, ∑' z : Site d, localTime z X * ENNReal.ofReal (green d y z) ∂(walkLaw d x) :=
        lintegral_congr hinner
    _ = ∑' z : Site d, ∫⁻ X, localTime z X * ENNReal.ofReal (green d y z) ∂(walkLaw d x) :=
        lintegral_tsum fun z =>
          ((measurable_localTime z).mul_const (ENNReal.ofReal (green d y z))).aemeasurable
    _ = ∑' z : Site d, (∫⁻ X, localTime z X ∂(walkLaw d x)) * ENNReal.ofReal (green d y z) :=
        tsum_congr fun z => lintegral_mul_const _ (measurable_localTime z)
    _ = ∑' z : Site d, ENNReal.ofReal (green d x z) * ENNReal.ofReal (green d y z) :=
        tsum_congr fun z => by rw [lintegral_localTime hd x z]

/-- The first intersection moment in the walk vocabulary, with the bound of
`eq:dgt4-intersection-first-moment`: for `d ≥ 5` the expected number of
intersections of two independent walks is at most `C(1+|x-y|)^{4-d}`. -/
theorem lintegral_interCount_le [NeZero d] (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Site d,
      (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ∂(walkLaw d y) ∂(walkLaw d x)) ≤
        ENNReal.ofReal (C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) := by
  classical
  obtain ⟨-, -, -, ⟨C, hC0, hCbound⟩, -⟩ := hGreen d hd
  refine ⟨C, hC0, fun x y => ?_⟩
  obtain ⟨hsummable, hle⟩ := hCbound x y
  rw [lintegral_interCount (by omega) x y]
  have hprod : ∀ z : Site d,
      ENNReal.ofReal (green d x z) * ENNReal.ofReal (green d y z)
        = ENNReal.ofReal (green d x z * green d y z) := fun z =>
    (ENNReal.ofReal_mul (green_nonneg x z)).symm
  rw [tsum_congr hprod,
    ← ENNReal.ofReal_tsum_of_nonneg
      (fun z => mul_nonneg (green_nonneg x z) (green_nonneg y z)) hsummable]
  exact ENNReal.ofReal_le_ofReal hle

end Sandpile
