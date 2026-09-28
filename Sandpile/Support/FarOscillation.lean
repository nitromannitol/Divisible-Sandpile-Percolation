import Sandpile.Support.FiniteKernelTail
import Sandpile.Support.FarComparison
import Sandpile.Support.PlaneRectangle

/-!
# Superpolynomial short-distance oscillation bounds for the far Green field

Short-distance oscillations of the far Green field on finite pair families and fixed-aspect plane
rectangles have superpolynomially small probability. `exists_far_pair_union_tail` unions the
two-point far-increment tail over a finite family of pairs; `exists_far_oscillation_bound` feeds
in a family growing polynomially in `r` and a separation scale `⌊r^α⌋` to get decay `C r^{-p}`;
`exists_aspect_rectangle_far_oscillation` and its box variant specialize this to pairs drawn from
a fixed-aspect-ratio plane rectangle. Two purely analytic lemmas support the polynomial-versus-
Gaussian comparison (`eventually_log_le_floor_rpow_sq`, `polynomial_exp_log_sq_le`), and
`latticeNorm_planeTranslate_sub_le` converts a coordinatewise separation bound into a lattice-norm
one.
-/

open MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable section

namespace Sandpile

/-- **A union bound over a finite family of pairs, from the two-point far-increment tail.**
Given the two-point exponential tail `exists_far_increment_tail` for the far Green field's
increment between two points at lattice-norm separation at most `M * L`, a union bound over a
finite family `S` of such pairs bounds the probability that some pair's increment exceeds `t` by
`S.card` times the two-point tail. -/
lemma exists_far_pair_union_tail (hBall : External.BallGreenBounds)
    (θ K M : ℝ) (hθ : 0 < θ) (hM : 1 ≤ M) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ r L : ℕ, 2 ≤ r → 2 ≤ L → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      ∀ S : Finset (Site 4 × Site 4),
        (∀ p ∈ S, External.BallGreen.latticeNorm (p.2 - p.1) ≤ M * L) →
      ∀ t : ℝ, 0 ≤ t →
        (LatticeProb.iidLaw 4 μ)
            {ζ | ∃ p ∈ S, t < |finiteKernelField (External.BallGreen.cutField r L φ) ζ p.1 -
              finiteKernelField (External.BallGreen.cutField r L φ) ζ p.2|} ≤
        ENNReal.ofReal ((S.card : ℝ) * C * Real.exp (-(c * min (t ^ 2) (t * (L : ℝ) ^ 2)))) := by
  obtain ⟨c, C, hc, hC, htail⟩ := exists_far_increment_tail hBall θ K M hθ hM
  refine ⟨c, C, hc, hC, ?_⟩
  intro μ hμ hexp hK hmean r L hr hL φ hφ S hS t ht
  let E (p : Site 4 × Site 4) :=
    {ζ | t < |finiteKernelField (External.BallGreen.cutField r L φ) ζ p.1 -
      finiteKernelField (External.BallGreen.cutField r L φ) ζ p.2|}
  have he : {ζ | ∃ p ∈ S, ζ ∈ E p} = ⋃ p ∈ S, E p := by ext ζ; simp
  rw [show {ζ | ∃ p ∈ S, t < |finiteKernelField (External.BallGreen.cutField r L φ) ζ p.1 -
      finiteKernelField (External.BallGreen.cutField r L φ) ζ p.2|} = ⋃ p ∈ S, E p from he]
  calc
    _ ≤ ∑ p ∈ S, (LatticeProb.iidLaw 4 μ) (E p) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal (C * Real.exp (-(c * min (t ^ 2) (t * (L : ℝ) ^ 2)))) :=
      Finset.sum_le_sum
        (fun p hp => htail μ hμ hexp hK hmean r L hr hL φ hφ p.1 p.2 (hS p hp) t ht)
    _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg S.card),
          ENNReal.ofReal_natCast, mul_assoc]

/-- **The floor of `r^α` eventually squares to more than `η log r`.** For large `r`, `⌊r^α⌋ ≥ 2`
and `η * log r ≤ ⌊r^α⌋ ^ 2`, since `log r = o(r^{2α})`. This is the scale comparison
`exists_far_oscillation_bound` needs to feed `L = ⌊r^α⌋` and `t = η log r` into
`exists_far_pair_union_tail`. -/
lemma eventually_log_le_floor_rpow_sq {α η : ℝ} (hα : 0 < α) (_hη : 0 < η) :
    ∀ᶠ r : ℕ in atTop, 2 ≤ r ∧ 2 ≤ ⌊(r : ℝ) ^ α⌋₊ ∧ η * Real.log r ≤ (⌊(r : ℝ) ^ α⌋₊ : ℝ) ^ 2 := by
  have hpowlim : Tendsto (fun r : ℕ => (r : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hlim :
      Tendsto (fun r : ℕ => 4 * η * (Real.log (r : ℝ) / (r : ℝ) ^ (2 * α))) atTop (𝓝 0) := by
    have hh := ((isLittleO_log_rpow_atTop (by positivity : 0 < 2 * α)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply, mul_zero] using hh.const_mul (4 * η)
  filter_upwards [eventually_ge_atTop 2, hpowlim.eventually (eventually_ge_atTop 2),
    (tendsto_order.mp hlim).2 1 (by norm_num)] with r hr hp hs
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hf : (r : ℝ) ^ α / 2 ≤ (⌊(r : ℝ) ^ α⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one ((r : ℝ) ^ α)
    linarith
  have hfpos : 0 ≤ (⌊(r : ℝ) ^ α⌋₊ : ℝ) := Nat.cast_nonneg _
  have hf2 := (sq_le_sq₀ (by positivity : 0 ≤ (r : ℝ) ^ α / 2) hfpos).mpr hf
  have he : ((r : ℝ) ^ α) ^ (2 : ℕ) = (r : ℝ) ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrpos.le]
    congr 1
    norm_num
    ring
  have hsmall : 4 * η * Real.log (r : ℝ) ≤ (r : ℝ) ^ (2 * α) := by
    have hh : (4 * η * Real.log (r : ℝ)) / (r : ℝ) ^ (2 * α) < 1 := by
      simpa only [mul_div_assoc] using hs
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hrpos _)).mp hh).le.trans_eq (one_mul _)
  refine ⟨hr,
    (Nat.le_floor_iff (Real.rpow_nonneg hrpos.le α)).mpr
      (by simpa only [Nat.cast_ofNat] using hp), ?_⟩
  have hh : ((r : ℝ) ^ α) ^ (2 : ℕ) ≤ 4 * (⌊(r : ℝ) ^ α⌋₊ : ℝ) ^ 2 := by nlinarith [hf2]
  rw [he] at hh
  nlinarith

/-- **A polynomial factor is beaten by Gaussian decay once `log r` clears a threshold.** For
`r ≥ 2` with `(m + p) / (c η²) ≤ log r`, the polynomial `r^m` times the Gaussian-type decay
`exp(-c(η log r)²)` is at most the power `r^{-p}`. This is the analytic core turning the
two-point tail's Gaussian decay in `L` into a power-law bound in `r` once `L = ⌊r^α⌋` and the
threshold `t = η log r` are substituted in. -/
lemma polynomial_exp_log_sq_le {c η p : ℝ} (hc : 0 < c) (hη : 0 < η) (m : ℕ)
    {r : ℕ} (hr : 2 ≤ r) (hlog : ((m : ℝ) + p) / (c * η ^ 2) ≤ Real.log r) :
    (r : ℝ) ^ m * Real.exp (-(c * (η * Real.log r) ^ 2)) ≤ (r : ℝ) ^ (-p) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlogpos : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hcη : 0 < c * η ^ 2 := by positivity
  have hmul : (m : ℝ) + p ≤ Real.log r * (c * η ^ 2) := (div_le_iff₀ hcη).mp hlog
  have hh := mul_le_mul_of_nonneg_right hmul hlogpos.le
  have hexp : Real.exp (-(c * (η * Real.log r) ^ 2)) ≤ (r : ℝ) ^ (-(m : ℝ) - p) := by
    rw [Real.rpow_def_of_pos hrpos]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ (r : ℝ) ^ m * (r : ℝ) ^ (-(m : ℝ) - p) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hrpos]
      congr 1
      ring

/-- **Short-distance oscillation over a family growing polynomially in `r`, at separation scale
`⌊r^α⌋`.** For a family `S` of at most `r^m` pairs, each at lattice-norm separation at most
`M * ⌊r^α⌋`, the probability that some pair's far-field increment exceeds `η log r` is at most
`C r^{-p}`, for `r` beyond an explicit threshold `r₀`. Combines the union tail
`exists_far_pair_union_tail` at `L = ⌊r^α⌋`, `t = η log r` with the scale comparison
`eventually_log_le_floor_rpow_sq` and the polynomial-versus-Gaussian estimate
`polynomial_exp_log_sq_le`. -/
lemma exists_far_oscillation_bound (hBall : External.BallGreenBounds)
    (θ K M α η p : ℝ) (hθ : 0 < θ) (hM : 1 ≤ M) (hα : 0 < α) (hη : 0 < η) (m : ℕ) :
    ∃ C > 0, ∃ r₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ r : ℕ, r₀ ≤ r → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      ∀ S : Finset (Site 4 × Site 4), S.card ≤ r ^ m →
        (∀ q ∈ S, External.BallGreen.latticeNorm (q.2 - q.1) ≤ M * ⌊(r : ℝ) ^ α⌋₊) →
        (LatticeProb.iidLaw 4 μ)
            {ζ | ∃ q ∈ S,
              η * Real.log r <
                |finiteKernelField (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ φ) ζ q.1 -
                  finiteKernelField
                    (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ φ) ζ q.2|} ≤
          ENNReal.ofReal (C * (r : ℝ) ^ (-p)) := by
  obtain ⟨c, C, hc, hC, htail⟩ := exists_far_pair_union_tail hBall θ K M hθ hM
  have hloglim : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ r : ℕ in atTop, 2 ≤ r ∧ 2 ≤ ⌊(r : ℝ) ^ α⌋₊ ∧
      η * Real.log r ≤ (⌊(r : ℝ) ^ α⌋₊ : ℝ) ^ 2 ∧
      ((m : ℝ) + p) / (c * η ^ 2) ≤ Real.log r := by
    filter_upwards [eventually_log_le_floor_rpow_sq hα hη,
      hloglim.eventually (eventually_ge_atTop (((m : ℝ) + p) / (c * η ^ 2)))] with r hr hl
    exact ⟨hr.1, hr.2.1, hr.2.2, hl⟩
  obtain ⟨r₀, hr₀⟩ := hev.exists_forall_of_atTop
  refine ⟨C, hC, r₀, ?_⟩
  intro μ hμ hexp hK hmean r hr φ hφ S hcard hS
  obtain ⟨hr2, hL, htL, hlog⟩ := hr₀ r hr
  have ht : 0 ≤ η * Real.log (r : ℝ) := mul_nonneg hη.le (Real.log_natCast_nonneg _)
  have hmin : min ((η * Real.log r) ^ 2) ((η * Real.log r) * (⌊(r : ℝ) ^ α⌋₊ : ℝ) ^ 2) =
      (η * Real.log r) ^ 2 := min_eq_left (by nlinarith [mul_le_mul_of_nonneg_left htL ht])
  have hh := htail μ hμ hexp hK hmean r ⌊(r : ℝ) ^ α⌋₊ hr2 hL φ hφ S hS (η * Real.log r) ht
  rw [hmin] at hh
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcardR : (S.card : ℝ) ≤ (r : ℝ) ^ m := by exact_mod_cast hcard
  calc
    _ ≤ (r : ℝ) ^ m * C * Real.exp (-(c * (η * Real.log r) ^ 2)) := by gcongr
    _ = C * ((r : ℝ) ^ m * Real.exp (-(c * (η * Real.log r) ^ 2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (polynomial_exp_log_sq_le hc hη m hr2 hlog) hC.le

/-- **Short-distance oscillation over pairs drawn from a fixed-aspect-ratio plane rectangle.**
For a plane rectangle of aspect ratio `ϑ ≥ 1` and side `r` (`planeRectangle ⌊ϑ r⌋ r`) translated
near a base point `x`, the probability that some pair `z, w` in it, at lattice-norm separation at
most `M ⌊r^α⌋`, has far-field increment exceeding `η log r` is at most `C r^{-p}`. Reduces to
`exists_far_oscillation_bound` at exponent `m = 6`, since a rectangle of at most `r^3` cells
(`card_planeRectangle_aspect_le_cube`) has at most `(r^3)^2 = r^6` pairs. -/
lemma exists_aspect_rectangle_far_oscillation (hBall : External.BallGreenBounds)
    (θ K M α η p ϑ : ℝ) (hθ : 0 < θ) (hM : 1 ≤ M) (hα : 0 < α) (hη : 0 < η) (hϑ : 1 ≤ ϑ) :
    ∃ C > 0, ∃ r₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ r : ℕ, r₀ ≤ r → ∀ x : Site 4,
        (LatticeProb.iidLaw 4 μ)
            {ζ | ∃ z w : planeRectangle ⌊ϑ * r⌋₊ r,
              External.BallGreen.latticeNorm
                  (planeTranslate x w - planeTranslate x z) ≤ M * ⌊(r : ℝ) ^ α⌋₊ ∧
              η * Real.log r <
                |finiteKernelField
                    (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
                    (planeTranslate x z) -
                  finiteKernelField
                    (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
                    (planeTranslate x w)|} ≤
          ENNReal.ofReal (C * (r : ℝ) ^ (-p)) := by
  classical
  obtain ⟨C, hC, r₀, hosc⟩ := exists_far_oscillation_bound hBall θ K M α η p hθ hM hα hη 6
  refine ⟨C, hC, max r₀ ⌈2 * (ϑ + 1)⌉₊, ?_⟩
  intro μ hμ hexp hK hmean r hr x
  let Q := planeRectangle ⌊ϑ * r⌋₊ r
  let P := (Finset.univ : Finset (Q × Q)).filter (fun q =>
    External.BallGreen.latticeNorm
      (planeTranslate x q.2 - planeTranslate x q.1) ≤ M * ⌊(r : ℝ) ^ α⌋₊)
  let S := P.image (fun q => (planeTranslate x q.1, planeTranslate x q.2))
  have hS : ∀ q ∈ S, External.BallGreen.latticeNorm (q.2 - q.1) ≤ M * ⌊(r : ℝ) ^ α⌋₊ := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hv).2
  have hrϑ : 2 * (ϑ + 1) ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hr)
  have hQ : Q.card ≤ r ^ 3 := card_planeRectangle_aspect_le_cube hϑ hrϑ
  have hcard : S.card ≤ r ^ 6 := by
    calc
      _ ≤ P.card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Q × Q)).card := Finset.card_filter_le _ _
      _ = Q.card ^ 2 := by simp [pow_two]
      _ ≤ (r ^ 3) ^ 2 := Nat.pow_le_pow_left hQ 2
      _ = _ := by ring
  have hh :=
    hosc μ hμ hexp hK hmean r ((le_max_left _ _).trans hr) farCutoff isCutoff_farCutoff S hcard hS
  apply (measure_mono ?_).trans hh
  intro ζ hζ
  obtain ⟨z, w, hdist, hinc⟩ := hζ
  refine ⟨(planeTranslate x z, planeTranslate x w), ?_, hinc⟩
  exact Finset.mem_image.mpr ⟨(z, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩, rfl⟩

/-- **A coordinatewise separation bound gives a lattice-norm bound, up to a factor of two.**
If two points of `Site 2`, translated into `Site 4` at a base point `x`, differ coordinatewise
by at most `R`, their images differ in lattice norm by at most `2R`: only two of the four
coordinates of the difference are nonzero, each bounded by `R`, so the Euclidean norm is at most
`√(2R²) ≤ 2R`. -/
lemma latticeNorm_planeTranslate_sub_le (x : Site 4) (z w : Site 2) {R : ℝ}
    (hR : 0 ≤ R) (hcoord : ∀ i : Fin 2, |(w i : ℝ) - (z i : ℝ)| ≤ R) :
    External.BallGreen.latticeNorm (planeTranslate x w - planeTranslate x z) ≤ 2 * R := by
  have he (i : Fin 4) : (planeTranslate x w - planeTranslate x z) i =
      if i = 0 then w 0 - z 0 else if i = 1 then w 1 - z 1 else 0 := by
    fin_cases i <;> simp [planeTranslate]
  have hb (i : Fin 4) : |((planeTranslate x w - planeTranslate x z) i : ℝ)| ≤ R := by
    rw [he]
    split_ifs
    · simpa only [Int.cast_sub] using hcoord 0
    · simpa only [Int.cast_sub] using hcoord 1
    · simpa using hR
  have hs (i : Fin 4) : (((planeTranslate x w - planeTranslate x z) i : ℝ)) ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hb i)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ _i : Fin 4, R ^ 2 := Finset.sum_le_sum (fun i _ => hs i)
    _ = _ := by simp; ring

/-- **`exists_aspect_rectangle_far_oscillation`, with a coordinatewise box separation bound in
place of the lattice-norm one.** The same conclusion, but the hypothesis on the pair `z, w` is
that each coordinate differs by at most `A * ⌊r^α⌋`, rather than a bound on the lattice norm of
the difference. Reduces to the lattice-norm form at `M = 2A` via
`latticeNorm_planeTranslate_sub_le`. -/
lemma exists_aspect_rectangle_far_oscillation_box (hBall : External.BallGreenBounds)
    (θ K A α η p ϑ : ℝ) (hθ : 0 < θ) (hA : 1 ≤ A) (hα : 0 < α) (hη : 0 < η) (hϑ : 1 ≤ ϑ) :
    ∃ C > 0, ∃ r₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ r : ℕ, r₀ ≤ r → ∀ x : Site 4,
        (LatticeProb.iidLaw 4 μ)
            {ζ | ∃ z w : planeRectangle ⌊ϑ * r⌋₊ r,
              (∀ i : Fin 2,
                  |((w : Site 2) i : ℝ) - ((z : Site 2) i : ℝ)| ≤ A * ⌊(r : ℝ) ^ α⌋₊) ∧
              η * Real.log r <
                |finiteKernelField
                    (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
                    (planeTranslate x z) -
                  finiteKernelField
                    (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ
                    (planeTranslate x w)|} ≤
          ENNReal.ofReal (C * (r : ℝ) ^ (-p)) := by
  obtain ⟨C, hC, r₀, hosc⟩ :=
    exists_aspect_rectangle_far_oscillation hBall θ K (2 * A) α η p ϑ hθ (by linarith) hα hη hϑ
  refine ⟨C, hC, r₀, ?_⟩
  intro μ hμ hexp hK hmean r hr x
  apply (measure_mono ?_).trans (hosc μ hμ hexp hK hmean r hr x)
  intro ζ hζ
  obtain ⟨z, w, hdist, hinc⟩ := hζ
  refine ⟨z, w, ?_, hinc⟩
  have hnn : 0 ≤ A * (⌊(r : ℝ) ^ α⌋₊ : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
  simpa only [mul_assoc] using latticeNorm_planeTranslate_sub_le x z w hnn hdist

end Sandpile
