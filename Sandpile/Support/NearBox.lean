import Sandpile.Support.FarOscillation
import Sandpile.Support.NearTail

/-!
# Near-field tail and bad-box probabilities

Polynomial tail bounds for the near-field kernel `nearKernel`, established after a uniform
choice of the mesoscopic cutoff exponent `α`. `exists_near_point_bound` gives a single-site
large-deviation bound `P (nearKernel-field ≤ -η log r) ≤ C r ^ (-b)` for measures with a finite
exponential moment and mean zero, and `exists_near_bad_box_bound` extends it by a union bound
over a box `S` of side `⌊r ^ α⌋₊ + 1`. The auxiliary lemmas `eventually_near_log_bound` and
`near_tail_logarithmic_regime` control how the cutoff exponent `α` must scale with `r` for the
logarithmic tail bound to stay effective.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace Sandpile

/-- For every `α > 0`, eventually in `r`: `2 ≤ r`, `2 ≤ ⌊r ^ α⌋₊`, and
`log (2 * ⌊r ^ α⌋₊ + 2) ≤ 2 * α * log r`; this keeps the mesoscopic box size `⌊r ^ α⌋₊`
controlled by a logarithm of `r`. -/
lemma eventually_near_log_bound {α : ℝ} (hα : 0 < α) :
    ∀ᶠ r : ℕ in atTop, 2 ≤ r ∧ 2 ≤ ⌊(r : ℝ) ^ α⌋₊ ∧
      Real.log (2 * (⌊(r : ℝ) ^ α⌋₊ : ℝ) + 2) ≤ 2 * α * Real.log r := by
  have hpowlim : Tendsto (fun r : ℕ => (r : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hloglim : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, hpowlim.eventually (eventually_ge_atTop 2),
    hloglim.eventually (eventually_ge_atTop (Real.log 4 / α))] with r hr hp hlog
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hf := Nat.floor_le (Real.rpow_nonneg hrpos.le α)
  have hL : 2 ≤ ⌊(r : ℝ) ^ α⌋₊ :=
    (Nat.le_floor_iff (Real.rpow_nonneg hrpos.le α)).mpr (by simpa only [Nat.cast_ofNat] using hp)
  have hfour : Real.log 4 ≤ α * Real.log (r : ℝ) := by
    have hh := (div_le_iff₀ hα).mp hlog
    linarith
  refine ⟨hr, hL, ?_⟩
  calc
    _ ≤ Real.log (4 * (r : ℝ) ^ α) := Real.log_le_log (by positivity) (by linarith)
    _ = Real.log 4 + α * Real.log (r : ℝ) := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hrpos α).ne',
        Real.log_rpow hrpos]
    _ ≤ _ := by linarith

/-- Under the log bound `log (2 * L + 2) ≤ 2 * α * log r` and `4 * α ≤ η`, the minimum of
`((η / 2) * log r) ^ 2 / log (2 * L + 2)` and `(η / 2) * log r` collapses to its second
argument, so the Bernstein-type tail rate reduces to the linear term. -/
lemma near_tail_logarithmic_regime {r L : ℕ} {α η : ℝ}
    (hr : 2 ≤ r) (_hα : 0 < α) (hη : 0 < η) (hsmall : 4 * α ≤ η)
    (hlog : Real.log (2 * (L : ℝ) + 2) ≤ 2 * α * Real.log r) :
    min (((η / 2) * Real.log r) ^ 2 / Real.log (2 * (L : ℝ) + 2))
      ((η / 2) * Real.log r) = (η / 2) * Real.log r := by
  have hrlog : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hLlog : 0 < Real.log (2 * (L : ℝ) + 2) :=
    Real.log_pos (by have := Nat.cast_nonneg (α := ℝ) L; linarith)
  apply min_eq_right
  apply (le_div_iff₀ hLlog).mpr
  have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ (η / 2) * Real.log (r : ℝ))
  have hs := mul_nonneg (sub_nonneg.mpr hsmall) (sq_nonneg (Real.log (r : ℝ)))
  nlinarith [mul_nonneg hη.le hs]

/-- Given `External.BallGreenBounds` and `θ, K, η > 0`, produces `b, α₀, C > 0` such that for
every small enough cutoff exponent `α ≤ α₀` there is a threshold `r₀` past which, for any
zero-mean measure `μ` with `∫ exp (θ * |x|) ∂μ ≤ K`, cutoff `φ`, and site `z`, the probability
that `finiteKernelField (nearKernel r ⌊r ^ α⌋₊ φ) ζ z ≤ -η * log r` is at most `C * r ^ (-b)`. -/
lemma exists_near_point_bound (hBall : External.BallGreenBounds)
    (θ K η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ b α₀ C : ℝ, 0 < b ∧ 0 < α₀ ∧ 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
      ∃ r₀ : ℕ, 2 ≤ r₀ ∧ ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
        Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
        (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
        ∀ r : ℕ, r₀ ≤ r → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ z : Site 4,
          (LatticeProb.iidLaw 4 μ)
            {ζ | finiteKernelField (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ) ζ z ≤ -η * Real.log r} ≤
            ENNReal.ofReal (C * (r : ℝ) ^ (-b)) := by
  obtain ⟨c, C, hc, hC, htail⟩ := exists_near_field_tail hBall θ K hθ
  refine ⟨c * η / 2, η / 4, C, by positivity, by positivity, hC, ?_⟩
  intro α hα hαsmall
  obtain ⟨r₀, hr₀⟩ := (eventually_near_log_bound hα).exists_forall_of_atTop
  refine ⟨max 2 r₀, le_max_left _ _, ?_⟩
  intro μ hμ hexp hK hmean r hr φ hφ z
  obtain ⟨hr2, hL, hlog⟩ := hr₀ r ((le_max_right _ _).trans hr)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlogpos : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have htpos : 0 < (η / 2) * Real.log (r : ℝ) := by positivity
  have hsub :
      {ζ : Site 4 → ℝ | finiteKernelField (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ) ζ z ≤ -η * Real.log r} ⊆
      {ζ | (η / 2) * Real.log r < |finiteKernelField (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ) ζ z|} := by
    intro ζ hζ
    change finiteKernelField (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ) ζ z ≤ -η * Real.log r at hζ
    change (η / 2) * Real.log r < |finiteKernelField (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ) ζ z|
    linarith [neg_le_abs (finiteKernelField (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ) ζ z)]
  have hh := htail μ hμ hexp hK hmean r ⌊(r : ℝ) ^ α⌋₊ hr2 hL φ hφ z ((η / 2) * Real.log r) htpos.le
  rw [near_tail_logarithmic_regime hr2 hα hη (by linarith) hlog] at hh
  have he : Real.exp (-(c * ((η / 2) * Real.log (r : ℝ)))) = (r : ℝ) ^ (-(c * η / 2)) := by
    rw [Real.rpow_def_of_pos hrpos]
    congr 1
    ring
  exact (measure_mono hsub).trans (by simpa only [he] using hh)

/-- A finite set `S` of sites with `S.card ≤ (⌊r ^ α⌋₊ + 1) ^ 2` has cardinality at most
`4 * r ^ (2 * α)`, obtained by squaring the elementary bound `⌊r ^ α⌋₊ ≤ r ^ α` on the floor. -/
lemma near_box_card_bound {r : ℕ} {α : ℝ} (hr : 2 ≤ r) (hα : 0 < α)
    (S : Finset (Site 4)) (hcard : S.card ≤ (⌊(r : ℝ) ^ α⌋₊ + 1) ^ 2) :
    (S.card : ℝ) ≤ 4 * (r : ℝ) ^ (2 * α) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hp : 1 ≤ (r : ℝ) ^ α := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ r)) hα.le
  have hf := Nat.floor_le (Real.rpow_nonneg hrpos.le α)
  have hcardR : (S.card : ℝ) ≤ ((⌊(r : ℝ) ^ α⌋₊ : ℝ) + 1) ^ 2 := by exact_mod_cast hcard
  have he : ((r : ℝ) ^ α) ^ (2 : ℕ) = (r : ℝ) ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrpos.le]
    congr 1
    norm_num
    ring
  rw [← he]
  nlinarith [Nat.cast_nonneg (α := ℝ) ⌊(r : ℝ) ^ α⌋₊,
    mul_nonneg (show 0 ≤ 2 * (r : ℝ) ^ α - ((⌊(r : ℝ) ^ α⌋₊ : ℝ) + 1) by linarith)
      (show 0 ≤ 2 * (r : ℝ) ^ α + ((⌊(r : ℝ) ^ α⌋₊ : ℝ) + 1) by positivity)]

/-- Union-bound strengthening of `exists_near_point_bound`: for a box `S` of at most
`(⌊r ^ α⌋₊ + 1) ^ 2` sites, the probability that `finiteKernelField (nearKernel r ⌊r ^ α⌋₊ φ) ζ z`
drops below `-η * log r` at some `z ∈ S` is still at most `C * r ^ (-b)`, the box-size factor
from `near_box_card_bound` being absorbed into the constant. -/
lemma exists_near_bad_box_bound (hBall : External.BallGreenBounds)
    (θ K η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ α b C : ℝ, 0 < α ∧ α < 1 ∧ 0 < b ∧ 0 < C ∧ ∃ r₀ : ℕ, 2 ≤ r₀ ∧
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
        Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
        (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
        ∀ r : ℕ, r₀ ≤ r → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
          ∀ S : Finset (Site 4), S.card ≤ (⌊(r : ℝ) ^ α⌋₊ + 1) ^ 2 →
            (LatticeProb.iidLaw 4 μ) {ζ | ∃ z ∈ S,
              finiteKernelField (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ) ζ z ≤ -η * Real.log r} ≤
              ENNReal.ofReal (C * (r : ℝ) ^ (-b)) := by
  obtain ⟨b, α₀, C, hb, hα₀, hC, hpoint⟩ := exists_near_point_bound hBall θ K η hθ hη
  let α := min (1 / 2 : ℝ) (min α₀ (b / 4))
  have hα : 0 < α := lt_min (by norm_num) (lt_min hα₀ (by positivity))
  have hαhalf : α ≤ 1 / 2 := min_le_left _ _
  have hα₀le : α ≤ α₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hαb : α ≤ b / 4 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨r₀, hr₀, htail⟩ := hpoint α hα hα₀le
  refine ⟨α, b / 2, 4 * C, hα, by linarith, by positivity, by positivity, r₀, hr₀, ?_⟩
  intro μ hμ hexp hK hmean r hr φ hφ S hcard
  have hr2 : 2 ≤ r := hr₀.trans hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  let E (z : Site 4) :=
    {ζ | finiteKernelField (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ) ζ z ≤ -η * Real.log r}
  have he : {ζ | ∃ z ∈ S, ζ ∈ E z} = ⋃ z ∈ S, E z := by ext ζ; simp
  change (LatticeProb.iidLaw 4 μ) {ζ | ∃ z ∈ S, ζ ∈ E z} ≤ _
  rw [he]
  calc
    _ ≤ ∑ z ∈ S, (LatticeProb.iidLaw 4 μ) (E z) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ S, ENNReal.ofReal (C * (r : ℝ) ^ (-b)) :=
      Finset.sum_le_sum (fun z _ => htail μ hμ hexp hK hmean r hr φ hφ z)
    _ = ENNReal.ofReal ((S.card : ℝ) * C * (r : ℝ) ^ (-b)) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg S.card),
        ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (4 * (r : ℝ) ^ (2 * α)) * C * (r : ℝ) ^ (-b) := by
          gcongr
          exact near_box_card_bound hr2 hα S hcard
        _ = (4 * C) * (r : ℝ) ^ (2 * α - b) := by
          rw [sub_eq_add_neg, Real.rpow_add hrpos]
          ring
        _ ≤ (4 * C) * (r : ℝ) ^ (-(b / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ r))
          linarith

end Sandpile
