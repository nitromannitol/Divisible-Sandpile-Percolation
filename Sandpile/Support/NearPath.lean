import Sandpile.Support.ColoredBoxes
import Sandpile.Support.BoxPathCount

/-!
# Superpolynomial control of near-field bad-box paths

Superpolynomial control of fixed-length simple paths of near-field bad boxes, with
polynomially many possible starting vertices. `exists_near_boxPath_tail` combines the
per-box tail bound `exists_near_many_boxes_bound` with the path-counting estimate
`measure_boxPathEvent_le`: the path length `n = 49m` and the exponent `m` are chosen so that
`b·m ≥ p + 3`, which absorbs both the `9ⁿ` path-counting factor and the polynomial number
`r³` of possible starting vertices `S`, leaving a net probability bound of order `r^{-p}`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section
namespace Sandpile

/-- **Superpolynomial control of a fixed-length simple path of near-field bad boxes.**  Fixes
an exponent `α < 1` and a path length `n = 49m`, with `m` large enough that `b·m ≥ p + 3`, so
that the per-box tail probability from `exists_near_many_boxes_bound` raised through the
path-counting bound `measure_boxPathEvent_le` beats both the `9ⁿ` path-counting factor and the
polynomial `r³` bound on the number `S.card` of possible starting vertices. -/
lemma exists_near_boxPath_tail (hBall : External.BallGreenBounds)
    (θ K η p : ℝ) (hθ : 0 < θ) (hη : 0 < η) (_hp : 0 < p) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧ ∃ n r₀ : ℕ, 2 ≤ r₀ ∧
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
        Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
        (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
        ∀ r : ℕ, r₀ ≤ r → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
          ∀ (x : Site 4) (S : Finset (Site 2)), S.card ≤ r ^ 3 →
            (LatticeProb.iidLaw 4 μ) (boxPathEvent n S (fun a =>
              kernelLowEvent (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ)
                (planeBox (coarsePlaneCenter x ⌊(r : ℝ) ^ α⌋₊ a) ⌊(r : ℝ) ^ α⌋₊)
                  (-η * Real.log r))) ≤
              ENNReal.ofReal (C * (r : ℝ) ^ (-p)) := by
  obtain ⟨α, b, C, hα, hα1, hb, hC, r₀, hr₀, hmany⟩ :=
    exists_near_many_boxes_bound hBall θ K η hθ hη
  let m : ℕ := ⌈(p + 3) / b⌉₊
  have hm : p + 3 ≤ b * (m : ℝ) := by
    have hh := Nat.le_ceil ((p + 3) / b)
    have he := (div_le_iff₀ hb).mp hh
    linarith
  let n := 49 * m
  let D := (9 : ℝ) ^ n * C ^ m
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨α, D, hα, hα1, hD, n, r₀, hr₀, ?_⟩
  intro μ hμ hexp hK hmean r hr φ hφ x S hcard
  have hr2 : 2 ≤ r := hr₀.trans hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  let E (a : Site 2) := kernelLowEvent (nearKernel r ⌊(r : ℝ) ^ α⌋₊ φ)
    (planeBox (coarsePlaneCenter x ⌊(r : ℝ) ^ α⌋₊ a) ⌊(r : ℝ) ^ α⌋₊) (-η * Real.log r)
  have hh := measure_boxPathEvent_le (LatticeProb.iidLaw 4 μ) n (49 * m) (by omega) S E
    (fun T hT => hmany μ hμ hexp hK hmean r hr φ hφ x m T hT)
  have he : ENNReal.ofReal ((S.card : ℝ) * (9 : ℝ) ^ n * (C ^ m * (r : ℝ) ^ (-b * (m : ℝ)))) =
      (S.card : ℝ≥0∞) * (3 ^ 2 : ℝ≥0∞) ^ n * ENNReal.ofReal (C ^ m * (r : ℝ) ^ (-b * (m : ℝ))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    norm_num
  rw [← he] at hh
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcardR : (S.card : ℝ) ≤ (r : ℝ) ^ 3 := by exact_mod_cast hcard
  calc
    _ ≤ (r : ℝ) ^ 3 * (9 : ℝ) ^ n * (C ^ m * (r : ℝ) ^ (-b * (m : ℝ))) := by gcongr
    _ = D * (r : ℝ) ^ ((3 : ℝ) - b * (m : ℝ)) := by
      dsimp [D]
      rw [sub_eq_add_neg, Real.rpow_add hrpos, Real.rpow_ofNat]
      ring_nf
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ r)) (by linarith)) hD.le

end Sandpile
