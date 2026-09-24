/-
The exploration of Step 2 of `prop:fixed-scale-crossings` exists (`sandpile.tex:2255-2296`),
and with it the proposition itself.

The rule of `CrossExploreRule`, run at the level `L/(2R)`, reveals the cells of the squares it
discovers; `CrossExploreRec` makes its revealed set a stopping set, `CrossExploreDecide` makes
it decide the crossing at the level `L/R` of the field it computes, and `CrossExploreCount`
bounds the expected number of cells it reveals by the layer sum of the arm estimate.  That is
the hypothesis `hexp` of `fixed_scale_crossings_of_cell_exploration`, so the proposition
follows.
-/
import Sandpile.Support.CrossExploreCount
import Sandpile.Support.CrossExploreReduction
import Sandpile.External.PinskerProved

open MeasureTheory ProbabilityTheory Filter
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped NNReal ENNReal

namespace Sandpile.Support

theorem toNat_cast_le {m : ℤ} {X : ℝ} (hX : 0 ≤ X) (h : (m : ℝ) ≤ X) :
    ((m.toNat : ℕ) : ℝ) ≤ X := by
  rcases le_or_gt 0 m with hm | hm
  · have he : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    have he' : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast he
    rw [he']
    exact h
  · have he : m.toNat = 0 := Int.toNat_eq_zero.mpr (le_of_lt hm)
    rw [he]
    simpa using hX

/-- **The exploration of Step 2 exists.**  At every model and every scale there is a rule
revealing the unit cells one at a time on the strength of the cells already revealed, which
decides the crossing of the field it computes, reveals subquadratically many cells in
expectation, and can reveal every cell meeting the unit ball about a point of the rectangle. -/
theorem exists_cell_exploration (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG) (d : ℕ) (hd : d = 2 ∨ d = 3)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ Cn α₁ : ℝ, 0 ≤ Cn ∧ 0 < α₁ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P, Continuous fun x => ballField d W s x ω) →
        ∀ L : ℝ, 0 < L → ∀ R : ℝ, max 1 θ⁻¹ ≤ R →
        ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (z : ι → Sandpile.Site d)
          (S : Ω → Finset ι) (X : Space 2 → Ω → ℝ),
          Function.Injective z ∧ 0 < Fintype.card ι ∧
          IsIndepStoppingSet (fun i => noiseBlockAlg W (cell d 1 (z i))) S ∧
          (∫ ω, ((S ω).card : ℝ) ∂P) ≤ Cn * R ^ (2 - α₁) ∧
          (∀ u : Space 2, X u =ᵐ[P] ballField d W 1 u) ∧
          IndepBlockDecides (fun i => noiseBlockAlg W (cell d 1 (z i))) S
            (closedCrossEvent X ![-(θ * R), 0] ![θ * R, 2 * R] 0 (L / R)) ∧
          (∀ u ∈ rectSet ![-(θ * R), 0] ![θ * R, 2 * R],
            ∀ y : Space d, ‖(planePoint (d := d) u) - y‖ < 1 →
              y ∈ ⋃ i, cell d 1 (z i)) := by
  classical
  obtain ⟨C, α, hC, hα, harm⟩ := uniform_positiveArm_power hRSW hPitt
  set c₀ : ℝ := 1 + θ + θ⁻¹ with hc₀
  have hθinv : 0 < θ⁻¹ := inv_pos.mpr hθ
  have hc₀ge : 3 ≤ c₀ := by
    rw [hc₀]
    have h2 : 2 ≤ θ + θ⁻¹ := by
      have hkey : θ + θ⁻¹ - 2 = (θ - 1) ^ 2 / θ := by field_simp; ring
      have hnn : (0 : ℝ) ≤ (θ - 1) ^ 2 / θ := div_nonneg (sq_nonneg (θ - 1)) hθ.le
      linarith
    linarith
  have hc₀pos : (0 : ℝ) < c₀ := by linarith
  refine ⟨(5 : ℝ) ^ d * (3 * (2 + 3 * (C * 9 ^ α + 4 ^ α))) * c₀ ^ (2 : ℝ), α / (1 + α),
    by positivity, by positivity, ?_⟩
  intro Ω _ P _ W hW hcont L hL R hR
  have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
  have hRθ : θ⁻¹ ≤ R := le_trans (le_max_right _ _) hR
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  set a : Fin 2 → ℝ := ![-(θ * R), 0] with ha
  set b : Fin 2 → ℝ := ![θ * R, 2 * R] with hb
  have ha0 : a 0 = -(θ * R) := rfl
  have ha1 : a 1 = 0 := rfl
  have hb0 : b 0 = θ * R := rfl
  have hb1 : b 1 = 2 * R := rfl
  have hab : ∀ i, a i < b i := crossing_rect_lt hθ hR
  set lev : ℝ := L / (2 * R) with hlevdef
  have hlevpos : 0 < lev := by rw [hlevdef]; positivity
  have hlevlt : lev < L / R := by
    rw [hlevdef, div_lt_div_iff₀ (by linarith) hR0]
    nlinarith
  have hbm := blockMeasurable_blockField (W := W) hd a b
  have hrule := isExplorationRule_exploreNext (lev := lev) hbm
  have hcont1 := hcont 1 one_pos le_rfl
  refine ⟨cellIdx d a b, inferInstance, inferInstance, Subtype.val,
    exploreSet (exploreNext d a b lev (blockField d W)), blockField d W,
    Subtype.val_injective, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_coe]
    exact Finset.card_pos.mpr (allSites_nonempty d hab)
  · exact isIndepStoppingSet_exploreSet hrule
  · -- the count
    have hJ : (((⌊b 1⌋ - ⌊a 1⌋).toNat : ℕ) : ℝ) + 1 ≤ 3 * (c₀ * R) := by
      have hm : ((⌊b 1⌋ - ⌊a 1⌋ : ℤ) : ℝ) ≤ 2 * R := by
        push_cast
        rw [ha1, hb1]
        have h1 : ((⌊(2 : ℝ) * R⌋ : ℤ) : ℝ) ≤ 2 * R := Int.floor_le _
        have h2 : ((⌊(0 : ℝ)⌋ : ℤ) : ℝ) = 0 := by norm_num
        linarith
      have := toNat_cast_le (by linarith : (0:ℝ) ≤ 2 * R) hm
      nlinarith
    have hK : (((⌊b 0⌋ - ⌊a 0⌋).toNat : ℕ) : ℝ) + 1 ≤ 3 * (c₀ * R) := by
      have hm : ((⌊b 0⌋ - ⌊a 0⌋ : ℤ) : ℝ) ≤ 2 * (θ * R) + 1 := by
        push_cast
        rw [ha0, hb0]
        have h1 : ((⌊θ * R⌋ : ℤ) : ℝ) ≤ θ * R := Int.floor_le _
        have h2 : -(θ * R) - 1 < ((⌊-(θ * R)⌋ : ℤ) : ℝ) := by
          linarith [Int.lt_floor_add_one (-(θ * R))]
        linarith
      have hnn : (0:ℝ) ≤ 2 * (θ * R) + 1 := by positivity
      have := toNat_cast_le hnn hm
      have hpos : (0:ℝ) ≤ θ⁻¹ * R := by positivity
      nlinarith
    have hcount := expected_cells_le (a := a) (b := b) (lev := lev) hd hW hcont1 hlevpos hC hα
      (harm d hd Ω P W hW hcont1) (by nlinarith : (1:ℝ) ≤ c₀ * R) hJ hK
    refine le_trans hcount ?_
    · have hsplit : (c₀ * R) ^ (2 - α / (1 + α)) = c₀ ^ (2 - α / (1 + α)) * R ^ (2 - α / (1 + α)) :=
        Real.mul_rpow hc₀pos.le hR0.le
      rw [hsplit]
      have hexp : c₀ ^ (2 - α / (1 + α)) ≤ c₀ ^ (2 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
        have : 0 ≤ α / (1 + α) := by positivity
        linarith
      have hnn : (0:ℝ) ≤ (5 : ℝ) ^ d * (3 * (2 + 3 * (C * 9 ^ α + 4 ^ α))) := by positivity
      have hRp : (0:ℝ) ≤ R ^ (2 - α / (1 + α)) := Real.rpow_nonneg hR0.le _
      calc (5 : ℝ) ^ d * (3 * (2 + 3 * (C * 9 ^ α + 4 ^ α)))
              * (c₀ ^ (2 - α / (1 + α)) * R ^ (2 - α / (1 + α)))
          ≤ (5 : ℝ) ^ d * (3 * (2 + 3 * (C * 9 ^ α + 4 ^ α)))
              * (c₀ ^ (2 : ℝ) * R ^ (2 - α / (1 + α))) := by
            refine mul_le_mul_of_nonneg_left ?_ hnn
            exact mul_le_mul_of_nonneg_right hexp hRp
        _ = (5 : ℝ) ^ d * (3 * (2 + 3 * (C * 9 ^ α + 4 ^ α))) * c₀ ^ (2 : ℝ)
              * R ^ (2 - α / (1 + α)) := by ring
  · exact fun u => blockField_ae_eq hd hW u
  · exact indepBlockDecides_exploreSet hbm hlevlt
  · intro u hu
    refine cover_of_nearSites_range (fun i : cellIdx d a b => (i : Sandpile.Site d)) u ?_
    intro x hx
    exact ⟨⟨x, nearSites_subset_allSites hu hx⟩, rfl⟩

/-- **`prop:fixed-scale-crossings`** (`sandpile.tex:2119-2135`), from the three steps of its
proof: the zero-level crossing of Step 1, the exploration of Step 2, and the adaptive
Cameron--Martin comparison of Step 3. -/
theorem fixed_scale_crossings_proved (hRSW : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG) (d : ℕ) (hd : d = 2 ∨ d = 3)
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : (Space d → ℝ) → Ω → ℝ), IsWhiteNoise d W P →
        (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂P, Continuous fun x => ballField d W s x ω) →
      ∀ L : ℝ, 0 ≤ L →
        ENNReal.ofReal p ≤ liminf (fun R : ℝ => P {ω |
          Crosses ![-(θ * R), 0] ![θ * R, 2 * R] 0
            {x | L / R ≤ ballField d W 1 x ω}}) atTop := by
  obtain ⟨Cn, α₁, hCn, hα₁, hexp⟩ := exists_cell_exploration hRSW hPitt d hd θ hθ
  exact fixed_scale_crossings_of_cell_exploration hRSW hPitt Sandpile.External.pinsker d hd θ hθ
    Cn α₁ hCn hα₁ hexp

end Sandpile.Support
