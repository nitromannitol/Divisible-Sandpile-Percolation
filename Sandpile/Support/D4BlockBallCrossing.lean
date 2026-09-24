/-
Step 3 of the dimension-four percolation proof for the ball field: the
good-block event of `𝓑_{2r}` at the level `-ε log(2r)` fails with probability
at most `B log³(2r)(2r)^{-γ}`, uniformly in the coarse site.  The four clauses
of the block event are the four blocking `∗`-crossings of
`thm:d4-ball-green-crossing` at aspects one and two, the two bottom-top ones
read at the reflected block corner.
-/
import Sandpile.Support.D4BlockUnion
import Sandpile.Support.D4SwapField
import Sandpile.Frozen.D4BallGreenCrossing

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Sandpile


/-- Step 3 of the dimension-four proof for the ball field: the good-block event
of the ball field at the level `-ε log(2r)` fails with polynomially small
probability, uniformly in the coarse site. -/
theorem measure_not_blockGood_ballField_le
    (hBallGreen : Sandpile.External.BallGreenBounds)
    (hRSW : Sandpile.External.PlanarRSW)
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ γ B : ℝ, 0 < γ ∧ 0 < B ∧ ∃ r₀ : ℕ, ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ r : ℕ, r₀ ≤ r → ∀ z : Sandpile.Site 2,
        LatticeProb.iidLaw 4 ν
            {ζ : Site 4 → ℝ | ¬ BlockGood r
              (fun u => ballGreenField (2 * r) ζ (planeEmbed u))
              (-(ε * Real.log ((2 * r : ℕ) : ℝ))) z}
          ≤ ENNReal.ofReal (B * (Real.log ((2 * r : ℕ) : ℝ)) ^ 3 *
              ((2 * r : ℕ) : ℝ) ^ (-γ)) := by
  obtain ⟨γ₁, C₁, hγ₁, hC₁, r₁, h₁⟩ :=
    Sandpile.Frozen.d4_ball_green_crossing hBallGreen hRSW ν₀ θ₀ K₀ 1 hν₀ hθ₀ le_rfl ε hε
  obtain ⟨γ₂, C₂, hγ₂, hC₂, r₂, h₂⟩ :=
    Sandpile.Frozen.d4_ball_green_crossing hBallGreen hRSW ν₀ θ₀ K₀ 2 hν₀ hθ₀ (by norm_num) ε hε
  refine ⟨min γ₁ γ₂, 2 * (C₁ + C₂), lt_min hγ₁ hγ₂, by positivity, max (max r₁ r₂) 1, ?_⟩
  intro ν hν hmean hvar hint hK r hr z
  have hr1 : r₁ ≤ 2 * r := by omega
  have hr2 : r₂ ≤ 2 * r := by omega
  have hrpos : 1 ≤ 2 * r := by omega
  set M : ℝ := ((2 * r : ℕ) : ℝ) with hM
  set L : ℝ := Real.log M with hL
  set x : Site 4 := planeEmbed ![2 * (r : ℤ) * z 0, 2 * (r : ℤ) * z 1] with hx
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    exact_mod_cast hrpos
  have hL0 : 0 ≤ L := Real.log_nonneg hM1
  have e1 := h₁ ν hν hmean hvar hint hK (2 * r) hr1 x
  have e1' := h₁ ν hν hmean hvar hint hK (2 * r) hr1
    (permuteSite (Equiv.swap (0 : Fin 4) 1) x)
  have e2 := h₂ ν hν hmean hvar hint hK (2 * r) hr2 x
  have e2' := h₂ ν hν hmean hvar hint hK (2 * r) hr2
    (permuteSite (Equiv.swap (0 : Fin 4) 1) x)
  have hswap1 := measure_star_crossing_swap_le' ν 1 (2 * r) (2 * r) x (-(ε * L))
  have hswap2 := measure_star_crossing_swap_le' ν 2 (2 * r) (2 * r) x (-(ε * L))
  have hmono : ∀ (C γ' : ℝ), 0 < C → min γ₁ γ₂ ≤ γ' →
      ENNReal.ofReal (C * L ^ 3 * M ^ (-γ'))
        ≤ ENNReal.ofReal (C * L ^ 3 * M ^ (-min γ₁ γ₂)) := by
    intro C γ' hC hle
    refine ENNReal.ofReal_le_ofReal ?_
    have hpow : M ^ (-γ') ≤ M ^ (-min γ₁ γ₂) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    have : (0 : ℝ) ≤ C * L ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_left hpow this
  have hfin := measure_not_blockGood_le (LatticeProb.iidLaw 4 ν) r
    (fun ζ : Site 4 → ℝ => ballGreenField (2 * r) ζ) (-(ε * L)) z
  refine hfin.trans ?_
  have b1 : LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | HasStarTopBottomCrossing 1 (2 * r) x
      {y | ballGreenField (2 * r) ζ y ≤ -(ε * L)}}
      ≤ ENNReal.ofReal (C₁ * L ^ 3 * M ^ (-min γ₁ γ₂)) :=
    e1.trans (hmono C₁ γ₁ hC₁ (min_le_left _ _))
  have b2 : LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | HasStarTopBottomCrossing 1 (2 * r) x
      {y | ballGreenField (2 * r) ζ (swapPlaneAbout x y) ≤ -(ε * L)}}
      ≤ ENNReal.ofReal (C₁ * L ^ 3 * M ^ (-min γ₁ γ₂)) :=
    hswap1.trans (e1'.trans (hmono C₁ γ₁ hC₁ (min_le_left _ _)))
  have b3 : LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | HasStarTopBottomCrossing 2 (2 * r) x
      {y | ballGreenField (2 * r) ζ y ≤ -(ε * L)}}
      ≤ ENNReal.ofReal (C₂ * L ^ 3 * M ^ (-min γ₁ γ₂)) :=
    e2.trans (hmono C₂ γ₂ hC₂ (min_le_right _ _))
  have b4 : LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | HasStarTopBottomCrossing 2 (2 * r) x
      {y | ballGreenField (2 * r) ζ (swapPlaneAbout x y) ≤ -(ε * L)}}
      ≤ ENNReal.ofReal (C₂ * L ^ 3 * M ^ (-min γ₁ γ₂)) :=
    hswap2.trans (e2'.trans (hmono C₂ γ₂ hC₂ (min_le_right _ _)))
  have hsum := add_le_add (add_le_add b1 b2) (add_le_add b3 b4)
  refine hsum.trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  ring_nf
  rfl

end Sandpile
