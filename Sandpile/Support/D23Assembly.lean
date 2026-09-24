/-
The assembly of the dimension-two and dimension-three critical level-set
percolation theorem (`sandpile.tex:2576-2612`) from the block-crossing estimate
`eq:d23-block-crossing-estimate`: the good-block process of the localized
odometer field is measurable, stationary and finite-range dependent, so the
block-crossing estimate gives, through \citet[Corollary~1.4]{LSS}, an infinite
nearest-neighbour component of the localized level set at the block scale
`R = ⌊√(t/T)⌋`, and the localized odometer at the block horizon `⌊R²T⌋ ≤ t` is
dominated by the odometer at time `t`, whose level `ct^{(4-d)/4}` is below
`cR^{2-d/2}`.
-/
import Sandpile.Support.D23Input
import Sandpile.Support.D23Component
import Sandpile.Support.D23Scale
import Sandpile.Support.D4GoodBlock

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Sandpile

open scoped Classical

/-- The critical level-set percolation theorem in dimensions two and three, from
the block-crossing estimate. -/
theorem d23_critical_level_percolation_of_block_crossing
    (hLSS : Sandpile.External.LSSDomination)
    (d : ℕ) (hd : d = 2 ∨ d = 3) (ν₀ θ₀ K₀ : ℝ) (_hν₀ : 0 < ν₀) (_hθ₀ : 0 < θ₀)
    (hCross : D23BlockCrossing d ν₀ θ₀ K₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
          LatticeProb.HasInfiniteComponent
            {z : Site 2 | c * (t : ℝ) ^ ((4 - (d : ℝ)) / 4) <
              Sandpile.odometer σ t (Sandpile.planeSite z)} := by
  classical
  have hd1 : 1 ≤ d := by rcases hd with h | h <;> omega
  have hd2 : 2 ≤ d := by rcases hd with h | h <;> omega
  have hd3 : d ≤ 3 := by rcases hd with h | h <;> omega
  obtain ⟨δ, hδ, hLSSmain⟩ := Sandpile.good_block_percolation hLSS 10
  obtain ⟨c, Tm, hc, hTm, R₀, hR₀, hbe⟩ := hCross δ hδ
  refine ⟨c / (2 * (4 * Tm) ^ ((4 - (d : ℝ)) / 4)), by positivity,
    ⌈4 * Tm * ((R₀ : ℝ) + 1) ^ 2⌉₊, ?_⟩
  intro ν hν hmean hvar hexpint hexp t ht
  haveI := hν
  have hR₀R : (1 : ℝ) ≤ (R₀ : ℝ) := by exact_mod_cast hR₀
  have htceil : 4 * Tm * ((R₀ : ℝ) + 1) ^ 2 ≤ (t : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast ht)
  have hsq1 : (1 : ℝ) ≤ ((R₀ : ℝ) + 1) ^ 2 := by nlinarith
  have h4T : 4 * Tm ≤ (t : ℝ) := by nlinarith
  have hTR₀ : Tm * ((R₀ : ℝ)) ^ 2 ≤ (t : ℝ) := by nlinarith
  set R : ℕ := ⌊Real.sqrt ((t : ℝ) / Tm)⌋₊ with hRdef
  have hR₀le : R₀ ≤ R := d23_le_floor_sqrt Tm hTm R₀ t hTR₀
  have hR1 : 1 ≤ R := le_trans hR₀ hR₀le
  have hhor : ⌊(R : ℝ) ^ 2 * Tm⌋₊ ≤ t := by
    have h : (R : ℝ) ^ 2 * Tm ≤ (t : ℝ) := d23_sq_floor_sqrt_le Tm hTm t
    exact Nat.floor_le_of_le h
  have htle : (t : ℝ) ≤ 4 * Tm * (R : ℝ) ^ 2 := d23_le_four_sq_floor_sqrt Tm hTm t h4T
  set s : ℕ := ⌊(R : ℝ) ^ 2 * Tm⌋₊ with hsdef
  set ℓ : ℝ := c * (R : ℝ) ^ (2 - (d : ℝ) / 2) with hℓdef
  have hlevel : c / (2 * (4 * Tm) ^ ((4 - (d : ℝ)) / 4)) * (t : ℝ) ^ ((4 - (d : ℝ)) / 4) < ℓ := by
    rw [hℓdef, d23_rpow_two_sub_half (R : ℝ) (Nat.cast_nonneg R) d]
    exact d23_level_lt d hd3 Tm c hTm hc t R hR1 htle
  have hone : ∀ z : Site 2, 1 - δ ≤
      ((LatticeProb.iidLaw d ν) {ζ : Site d → ℝ |
        decide (BlockGood R (d23Field d R s ζ) ℓ z) = true}).toReal := by
    intro z
    have hbad := hbe ν hν hmean hvar hexpint hexp R hR₀le z
    have hms := measurableSet_blockGood_d23Field hd1 R s ℓ z
    have hset : {ζ : Site d → ℝ | decide (BlockGood R (d23Field d R s ζ) ℓ z) = true}
        = {ζ : Site d → ℝ | BlockGood R (d23Field d R s ζ) ℓ z} := by
      ext ζ; simp
    rw [hset]
    have hsum := measure_add_measure_compl (μ := LatticeProb.iidLaw d ν) hms
    have h2 : ((LatticeProb.iidLaw d ν) {ζ : Site d → ℝ |
          BlockGood R (d23Field d R s ζ) ℓ z}).toReal
        + ((LatticeProb.iidLaw d ν) {ζ : Site d → ℝ |
          BlockGood R (d23Field d R s ζ) ℓ z}ᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum]
      simp
    have h3 : ((LatticeProb.iidLaw d ν) {ζ : Site d → ℝ |
        BlockGood R (d23Field d R s ζ) ℓ z}ᶜ).toReal ≤ δ :=
      ENNReal.toReal_le_of_le_ofReal hδ.le hbad
    linarith
  have hLSSconc := hLSSmain (Site d → ℝ) (LatticeProb.iidLaw d ν) R hR1
    (fun ζ => d23Field d R s ζ) ℓ
    (fun z => measurable_decide_blockGood_d23Field hd1 R s ℓ z)
    (fun w => blockGood_d23Field_law_stationary ν hd1 R s ℓ w)
    (fun S W _ _ hdist => indep_blockGood_d23_of_dist ν hd1 hd2 R s hR1 ℓ ((10 : ℕ) : ℝ)
      (by norm_num) S W hdist)
    hone
  exact infinite_odometer_component_of_d23Field hd1 ν R s t hhor _ ℓ hlevel hLSSconc

end Sandpile
