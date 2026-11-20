import Sandpile.Frozen.CriticalToppling
import Sandpile.Frozen.CriticalMeanOne
import Sandpile.External.MultivariateBerryEsseenProved

/-!
# Critical lower-tail estimates

The critical toppling and mean-one bounds with the multivariate Berry–Esseen comparison supplied.
-/

open MeasureTheory ProbabilityTheory

/-- The critical toppling lower-tail bound. -/
theorem Sandpile.critical_toppling
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν₀ M : ℝ) (hν₀ : 0 < ν₀)
    (a : ℝ) (ha : 0 < a) (ha' : a < 4 / (4 - (d : ℝ))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
      Integrable (fun z => |z| ^ 3) ν →
      ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
      ∀ (t : ℕ) (L : ℝ), 3 ≤ t → 2 ≤ L → L ^ a ≤ (t : ℝ) / 2 →
        Sandpile.centeredMassLaw d ν
            {σ | Sandpile.odometer σ t 0 ≤ (t : ℝ) ^ ((4 - (d : ℝ)) / 4) / L} ≤
          ENNReal.ofReal (C * L ^ (-c) + C * Sandpile.lowerTailRemainder d t L a) :=
  Sandpile.Frozen.critical_toppling Sandpile.External.multivariateBerryEsseen_holds
    d hd hd3 ν₀ M hν₀ a ha ha'

/-- The critical mean-one lower-tail bound. -/
theorem Sandpile.critical_mean_one
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (hthird : Integrable (fun z => |z| ^ 3) ν)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ' : γ < (4 - (d : ℝ)) / 4) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ t : ℕ, 2 ≤ t →
      Sandpile.centeredMassLaw d ν {σ | Sandpile.odometer σ t 0 ≤ (t : ℝ) ^ γ} ≤
        ENNReal.ofReal (C * (t : ℝ) ^ (-α)) :=
  Sandpile.Frozen.critical_mean_one Sandpile.External.multivariateBerryEsseen_holds
    d hd hd3 ν hprob hmean hvar hvar' hthird γ hγ hγ'
