import Sandpile.Law
import Sandpile.External.BerryEsseen
import Sandpile.External.VarianceScale
import Sandpile.Support.CriticalAssembly

/-!
# The critical lower tail of the odometer

`Sandpile.lowerTailRemainder` is the correction factor of `eq:dlt4-green-lower-tail`,
`(\log t)^{3/4}t^{-1/4}L^{a/4}` in dimensions `1` and `3` and `(\log t)^{7/4}t^{-1/2}L^{a/2}` in
dimension `2`.  `Sandpile.Frozen.critical_toppling` is `thm:critical-toppling`: for `d ≤ 3` and
every mean-zero i.i.d. scenery whose variance is bounded below by `ν₀²` and whose third absolute
moment is at most `M` times the `3/2` power of the variance, the odometer's lower tail at the
critical scale `t^{(4-d)/4}/L` is at most `C L^{-c} + C` times that remainder, uniformly for
`t ≥ 3` and `L ≥ 2` with `L^a ≤ t/2`, with `c` and `C` depending only on `d`, `a`, `ν₀` and `M`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

/-- The Berry--Esseen remainder of `eq:dlt4-green-lower-tail`: the factor that
multiplies `C` in the second summand, `(\log t)^{3/4}t^{-1/4}L^{a/4}` for
`d ∈ {1, 3}` and `(\log t)^{7/4}t^{-1/2}L^{a/2}` for `d = 2`. -/
noncomputable def Sandpile.lowerTailRemainder (d : ℕ) (t : ℕ) (L a : ℝ) : ℝ :=
  if d = 2 then
    Real.log t ^ ((7 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 2) * L ^ (a / 2)
  else
    Real.log t ^ ((3 : ℝ) / 4) * (t : ℝ) ^ (-(1 : ℝ) / 4) * L ^ (a / 4)

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.critical_toppling
    (hBerryEsseen : Sandpile.External.MultivariateBerryEsseen)
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
          ENNReal.ofReal (C * L ^ (-c) + C * Sandpile.lowerTailRemainder d t L a)
-- FROZEN-STATEMENT-END
:= by
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  obtain ⟨c, C, hc, hC, hbound⟩ :=
    Sandpile.exists_critical_toppling_bound hVarScale hBerryEsseen d hd hd3 ν₀ M hν₀ a ha ha'
  refine ⟨c, C, hc, hC, ?_⟩
  intro ν hprob hmean hvar hvar' hint hν₀var hmom t L ht hL hLa
  haveI := hprob
  have hne0 : evariance (id : ℝ → ℝ) ν ≠ 0 := ne_of_gt hvar
  have hnetop : evariance (id : ℝ → ℝ) ν ≠ ⊤ := ne_of_lt hvar'
  have hvarR : 0 < variance (id : ℝ → ℝ) ν := by
    show 0 < (evariance (id : ℝ → ℝ) ν).toReal
    exact ENNReal.toReal_pos hne0 hnetop
  have hν₀R : ν₀ ^ 2 ≤ variance (id : ℝ → ℝ) ν :=
    (ENNReal.ofReal_le_iff_le_toReal hnetop).mp hν₀var
  have hkey := hbound ν hprob hmean hvarR hint hν₀R hmom t L ht hL hLa
  have hlogt : (0 : ℝ) ≤ Real.log (t : ℝ) := Real.log_natCast_nonneg t
  have hL0R : (0 : ℝ) < L := by linarith
  have h2 : (0 : ℝ) ≤ Sandpile.lowerTailRemainder d t L a := by
    rw [Sandpile.lowerTailRemainder]
    split <;>
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hlogt _)
        (Real.rpow_nonneg (Nat.cast_nonneg t) _)) (Real.rpow_nonneg hL0R.le _)
  have h1 : (0 : ℝ) < L ^ (-c) := Real.rpow_pos_of_pos hL0R _
  have hrhs0 : (0 : ℝ) ≤ C * L ^ (-c) + C * Sandpile.lowerTailRemainder d t L a := by
    have := mul_nonneg hC.le h2
    nlinarith
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hrhs0).mpr ?_
  rw [Sandpile.lowerTailRemainder]
  exact hkey
