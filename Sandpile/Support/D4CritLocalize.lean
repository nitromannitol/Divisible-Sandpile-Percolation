import Sandpile.Frozen.MeanLocalization
import Sandpile.External.HeatKernelBoundsProved
import Sandpile.Support.D4CriticalAssembly

/-!
# Mean-localization bound with uniform constants

The mean-localization bound of `lem:mean-localization` with its constants bound before the
scenery law, as the dimension-four percolation argument needs them: the localization radius
`A_loc` is chosen once for the whole law class, so the deficit constants must not depend on the
law. The constants are those of the maximal-displacement bound of `eq:rw-max-displacement`,
which is a statement about simple random walk alone.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- `lem:mean-localization` with constants uniform over the scenery law:
for every dimension and every time scale `T`, there are `C` and `c` such that,
for every law, every localization radius `A ≥ 1`, every `R ≥ 1` and every
`t ≤ T R²`, the mean odometer loses at most `C e^{-cA²/T}` of itself when the
odometer is localized to the box `Q(x, A R)`. -/
theorem mean_localization_uniform (d : ℕ) (hd : 1 ≤ d) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => max z 0) ν →
      ∀ A : ℝ, 1 ≤ A → ∀ R : ℝ, 1 ≤ R → ∀ t : ℕ, (t : ℝ) ≤ T * R ^ 2 →
        ∀ x : Sandpile.Site d,
          0 ≤ (∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) -
                ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox x (A * R)) ζ t x
                  ∂(LatticeProb.iidLaw d ν) ∧
            (∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) -
                (∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox x (A * R)) ζ t x
                  ∂(LatticeProb.iidLaw d ν)) ≤
              C * Real.exp (-(c * A ^ 2 / T)) *
                ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨-, -, C₀, c₀, hC₀, hc₀, hbnd⟩ := Sandpile.External.heatKernelBounds d hd
  refine ⟨C₀, c₀, hC₀, hc₀, ?_⟩
  intro ν hprob hpos
  haveI := hprob
  intro A hA R hR t htR x
  have hAR1 : (1 : ℝ) ≤ A * R := by nlinarith
  have hfloor : 1 ≤ ⌊A * R⌋ := by
    have : ((1 : ℤ) : ℝ) ≤ A * R := by exact_mod_cast hAR1
    exact Int.le_floor.mpr this
  have hx : x ∈ Sandpile.supBox x (A * R) := by
    show ∀ i, |x i - x i| ≤ ⌊A * R⌋
    intro i
    simp only [sub_self, abs_zero]
    omega
  set D : Set (Sandpile.Site d) := Sandpile.supBox x (A * R) with hD
  have hU0 : 0 ≤ ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) :=
    Sandpile.integral_odometerOf_nonneg d ν t 0
  rcases Nat.eq_zero_or_pos t with ht0 | ht1
  · subst ht0
    have hL : (∫ ζ, Sandpile.localizedOdometer D ζ 0 x ∂(LatticeProb.iidLaw d ν)) = 0 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall fun ζ =>
        Sandpile.localizedOdometer_zero hd D ζ x)]
      exact integral_zero _ _
    have hUz : (∫ ζ, Sandpile.odometerOf ζ 0 0 ∂(LatticeProb.iidLaw d ν)) = 0 := by
      show (∫ _ : Sandpile.Site d → ℝ, (0 : ℝ) ∂(LatticeProb.iidLaw d ν)) = 0
      exact integral_zero _ _
    rw [hL, hUz]
    norm_num
  -- the exit probability, by the maximal-displacement estimate
  have hU := Sandpile.mean_localization_bound hd ν hpos D t x hx
  set R' : ℕ := (⌊A * R⌋).toNat + 1 with hR'def
  have hR'1 : 1 ≤ R' := by omega
  have hR'int : ((R' : ℕ) : ℤ) = ⌊A * R⌋ + 1 := by omega
  have hR'real : A * R < (R' : ℝ) := by
    have h2 : A * R < (⌊A * R⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h3 : ((R' : ℕ) : ℝ) = (⌊A * R⌋ : ℝ) + 1 := by
      have hc := congrArg (fun z : ℤ => (z : ℝ)) hR'int
      push_cast at hc
      exact hc
    rw [h3]
    exact h2
  have hsub : {X : ℕ → Sandpile.Site d | Sandpile.exitNat D t X ≤ t}
      ⊆ {X : ℕ → Sandpile.Site d |
          ∃ k ≤ t, (R' : ℝ) ≤ Sandpile.External.latticeDist (X k) x} := by
    intro X hX
    obtain ⟨j, hj, hjD⟩ := Sandpile.exitNat_le_iff.mp hX
    have hex : ∃ i, ⌊A * R⌋ < |X j i - x i| := by
      by_contra hc
      push Not at hc
      exact hjD (fun i => hc i)
    obtain ⟨i, hi⟩ := hex
    refine ⟨j, hj, ?_⟩
    have hint : ((R' : ℕ) : ℤ) ≤ |X j i - x i| := by omega
    have hterm : ((R' : ℕ) : ℝ) ≤ |((X j i - x i : ℤ) : ℝ)| := by
      have hcast : (((|X j i - x i| : ℤ)) : ℝ) = |((X j i - x i : ℤ) : ℝ)| := by
        push_cast [Int.cast_abs]
        ring
      calc ((R' : ℕ) : ℝ) = (((R' : ℕ) : ℤ) : ℝ) := by push_cast; ring
        _ ≤ ((|X j i - x i| : ℤ) : ℝ) := by exact_mod_cast hint
        _ = |((X j i - x i : ℤ) : ℝ)| := hcast
    have hsq : ((R' : ℕ) : ℝ) ^ 2 ≤ ((X j i - x i : ℤ) : ℝ) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ((R' : ℕ) : ℝ) := by positivity
      nlinarith [hterm, abs_nonneg ((X j i - x i : ℤ) : ℝ),
        sq_abs ((X j i - x i : ℤ) : ℝ)]
    have hsum : ((X j i - x i : ℤ) : ℝ) ^ 2
        ≤ ∑ i' : Fin d, ((X j i' - x i' : ℤ) : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i' => ((X j i' - x i' : ℤ) : ℝ) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    show ((R' : ℕ) : ℝ) ≤ Real.sqrt (∑ i' : Fin d, ((X j i' - x i' : ℤ) : ℝ) ^ 2)
    calc ((R' : ℕ) : ℝ) = Real.sqrt (((R' : ℕ) : ℝ) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (∑ i' : Fin d, ((X j i' - x i' : ℤ) : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (le_trans hsq hsum)
  have hP : ((Sandpile.walkLaw d x)
        {X : ℕ → Sandpile.Site d | Sandpile.exitNat D t X ≤ t}).toReal
      ≤ C₀ * Real.exp (-c₀ * (R' : ℝ) ^ 2 / (t : ℝ)) := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have hR'1real : (1 : ℝ) ≤ (R' : ℝ) := by exact_mod_cast hR'1
    exact le_trans (measure_mono hsub) (hbnd t (R' : ℝ) ht1 hR'1real x)
  have ht0R : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
  have hexp : Real.exp (-c₀ * (R' : ℝ) ^ 2 / (t : ℝ))
      ≤ Real.exp (-(c₀ * A ^ 2 / T)) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : c₀ * A ^ 2 / T ≤ c₀ * (R' : ℝ) ^ 2 / (t : ℝ) := by
      rw [div_le_div_iff₀ hT ht0R]
      have hARnn : (0 : ℝ) ≤ A * R := by nlinarith
      have hsq : (A * R) ^ 2 ≤ (R' : ℝ) ^ 2 := by nlinarith [hR'real, hARnn]
      have h2 : c₀ * A ^ 2 * (t : ℝ) ≤ c₀ * A ^ 2 * (T * R ^ 2) :=
        mul_le_mul_of_nonneg_left htR (by positivity)
      have h3 : c₀ * A ^ 2 * (T * R ^ 2) = (c₀ * T) * (A * R) ^ 2 := by ring
      have h4 : (c₀ * T) * (A * R) ^ 2 ≤ (c₀ * T) * (R' : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have h5 : (c₀ * T) * (R' : ℝ) ^ 2 = c₀ * (R' : ℝ) ^ 2 * T := by ring
      linarith
    have hrw : -c₀ * (R' : ℝ) ^ 2 / (t : ℝ) = -(c₀ * (R' : ℝ) ^ 2 / (t : ℝ)) := by ring
    rw [hrw]
    exact neg_le_neg h1
  refine ⟨hU.1, le_trans hU.2 ?_⟩
  refine mul_le_mul_of_nonneg_right (le_trans hP ?_) hU0
  exact mul_le_mul_of_nonneg_left hexp hC₀.le


/-- The Step-1a localized mean lower bound with the mean bounds carried only
beyond a threshold `t₁`, as `thm:critical-toppling-d4` gives them. -/
theorem uniform_localized_mean_lower_thresh
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (_hmean : ∫ z, z ∂ν = 0)
    (_hpos : Integrable (fun z => max z 0) ν)
    (c₀ C₀ c₁ C₁ Aloc : ℝ) (r t₁ : ℕ) (hrt : t₁ ≤ r ^ 2) (hc₀ : 0 < c₀) (_hC₀ : 0 < C₀)
    (_hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
    (hAloc : 1 ≤ Aloc) (hr : 2 ≤ r)
    (hlow : ∀ t : ℕ, t₁ ≤ t → c₀ * Real.log t ≤
        Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t)
    (hup : ∀ t : ℕ, t₁ ≤ t →
      Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t ≤ C₀ * Real.log t)
    (hloc : ∀ A : ℝ, 1 ≤ A → ∀ R : ℝ, 1 ≤ R → ∀ t : ℕ, (t : ℝ) ≤ 1 * R ^ 2 →
        ∀ x : Sandpile.Site 4,
          0 ≤ (∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)) -
                ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox x (A * R)) ζ t x
                  ∂(LatticeProb.iidLaw 4 ν) ∧
            (∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν)) -
                (∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox x (A * R)) ζ t x
                  ∂(LatticeProb.iidLaw 4 ν)) ≤
              C₁ * Real.exp (-(c₁ * A ^ 2 / 1)) *
                ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw 4 ν))
    (hsmall : C₀ * C₁ * Real.exp (-(c₁ * Aloc ^ 2)) ≤ c₀ / 4) :
    ∀ w : Sandpile.Site 4,
      c₀ * Real.log ((r : ℕ) ^ 2) / 2 ≤
        ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox w (Aloc * (r : ℝ))) ζ (r ^ 2) w
          ∂(LatticeProb.iidLaw 4 ν) := by
  intro w
  have h4 : (1 : ℕ) ≤ 4 := by omega
  have htrans : Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) (r ^ 2)
      = ∫ ζ, Sandpile.odometerOf ζ (r ^ 2) 0 ∂(LatticeProb.iidLaw 4 ν) :=
    meanOdometer_centeredMassLaw_eq 4 ν h4 (r ^ 2)
  have hr2 : 2 ≤ r ^ 2 := by nlinarith
  have hlow' := hlow (r ^ 2) hrt
  rw [htrans] at hlow'
  have hup' := hup (r ^ 2) hrt
  rw [htrans] at hup'
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
  have htR : ((r ^ 2 : ℕ) : ℝ) ≤ 1 * (r : ℝ) ^ 2 := by
    have : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) * (r : ℝ) := by push_cast; ring
    rw [this]
    nlinarith [hr]
  have hD := hloc Aloc hAloc (r : ℝ) hrR (r ^ 2) htR w
  set Mloc := ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox w (Aloc * (r : ℝ))) ζ (r ^ 2) w
    ∂(LatticeProb.iidLaw 4 ν) with hMloc
  set Mu := ∫ ζ, Sandpile.odometerOf ζ (r ^ 2) 0 ∂(LatticeProb.iidLaw 4 ν) with hMu
  have hdef : Mu - Mloc ≤ C₁ * Real.exp (-(c₁ * Aloc ^ 2)) * Mu := by
    have := hD.2
    simp only [div_one] at this
    exact this
  have hdef' : Mu - Mloc ≤ C₁ * Real.exp (-(c₁ * Aloc ^ 2 / 1)) * Mu := by
    simpa using hdef
  have hsmall' : C₁ * C₀ * Real.exp (-(c₁ * Aloc ^ 2)) ≤ c₀ / 4 := by
    nlinarith [hsmall]
  have hK := localization_deficit_arith C₁ c₁ Aloc Mu C₀ c₀ ((r ^ 2 : ℕ) : ℝ)
    (Mu - Mloc) (le_of_lt hC₁) hD.1 hdef hup' (by exact_mod_cast hr2) hsmall'
  have hlog : 0 ≤ Real.log ((r ^ 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ r ^ 2))
  have hmean2 : c₀ * Real.log ((r ^ 2 : ℕ) : ℝ) ≤ Mloc + (Mu - Mloc) := by
    have : Mloc + (Mu - Mloc) = Mu := by ring
    linarith
  have := localized_mean_lower_arith c₀ ((r ^ 2 : ℕ) : ℝ) Mloc (Mu - Mloc)
    (by exact_mod_cast hr2) hc₀ hmean2 (hK.trans (by linarith))
  have hcast : ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) ^ 2 := by push_cast; ring
  calc c₀ * Real.log ((r : ℕ) ^ 2) / 2 ≤ Mloc := by
        have h2 : c₀ * Real.log ((r ^ 2 : ℕ) : ℝ) / 2 ≤ Mloc := this
        rw [hcast] at h2
        exact h2
    _ = ∫ ζ, Sandpile.localizedOdometer (Sandpile.supBox w (Aloc * (r : ℝ))) ζ (r ^ 2) w
          ∂(LatticeProb.iidLaw 4 ν) := rfl

end Sandpile
