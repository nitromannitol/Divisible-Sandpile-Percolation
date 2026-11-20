import Sandpile.Support.BrownianValueContinuity
import Sandpile.Support.BrownianValueAboveGain

/-!
# Growth of Brownian stopping values

Polynomial-growth rewards give Brownian stopping values with a uniform
polynomial bound in the starting point.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

/-- Brownian stopping values inherit a polynomial growth bound, uniformly
over finite sub-horizons. -/
theorem Sandpile.Support.exists_brownian_snellValue_growth_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, ∀ t ≤ T, ∀ y,
      |Sandpile.External.Snell.snellValue (B y) P G t| ≤ C * (1 + ‖y‖) ^ n := by
  obtain ⟨C, k, hCk⟩ := hgrow
  have hC : 0 ≤ C := by
    have h := hCk 0 ⟨le_rfl, T.coe_nonneg⟩ 0
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  obtain ⟨n, hn⟩ := exists_nat_ge k
  obtain ⟨M, hMm, hM0, hMbound, hMint⟩ :=
    Sandpile.Support.exists_brownian_path_bound 0 P (B 0) (hB 0) (hBm 0) (hBc 0) T
  have hDint : Integrable (fun ω => (1 + M ω) ^ n) P := by
    by_cases hn0 : n = 0
    · subst n
      simpa only [pow_zero] using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
    · have hLp : MemLp M n P := by
        apply (integrable_norm_rpow_iff hMm.aestronglyMeasurable
          (by exact_mod_cast hn0) (ENNReal.natCast_ne_top n)).mp
        simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
          abs_of_nonneg (hM0 _)] using hMint n
      have hLp' : MemLp (fun ω => 1 + M ω) n P := (memLp_const (1 : ℝ)).add hLp
      have hi := hLp'.integrable_norm_pow hn0
      simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg zero_le_one (hM0 _))] using hi
  have hDnonneg : 0 ≤ ∫ ω, (1 + M ω) ^ n ∂P :=
    integral_nonneg fun ω => pow_nonneg (by linarith [hM0 ω]) n
  refine ⟨C * (1 + ∫ ω, (1 + M ω) ^ n ∂P), by positivity, n, ?_⟩
  intro t ht y
  let W : ℝ≥0 → Ω → Sandpile.Continuum.Space d := B 0
  let By : ℝ≥0 → Ω → Sandpile.Continuum.Space d := fun s ω => y + W s ω
  have hBy : Sandpile.Continuum.IsBrownian d y By P :=
    Sandpile.Support.isBrownian_add_const d P W (hB 0) y
  have hBym : ∀ s, StronglyMeasurable (By s) := fun s =>
    (measurable_const.add (hBm 0 s).measurable).stronglyMeasurable
  have hByc : ∀ ω, Continuous fun s => By s ω := fun ω => continuous_const.add (hBc 0 ω)
  have hle : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  have hGt : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (t : ℝ) ×ˢ Set.univ) := hG.mono (by
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hle⟩, hp.2⟩)
  have hgt : ∃ C k : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) (t : ℝ),
      ∀ z, |G r z| ≤ C * (1 + ‖z‖) ^ k :=
    ⟨C, k, fun r hr z => hCk r ⟨hr.1, hr.2.trans hle⟩ z⟩
  have hval : Sandpile.External.Snell.snellValue (B y) P G t =
      Sandpile.External.Snell.snellValue By P G t :=
    Sandpile.Support.snellValue_eq_of_isBrownian y P P (B y) By (hB y) hBy
      (hBm y) hBym (hBc y) hByc t G hGt hgt
  rw [hval]
  let A : ℝ := C * (1 + ‖y‖) ^ n
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrewards : ∀ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping By σ →
      (∀ ω, σ ω ≤ t) → Integrable (fun ω => G ((t : ℝ) - σ ω) (By (σ ω) ω)) P :=
    (Sandpile.Support.brownian_stopping_payoffs_integrable_and_bddAbove y P By hBy hBym hByc t G hGt hgt).1
  have hpaybound : ∀ σ : Ω → ℝ≥0, (∀ ω, σ ω ≤ t) →
      ∀ᵐ ω ∂P, |G ((t : ℝ) - σ ω) (By (σ ω) ω)| ≤ A * (1 + M ω) ^ n := by
    intro σ hσt
    filter_upwards [hMbound] with ω hω
    have hr : (t : ℝ) - σ ω ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨sub_nonneg.mpr (by exact_mod_cast hσt ω),
       (sub_le_self _ (σ ω).coe_nonneg).trans hle⟩
    have hbase : 1 + ‖By (σ ω) ω‖ ≤ (1 + ‖y‖) * (1 + M ω) := by
      have hh := hω (σ ω) ((hσt ω).trans ht)
      dsimp [By, W]
      nlinarith [norm_add_le y (B 0 (σ ω) ω), norm_nonneg y, hM0 ω]
    calc
      |G ((t : ℝ) - σ ω) (By (σ ω) ω)| ≤ C * (1 + ‖By (σ ω) ω‖) ^ k := hCk _ hr _
      _ ≤ C * (1 + ‖By (σ ω) ω‖) ^ n := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa only [Real.rpow_natCast] using
          (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + ‖By (σ ω) ω‖ by linarith [norm_nonneg (By (σ ω) ω)]) hn)
      _ ≤ C * ((1 + ‖y‖) * (1 + M ω)) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase n) hC
      _ = A * (1 + M ω) ^ n := by simp only [A, mul_pow]; ring
  have hne : (Sandpile.External.Snell.attainable By P G t).Nonempty := by
    refine ⟨∫ ω, G t (By 0 ω) ∂P, (fun _ => 0),
      Sandpile.Continuum.isBrownianStopping_const By 0, ?_, ?_⟩
    · intro ω
      exact t.coe_nonneg
    · simp only [NNReal.coe_zero, sub_zero]
  have hup : Sandpile.External.Snell.snellValue By P G t ≤ A * ∫ ω, (1 + M ω) ^ n ∂P := by
    change sSup (Sandpile.External.Snell.attainable By P G t) ≤ _
    apply csSup_le hne
    rintro a ⟨σ, hσ, hσt, rfl⟩
    have hσt' : ∀ ω, σ ω ≤ t := fun ω => by exact_mod_cast hσt ω
    calc
      _ ≤ ∫ ω, A * (1 + M ω) ^ n ∂P := by
        apply integral_mono_ae (hrewards σ hσ hσt') (hDint.const_mul A)
        filter_upwards [hpaybound σ hσt'] with ω hω
        exact (le_abs_self _).trans hω
      _ = _ := integral_const_mul _ _
  have hlo : -A ≤ Sandpile.External.Snell.snellValue By P G t := by
    have hh := Sandpile.Support.le_brownian_snellValue y P By hBy hBym hByc t G hGt hgt
    have hGbound : |G t y| ≤ A := by
      calc |G t y| ≤ C * (1 + ‖y‖) ^ k := hCk t ⟨t.coe_nonneg, hle⟩ y
        _ ≤ A := by
          dsimp [A]
          apply mul_le_mul_of_nonneg_left _ hC
          simpa only [Real.rpow_natCast] using
            (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + ‖y‖ by linarith [norm_nonneg y]) hn)
    linarith [(abs_le.1 hGbound).1]
  apply abs_le.mpr
  constructor
  · dsimp [A] at *
    nlinarith [mul_nonneg (mul_nonneg hC (pow_nonneg (show 0 ≤ 1 + ‖y‖ by positivity) n)) hDnonneg]
  · dsimp [A] at *
    nlinarith [mul_nonneg (mul_nonneg hC (pow_nonneg (show 0 ≤ 1 + ‖y‖ by positivity) n)) hDnonneg]
