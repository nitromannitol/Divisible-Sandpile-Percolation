import LatticeProb.Prob.LpSmooth
import LatticeProb.Prob.WeightedConc
import Sandpile.Support.Norms

/-!
# The weighted exponential concentration lemma, frozen

Weighted exponential concentration lemma of `sandpile.tex`, frozen (`sandpile.tex:1345-1405`,
label `lem:weighted-exp-conc`), all four parts, for a Lipschitz-in-resampling functional `F` of
independent coordinates `ξ_1, …, ξ_N` with Lipschitz weights `ℓ_i ≥ 0`, not all zero: (a) an
`Lᵖ` bound on `F - E F` for `p ≥ 2` in terms of the resampling moments and the `ℓ²`/`ℓᵖ` norms of
`ℓ`; (b) a sub-Gaussian/sub-exponential tail bound for i.i.d. coordinates with a common
exponential moment; (c) a matching bound on the log-moment generating function of `∑ ℓ_i ξ_i`; and
(d) an exponential-moment bound on `F - E F` itself. The `N` coordinates are the product space
`Fin N → ℝ` under `Measure.pi μ`, the resampled configuration `ξ^{(i)}` is `Function.update ξ i y`,
the resampling moment `E|ξ_i - ξ_i'|^p` is `Sandpile.resampleMoment (μ i) p`, and
`‖ℓ‖_{ℓ²}, ‖ℓ‖_{ℓ^∞}` are `Sandpile.lTwoNorm`, `Sandpile.lInfNorm`; the hypothesis `∃ i, ℓ i ≠ 0`
keeps both norms strictly positive, avoiding division by zero and the junk value of `iSup` at
`N = 0`. Parts (b)-(d) pair the exponential-moment bound `E e^{θ₀|ξ₁|} ≤ K₀` with the
integrability of the exponential, since the Bochner integral of a non-integrable function is the
junk value zero.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.weighted_exp_concentration :
    (∀ p : ℝ, 2 ≤ p → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (μ : Fin N → Measure ℝ), (∀ i, IsProbabilityMeasure (μ i)) →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          (∀ i, Integrable (fun z => |z| ^ p) (μ i)) →
          (∫ ξ, |F ξ - ∫ η, F η ∂(Measure.pi μ)| ^ p ∂(Measure.pi μ)) ^ (1 / p) ≤
            C * ((∑ i, ℓ i ^ 2 * Sandpile.resampleMoment (μ i) p ^ (2 / p)) ^ (1 / 2 : ℝ) +
              (∑ i, ℓ i ^ p * Sandpile.resampleMoment (μ i) p) ^ (1 / p))) ∧
    (∀ θ₀ K₀ : ℝ, 0 < θ₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          ∀ r : ℝ, 0 ≤ r →
            (Measure.pi fun _ : Fin N => ν)
                {ξ | r ≤ |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} ≤
              ENNReal.ofReal (C * Real.exp (-(c * min (r ^ 2 / Sandpile.lTwoNorm ℓ ^ 2)
                (r / Sandpile.lInfNorm ℓ))))) ∧
    (∀ θ₀ K₀ : ℝ, 0 < θ₀ → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          ∀ lam : ℝ, |lam| * Sandpile.lInfNorm ℓ ≤ c →
            Integrable (fun ξ => Real.exp (lam * ∑ i, ℓ i * ξ i))
                (Measure.pi fun _ : Fin N => ν) ∧
              Real.log (∫ ξ, Real.exp (lam * ∑ i, ℓ i * ξ i)
                  ∂(Measure.pi fun _ : Fin N => ν)) ≤
                C * lam ^ 2 * Sandpile.lTwoNorm ℓ ^ 2) ∧
    (∀ θ₀ K₀ : ℝ, 0 < θ₀ → ∃ C : ℝ → ℝ,
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          ∀ lam : ℝ, |lam| * Sandpile.lInfNorm ℓ < θ₀ →
            Integrable (fun ξ => Real.exp (lam * (F ξ -
                ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν))))
                (Measure.pi fun _ : Fin N => ν) ∧
              ∫ ξ, Real.exp (lam * (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)))
                  ∂(Measure.pi fun _ : Fin N => ν) ≤
                Real.exp (C (θ₀ - |lam| * Sandpile.lInfNorm ℓ) * lam ^ 2 *
                  Sandpile.lTwoNorm ℓ ^ 2))
-- FROZEN-STATEMENT-END
:= by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a), the `L^p` bound, from the square-function bound
    intro p hp
    have hp0 : (0 : ℝ) < p := by linarith
    obtain ⟨C, hCpos, hbound⟩ := LatticeProb.exists_lp_square_pi hp
    refine ⟨C ^ ((1 : ℝ) / 2), Real.rpow_pos_of_pos hCpos _, ?_⟩
    intro N μ hμ F hFm ℓ hℓ _hne hLip hmom
    have hkey := hbound N μ hμ F hFm ℓ hℓ hLip hmom
    set S : ℝ := ∑ i, ℓ i ^ 2 * Sandpile.resampleMoment (μ i) p ^ (2 / p) with hS
    set T : ℝ := ∑ i, ℓ i ^ p * Sandpile.resampleMoment (μ i) p with hT
    set I : ℝ := ∫ ξ, |F ξ - ∫ η, F η ∂(Measure.pi μ)| ^ p ∂(Measure.pi μ) with hI
    have hI0 : 0 ≤ I := integral_nonneg fun ξ => Real.rpow_nonneg (abs_nonneg _) _
    have hmom0 : ∀ i, 0 ≤ Sandpile.resampleMoment (μ i) p := fun i =>
      LatticeProb.pairMoment_nonneg (μ i) p
    have hS0 : 0 ≤ S := by
      refine Finset.sum_nonneg fun i _ => ?_
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hmom0 i) _)
    have hT0 : 0 ≤ T := by
      refine Finset.sum_nonneg fun i _ => ?_
      exact mul_nonneg (Real.rpow_nonneg (hℓ i) _) (hmom0 i)
    have hhalf : I ^ ((1 : ℝ) / p) = (I ^ (2 / p)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hI0]
      congr 1
      field_simp
    have hstep : (I ^ (2 / p)) ^ ((1 : ℝ) / 2) ≤ (C * S) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hkey (by norm_num)
    have hsplit : (C * S) ^ ((1 : ℝ) / 2) = C ^ ((1 : ℝ) / 2) * S ^ ((1 : ℝ) / 2) :=
      Real.mul_rpow hCpos.le hS0
    have hTnn : 0 ≤ T ^ ((1 : ℝ) / p) := Real.rpow_nonneg hT0 _
    have hCnn : 0 ≤ C ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hCpos.le _
    calc I ^ ((1 : ℝ) / p) = (I ^ (2 / p)) ^ ((1 : ℝ) / 2) := hhalf
      _ ≤ (C * S) ^ ((1 : ℝ) / 2) := hstep
      _ = C ^ ((1 : ℝ) / 2) * S ^ ((1 : ℝ) / 2) := hsplit
      _ ≤ C ^ ((1 : ℝ) / 2) * (S ^ ((1 : ℝ) / 2) + T ^ ((1 : ℝ) / p)) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hCnn
  · -- (b)
    intro θ₀ K₀ hθ₀
    exact LatticeProb.weighted_exp_conc_tail θ₀ K₀ hθ₀
  · -- (c)
    intro θ₀ K₀ hθ₀
    exact LatticeProb.weighted_exp_conc_mgf θ₀ K₀ hθ₀
  · -- (d)
    intro θ₀ K₀ hθ₀
    exact ⟨fun g => 4 * (Real.exp K₀ * K₀) / g ^ 2,
      LatticeProb.weighted_exp_conc_exp θ₀ K₀ hθ₀⟩
