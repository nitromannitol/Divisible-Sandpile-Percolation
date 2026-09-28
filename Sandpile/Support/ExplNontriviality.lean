import Sandpile.Support.ExplMassShift
import Sandpile.Support.PercolationEvents
import Sandpile.Frozen.CriticalLevels

/-!
# Theorem 1.1 From Theorem 1.2 by a Mass Shift

Theorem 1.1 of `sandpile.tex` (`sandpile.tex:95-104`) from Theorem 1.2
(`sandpile.tex:113-126`), which is exactly the paper's own derivation at
`sandpile.tex:317-342`.

"Given a mean-`ρ` field, raise every mass by `1-ρ`: `σ̂ = σ + (1-ρ)`.  The
shifted field has mean one and the same fluctuations about its mean, so
Theorem 1.2 applies to it with constants uniform in `ρ ∈ [ρ₀,1)`.  Let `û_t` be
its odometer and observe that `0 ≤ û_t(x) - u_t(x) ≤ (1-ρ)t/(2d)`.  Consequently,
for every `a > 0`, `{x : û_t(x) > a} ⊆ {x : u_t(x) > a - (1-ρ)t/(2d)}`.  If
`ρ > 1 - 2dc h(t₀)/t₀`, then `t = t₀` satisfies `(1-ρ)t/(2d) < c h(t)`, and hence
the percolating set `{x : û_t(x) > c h(t)}` is contained in `{x : u_t(x) > 0\}`,
which is contained in `𝒯^{(ρ)}`.  The theorem therefore holds with
`ρ₊ = max{ρ₀, 1 - 2dc h(t₀)/t₀}`, which lies in `[ρ₀,1)` because `h(t₀) > 0`."

Two places need more than the paper writes.

The time at which the argument is run has to make `h(t) > 0`.  In dimension four
`h(t) = log t` and in dimensions five and higher `h(t) = (log t)^{2/d}`, both of
which vanish at `t = 1`, so the time used here is `max t₀ 2`; the paper's `t₀` is
already the threshold of Theorem 1.2 and may be taken that large.

Transferring the almost-sure statement from the shifted field back to the
original one is a pushforward: raising every coordinate by `a` maps the i.i.d.
law of `μ` to the i.i.d. law of the shift of `μ` (`massLaw_map_add_const`), and
`MeasureTheory.ae_of_ae_map` carries the conclusion back along it.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Sandpile.Support

open Sandpile LatticeProb

/-- The critical scale `h(t)` of Theorem 1.2 is positive from time two on, in
every dimension: `t^{(4-d)/4}` for `d ≤ 3`, `log t` for `d = 4` and
`(log t)^{2/d}` for `d ≥ 5`. -/
theorem criticalScale_pos (d : ℕ) (t : ℕ) (ht : 2 ≤ t) : 0 < Sandpile.criticalScale d t := by
  have ht1 : (1 : ℝ) < (t : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two ht
  have ht0 : (0 : ℝ) < (t : ℝ) := by linarith
  have hlog : (0 : ℝ) < Real.log t := Real.log_pos ht1
  unfold Sandpile.criticalScale
  split_ifs with h1 h2
  · exact Real.rpow_pos_of_pos ht0 _
  · exact hlog
  · exact Real.rpow_pos_of_pos hlog _

/-- A set on which the odometer is already positive at some finite time lies in the
toppled set, so an infinite component of it is one of the toppled set.  This is the
last sentence of the paper's derivation, `{x : u_t(x) > 0} ⊆ 𝒯^{(ρ)}`. -/
theorem hasInfiniteComponent_toppledSet_of {d : ℕ} (σ : Site d → ℝ) (t : ℕ)
    (S : Set (Site d)) (hS : HasInfiniteComponent S)
    (hpos : ∀ x ∈ S, 0 < odometer σ t x) :
    HasInfiniteComponent (toppledSet σ) := by
  refine hasInfiniteComponent_mono ?_ hS
  intro x hx
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (hpos x hx)) (Sandpile.le_odometerLimit σ t x)

/-- **Theorem 1.1 from Theorem 1.2.**  `hCrit` is the exact conclusion of
`thm:main-critical-level-percolation` at the same `d`, `ν₀`, `θ₀` and `K₀`. -/
theorem percolation_below_criticality_of_critical_levels
    (d : ℕ) (hd : 2 ≤ d) (μ : ℝ → Measure ℝ) (hprob : ∀ ρ, IsProbabilityMeasure (μ ρ))
    (hmean : ∀ ρ ∈ Set.Ioc (0 : ℝ) 1, ∫ s, s ∂(μ ρ) = ρ)
    (ρ₀ ν₀ θ₀ K₀ : ℝ) (hρ₀ : ρ₀ ∈ Set.Ioo (0 : ℝ) 1) (hθ₀ : 0 < θ₀)
    (hvar : ∀ ρ ∈ Set.Ico ρ₀ 1, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (μ ρ))
    (hexpint : ∀ ρ ∈ Set.Ico ρ₀ 1, Integrable (fun s => Real.exp (θ₀ * |s - ρ|)) (μ ρ))
    (hexp : ∀ ρ ∈ Set.Ico ρ₀ 1, ∫ s, Real.exp (θ₀ * |s - ρ|) ∂(μ ρ) ≤ K₀)
    (hCrit : ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ (m : Measure ℝ), IsProbabilityMeasure m →
      ∫ s, s ∂m = 1 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id m →
      Integrable (fun s => Real.exp (θ₀ * |s - 1|)) m →
      ∫ s, Real.exp (θ₀ * |s - 1|) ∂m ≤ K₀ →
      ∀ t : ℕ, t₀ ≤ t →
        ∀ᵐ σ ∂(Sandpile.massLaw d m),
          Sandpile.HasInfiniteComponent
            {x | c * Sandpile.criticalScale d t < Sandpile.odometer σ t x}) :
    ∃ ρPlus ∈ Set.Ico ρ₀ 1, ∀ ρ ∈ Set.Ioo ρPlus 1,
      ∀ᵐ σ ∂(Sandpile.massLaw d (μ ρ)),
        Sandpile.HasInfiniteComponent (Sandpile.toppledSet σ) := by
  classical
  obtain ⟨c, hc, t₀, hCrit⟩ := hCrit
  have hd1 : 1 ≤ d := le_trans one_le_two hd
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  have hdne : (d : ℝ) ≠ 0 := by linarith
  have ht2 : 2 ≤ max t₀ 2 := le_max_right _ _
  have ht0 : t₀ ≤ max t₀ 2 := le_max_left _ _
  have hhpos : 0 < Sandpile.criticalScale d (max t₀ 2) := criticalScale_pos d _ ht2
  have htpos : (0 : ℝ) < ((max t₀ 2 : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((max t₀ 2 : ℕ) : ℝ) := by exact_mod_cast ht2
    linarith
  have htne : ((max t₀ 2 : ℕ) : ℝ) ≠ 0 := ne_of_gt htpos
  set g : ℝ :=
    2 * (d : ℝ) * c * Sandpile.criticalScale d (max t₀ 2) / ((max t₀ 2 : ℕ) : ℝ) with hgdef
  have hgpos : 0 < g := by
    rw [hgdef]
    positivity
  refine ⟨max ρ₀ (1 - g), ⟨le_max_left _ _, max_lt hρ₀.2 (by linarith)⟩, ?_⟩
  intro ρ hρ
  obtain ⟨hρ1, hρ2⟩ := hρ
  have hρ₀le : ρ₀ ≤ ρ := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hρ1)
  have hgap : 1 - g < ρ := lt_of_le_of_lt (le_max_right _ _) hρ1
  have hρmem : ρ ∈ Set.Ico ρ₀ 1 := ⟨hρ₀le, hρ2⟩
  have hρmem' : ρ ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_lt_of_le hρ₀.1 hρ₀le, le_of_lt hρ2⟩
  haveI : IsProbabilityMeasure (μ ρ) := hprob ρ
  have hapos : (0 : ℝ) < 1 - ρ := by linarith
  have hid : Integrable (id : ℝ → ℝ) (μ ρ) :=
    integrable_id_of_exp_moment_at (μ ρ) θ₀ ρ hθ₀ (hexpint ρ hρmem)
  haveI hmprob : IsProbabilityMeasure ((μ ρ).map fun s => s + (1 - ρ)) :=
    MeasureTheory.Measure.isProbabilityMeasure_map (by fun_prop)
  have hmmean : ∫ s, s ∂((μ ρ).map fun s => s + (1 - ρ)) = 1 := by
    rw [integral_id_map_add_const (μ ρ) (1 - ρ) hid, hmean ρ hρmem']
    ring
  have hmvar : ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ((μ ρ).map fun s => s + (1 - ρ)) := by
    rw [evariance_id_map_add_const (μ ρ) (1 - ρ) hid]
    exact hvar ρ hρmem
  have hmint : Integrable (fun s => Real.exp (θ₀ * |s - 1|))
      ((μ ρ).map fun s => s + (1 - ρ)) :=
    integrable_exp_map_add_const (μ ρ) θ₀ ρ (hexpint ρ hρmem)
  have hmexp : ∫ s, Real.exp (θ₀ * |s - 1|) ∂((μ ρ).map fun s => s + (1 - ρ)) ≤ K₀ := by
    rw [integral_exp_map_add_const (μ ρ) θ₀ ρ]
    exact hexp ρ hρmem
  have hae := hCrit ((μ ρ).map fun s => s + (1 - ρ)) hmprob hmmean hmvar hmint hmexp
    (max t₀ 2) ht0
  rw [← massLaw_map_add_const d (μ ρ) (1 - ρ)] at hae
  have hmeas : Measurable fun (σ : Site d → ℝ) (i : Site d) => σ i + (1 - ρ) :=
    measurable_pi_lambda _ fun i => by
      have : Measurable fun σ : Site d → ℝ => σ i := measurable_pi_apply i
      exact this.add_const (1 - ρ)
  have hae' := MeasureTheory.ae_of_ae_map
    (f := fun (σ : Site d → ℝ) (i : Site d) => σ i + (1 - ρ)) hmeas.aemeasurable hae
  -- the two odometers, and the strict gap that turns the level set into the toppled set
  have hb : (0 : ℝ) ≤ (1 - ρ) / (2 * (d : ℝ)) := by positivity
  have hkey : ((max t₀ 2 : ℕ) : ℝ) * ((1 - ρ) / (2 * (d : ℝ)))
      < c * Sandpile.criticalScale d (max t₀ 2) := by
    have h1 : 1 - ρ < g := by linarith
    have hgt : g * ((max t₀ 2 : ℕ) : ℝ)
        = 2 * (d : ℝ) * c * Sandpile.criticalScale d (max t₀ 2) := by
      rw [hgdef]; field_simp
    have hat : (1 - ρ) * ((max t₀ 2 : ℕ) : ℝ) < g * ((max t₀ 2 : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_right h1 htpos
    rw [show ((max t₀ 2 : ℕ) : ℝ) * ((1 - ρ) / (2 * (d : ℝ)))
        = ((1 - ρ) * ((max t₀ 2 : ℕ) : ℝ)) / (2 * (d : ℝ)) from by ring,
      div_lt_iff₀ hdpos]
    nlinarith [hat, hgt]
  filter_upwards [hae'] with σ hσ
  refine hasInfiniteComponent_toppledSet_of σ (max t₀ 2) _ hσ ?_
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  have hfun : (fun y => σ y + 2 * (d : ℝ) * ((1 - ρ) / (2 * (d : ℝ))))
      = fun y => σ y + (1 - ρ) := by
    funext y
    congr 1
    field_simp
  have hshift := odometer_add_const_le hd1 σ ((1 - ρ) / (2 * (d : ℝ))) hb (max t₀ 2) x
  rw [hfun] at hshift
  linarith

end Sandpile.Support
