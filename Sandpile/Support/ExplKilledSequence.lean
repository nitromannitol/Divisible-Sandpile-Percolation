/-
The ball comparison and the varying-law form of the cube-killed scaling limit of
`sandpile.tex:1929-1956` (label `rem:dlt4-killed-scaling`).

Comparison.  The Euclidean unit ball lies in the cube `u+[-1,1]^d`, so every stopping rule
allowed by the ball value is allowed by the cube value, and `𝒰_{Z,□}(T,u) ≥ 𝒰_{Z,1}(T,u)`.
The general inequality `brownianValueBall_le_brownianValueCube` asks the payoffs of the
unrestricted family to be bounded above; the comparison needs only the cube payoffs, and a
reward that is continuous on `ℝ × ℝ^d` is bounded on the compact strip over the cube, which
bounds every cube payoff.  That is `brownianValueBall_le_brownianValueCube_of_continuous`, and
it applies to every sample point at which the heat potential is continuous.

Varying laws.  The estimates under `Sandpile.dlt4_killed_scaling_of_inputs` see the scenery
law only through an exponential moment: the tightness and oscillation bounds of the heat
potential are uniform over laws with a common bound, and the only limit input is the
finite-dimensional convergence of the interpolated potential, which
`heat_potential_fd_seq` proves along a sequence of laws whose variances converge.  The
coupling theorem `Sandpile.dlt4_killed_scaling_seq_of_fdd` is therefore the fixed-law proof
run along `(νs k, Rseq k)`; here it is stated jointly in the law index and the scale, which
is the form of the remark: for every accuracy there are an index `k₀` and a scale `R₀` beyond
which every pair `(νs k, R)` carries the coupling.  The joint form follows from the diagonal
one by contradiction: a failing pair for each threshold gives a diagonal sequence of laws and
scales, along which the diagonal form applies.

The limiting field is `gaussianPotential d v W = √v · gaussianPotential d 1 W`, the value for
unit-variance scenery times the limiting standard deviation; the cube value is positively
homogeneous in the reward, so the limiting value is that multiple of the unit-variance one.
A field that is continuous at one positive variance is continuous at every variance, since the
variance enters only as a constant factor.
-/
import Sandpile.Support.ExplKilledValue
import Sandpile.Support.StopValue
import Sandpile.Support.KillCutoff
import Sandpile.Support.D23KilledCoupling
import Sandpile.Support.ContFDSeq
import Sandpile.Support.ContContinuumMCT

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- The cube payoffs of a reward that is continuous on `ℝ × ℝ^d` are bounded above: the reward
is bounded on the compact strip over the cube, and a cube payoff is an average of the reward
read inside the cube. -/
theorem bddAbove_cubeStoppingPayoffs_of_continuous_field
    (P : Measure ΩB) [IsProbabilityMeasure P] (B : ℝ≥0 → ΩB → Space d) (u : Space d)
    (hB : IsBrownian d u B P) (h : ℝ → Space d → ℝ)
    (hh : Continuous fun q : ℝ × Space d => h q.1 q.2) (T L : ℝ) (hL : 0 ≤ L) :
    BddAbove (cubeStoppingPayoffs B P h T L u) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod
    (isCompact_closedBall (0 : Space d) (‖u‖ + Real.sqrt d * L))).exists_bound_of_continuousOn
    (f := fun q : ℝ × Space d => h q.1 q.2) (s := Set.Icc (0 : ℝ) T ×ˢ
      Metric.closedBall (0 : Space d) (‖u‖ + Real.sqrt d * L)) hh.continuousOn
  refine bddAbove_cubeStoppingPayoffs_of_continuousOn hB h T L M hL hh.continuousOn ?_
  intro s hs y hy
  have hyn := norm_le_of_cube hL hy
  have hb := hM (s, y) ⟨hs, by simpa only [Metric.mem_closedBall, dist_zero_right] using hyn⟩
  simpa only [Real.norm_eq_abs] using hb

/-- **`𝒰_{h,□}(T,u) ≥ 𝒰_{h,1}(T,u)` for a continuous reward** (`sandpile.tex:1946-1948`): the
Euclidean unit ball is contained in the cube `u+[-1,1]^d`. -/
theorem brownianValueBall_le_brownianValueCube_of_continuous
    (P : Measure ΩB) [IsProbabilityMeasure P] (B : ℝ≥0 → ΩB → Space d) (u : Space d)
    (hB : IsBrownian d u B P) (h : ℝ → Space d → ℝ)
    (hh : Continuous fun q : ℝ × Space d => h q.1 q.2) (T : ℝ) (hT : 0 ≤ T) :
    brownianValueBall B P h T 1 u ≤ brownianValueCube B P h T 1 u :=
  brownianValueBall_le_brownianValueCube_of_bddAbove_cube B P h T 1 1 hT le_rfl u
    (bddAbove_cubeStoppingPayoffs_of_continuous_field P B u hB h hh T 1 zero_le_one)

/-- The Gaussian potential of variance `v` is `√v` times the one of unit variance. -/
theorem gaussianPotential_eq_sqrt_mul_one {Ω : Type*} (v : ℝ) (W : (Space d → ℝ) → Ω → ℝ)
    (t : ℝ) (x : Space d) (ω : Ω) :
    gaussianPotential d v W t x ω = Real.sqrt v * gaussianPotential d 1 W t x ω := by
  simp only [gaussianPotential, Real.sqrt_one, one_mul]

/-- **The limit is `√v` times the value for unit-variance scenery** (`sandpile.tex:1953-1955`):
the cube-killed value of the Gaussian potential of variance `v` is `√v` times that of the
Gaussian potential of unit variance, at every sample point. -/
theorem brownianValueCube_gaussianPotential_eq_sqrt_mul {Ω : Type*} (B : ℝ≥0 → ΩB → Space d)
    (P : Measure ΩB) (v : ℝ) (W : (Space d → ℝ) → Ω → ℝ) (ω : Ω) (T L : ℝ) (u : Space d) :
    brownianValueCube B P (fun t y => gaussianPotential d v W t y ω) T L u =
      Real.sqrt v * brownianValueCube B P (fun t y => gaussianPotential d 1 W t y ω) T L u := by
  have hfun : (fun t y => gaussianPotential d v W t y ω) =
      fun t y => Real.sqrt v * gaussianPotential d 1 W t y ω := by
    funext t y
    exact gaussianPotential_eq_sqrt_mul_one v W t y ω
  rw [hfun]
  exact brownianValueCube_const_mul B P _ T L u _ (Real.sqrt_nonneg v)

/-- A sample point at which the Gaussian potential of one positive variance is continuous is one
at which the potential of every variance is continuous: the variance is a constant factor. -/
theorem continuous_gaussianPotential_of_pos_variance {Ω : Type*} (v w : ℝ) (hw : 0 < w)
    (W : (Space d → ℝ) → Ω → ℝ) (ω : Ω)
    (h : Continuous fun q : ℝ × Space d => gaussianPotential d w W q.1 q.2 ω) :
    Continuous fun q : ℝ × Space d => gaussianPotential d v W q.1 q.2 ω := by
  have hs : Real.sqrt w ≠ 0 := (Real.sqrt_pos.2 hw).ne'
  have hfun : (fun q : ℝ × Space d => gaussianPotential d v W q.1 q.2 ω) =
      fun q => (Real.sqrt v / Real.sqrt w) * gaussianPotential d w W q.1 q.2 ω := by
    funext q
    simp only [gaussianPotential]
    field_simp
  rw [hfun]
  exact continuous_const.mul h

end Sandpile.Continuum

open Sandpile Sandpile.Continuum

/-- **The cube-killed scaling limit along a sequence of scenery laws** (`sandpile.tex:1950-1955`).
For laws of mean zero with a common exponential moment bound and variances converging to
`v > 0`, the rescaled localized odometers built from the law `νs k` at the scale `R` are coupled
with the cube-killed value of the Gaussian potential of the limiting variance `v`, once both the
law index and the scale are large. -/
theorem Sandpile.dlt4_killed_scaling_sequence_of_inputs
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.CubeStoppingStability)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (θ M v : ℝ) (hθ : 0 < θ) (hv : 0 < v)
    (νs : ℕ → Measure ℝ) (hprob : ∀ k, IsProbabilityMeasure (νs k))
    (hmean : ∀ k, ∫ z, z ∂(νs k) = 0)
    (hexp : ∀ k, Integrable (fun z => Real.exp (θ * |z|)) (νs k))
    (hM : ∀ k, ∫ z, Real.exp (θ * |z|) ∂(νs k) ≤ M)
    (hvar : Tendsto (fun k => variance id (νs k)) atTop (𝓝 v))
    (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (hZcont : ∀ᵐ ω ∂PW, Continuous fun q : ℝ × Sandpile.Continuum.Space d =>
      Sandpile.Continuum.gaussianPotential d v W q.1 q.2 ω)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K) (T : ℝ) (hT : 0 < T)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ k₀ : ℕ, ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, R₀ ≤ R →
      ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
        P.map Prod.fst = Sandpile.centeredMassLaw d (νs k) ∧
        P.map Prod.snd = PW ∧
        P {p | ∃ u ∈ K,
            ε < |R ^ (-(2 - (d : ℝ) / 2)) *
                  Sandpile.localizedOdometer (Sandpile.supBox (fun i => ⌊R * u i⌋) R)
                    (Sandpile.scenery d p.1) ⌊T * R ^ 2⌋₊ (fun i => ⌊R * u i⌋)
                - Sandpile.Continuum.brownianValueCube (B u) PB
                    (fun t y => Sandpile.Continuum.gaussianPotential d v W t y p.2)
                    T 1 u|}
          ≤ ENNReal.ofReal δ := by
  classical
  by_contra hno
  have hfail : ∀ n : ℕ, ∃ k : ℕ, n ≤ k ∧ ∃ R : ℝ, (n : ℝ) + 1 ≤ R ∧
      ¬ ∃ P : Measure ((Sandpile.Site d → ℝ) × ΩW), IsProbabilityMeasure P ∧
        P.map Prod.fst = Sandpile.centeredMassLaw d (νs k) ∧
        P.map Prod.snd = PW ∧
        P {p | ∃ u ∈ K,
            ε < |R ^ (-(2 - (d : ℝ) / 2)) *
                  Sandpile.localizedOdometer (Sandpile.supBox (fun i => ⌊R * u i⌋) R)
                    (Sandpile.scenery d p.1) ⌊T * R ^ 2⌋₊ (fun i => ⌊R * u i⌋)
                - Sandpile.Continuum.brownianValueCube (B u) PB
                    (fun t y => Sandpile.Continuum.gaussianPotential d v W t y p.2)
                    T 1 u|}
          ≤ ENNReal.ofReal δ := by
    intro n
    by_contra hn
    apply hno
    refine ⟨n, (n : ℝ) + 1, by positivity, fun k hk R hR => ?_⟩
    by_contra hg
    exact hn ⟨k, hk, R, hR, hg⟩
  choose kseq hk hRex using hfail
  choose Rseq hR hbad using hRex
  have hkt : Tendsto kseq atTop atTop := tendsto_atTop_mono hk tendsto_id
  have hRt : Tendsto Rseq atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith [hR n]) tendsto_natCast_atTop_atTop
  haveI : ∀ n, IsProbabilityMeasure (νs (kseq n)) := fun n => hprob (kseq n)
  have hfdd : ∀ (m : ℕ) (r : Fin m → ℝ) (w : Fin m → Space d),
      (∀ i, r i ∈ Set.Icc (0 : ℝ) T) →
      TendstoInDistribution
        (fun n (σ : Site d → ℝ) (i : Fin m) =>
          Frozen.HeatPotentialInvariance.linInterp d (Rseq n) (scenery d σ) (r i) (w i))
        atTop (fun ω i => gaussianPotential d v W (r i) (w i) ω)
        (fun n => centeredMassLaw d (νs (kseq n))) PW := by
    intro m r w hr
    exact Support.heat_potential_fd_seq hLocalCLT hd hd3
      (Support.continuum_double_time_limit hd hd3) θ M v hθ hv (fun n => νs (kseq n))
      (fun n => hmean (kseq n)) (fun n => hexp (kseq n)) (fun n => hM (kseq n))
      (hvar.comp hkt) Rseq hRt PW W hW r (fun i => (hr i).1) w (∑ i, ‖w i‖)
      (fun i => Finset.single_le_sum (f := fun j => ‖w j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i))
  have hev := Sandpile.dlt4_killed_scaling_seq_of_fdd hStab hd hd3 θ M hθ
    (fun n => νs (kseq n)) (fun n => hmean (kseq n)) (fun n => hexp (kseq n))
    (fun n => hM (kseq n)) Rseq hRt PW (fun ω t x => gaussianPotential d v W t x ω) hZcont
    ΩB PB B hB K hK T hT hfdd ε δ hε hδ
  obtain ⟨n, hn⟩ := hev.exists
  exact hbad n hn
