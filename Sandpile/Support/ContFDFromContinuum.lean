import Sandpile.Support.ContInterpDoubleTime

/-!
# The finite-dimensional clause, reduced to a single continuum statement

The finite-dimensional clause of `prop:dlt4-heat-potential-invariance` in dimensions one to
three, reduced to a single continuum statement. `Sandpile.Support.heat_potential_fd_of_double_time`
reduced the clause to the convergence of the rescaled double time sums of transition
probabilities. `ContSmallTime`, `ContTimeCut`, `ContDoubleTimeLimit` and `ContInterpDoubleTime`
prove that convergence from the local central limit theorem, for every pair of horizons and
every pair of points of space, EXCEPT for one step that has nothing to do with the lattice: that
the continuum double time integrals against the trapezoidal time weights increase, as the
resolution improves, to the double time integral of the proposition. That step is
`ContinuumDoubleTimeLimit` below, and it is monotone convergence: the weights increase pointwise
to the indicator of the open time rectangle, and the Brownian heat kernel is integrable over that
rectangle below dimension four (`Sandpile.Support.lintegral_double_time_two_lt_top`). The `max`
in its statement is inert, since the two weights vanish below `1/n` and the kernel is therefore
never read below `2/n`. `tendsto_interpDoubleTimeSum_of_continuum` derives the interpolated
double time sum convergence from `ContinuumDoubleTimeLimit`, and
`heat_potential_fd_of_continuum` assembles the finite-dimensional clause itself from it.
-/

open LatticeProb.TimeCut

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- The one continuum statement the finite-dimensional clause still rests on. -/
def ContinuumDoubleTimeLimit (d : ℕ) : Prop :=
  ∀ r r' : ℝ, 0 < r → 0 < r' → ∀ w w' : Space d,
    Tendsto (fun n : ℕ =>
        ∫ s in Set.Ico (0 : ℝ) (r + r' + 1), ∫ u in Set.Ico (0 : ℝ) (r + r' + 1),
          lowerCut n r s * lowerCut n r' u *
            heatKernelBM d (max (s + u) (2 * (1 / ((n : ℝ) + 1)))) w w') atTop
      (𝓝 (∫ s in (0 : ℝ)..r, ∫ u in (0 : ℝ)..r', heatKernelBM d (s + u) w w'))

/-- Given the local CLT and the continuum hypothesis `hMCT`, the interpolated double time sum
`interpDoubleTimeSum` converges as the mesh resolution `R → ∞` to the continuum double time
integral of the Brownian heat kernel. The cases `r = 0` and `r' = 0` are handled directly by the
zero-horizon lemmas `tendsto_interpDoubleTimeSum_zero_left`/`_right`, and the case `r, r' > 0`
follows `tendsto_interpDoubleTimeSum` fed by `hMCT`. -/
theorem tendsto_interpDoubleTimeSum_of_continuum
    (hLCLT : Sandpile.External.LocalCLT) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hMCT : ContinuumDoubleTimeLimit d)
    {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (w w' : Space d) :
    Tendsto (fun R : ℝ => interpDoubleTimeSum d R r r' w w') atTop
      (𝓝 (∫ s in (0 : ℝ)..r, ∫ u in (0 : ℝ)..r', heatKernelBM d (s + u) w w')) := by
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · have hI : (∫ s in (0 : ℝ)..r, ∫ u in (0 : ℝ)..r', heatKernelBM d (s + u) w w') = 0 := by
      rw [← hr0, intervalIntegral.integral_same]
    rw [hI, ← hr0]
    exact tendsto_interpDoubleTimeSum_zero_left hd hd3 hr' w w'
  · rcases eq_or_lt_of_le hr' with hr'0 | hr'pos
    · have hI : (∫ s in (0 : ℝ)..r, ∫ u in (0 : ℝ)..r', heatKernelBM d (s + u) w w') = 0 := by
        have hinner : ∀ s : ℝ, (∫ u in (0 : ℝ)..r', heatKernelBM d (s + u) w w') = 0 := by
          intro s
          rw [← hr'0, intervalIntegral.integral_same]
        simp only [hinner]
        exact intervalIntegral.integral_zero
      rw [hI, ← hr'0]
      exact tendsto_interpDoubleTimeSum_zero_right hd hd3 hr w w'
    · exact tendsto_interpDoubleTimeSum hLCLT hd hd3 hrpos hr'pos w w' (hMCT r r' hrpos hr'pos w w')

/-- **The finite-dimensional clause of `prop:dlt4-heat-potential-invariance`, in dimensions one
to three, derived from the single continuum hypothesis `hMCT`.** Combines
`heat_potential_fd_of_double_time` with the double time sum convergence supplied by
`tendsto_interpDoubleTimeSum_of_continuum`. -/
theorem heat_potential_fd_of_continuum
    (hLCLT : Sandpile.External.LocalCLT) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (hMCT : ContinuumDoubleTimeLimit d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    {m : ℕ} (r : Fin m → ℝ) (hr : ∀ i, 0 ≤ r i) (w : Fin m → Space d) (L : ℝ)
    (hw : ∀ i, ‖w i‖ ≤ L) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site d → ℝ) (i : Fin m) =>
        Sandpile.Frozen.HeatPotentialInvariance.linInterp d R (Sandpile.scenery d σ) (r i) (w i))
      atTop
      (fun (ω : ΩW) (i : Fin m) =>
        Sandpile.Continuum.gaussianPotential d (variance (id : ℝ → ℝ) ν) W (r i) (w i) ω)
      (fun _ => Sandpile.centeredMassLaw d ν) PW :=
  heat_potential_fd_of_double_time hd hd3 ν hsq hmean PW W hW r hr w L hw
    (fun i j => tendsto_interpDoubleTimeSum_of_continuum hLCLT hd hd3 hMCT (hr i) (hr j)
      (w i) (w j))

end Sandpile.Support
