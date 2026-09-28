import Sandpile.Support.ExitConcentration
import Sandpile.External.BallGreenBounds
import Sandpile.External.BallGreenBoundsProved

/-!
# Concentration of the exit-averaged localized value in dimension four

`eaCube` is the cube `Q(x,L) = {y ∈ ℤ⁴ : max_i |y_i - x_i| ≤ L}`, and `eaExitValue` is the
exit-averaged localized value `Y_r(z)` of `sandpile.tex:3864-3872`, the expectation over the
random walk from `z` of the localized odometer evaluated where the walk exits `Q(z,r)`,
conditioned on the scenery.  `Sandpile.Frozen.d4_exit_average_concentration` is
`lem:d4-exit-average-concentration`: for a mean-zero i.i.d. scenery with a controlled exponential
moment, the deviation of `Y_r(z)` from its mean has a two-regime sub-Gaussian and
sub-exponential tail `C\exp(-c\min(s^2, sr^2))`, uniformly over `z`, `r ≥ 2`, and the
localization parameters, with `c` and `C` depending only on `θ₀` and `K₀`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

/-- `Q(x,L) = {y ∈ ℤ⁴ : max_i |y_i - x_i| ≤ L}` (`sandpile.tex:680-682`). -/
def eaCube (x : Site 4) (L : ℝ) : Set (Site 4) :=
  {y | ∀ i : Fin 4, |((y i : ℝ) - (x i : ℝ))| ≤ L}

/-- `Y_r(z) = E_z[1_{{τ_{Q(z,r)} ≤ A_ex r²}} u_{r²}^{Q(X_τ,A_loc r)}(X_τ) | ζ]`
(`sandpile.tex:3864-3872`). -/
noncomputable def eaExitValue (Aex : ℕ) (Aloc : ℝ) (r : ℕ) (ζ : Site 4 → ℝ)
    (z : Site 4) : ℝ :=
  ∫ X, Set.indicator
      {X : ℕ → Site 4 | exitTime (eaCube z (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)}
      (fun X => localizedOdometer
        (eaCube (X (exitTime (eaCube z (r : ℝ)) X).toNat) (Aloc * r)) ζ (r ^ 2)
        (X (exitTime (eaCube z (r : ℝ)) X).toNat)) X
    ∂(walkLaw 4 z)

end Sandpile

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_exit_average_concentration
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ Aloc : ℝ, 1 ≤ Aloc → ∀ Aex : ℕ, 1 ≤ Aex →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ r : ℕ, 2 ≤ r → ∀ s : ℝ, 0 ≤ s → ∀ z : Sandpile.Site 4,
          LatticeProb.iidLaw 4 ν
              {ζ | s < |Sandpile.eaExitValue Aex Aloc r ζ z -
                ∫ η, Sandpile.eaExitValue Aex Aloc r η z ∂(LatticeProb.iidLaw 4 ν)|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2) (s * (r : ℝ) ^ 2))))
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨c, C, hc, hC, htail⟩ :=
    Sandpile.exists_cube_exit_concentration Sandpile.External.ballGreenBounds θ₀ K₀ hθ₀
  refine ⟨c, C, hc, hC, ?_⟩
  intro Aloc _hAloc Aex _hAex ν hν _hmean hexp hK r hr s hs z
  have he : ∀ ζ : Sandpile.Site 4 → ℝ,
      Sandpile.eaExitValue Aex Aloc r ζ z =
        Sandpile.localizedExitAverage (Sandpile.eaCube z r) (Aex * r ^ 2)
          (fun w => Sandpile.eaCube w (Aloc * r)) (r ^ 2) ζ z := by
    intro ζ
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun X =>
      (Sandpile.localizedExitPayoff_eq_indicator (Sandpile.eaCube z r) (Aex * r ^ 2)
        (fun w => Sandpile.eaCube w (Aloc * r)) (r ^ 2) ζ X).symm
  simpa only [he, Sandpile.eaCube] using
    htail ν hν hexp hK r hr (Aex * r ^ 2) (fun w => Sandpile.eaCube w (Aloc * r)) z s hs
