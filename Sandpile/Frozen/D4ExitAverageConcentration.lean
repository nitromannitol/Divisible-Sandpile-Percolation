/-
Lemma of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3947-3958`
(label `lem:d4-exit-average-concentration`):

  "Fix $\theta_{0}>0$ and $K_{0}<\infty$.  There are $c>0$ and $C<\infty$,
   depending only on $\theta_{0}$ and $K_{0}$, such that, for every mean-zero
   i.i.d.\ field $(\zeta(x))_{x\in\Z^4}$ with
   $\E e^{\theta_{0}|\zeta(0)|}\leq K_{0}$, every integer $r\geq2$, and every
   $s\geq0$,
   \[
     \sup_{z\in\Z^4}\P\bigl(|Y_r(z)-\E Y_r(z)|>s\bigr)
     \leq C\exp\{-c\min(s^2,sr^2)\}\, .
   \]"

Modelling.  The statement is about the scenery alone, so the field is
`LatticeProb.iidLaw 4 ν` with one-site law `ν`, and `E Y_r(z)` is the integral
of `Y_r(·)(z)` against that law.  The exponential moment is an integral bound.

`Y_r` is the exit-averaged localized value of `sandpile.tex:3869-3877`,
repeated here as `eaExitValue`, together with the box `Q(x,L)` it uses:

  `Y_r(z) = E_z[1_{{τ_{Q(z,r)} ≤ A_ex r²}} u_{r²}^{Q(X_τ,A_loc r)}(X_τ) | ζ]`,

an integral against `Sandpile.walkLaw 4 z`, the law of simple random walk
started at `z`, with `u^D_t` the localized value `Sandpile.localizedOdometer`
of `eq:localized-odometer`.  Conditioning on the scenery is exactly this: the
scenery is a parameter and the integral is over the walk only.  As in
`lem:localization-killing`, `exitTime` has type `ℕ∞`, the event
`{τ ≤ A_ex r²}` is written in `ℕ∞`, and the walk is evaluated at
`(exitTime …).toNat`; the integrand is a `Set.indicator` of that event, so on
its complement, where `toNat` may take the junk value `0`, the value is
multiplied by zero and never read.

Quantifier order.  `c` and `C` are bound after `θ₀` and `K₀` and before the
law, since the paper says they depend only on `θ₀` and `K₀`.  The parameters
`A_loc ≥ 1` and the integer `A_ex ≥ 1` are fixed in the running text before the
lemma, but the lemma asserts that `c` and `C` depend on `θ₀` and `K₀` alone, so
they are bound after `c` and `C`: the constants are uniform over the choice of
`A_loc` and `A_ex`, which is what the proof gives, the two norm bounds on the
influence weights being uniform in them.  The supremum over `z` is written as a
universally quantified `z` inside the bound, the same statement without an
`sSup` junk value, and the bound is on the measure of the deviation event in
`ℝ≥0∞` against `ENNReal.ofReal` of the paper's right-hand side, so no `toReal`
junk value can weaken it.  The threshold `r ≥ 2` is the paper's.

The exponential-moment bound is stated together with the integrability of the
exponential, as the paper's `K₀ < ∞` requires: the Bochner integral of a
non-integrable nonnegative function is zero, so the bound alone would hold for
every law with no exponential moment.
-/
import Sandpile.Support.ExitConcentration
import Sandpile.External.BallGreenBounds

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
    (hBallGreen : Sandpile.External.BallGreenBounds)
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
  obtain ⟨c, C, hc, hC, htail⟩ := Sandpile.exists_cube_exit_concentration hBallGreen θ₀ K₀ hθ₀
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
