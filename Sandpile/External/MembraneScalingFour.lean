import Sandpile.Law
import Sandpile.Continuum.Membrane
import Sandpile.Support.D4PotentialKernel

/-!
# The four-dimensional discrete membrane scaling limit

External input: the scaling limit of the four-dimensional discrete membrane
field.  Step 1 of the proof of `prop:d4-superdiffusive-limit` records at
`sandpile.tex:3341-3342` that

  "Convergence of the discrete membrane field to the continuum membrane field
   is standard; see for example \citet*[Theorem~2]{CHR} and
   \citet*[Theorem~3.11]{CDH}.  We indicate the argument, the one new point
   being that the time truncation in $V_{t_R}$ washes out at superdiffusive
   times."

The cited half is assumed here; the new point is not.  The paper's own sentence
is proved in this repository: `Sandpile.tendsto_multiplier` and
`Sandpile.multiplier_uniform_bound` are the multiplier statements of
`sandpile.tex:3345-3352`, and the `ℓ²` hypothesis below is the quantitative form
of "the time truncation washes out", discharged at `t_R = ⌊R^α⌋` with `α > 2`.

The untruncated field.  The discrete membrane field of the two citations is the
`t → ∞` limit of `V_t`, which in dimension four exists only modulo additive
constants and only in `L²`: its kernel is the potential kernel
`a(x,y) = ∑_{j≥0}(p_j(x,y) - p_j(0,y))` of `Sandpile.potentialKernel`, and
`∑_y |a(x,y)|` diverges in dimension four, so no pointwise sum defines it.  The
untruncated field therefore enters through its kernel, which is bounded
(`Sandpile.exists_potentialKernel_bound_four`) and is all the statement needs:
the hypothesis compares the kernel of the truncated field with `a` in the paired
`ℓ²` sense, which for a field linear in an i.i.d. scenery is exactly `L²`
closeness of the two paired fields.  Slutsky then transfers the cited limit of
the untruncated field to the truncated one, which is what the conclusion
asserts.

Modelling.  The scenery is carried by `centeredMassLaw 4 ν`, the law of
`σ = 1 + 8ζ`, so the membrane field is `Sandpile.membrane (Sandpile.scenery 4 σ)`
and its kernel is `Sandpile.greenTime 4 t`.  The `ω`-representative of
`eq:d4-omega-representative` is `Sandpile.Continuum.omegaRep D w`, and a lattice
field is paired through `Sandpile.Continuum.latticePairing`, exactly as in the
conclusion of `prop:d4-superdiffusive-limit`.  The limit is the centred Gaussian
with covariance `Sandpile.omegaMembraneCov4`, that is `𝒢_4^ω`.

Junk values.  The `ℓ²` hypothesis is a `tsum` in `ℝ≥0∞`, so a defect family that
fails to be square summable has the value `⊤` and cannot satisfy the hypothesis
through the junk value zero of a divergent real series.  The scenery law carries
mean zero and a variance that is positive and finite, which are the hypotheses of
the cited theorems; no exponential moment is needed for them.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.External

/-- The `ω`-paired defect at the site `y` between the kernel `g_t(·,y)` of the
time-truncated membrane field `V_t` and the four-dimensional potential kernel
`a(·,y)`.  Because the `ω`-representative pairs against `φ - ω∫_Dφ`, which
integrates to zero, this is also the defect between the two CENTRED kernels
`g_t(·,y) - g_t(0,y)` and `a(·,y) - a(0,y) = a(·,y)`. -/
noncomputable def membraneDefect (R : ℝ) (t : ℕ)
    (D : Set (Sandpile.Continuum.Space 4)) (w φ : Sandpile.Continuum.Space 4 → ℝ)
    (y : Sandpile.Site 4) : ℝ :=
  Sandpile.Continuum.omegaRep D w
    (Sandpile.Continuum.latticePairing R
      (fun x => Sandpile.greenTime 4 t x y - Sandpile.potentialKernel 4 x y)) φ

end Sandpile.External

-- FROZEN-STATEMENT-BEGIN
/-- The scaling limit of the four-dimensional discrete membrane field
(`sandpile.tex:3341-3342`, citing Cipriani-Hazra-Ruszel Theorem 2 and
Cipriani-Dan-Hazra Theorem 3.11): a lattice field whose kernel approaches the
four-dimensional potential kernel in the paired `ℓ²` sense has `ω`-representative
converging to `𝒢_4^ω` in `H^{-s}(D)`.  Assumed, not proved. -/
def Sandpile.External.MembraneScalingLimitFour : Prop :=
  ∀ ν : Measure ℝ, ∀ _hprob : IsProbabilityMeasure ν, ∫ z, z ∂ν = 0 →
    0 < evariance id ν → evariance id ν < ⊤ →
    ∀ D : Set (Sandpile.Continuum.Space 4), Sandpile.Continuum.IsDomain D →
    ∀ w : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsAveragingDensity D w →
    ∀ s : ℝ, 0 < s → ∀ T : ℝ → ℕ,
      (∀ φ : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsTestFn D φ →
          Tendsto (fun R : ℝ => ∑' y : Sandpile.Site 4,
            ENNReal.ofReal (Sandpile.External.membraneDefect R (T R) D w φ y ^ 2))
            atTop (nhds 0)) →
      (∀ φ : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsTestFn D φ →
          TendstoInDistribution
            (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
              Sandpile.Continuum.omegaRep D w
                (Sandpile.Continuum.latticePairing R
                  (Sandpile.membrane (Sandpile.scenery 4 σ) (T R))) φ)
            atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
            (gaussianReal 0 (Real.toNNReal
              (Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ)))) ∧
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
          Sandpile.centeredMassLaw 4 ν
              {σ | M < Sandpile.Continuum.negSobolevNorm 4 s D
                (Sandpile.Continuum.omegaRep D w
                  (Sandpile.Continuum.latticePairing R
                    (Sandpile.membrane (Sandpile.scenery 4 σ) (T R))))} ≤
            ENNReal.ofReal ε)
-- FROZEN-STATEMENT-END
