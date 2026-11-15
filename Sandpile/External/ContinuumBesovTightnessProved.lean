import Sandpile.External.ContinuumBesovTightness
import LatticeProb.Prob.NegSobolevTightness

/-!
# The Furlan-Mourrat Besov tightness criterion, proved

This module discharges the external input `Sandpile.External.ContinuumBesovTightness`, the
covariance form of the tightness criterion of Furlan and Mourrat (Theorem 2.30 at `p = q = 2`,
together with the identification of `B^{-s,loc}_{2,2}(ℝ^d)` with `H^{-s}_loc(ℝ^d)`) that the paper
invokes at `sandpile.tex:1661-1680`, instead of assuming it.

The shared library proves the same statement, over the same space `ℝ^d`, the same test functions
and the same negative Sobolev norms on bounded domains, as
`LatticeProb.Sobolev.continuumBesovTightness_holds`.  Its proof cuts the field off by a test
function equal to one near the closure of the domain, bounds the expected Fourier `H^{-s}` energy
of the cut-off rescaled field uniformly in the scale (through the heat-kernel covariance identity,
a Riesz-kernel estimate and the Gamma representation of the Fourier weight, which is where
`s > β / 2` enters), and concludes by Markov's inequality.  The library's tightness predicate has
the same body as `Sandpile.Continuum.TightInNegSobolev`, so its statement is this one up to
unfolding.

The `Prop` and its name are left untouched, so no frozen statement changes.
-/

-- FROZEN-STATEMENT-BEGIN
/-- The covariance form of the tightness criterion of Furlan and Mourrat, Theorem 2.30, at
`p = q = 2` with regularity exponent `-β/2` and `α = -s`, together with the identification of
`B^{-s,loc}_{2,2}(ℝ^d)` with `H^{-s}_loc(ℝ^d)`, proved rather than assumed. -/
theorem Sandpile.External.continuumBesovTightness_holds (Ω : Type*) [MeasurableSpace Ω] :
    Sandpile.External.ContinuumBesovTightness Ω
-- FROZEN-STATEMENT-END
:= LatticeProb.Sobolev.continuumBesovTightness_holds Ω
