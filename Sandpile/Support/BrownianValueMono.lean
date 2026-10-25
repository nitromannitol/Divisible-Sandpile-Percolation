module

public import Sandpile.Support.BrownianValueMono.GreenZeroDim
public import Sandpile.Support.BrownianValueMono.AffineZeroDim
public import Sandpile.Support.BrownianValueMono.HorizonFreeZeroDim
public import Sandpile.Support.BrownianValueMono.Envelope
public import Sandpile.Support.BrownianValueMono.PositiveDim
public import Sandpile.Support.BrownianValueMono.ZeroDimPackaged
public import Sandpile.Support.BrownianValueMono.MonoHorizon

@[expose] public section

/-!
# Horizon monotonicity of the Gaussian heat potential's Brownian value

Aggregates the `BrownianValueMono` development, which proves
`Sandpile.Continuum.brownianValue_mono_horizon_gaussianPotential` (assembled in `MonoHorizon`):
the Brownian value `𝒰_Z(s,z)` of the Gaussian heat potential `Z` is monotone nondecreasing in the
horizon, `𝒰_Z(s,z) ≤ 𝒰_Z(T,z)` for `0 ≤ s ≤ T`. The proof case-splits on the dimension. For
`1 ≤ d ≤ 3`, `PositiveDim` supplies the two hypotheses of the horizon-monotonicity lemma
(horizon-freeness of stopping payoffs and boundedness at the top horizon) from the samplewise
polynomial growth of the field (`Envelope`) and the backward heat-increment martingale. For
`d = 0`, `Space 0` is a single point; `GreenZeroDim` and `AffineZeroDim` establish that the field
is then exactly affine in time, `HorizonFreeZeroDim` derives horizon-freeness directly from that
affine identity, and `ZeroDimPackaged` supplies the same two hypotheses this way.
-/
