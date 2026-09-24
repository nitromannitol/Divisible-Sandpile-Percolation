import Mathlib

/-!
# Theorem 1.3(ii)(c) (`thm:main-explosion`): comparator challenge

Mathlib-only comparator challenge for Theorem 1.3(ii)(c) (`thm:main-explosion`)
of Bou-Rabee and Panagiotis, *Quantitative explosion and percolation of the
divisible sandpile* (arXiv:2609.02829).  The certified statement is
`Sandpile.Frozen.four_sobolev`, restated in `Sandpile/MainTheorems.lean` as
`Sandpile.four_sobolev`.  Content: in `d = 4`, the centred odometer is tight in
every negative Sobolev space at diffusive times, and at polynomial
superdiffusive times converges, modulo constants, to the four-dimensional
membrane model.

Only Mathlib is imported.  The vocabulary between `VOCABULARY-BEGIN` and
`VOCABULARY-END` rebuilds, from Mathlib primitives, every definition needed to
read the twelve main theorems: the lattice, i.i.d. laws, the heat kernel and the
Brownian exit time (copied from `Lattice-Probability`), the odometer and its
limit, the walk and its stopping problems, the continuum kernels, Sobolev norms,
white noise, Brownian motion and the Brownian stopping values, the planar
crossing events and the continuum planar fields, and the cited results.  It is a
statement-level copy of the definitions the repository uses (see
`Audit/README.md` for the provenance table) and is byte-identical in all twelve
challenges.  The sole intentional `sorry` is the proof of the final theorem.

## Cited results

The paper uses results from the literature without proof.  The certified
statement takes each one its proof uses as an explicit hypothesis, and this
challenge carries the same hypotheses, restated in the vocabulary.  Of these,
`HeatKernelBounds` and `VarianceScale` are also proved in the repository
(`Sandpile/External/*Proved.lean`), but the certified statement keeps them as
hypotheses, and so does the challenge.

* `External.HeatKernelBounds`: the heat-kernel bounds (Lawler and Limic,
  Propositions 2.4.1 and 2.4.4);
* `External.VarianceScale`: the finite-time variance scale, membrane
  correlations and window bounds of `ssec:green-estimates`;
* `External.ContinuumBesovTightness`: the Besov tightness criterion (Furlan and
  Mourrat, Theorem 2.30);
* `External.MembraneScalingLimitFour`: the scaling limit of the four-dimensional
  membrane model (Cipriani, Hazra and Ruszel, Theorem 2; Cipriani, Dan and Hazra,
  Theorem 3.11).

## Presentation deltas

None at the level of the displayed statement: the theorem below is the statement
of `Sandpile.four_sobolev` with every repository and library name replaced by
its vocabulary copy.
-/

-- VOCABULARY-BEGIN
namespace SandpileAudit

universe u

/-! ## 1. Sites, the lattice, i.i.d. laws, the heat kernel and the exit time

Copied from the shared library `Lattice-Probability` (`LatticeProb/Site.lean`,
`LatticeProb/IID.lean`, `LatticeProb/Walk/LocalCLT.lean`,
`LatticeProb/Walk/LatticeGreen.lean`, `LatticeProb/Gauss/Coords.lean`,
`LatticeProb/Prob/BrownianExitTime.lean`).  The repository re-exports `Site`,
`unit`, `lattice`, `nbrSum` and `HasInfiniteComponent` into its own namespace and
names the heat kernel and the finite-time Green kernel `Sandpile.heatKernel` and
`Sandpile.greenTime`, as abbreviations of the library's; each is copied once. -/

section LatticeProb

open MeasureTheory
open scoped ENNReal NNReal

/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ

/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1

/-- The nearest-neighbour lattice on `ℤ^d`. -/
def lattice (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := ∃ i : Fin d, y = x + unit i ∨ x = y + unit i
  symm := ⟨fun _ _ h => h.imp fun _ hi => hi.symm⟩
  loopless := ⟨fun x h => by
    obtain ⟨i, hi | hi⟩ := h
    · have := congrFun hi i; simp [unit] at this
    · have := congrFun hi i; simp [unit] at this⟩

/-- The sum of `u` over the neighbours of `x`, direction by direction. -/
def nbrSum {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))

/-- The simple random walk operator `(P u)(x) = (1/2d) ∑_{y ∼ x} u(y)`. -/
noncomputable def walkOp {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  nbrSum u x / (2 * d)

/-- The vertices joined to `x` inside `S`, along edges of the lattice. -/
def componentIn {d : ℕ} (S : Set (Site d)) (x : Site d) : Set (Site d) :=
  {y | ∃ (hx : x ∈ S) (hy : y ∈ S), ((lattice d).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩}

/-- `S` contains an infinite nearest-neighbour component. -/
def HasInfiniteComponent {d : ℕ} (S : Set (Site d)) : Prop :=
  ∃ x ∈ S, (componentIn S x).Infinite

/-- The law of an i.i.d. field on `ℤ^d` with one-site law `μ`. -/
noncomputable def iidLaw (d : ℕ) {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    Measure (Site d → α) :=
  Measure.infinitePi fun _ : Site d => μ

/-- One instruction at `y`: a uniformly chosen neighbour. -/
noncomputable def instructionLaw {d : ℕ} (y : Site d) : Measure (Site d) :=
  ((2 * (d : ℝ≥0∞))⁻¹) • Finset.univ.sum fun i : Fin d =>
    Measure.dirac (y + unit i) + Measure.dirac (y - unit i)

/-- The `k`-step transition probability `p_k(x, y)` of simple random walk,
recursing in the starting point `x`. -/
noncomputable def heatKernel (d : ℕ) : ℕ → Site d → Site d → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | k + 1 => fun x y =>
      (∑ i : Fin d, (heatKernel d k (x + unit i) y + heatKernel d k (x - unit i) y)) / (2 * d)

/-- The finite-time Green kernel `g_t(x, y) = ∑_{k<t} p_k(x, y)`. -/
noncomputable def greenTime (d : ℕ) (t : ℕ) (x y : Site d) : ℝ :=
  ∑ k ∈ Finset.range t, heatKernel d k x y

/-- The law of an independent family of standard Gaussians indexed by `ι`. -/
noncomputable def gaussLaw (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi fun _ : ι => ProbabilityTheory.gaussianReal 0 1

open Classical in
/-- The first time the motion is at distance at least `A` from `u`. -/
noncomputable def exitTime {Ω : Type*} {d : ℕ} (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (A : ℝ) (ω : Ω) : ℝ≥0∞ :=
  if _h : ∃ s : ℝ≥0, A ≤ ‖B s ω - u‖ then ((sInf {s : ℝ≥0 | A ≤ ‖B s ω - u‖} : ℝ≥0) : ℝ≥0∞)
  else ⊤

end LatticeProb

/-! ## 2. The divisible sandpile, the walk and the stopping problems

Copied from `Sandpile/Basic.lean`, `Sandpile/Law.lean` and `Sandpile/Walk.lean`. -/

section Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- One step of the recursion `eq:intro-recursion`. -/
noncomputable def relax {d : ℕ} (σ u : Site d → ℝ) (x : Site d) : ℝ :=
  max 0 ((σ x - 1 + nbrSum u x) / (2 * d))

/-- The finite-time odometer `u_t`, starting from `u_0 = 0`. -/
noncomputable def odometer {d : ℕ} (σ : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | t + 1 => relax σ (odometer σ t)

/-- The odometer limit `u_∞`, in `ℝ≥0∞` so that an exploding site has a value. -/
noncomputable def odometerLimit {d : ℕ} (σ : Site d → ℝ) (x : Site d) : ℝ≥0∞ :=
  ⨆ t : ℕ, ENNReal.ofReal (odometer σ t x)

/-- The toppled set `𝒯 = {x : u_∞(x) > 0}`. -/
noncomputable def toppledSet {d : ℕ} (σ : Site d → ℝ) : Set (Site d) :=
  {x | 0 < odometerLimit σ x}

/-- The law of an i.i.d. mass field with one-site law `μ`. -/
noncomputable def massLaw (d : ℕ) (μ : MeasureTheory.Measure ℝ) :
    MeasureTheory.Measure (Site d → ℝ) :=
  iidLaw d μ

/-- The centred field `ζ` scaled into a mass field: `σ = 1 + 2d ζ`. -/
noncomputable def centeredMassLaw (d : ℕ) (ν : Measure ℝ) : Measure (Site d → ℝ) :=
  massLaw d (ν.map fun z => 1 + 2 * (d : ℝ) * z)

instance {d : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (massLaw d μ) := by
  unfold massLaw iidLaw; infer_instance

instance {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (centeredMassLaw d ν) := by
  unfold centeredMassLaw
  have : IsProbabilityMeasure (ν.map fun z => 1 + 2 * (d : ℝ) * z) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  infer_instance

/-- `E u_t(0)`, the mean odometer at the origin after `t` steps. -/
noncomputable def meanOdometer {d : ℕ} (P : Measure (Site d → ℝ)) (t : ℕ) : ℝ :=
  ∫ σ, odometer σ t 0 ∂P

/-- The Green function `G(x, y) = ∑_{k≥0} p_k(x, y)`.  Transient dimensions only:
for `d ≤ 2` the series diverges and this takes the junk value zero. -/
noncomputable def green (d : ℕ) (x y : Site d) : ℝ := ∑' k : ℕ, heatKernel d k x y

/-- `P_x(X_k = y, k < τ_D)`, the transition kernel of the walk killed on
leaving `D`. -/
noncomputable def killedKernel {d : ℕ} (D : Set (Site d)) : ℕ → Site d → Site d → ℝ
  | 0 => fun x y => D.indicator (fun z => if z = y then (1 : ℝ) else 0) x
  | k + 1 => fun x y => D.indicator (fun z =>
      (∑ i : Fin d, (killedKernel D k (z + unit i) y + killedKernel D k (z - unit i) y)) / (2 * d)) x

/-- The killed finite-time Green kernel `g_t^D(x, y)`. -/
noncomputable def killedGreenTime {d : ℕ} (D : Set (Site d)) (t : ℕ) (x y : Site d) : ℝ :=
  ∑ k ∈ Finset.range t, killedKernel D k x y

/-- The killed Green kernel `g^D(x, y)`. -/
noncomputable def killedGreen {d : ℕ} (D : Set (Site d)) (x y : Site d) : ℝ :=
  ∑' k : ℕ, killedKernel D k x y

/-- The law of one increment of the walk: uniform on the `2d` unit vectors. -/
noncomputable def stepLaw (d : ℕ) : Measure (Site d) := instructionLaw (0 : Site d)

/-- The path started at `x` with increments `ξ`. -/
def walkPath {d : ℕ} (x : Site d) (ξ : ℕ → Site d) (k : ℕ) : Site d :=
  x + ∑ j ∈ Finset.range k, ξ j

/-- The law of simple random walk started at `x`, on path space `ℕ → Site d`. -/
noncomputable def walkLaw (d : ℕ) (x : Site d) : Measure (ℕ → Site d) :=
  (Measure.infinitePi fun _ : ℕ => stepLaw d).map (walkPath x)

/-- `τ` is a stopping time of the walk: whether it takes the value `k` is
determined by the positions up to time `k`. -/
def IsWalkStopping {d : ℕ} (τ : (ℕ → Site d) → ℕ) : Prop :=
  ∀ (k : ℕ) (X Y : ℕ → Site d), (∀ j ≤ k, X j = Y j) → τ X = k → τ Y = k

/-- The supremum of `E_x F(τ, X)` over stopping times `τ ≤ n`. -/
noncomputable def stoppingSup {d : ℕ} (n : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) : ℝ :=
  sSup {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
    a = ∫ X, F (τ X) X ∂(walkLaw d x)}

/-- The scenery `ζ = (σ - 1) / (2d)` of `eq:mass-excess-notation`. -/
noncomputable def scenery (d : ℕ) (σ : Site d → ℝ) (x : Site d) : ℝ := (σ x - 1) / (2 * d)

/-- The averaging operator `Pf(x) = (2d)^{-1} ∑_{y ∼ x} f(y)`. -/
noncomputable def avg {d : ℕ} (f : Site d → ℝ) : Site d → ℝ := walkOp f

/-- The membrane field `V_n` of `eq:membrane-recursion`: the odometer recursion
with the reflection removed. -/
noncomputable def membrane {d : ℕ} (ζ : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => ζ x + avg (membrane ζ n) x

/-- The critical scale `h(t)` of Theorem 1.2 (`Sandpile/Support/Crit23Scale.lean`). -/
noncomputable def criticalScale (d : ℕ) (t : ℕ) : ℝ :=
  if d ≤ 3 then (t : ℝ) ^ ((4 - (d : ℝ)) / 4)
  else if d = 4 then Real.log t
  else (Real.log t) ^ ((2 : ℝ) / d)

/-- The sup-norm box `Q(x, L) = {y ∈ ℤ^d : max_i |y_i - x_i| ≤ L}` of the
notation section, at a real radius `L`, written with the integer floor of `L`
(`Sandpile/Frozen/MeanLocalization.lean`). -/
def supBox {d : ℕ} (x : Site d) (L : ℝ) : Set (Site d) :=
  {y | ∀ i, |y i - x i| ≤ ⌊L⌋}

/-- The payoffs of the killed optimal-stopping problem on `D`: the payoffs of the
stopping times bounded by `n` which have not left `D` strictly before they stop
(`Sandpile/Support/KillRep.lean`). -/
def killedSet {d : ℕ} (D : Set (Site d)) (n : ℕ) (x : Site d) (F : ℕ → (ℕ → Site d) → ℝ) :
    Set ℝ :=
  {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
    (∀ X, ∀ j < τ X, X j ∈ D) ∧ a = ∫ X, F (τ X) X ∂(walkLaw d x)}

/-- The value of the killed optimal-stopping problem on `D`. -/
noncomputable def killedStoppingSup {d : ℕ} (D : Set (Site d)) (n : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) : ℝ :=
  sSup (killedSet D n x F)

/-- The potential kernel `a(x,y) = ∑_{j≥0}(p_j(x,y) - p_j(0,y))` of
`sandpile.tex:3341-3366` (`Sandpile/Support/D4PotentialKernel.lean`). -/
noncomputable def potentialKernel (d : ℕ) (x y : Site d) : ℝ :=
  ∑' j : ℕ, (heatKernel d j x y - heatKernel d j 0 y)

end Model

/-! ## 3. Continuum objects

Copied from `Sandpile/Continuum/Kernel.lean`, `Sobolev.lean`, `Membrane.lean`,
`WhiteNoise.lean` and `Stopping.lean`, and from `Sandpile/Support/ExplInterp.lean`,
`ExplFluctuation.lean` and `ExplKilledValue.lean`. -/

namespace Continuum

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal FourierTransform

/-- `ℝ^d` with its Euclidean norm. -/
abbrev Space (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The Brownian heat kernel `p_t^{BM}(x,y)` for generator `Δ/(2d)`. -/
noncomputable def heatKernelBM (d : ℕ) (t : ℝ) (x y : Space d) : ℝ :=
  (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) * Real.exp (-(d : ℝ) * ‖x - y‖ ^ 2 / (2 * t))

/-- The finite-time Brownian Green kernel `g_t^{BM}(x,y) = ∫_0^t p_s^{BM}(x,y) ds`. -/
noncomputable def greenTimeBM (d : ℕ) (t : ℝ) (x y : Space d) : ℝ :=
  ∫ s in (0 : ℝ)..t, heatKernelBM d s x y

/-- `φ ∈ C_c^∞(D)`. -/
def IsTestFn {d : ℕ} (D : Set (Space d)) (φ : Space d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D

/-- `‖φ‖_{H^s}²`, through the Fourier transform. -/
noncomputable def sobolevNormSq (d : ℕ) (s : ℝ) (φ : Space d → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ : Space d, ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)

/-- `‖F‖_{H^{-s}(D)}` for a functional `F` on test functions. -/
noncomputable def negSobolevNorm (d : ℕ) (s : ℝ) (D : Set (Space d))
    (F : (Space d → ℝ) → ℝ) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ φ : Space d → ℝ,
    IsTestFn D φ ∧ sobolevNormSq d s φ ≤ 1 ∧ v = ENNReal.ofReal |F φ|}

/-- The piecewise-constant embedding `f^{(R)}(z) = f(⌊Rz⌋)`. -/
noncomputable def embed {d : ℕ} (R : ℝ) (f : Site d → ℝ) (z : Space d) : ℝ :=
  f (fun i => ⌊R * z i⌋)

/-- The pairing `f^{(R)}(φ) = ∫ f(⌊Rz⌋) φ(z) dz`. -/
noncomputable def latticePairing {d : ℕ} (R : ℝ) (f : Site d → ℝ) (φ : Space d → ℝ) : ℝ :=
  ∫ z : Space d, embed R f z * φ z

/-- A bounded smooth domain of `ℝ^d`: the paper's `D` in `H^{-s}(D)`.  Only
boundedness, openness, and nonemptiness are used by the statements. -/
def IsDomain {d : ℕ} (D : Set (Space d)) : Prop :=
  IsOpen D ∧ Bornology.IsBounded D ∧ D.Nonempty

/-- The covariance of the time-weighted continuum membrane field `ℋ_{κ,T}` with
scenery variance `ν2`.  `κ = 0` is the finite-time membrane field `𝒢_{d,T}`. -/
noncomputable def weightedMembraneCov (d : ℕ) (ν2 κ T : ℝ) (φ ψ : Space d → ℝ) : ℝ :=
  ν2 * ∫ x : Space d, ∫ y : Space d, φ x * ψ y *
    (∫ r in (0 : ℝ)..T, ∫ r' in (0 : ℝ)..T,
      (1 - r / T) ^ κ * (1 - r' / T) ^ κ * heatKernelBM d (r + r') x y)

/-- The covariance of the four-dimensional continuum membrane model `𝒢_4`,
modulo additive constants, with scenery variance `ν2`. -/
noncomputable def membraneCov4 (ν2 : ℝ) (φ ψ : Space 4 → ℝ) : ℝ :=
  64 * ν2 * ∫ ξ : Space 4,
    (𝓕 (fun x => (φ x : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => (ψ x : ℂ)) ξ) /
      ((2 * Real.pi * ‖ξ‖ : ℝ) ^ 4 : ℂ)).re

/-- `F^ω(φ) = F(φ - ω ∫_D φ)`: the representative on `D` of a distribution modulo
constants whose `ω`-average is zero (`eq:d4-omega-representative`). -/
noncomputable def omegaRep {d : ℕ} (D : Set (Space d)) (w : Space d → ℝ)
    (F : (Space d → ℝ) → ℝ) (φ : Space d → ℝ) : ℝ :=
  F (fun x => φ x - w x * ∫ y in D, φ y)

/-- The `ω`-densities of `eq:d4-omega-representative`: `ω ∈ C_c^∞(D)`, `ω ≥ 0`,
`∫_D ω = 1`. -/
def IsAveragingDensity {d : ℕ} (D : Set (Space d)) (w : Space d → ℝ) : Prop :=
  IsTestFn D w ∧ (∀ x, 0 ≤ w x) ∧ ∫ x in D, w x = 1

/-- The family `F R` of random functionals is tight in `H^{-s}_loc(ℝ^d)`. -/
def TightInNegSobolev {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (s : ℝ)
    (P : Measure Ω) (F : ℝ → Ω → (Space d → ℝ) → ℝ) : Prop :=
  ∀ D : Set (Space d), IsDomain D → ∀ ε : ℝ, 0 < ε →
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
      P {ω | M < negSobolevNorm d s D (F R ω)} ≤ ENNReal.ofReal ε

/-- `F R ⟹ 𝔉 in H^{-s}_loc(ℝ^d)`, where `𝔉` is the centred Gaussian random
distribution with covariance `K`: every pairing converges in distribution to the
centred Gaussian of the matching variance, and the norms are tight. -/
def TendstoInNegSobolev {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (s : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → (Space d → ℝ) → ℝ)
    (K : (Space d → ℝ) → (Space d → ℝ) → ℝ) : Prop :=
  (∀ φ : Space d → ℝ, IsTestFn Set.univ φ →
      TendstoInDistribution (fun R : ℝ => fun ω : Ω => F R ω φ) atTop (id : ℝ → ℝ)
        (fun _ => P) (gaussianReal 0 (Real.toNNReal (K φ φ)))) ∧
    TightInNegSobolev d s P F

/-- `W` is white noise on `ℝ^d` under `P`: a mean-zero Gaussian family indexed by
square-integrable functions, linear in the index, with covariance the `L²` inner
product. -/
structure IsWhiteNoise {Ω : Type u} [MeasurableSpace Ω] (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) : Prop where
  /-- The finite-dimensional laws are Gaussian. -/
  gaussian : IsGaussianProcess W P
  /-- Each `W f` is measurable. -/
  meas : ∀ f : Space d → ℝ, MemLp f 2 (volume : Measure (Space d)) → Measurable (W f)
  /-- Each `W f` is centred. -/
  mean : ∀ f : Space d → ℝ, MemLp f 2 (volume : Measure (Space d)) →
    ∫ ω, W f ω ∂P = 0
  /-- The covariance is the `L²` inner product. -/
  cov : ∀ f g : Space d → ℝ, MemLp f 2 (volume : Measure (Space d)) →
    MemLp g 2 (volume : Measure (Space d)) →
    ∫ ω, W f ω * W g ω ∂P = ∫ y : Space d, f y * g y
  /-- Additivity in the index. -/
  add : ∀ f g : Space d → ℝ, MemLp f 2 (volume : Measure (Space d)) →
    MemLp g 2 (volume : Measure (Space d)) →
    W (f + g) =ᵐ[P] fun ω => W f ω + W g ω
  /-- Homogeneity in the index. -/
  smul : ∀ (a : ℝ) (f : Space d → ℝ), MemLp f 2 (volume : Measure (Space d)) →
    W (a • f) =ᵐ[P] fun ω => a * W f ω
  /-- Along each strongly measurable spatial L2 family there is a jointly measurable
  version, equal to the specified coordinate almost surely at every parameter. -/
  jointMeas : ∀ {U : Type u} [MeasurableSpace U] (μ : Measure U) [SigmaFinite μ]
      (f : U → Space d → ℝ) (hf : ∀ u, MemLp (f u) 2 volume),
      StronglyMeasurable (fun u => (hf u).toLp (f u)) →
      ∃ g : U → Ω → ℝ, StronglyMeasurable (Function.uncurry g) ∧
        ∀ u, g u =ᵐ[P] W (f u)

/-- The point field `Z(t,x) = √Var(ζ(0)) 𝒲(g_t^{BM}(x,·))`. -/
noncomputable def gaussianPotential {Ω : Type*} (d : ℕ) (ν2 : ℝ)
    (W : (Space d → ℝ) → Ω → ℝ) (t : ℝ) (x : Space d) (ω : Ω) : ℝ :=
  Real.sqrt ν2 * W (fun y => greenTimeBM d t x y) ω

/-- `B` is Brownian motion on `ℝ^d` with generator `Δ/(2d)` started at `x`. -/
structure IsBrownian {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (x : Space d)
    (B : ℝ≥0 → Ω → Space d) (P : Measure Ω) : Prop where
  /-- The process starts at `x`. -/
  start : ∀ᵐ ω ∂P, B 0 ω = x
  /-- Each coordinate, centred and scaled by `√d`, is a real Brownian motion. -/
  coord : ∀ i : Fin d, IsBrownianReal (fun t ω => Real.sqrt d * (B t ω i - x i)) P
  /-- The coordinate processes are independent. -/
  indep : iIndepFun (fun (i : Fin d) (ω : Ω) => fun t : ℝ≥0 => B t ω i) P

/-- The natural filtration of the process, on the measurable space generated by its full path. -/
noncomputable def brownianFiltration {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) :
    Filtration ℝ≥0 (MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance) := by
  letI : MeasurableSpace Ω :=
    MeasurableSpace.comap (fun ω => fun t => B t ω) inferInstance
  have hp : Measurable (fun ω => fun t => B t ω) := measurable_iff_comap_le.mpr le_rfl
  exact Filtration.natural B fun t => ((measurable_pi_apply t).comp hp).stronglyMeasurable

/-- A finite stopping time of the motion's natural filtration. -/
def IsBrownianStopping {Ω : Type*} {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (τ : Ω → ℝ≥0) : Prop :=
  IsStoppingTime (brownianFiltration B) fun ω => (τ ω : ℝ≥0∞)

/-- `𝒟_h(t,x) = sup_{τ ≤ t} E_x^{BM}[-h(t-τ, B_τ)]`. -/
noncomputable def brownianDiscount {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (P : Measure Ω) (h : ℝ → Space d → ℝ) (t : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ τ : Ω → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ t) ∧
    a = ∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P}

/-- `𝒰_h(t,x) = h(t,x) + 𝒟_h(t,x)`. -/
noncomputable def brownianValue {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (P : Measure Ω) (h : ℝ → Space d → ℝ)
    (t : ℝ) (x : Space d) : ℝ :=
  h t x + brownianDiscount B P h t

/-- The payoffs attainable in the cube-killed discount `𝒟_{h,□}(T,u)`: the payoffs of the
stopping times bounded by `T` which have not left the cube of half-width `L` about `u`
strictly before they stop. -/
def cubeStoppingPayoffs {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}
    (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h : ℝ → Space d → ℝ)
    (T L : ℝ) (u : Space d) : Set ℝ :=
  {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ T) ∧
    (∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ∀ i, |B s ω i - u i| ≤ L) ∧
    a = ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P}

/-- `𝒟_{h,□}(T,u)`, the discount of the value killed on exiting the cube of half-width `L`
about `u`. -/
noncomputable def brownianDiscountCube {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}
    (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L : ℝ) (u : Space d) : ℝ :=
  sSup (cubeStoppingPayoffs B P h T L u)

/-- The multilinear interpolation from the mesh `R^{-1}ℤ^d` of the lattice field
`f`: at `z` it is the multi-affine combination of the values of `f` at the `2^d`
lattice corners of the cell containing `Rz`, with weights the products of the
coordinatewise fractional parts. -/
noncomputable def multilinearInterp {d : ℕ} (R : ℝ) (f : Site d → ℝ) (z : Space d) : ℝ :=
  ∑ ε : Fin d → Bool,
    (∏ i : Fin d, if ε i then Int.fract (R * z i) else 1 - Int.fract (R * z i)) *
      f fun i => ⌊R * z i⌋ + if ε i then 1 else 0

/-- The diffusively rescaled odometer fluctuation of Theorem 1.3(iii)(c)-(d),
paired with a test function, where `P` supplies the mean `E u_t(0)`. -/
noncomputable def diffusiveFluctuation {d : ℕ} (P : MeasureTheory.Measure (Site d → ℝ))
    (T R : ℝ) (σ : Site d → ℝ) (φ : Space d → ℝ) : ℝ :=
  R ^ (((d : ℝ) - 4) / 2) *
    latticePairing R
      (fun x => odometer σ ⌊T * R ^ 2⌋₊ x - meanOdometer P ⌊T * R ^ 2⌋₊) φ

end Continuum

open MeasureTheory in
/-- The covariance of `𝒢_4^ω`, the `ω`-representative of the four-dimensional
continuum membrane model (`Sandpile/Continuum/Membrane.lean`). -/
noncomputable def omegaMembraneCov4 (D : Set (Continuum.Space 4))
    (w : Continuum.Space 4 → ℝ) (ν2 : ℝ)
    (φ ψ : Continuum.Space 4 → ℝ) : ℝ :=
  Continuum.omegaRep D w
    (fun χ => Continuum.omegaRep D w
      (Continuum.membraneCov4 ν2 χ) ψ) φ

/-! ## 4. Planar crossings, the `∗`-lattice and continuum planar fields

Copied from `Sandpile/Support/PlanarLaw.lean`, `PlaneRectangle.lean`,
`CrossingDefinitions.lean`, `StarCrossings.lean`, `ExteriorBoundary.lean`,
`CrossField.lean` and `ContinuumPlanar.lean`, and from
`Sandpile/Frozen/DGT4LevelShiftDecoupling.lean` (the `∗`-lattice). -/

section Planar

open MeasureTheory ProbabilityTheory

/-- Translation of a planar field. -/
def planarFieldShift (v : Site 2) (F : Site 2 → ℝ) (z : Site 2) : ℝ := F (z + v)

/-- Interchange of the two coordinates of a planar field. -/
def planarFieldTranspose (F : Site 2 → ℝ) (z : Site 2) : ℝ := F ![z 1, z 0]

/-- Reflection of the first coordinate of a planar field. -/
def planarFieldReflect (F : Site 2 → ℝ) (z : Site 2) : ℝ := F ![-z 0, z 1]

/-- The law is invariant under translations, the interchange of the coordinates
and the reflection. -/
def IsSymmetricPlanarLaw (μ : Measure (Site 2 → ℝ)) : Prop :=
  (∀ v : Site 2, MeasurePreserving (planarFieldShift v) μ μ) ∧
    MeasurePreserving planarFieldTranspose μ μ ∧ MeasurePreserving planarFieldReflect μ μ

/-- The law is positively associated on increasing events. -/
def IsAssociatedPlanarLaw (μ : Measure (Site 2 → ℝ)) : Prop :=
  ∀ A B : Set (Site 2 → ℝ), IsUpperSet A → IsUpperSet B → MeasurableSet A → MeasurableSet B →
    μ.real A * μ.real B ≤ μ.real (A ∩ B)

/-- The rectangle `[0,w] × [0,h]` of `ℤ²`. -/
noncomputable def planeRectangle (w h : ℕ) : Finset (Site 2) :=
  Fintype.piFinset (fun i => Finset.Icc (0 : ℤ) (![(w : ℤ), (h : ℤ)] i))

/-- A simple path in `Q` from the left to the right (`sandpile.tex:3448-3450`):
a nonempty list of sites of `Q`, without repetitions, consecutive entries
adjacent in `ℤ²`, the first entry on the left side of `Q` and the last entry on
its right side. -/
def IsCrossingPath (Q : Finset (Site 2)) (Γ : List Q) : Prop :=
  Γ ≠ [] ∧ Γ.Nodup ∧
    List.IsChain (fun z w : Q => (lattice 2).Adj (z : Site 2) (w : Site 2)) Γ ∧
    (∀ z ∈ Γ.head?, ∀ w ∈ Q, (z : Site 2) 0 ≤ w 0) ∧
    (∀ z ∈ Γ.getLast?, ∀ w ∈ Q, w 0 ≤ (z : Site 2) 0)

/-- The crossing value `L_Q(F) = max_Γ min_{z∈Γ} F_z` of
`sandpile.tex:3444-3450`. -/
noncomputable def crossingValue (Q : Finset (Site 2)) (F : Q → ℝ) : ℝ :=
  sSup {a : ℝ | ∃ Γ : List Q, IsCrossingPath Q Γ ∧ a = sInf (F '' {z : Q | z ∈ Γ})}

/-- The fields whose crossing value of the `w × h` rectangle is at least `level`. -/
def planarCrossingEvent (w h : ℕ) (level : ℝ) : Set (Site 2 → ℝ) :=
  {F | level ≤ crossingValue (planeRectangle w h) (fun z => F z)}

/-- The probability of an event, as a point of `[0, 1]`. -/
def probabilityInUnitInterval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) : Set.Icc (0 : ℝ) 1 :=
  ⟨μ.real A, measureReal_nonneg, measureReal_le_one⟩

/-- The `∗`-lattice of `sandpile.tex:6368-6369`: "A set is $\ast$-connected if
it is connected by steps that change each coordinate by at most one." -/
def starLattice (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := x ≠ y ∧ ∀ i, (x i - y i).natAbs ≤ 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => by have := h.2 i; omega⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The `∗`-lattice, under the name the cited result uses. -/
abbrev starLatticeGraph (d : ℕ) : SimpleGraph (Site d) :=
  starLattice d

/-- Exterior nearest-neighbor boundary, with accessibility expressed by a simple infinite path. -/
def exteriorVertexBoundary {d : ℕ} (D : Set (Site d)) : Set (Site d) :=
  {z | z ∉ D ∧ (∃ y ∈ D, (lattice d).Adj y z) ∧
    ∃ p : ℕ → Site d, Function.Injective p ∧ p 0 = z ∧
      ∀ n, p n ∉ D ∧ (lattice d).Adj (p n) (p (n + 1))}

namespace Continuum

/-- A symmetry of the square lattice of the plane: a permutation of the two
coordinates, a sign on each coordinate, and a translation. -/
structure PlaneSymmetry where
  /-- The permutation of the two coordinates. -/
  perm : Equiv.Perm (Fin 2)
  /-- The sign attached to each coordinate. -/
  sign : Fin 2 → ℝ
  /-- Each sign is `1` or `-1`. -/
  sign_eq : ∀ k, sign k = 1 ∨ sign k = -1
  /-- The translation part. -/
  shift : Fin 2 → ℝ

/-- The plane map of a symmetry. -/
noncomputable def PlaneSymmetry.toFun (T : PlaneSymmetry) (u : Space 2) : Space 2 :=
  WithLp.toLp 2 (fun k => T.sign k * u (T.perm k) + T.shift k)

/-- The law of the field on the space of planar functions, with its product
σ-algebra. -/
noncomputable def fieldLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Space 2 → Ω → ℝ) : Measure (Space 2 → ℝ) :=
  P.map (fun ω u => X u ω)

/-- The field is stationary, sign-symmetric and invariant in law under the
symmetries of the square lattice of the plane (`sandpile.tex:2103-2104`). -/
def IsSymmetricField {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Space 2 → Ω → ℝ) : Prop :=
  ∀ (T : PlaneSymmetry) (ε : ℝ), (ε = 1 ∨ ε = -1) →
    fieldLaw P (fun u ω => ε * X (T.toFun u) ω) = fieldLaw P X

/-- Positive association of the finite-dimensional distributions of the field,
in the form Pitt's Gaussian FKG theorem supplies (`sandpile.tex:2104`). -/
def IsAssociatedField {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Space 2 → Ω → ℝ) : Prop :=
  ∀ (k : ℕ) (q : Fin k → Space 2) (f g : (Fin k → ℝ) → ℝ),
    Monotone f → Monotone g → Measurable f → Measurable g →
    (∃ M : ℝ, ∀ x, |f x| ≤ M) → (∃ M : ℝ, ∀ x, |g x| ≤ M) →
    (∫ ω, f (fun i => X (q i) ω) ∂P) * (∫ ω, g (fun i => X (q i) ω) ∂P)
      ≤ ∫ ω, f (fun i => X (q i) ω) * g (fun i => X (q i) ω) ∂P

end Continuum

namespace FixedScaleCrossings

/-- The identification of `sandpile.tex:2081`: `u ∈ ℝ²` is read as `(u,0)` in
`ℝ^3`.  For `d = 2` this is the identity. -/
def planePoint {d : ℕ} (u : Continuum.Space 2) : Continuum.Space d :=
  WithLp.toLp 2 (fun i : Fin d => if h : (i : ℕ) < 2 then u ⟨(i : ℕ), h⟩ else 0)

/-- The Green function of the ball of radius `s` about `u`, in dimension two and in
dimension three (`sandpile.tex:2076-2088`). -/
noncomputable def ballKernel (d : ℕ) (s : ℝ) (u : Continuum.Space 2)
    (z : Continuum.Space d) : ℝ :=
  if ‖(planePoint u : Continuum.Space d) - z‖ < s then
    (if d = 2 then
      (1 / (2 * Real.pi)) * Real.log (s / ‖(planePoint u : Continuum.Space d) - z‖)
    else
      (1 / (4 * Real.pi)) *
        (1 / ‖(planePoint u : Continuum.Space d) - z‖ - 1 / s))
  else 0

/-- The axis-parallel rectangle with corners `a` and `b`. -/
def rectSet (a b : Fin 2 → ℝ) : Set (Continuum.Space 2) :=
  {p | ∀ i : Fin 2, a i ≤ p i ∧ p i ≤ b i}

/-- `S` crosses the rectangle with corners `a`, `b` in the coordinate direction
`i`, in the sense of `sandpile.tex:2112-2118`: the set contains a compact
connected subset of the rectangle joining the two opposite sides. -/
def Crosses (a b : Fin 2 → ℝ) (i : Fin 2) (S : Set (Continuum.Space 2)) : Prop :=
  ∃ Γ : Set (Continuum.Space 2), Γ ⊆ S ∩ rectSet a b ∧ IsCompact Γ ∧ IsConnected Γ ∧
    (∃ p ∈ Γ, p i = a i) ∧ (∃ q ∈ Γ, q i = b i)

end FixedScaleCrossings

end Planar

/-! ## 5. The results the paper cites without proof

Each is a proposition, taken as an explicit hypothesis by the theorems that use it; none is
proved in the challenges.  Copied, with the auxiliary definitions they name, from
`Sandpile/External/`. -/

namespace External

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace BallGreen

/-- The Euclidean norm `|u|` of a site of `ℤ⁴`. -/
noncomputable def latticeNorm (u : Site 4) : ℝ :=
  Real.sqrt (∑ i : Fin 4, ((u i : ℤ) : ℝ) ^ 2)

/-- The box `Q(0,r)` of `ℤ⁴`. -/
def box (r : ℕ) : Set (Site 4) :=
  {y | ∀ i : Fin 4, (y i).natAbs ≤ r}

/-- The cutoff of `eq:d4ball-far-cube`: `φ` is `[0,1]`-valued and `2`-Lipschitz on
`[0,∞)`, zero on `[0,1]` and one on `[2,∞)`. -/
def IsCutoff (φ : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 0 ≤ s → φ s ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |φ s - φ t| ≤ 2 * |s - t|) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 → φ s = 0) ∧
    (∀ s : ℝ, 2 ≤ s → φ s = 1)

/-- The cut-off ball-killed Green field `h(u) = g^{Q(0,r)}(0,u) φ(|u|/L)`. -/
noncomputable def cutField (r : ℕ) (L : ℕ) (φ : ℝ → ℝ) (u : Site 4) : ℝ :=
  killedGreen (box r) 0 u * φ (latticeNorm u / (L : ℝ))

/-- The finite-time tail `q_{r,A}(u) = g^{Q(0,r)}(0,u) - g_{⌊Ar²⌋}^{Q(0,r)}(0,u)`. -/
noncomputable def timeTail (r : ℕ) (A : ℝ) (u : Site 4) : ℝ :=
  killedGreen (box r) 0 u -
    killedGreenTime (box r) ⌊A * (r : ℝ) ^ 2⌋₊ 0 u

end BallGreen

/-- The dimension-four ball-killed Green estimates of `ssec:green-estimates`
(Lawler and Limic, Theorem 4.3.1 and Chapter 6).  Assumed. -/
def BallGreenBounds : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
    (∀ u : Site 4,
        0 ≤ killedGreen (BallGreen.box r) 0 u ∧
          killedGreen (BallGreen.box r) 0 u ≤
            green 4 0 u ∧
          green 4 0 u ≤
            C / (1 + BallGreen.latticeNorm u) ^ 2) ∧
    (∑' u : Site 4,
        killedGreen (BallGreen.box r) 0 u ^ 2) ≤
      C * Real.log (r : ℝ) ∧
    (∀ L : ℕ, 2 ≤ L →
        (∑' u : {u : Site 4 //
              BallGreen.latticeNorm u ≤ 2 * (L : ℝ)},
            killedGreen (BallGreen.box r) 0
              (u : Site 4) ^ 2) ≤
          C * Real.log (2 * (L : ℝ) + 2)) ∧
    (∀ R : ℕ, 2 ≤ R → ∀ i : Fin 4,
        (∑' u : {u : Site 4 //
              (R : ℝ) ≤ BallGreen.latticeNorm u ∧
                BallGreen.latticeNorm u ≤ 2 * (R : ℝ)},
            (killedGreen (BallGreen.box r) 0
                ((u : Site 4) + unit i) -
              killedGreen (BallGreen.box r) 0
                (u : Site 4)) ^ 2) ≤ C / (R : ℝ) ^ 2) ∧
    (∀ L : ℕ, 2 ≤ L → ∀ φ : ℝ → ℝ, BallGreen.IsCutoff φ →
        (∀ u : Site 4,
            |BallGreen.cutField r L φ u| ≤ C / (L : ℝ) ^ 2) ∧
          (∑' u : Site 4,
              BallGreen.cutField r L φ u ^ 3) ≤ C / (L : ℝ) ^ 2 ∧
          ∀ M : ℝ, 1 ≤ M → ∀ w : Site 4,
            BallGreen.latticeNorm w ≤ M * (L : ℝ) →
              (∑' u : Site 4,
                  (BallGreen.cutField r L φ u -
                    BallGreen.cutField r L φ (u - w)) ^ 2) ≤
                C * (1 + M) ^ 4) ∧
    (∀ A : ℝ, 1 ≤ A →
        (∀ u : Site 4,
            |BallGreen.timeTail r A u| ≤
              C / (r : ℝ) ^ 2 * Real.exp (-c * A)) ∧
          (∑' u : Site 4,
              BallGreen.timeTail r A u ^ 2) ≤
            C * Real.exp (-c * A))

/-- The Euclidean norm `|z|` of a lattice site. -/
noncomputable def latticeNorm {d : ℕ} (z : Site d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ((z i : ℤ) : ℝ) ^ 2)

/-- The time tail `∑_{j ≥ m} p_j(0,y)`, as a sum over the `j` of `ℕ` with `m ≤ j`. -/
noncomputable def tailKernel (d : ℕ) (m : ℕ) (y : Site d) : ℝ :=
  ∑' j : {j : ℕ // m ≤ j}, heatKernel d (j : ℕ) 0 y

/-- The `d ≥ 5` Green-function estimates of `ssec:green-estimates` (Lawler and Limic,
Theorem 4.3.1, and Lawler, Chapter 3).  Assumed. -/
def GreenBoundsHigh : Prop :=
  ∀ d : ℕ, 5 ≤ d →
    (∃ C : ℝ, 0 < C ∧
        ∀ r : ℕ, 1 ≤ r →
          (Summable fun z : {z : Site d // (r : ℝ) ≤ latticeNorm z} =>
              green d 0 (z : Site d) ^ 2) ∧
            (∑' z : {z : Site d // (r : ℝ) ≤ latticeNorm z},
                green d 0 (z : Site d) ^ 2) ≤
              C * (r : ℝ) ^ (4 - (d : ℝ)) ∧
            ∀ z : Site d, (r : ℝ) ≤ latticeNorm z →
              green d 0 z ≤ C * (r : ℝ) ^ (2 - (d : ℝ))) ∧
    (Summable fun z : Site d => green d 0 z ^ 2) ∧
    (∃ C : ℝ, 0 < C ∧
        ∀ m : ℕ, 1 ≤ m →
          (∀ y : Site d,
              (Summable fun j : {j : ℕ // m ≤ j} =>
                heatKernel d (j : ℕ) 0 y) ∧
              tailKernel d m y ≤ C * (m : ℝ) ^ ((2 - (d : ℝ)) / 2)) ∧
            (Summable fun y : Site d => tailKernel d m y ^ 2) ∧
            (∑' y : Site d, tailKernel d m y ^ 2) ≤
              C * (m : ℝ) ^ ((4 - (d : ℝ)) / 2)) ∧
    (∃ C : ℝ, 0 < C ∧
        ∀ x y : Site d,
          (Summable fun z : Site d => green d x z * green d y z) ∧
            (∑' z : Site d, green d x z * green d y z) ≤
              C * (1 + latticeNorm (x - y)) ^ (4 - (d : ℝ))) ∧
    (∃ C : ℝ, 0 < C ∧
        ∀ x y : Site d,
          (Summable fun p : Site d × Site d =>
              green d x p.1 * green d p.1 p.2 ^ 2 * green d y p.2) ∧
            (∑' p : Site d × Site d,
                green d x p.1 * green d p.1 p.2 ^ 2 *
                  green d y p.2) ≤
              C * (1 + latticeNorm (x - y)) ^ (4 - (d : ℝ)))

namespace Variance

/-- The rate on the right of `eq:Qt-table`: `t^{3/2}`, `t`, `t^{1/2}`, `log t` and `1` in
dimensions one, two, three, four and five or more. -/
noncomputable def varianceRate (d : ℕ) (t : ℕ) : ℝ :=
  if d = 1 then (t : ℝ) ^ ((3 : ℝ) / 2)
  else if d = 2 then (t : ℝ)
  else if d = 3 then (t : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 4 then Real.log (t : ℝ)
  else 1

/-- The rate on the right of `eq:corr-bound`, with the constant stripped off. -/
noncomputable def corrRate (d : ℕ) (m n : ℕ) : ℝ :=
  if d = 2 then (1 + Real.log ((n : ℝ) / (m : ℝ))) * Real.sqrt ((m : ℝ) / (n : ℝ))
  else if d = 4 then Real.sqrt ((1 + Real.log (m : ℝ)) / (1 + Real.log (n : ℝ)))
  else ((m : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4)

/-- The time window `∑_{k=m}^{n-1} p_k(x,z)`. -/
noncomputable def windowKernel (m n : ℕ) (x z : Site 4) : ℝ :=
  ∑ k ∈ Finset.Ico m n, heatKernel 4 k x z

end Variance

/-- The finite-time variance scale `eq:Qt-table`, the membrane correlation bound
`eq:corr-bound`, and the dimension-four window and tail bounds of
`ssec:green-estimates`, in their Green-kernel form.  Assumed. -/
def VarianceScale : Prop :=
  (∀ d : ℕ, 1 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ t : ℕ, 2 ≤ t →
          c * Variance.varianceRate d t ≤
              ∑' y : Site d, greenTime d t 0 y ^ 2 ∧
            (∑' y : Site d, greenTime d t 0 y ^ 2) ≤
              C * Variance.varianceRate d t) ∧
  (∀ d : ℕ, 1 ≤ d → d ≤ 4 →
      ∃ C : ℝ, 0 < C ∧
        ∀ m n : ℕ, 1 ≤ m → m ≤ n →
          (∑' x : Site d,
              greenTime d m 0 x * greenTime d n 0 x) ≤
            C * Variance.corrRate d m n *
              Real.sqrt (∑' x : Site d, greenTime d m 0 x ^ 2) *
              Real.sqrt (∑' x : Site d, greenTime d n 0 x ^ 2)) ∧
  (∃ C : ℝ, 0 < C ∧
      (∀ m n : ℕ, 1 ≤ m → m < n → ∀ x : Site 4,
          (∑' z : Site 4,
              Variance.windowKernel m n x z ^ 2) ≤
            C * (1 + Real.log (((n : ℝ) + 2) / ((m : ℝ) + 2))) ∧
          ∀ z : Site 4,
            Variance.windowKernel m n x z ≤ C / (m : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → ∀ x : Site 4,
          (∑' z : Site 4, greenTime 4 n x z ^ 2) ≤
            C * Real.log ((n : ℝ) + 2) ∧
          ∀ z : Site 4, greenTime 4 n x z ≤ C))

/-- The universal RSW comparison for symmetric, positively associated planar
site percolation, expressed through real field superlevel sets (Köhler-Schindler and
Tassion, Theorem 1 and Comment 1).  Assumed. -/
def PlanarRSW : Prop :=
  ∀ ρ : ℕ, 1 ≤ ρ → ∃ ψ : Set.Icc (0 : ℝ) 1 ≃o Set.Icc (0 : ℝ) 1,
    ∀ μ : Measure (Site 2 → ℝ), ∀ [IsProbabilityMeasure μ],
      IsSymmetricPlanarLaw μ → IsAssociatedPlanarLaw μ →
      ∀ n : ℕ, 1 ≤ n → ∀ level : ℝ,
        (ψ (probabilityInUnitInterval μ
          (planarCrossingEvent (2 * n) (2 * ρ * n) level)) : ℝ) ≤
        μ.real (planarCrossingEvent (2 * ρ * n) (2 * n) level)

/-- The Euclidean distance `|x - y|` between lattice sites. -/
noncomputable def latticeDist {d : ℕ} (x y : Site d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2)

/-- `x` and `w` have the same parity: the sum of the coordinates of `x - w` is even. -/
def SameParity {d : ℕ} (x w : Site d) : Prop :=
  Even (∑ i : Fin d, (x i - w i))

/-- The Gaussian upper bound, the total-variation gradient bound and the
maximal-displacement bound for the heat kernel (`ssec:green-estimates`; Lawler and Limic,
Propositions 2.4.1 and 2.4.4, with Hoeffding's inequality).  Assumed. -/
def HeatKernelBounds : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x y : Site d,
          heatKernel d n x y ≤
            C * (n : ℝ) ^ (-(d : ℝ) / 2) *
              Real.exp (-c * latticeDist x y ^ 2 / (n : ℝ))) ∧
    (∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, 1 ≤ n → ∀ x w : Site d, SameParity x w →
          ∑' y : Site d, |heatKernel d n x y - heatKernel d n w y| ≤
            C * latticeDist x w * (n : ℝ) ^ (-(1 : ℝ) / 2)) ∧
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (n : ℕ) (R : ℝ), 1 ≤ n → 1 ≤ R → ∀ x : Site d,
          walkLaw d x
              {X : ℕ → Site d |
                ∃ k ≤ n, R ≤ latticeDist (X k) x} ≤
            ENNReal.ofReal (C * Real.exp (-c * R ^ 2 / (n : ℝ))))

/-- Domination of stationary finite-range dependent planar site processes by
supercritical Bernoulli percolation (Liggett, Schonmann and Stacey, Corollary 1.4).
Assumed. -/
def LSSDomination : Prop :=
  ∀ k : ℕ,
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : Site 2 → Ω → Bool),
      (∀ z : Site 2, Measurable (X z)) →
      (∀ w : Site 2,
        MeasureTheory.Measure.map (fun ω z => X (z + w) ω) P =
          MeasureTheory.Measure.map (fun ω z => X z ω) P) →
      (∀ S T : Set (Site 2), S.Finite → T.Finite →
        (∀ s ∈ S, ∀ t ∈ T, (k : ℝ) < latticeDist s t) →
        ProbabilityTheory.Indep
          (MeasurableSpace.generateFrom
            (S.image fun s => {ω : Ω | X s ω = true}))
          (MeasurableSpace.generateFrom
            (T.image fun t => {ω : Ω | X t ω = true})) P) →
      (∀ z : Site 2, 1 - δ ≤ (P {ω : Ω | X z ω = true}).toReal) →
      ∀ᵐ ω ∂P, HasInfiniteComponent {z : Site 2 | X z ω}

/-- Timár's exterior-boundary connectivity theorem on the lattice (Timár, Theorem 3).
Assumed. -/
def ExteriorBoundaryConnected : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ D : Set (Site d), D.Finite →
    ((starLatticeGraph d).induce D).Connected →
    ((starLatticeGraph d).induce (exteriorVertexBoundary D)).Connected

/-- The universal RSW comparison for symmetric, positively associated continuous
planar fields, expressed through superlevel-set crossings (the continuum form of
Köhler-Schindler and Tassion, Theorem 1).  Assumed. -/
def ContinuumRSW : Prop :=
  ∀ ρ : ℝ, 1 ≤ ρ → ∃ ψ : Set.Icc (0 : ℝ) 1 ≃o Set.Icc (0 : ℝ) 1,
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Continuum.Space 2 → Ω → ℝ),
      (∀ u, Measurable (X u)) →
      (∀ᵐ ω ∂P, Continuous fun u => X u ω) →
      Continuum.IsSymmetricField P X →
      Continuum.IsAssociatedField P X →
      ∀ R : ℝ, 1 ≤ R → ∀ level : ℝ,
        (ψ (probabilityInUnitInterval P
            {ω | FixedScaleCrossings.Crosses ![0, 0] ![(2 * R), (2 * ρ * R)] 0
              {u | level ≤ X u ω}}) : ℝ) ≤
          P.real {ω |
            FixedScaleCrossings.Crosses ![0, 0] ![(2 * ρ * R), (2 * R)] 0
              {u | level ≤ X u ω}}

/-- Pitt's Gaussian FKG theorem: a centred Gaussian planar field with nonnegative
covariances is positively associated (Pitt).  Assumed. -/
def PittGaussianFKG : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Continuum.Space 2 → Ω → ℝ),
    ProbabilityTheory.IsGaussianProcess X P →
    (∀ u, Measurable (X u)) →
    (∀ u, Integrable (X u) P ∧ ∫ ω, X u ω ∂P = 0) →
    (∀ u v, Integrable (fun ω => X u ω * X v ω) P ∧ 0 ≤ ∫ ω, X u ω * X v ω ∂P) →
    Continuum.IsAssociatedField P X

/-- The Green function of a Euclidean ball, in occupation-density form (Mörters and Peres,
*Brownian Motion*, Chapter 3).  Assumed. -/
def BallOccupationDensity : Prop :=
  ∀ (d : ℕ), d = 2 ∨ d = 3 → ∀ (s : ℝ), 0 < s →
  ∀ (u : Continuum.Space 2)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Continuum.Space d),
    Continuum.IsBrownian d (FixedScaleCrossings.planePoint (d := d) u) B P →
    (∀ ω, Continuous fun t => B t ω) → (∀ t, StronglyMeasurable (B t)) →
  ∀ φ : Continuum.Space d → ℝ, Measurable φ → (∃ M, ∀ z, |φ z| ≤ M) →
    Integrable (fun ω =>
      ∫ r in (0:ℝ)..(exitTime B (FixedScaleCrossings.planePoint (d := d) u) s ω).toReal,
        φ (B r.toNNReal ω)) P ∧
    (∫ ω, (∫ r in (0:ℝ)..(exitTime B (FixedScaleCrossings.planePoint (d := d) u) s ω).toReal,
        φ (B r.toNNReal ω)) ∂P)
      = 2 * (d : ℝ) * ∫ z, φ z * FixedScaleCrossings.ballKernel d s u z

namespace Lclt

/-- The Euclidean distance `|x - y|` between lattice sites. -/
noncomputable def latticeDist {d : ℕ} (x y : Site d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2)

/-- The lattice site `x` scaled by `R^{-1}`, as a point of `ℝ^d`. -/
noncomputable def scaledSite {d : ℕ} (R : ℝ) (x : Site d) :
    Continuum.Space d :=
  WithLp.toLp 2 (fun i : Fin d => ((x i : ℤ) : ℝ) / R)

end Lclt

/-- The local central limit theorem in the parity form `eq:lclt-parity` (Lawler and
Limic, Theorem 2.1.3).  Assumed. -/
def LocalCLT : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ δ T C₀ : ℝ, 0 < δ → δ < T →
      ∀ ε : ℝ, 0 < ε →
        ∃ R₀ : ℝ, 0 < R₀ ∧
          ∀ R : ℝ, R₀ ≤ R →
            ∀ (ℓ : ℕ) (x y : Site d),
              δ * R ^ 2 ≤ (ℓ : ℝ) → (ℓ : ℝ) ≤ T * R ^ 2 →
                Lclt.latticeDist x y ≤ C₀ * R →
                  0 < heatKernel d ℓ x y →
                    R ^ d *
                        |heatKernel d ℓ x y -
                          2 / R ^ d *
                            Continuum.heatKernelBM d ((ℓ : ℝ) / R ^ 2)
                              (Lclt.scaledSite R x)
                              (Lclt.scaledSite R y)| ≤ ε

/-- Stability of cube-killed optimal-stopping values under uniform convergence of
bounded rewards, with the invariance principle for the killed stopped walk
(Coquet and Toldo, Theorem 3 and Corollary 4).  Assumed. -/
def CubeStoppingStability : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : Continuum.Space d → ℝ≥0 → ΩB → Continuum.Space d),
      (∀ y : Continuum.Space d, Continuum.IsBrownian d y (B y) PB) →
    ∀ T₀ T₁ : ℝ, 0 < T₀ → T₀ ≤ T₁ →
    ∀ K : Set (Continuum.Space d), IsCompact K →
    ∀ G : ℝ → Continuum.Space d → ℝ,
      Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2) →
    ∀ G' : ℝ → ℝ → Continuum.Space d → ℝ,
    ∀ M : ℝ,
      (∀ (s : ℝ) (y : Continuum.Space d), |G s y| ≤ M) →
      (∀ (R s : ℝ) (y : Continuum.Space d), |G' R s y| ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, R₁ ≤ R →
        ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ y : Continuum.Space d,
          |G' R s y - G s y| ≤ ε) →
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
          |killedStoppingSup (supBox (fun i => ⌊R * x i⌋) R)
                ⌊R ^ 2 * T⌋₊ (fun i => ⌊R * x i⌋)
                (fun (k : ℕ) (X : ℕ → Site d) =>
                  G' R (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                    (Lclt.scaledSite R (X k))) -
              Continuum.brownianDiscountCube (B x) PB (fun s y => -G s y) T 1 x| ≤ ε

/-- Stability of optimal-stopping values under uniform convergence of bounded
rewards, with the invariance principle for the stopped walk (Coquet and Toldo,
Theorem 3 and Corollary 4).  Assumed. -/
def ContinuumStoppingStability : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : Continuum.Space d → ℝ≥0 → ΩB → Continuum.Space d),
      (∀ y : Continuum.Space d, Continuum.IsBrownian d y (B y) PB) →
    ∀ T₀ T₁ : ℝ, 0 < T₀ → T₀ ≤ T₁ →
    ∀ K : Set (Continuum.Space d), IsCompact K →
    ∀ G : ℝ → Continuum.Space d → ℝ,
      Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2) →
    ∀ G' : ℝ → ℝ → Continuum.Space d → ℝ,
    ∀ M : ℝ,
      (∀ (s : ℝ) (y : Continuum.Space d), |G s y| ≤ M) →
      (∀ (R s : ℝ) (y : Continuum.Space d), |G' R s y| ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, R₁ ≤ R →
        ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ y : Continuum.Space d,
          |G' R s y - G s y| ≤ ε) →
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
          |stoppingSup ⌊R ^ 2 * T⌋₊ (fun i => ⌊R * x i⌋)
                (fun (k : ℕ) (X : ℕ → Site d) =>
                  G' R (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                    (Lclt.scaledSite R (X k))) -
              Continuum.brownianDiscount (B x) PB (fun s y => -G s y) T| ≤ ε

namespace Snell

/-- The value `V(t,x) = sup_{0 ≤ τ ≤ t} E_x G(t - τ, B_τ)` of the finite-horizon
stopping problem with gain `G`. -/
noncomputable def snellValue {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (P : Measure Ω)
    (G : ℝ → Continuum.Space d → ℝ) (t : ℝ) : ℝ :=
  sSup {a : ℝ | ∃ τ : Ω → ℝ≥0, Continuum.IsBrownianStopping B τ ∧
    (∀ ω, (τ ω : ℝ) ≤ t) ∧ a = ∫ ω, G (t - τ ω) (B (τ ω) ω) ∂P}

/-- The payoffs attainable at horizon `t` by an admissible stopping time. -/
def attainable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Continuum.Space d) (P : Measure Ω)
    (G : ℝ → Continuum.Space d → ℝ) (t : ℝ) : Set ℝ :=
  {a : ℝ | ∃ τ : Ω → ℝ≥0, Continuum.IsBrownianStopping B τ ∧
    (∀ ω, (τ ω : ℝ) ≤ t) ∧ a = ∫ ω, G (t - τ ω) (B (τ ω) ω) ∂P}

end Snell

/-- The finite-horizon optimal-stopping theorem for Brownian motion with a continuous
gain of polynomial growth (Peskir and Shiryaev, Theorem 2.2).  Assumed. -/
def ContinuumOptimalStopping (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (d : ℕ) (T : ℝ), 0 < T →
    ∀ G : ℝ → Continuum.Space d → ℝ,
      ContinuousOn (fun p : ℝ × Continuum.Space d => G p.1 p.2)
        (Set.Icc 0 T ×ˢ (Set.univ : Set (Continuum.Space d))) →
      (∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ y : Continuum.Space d, |G t y| ≤ C * (1 + ‖y‖) ^ k) →
      ∀ x : Continuum.Space d,
        ∀ (P : Measure Ω) [IsProbabilityMeasure P]
          (B : Continuum.Space d → ℝ≥0 → Ω → Continuum.Space d),
          (∀ y : Continuum.Space d, Continuum.IsBrownian d y (B y) P) →
          ∃ M : ℝ≥0 → Ω → ℝ,
            (∀ s : ℝ≥0, Measurable (M s)) ∧
            (∀ s : ℝ≥0, (s : ℝ) ≤ T →
              M s =ᵐ[P] fun ω =>
                Snell.snellValue (B (B x s ω)) P G (T - (s : ℝ))) ∧
            (∀ (ω : Ω) (s : ℝ≥0),
              ContinuousWithinAt (fun r : ℝ≥0 => M r ω) (Set.Ici s) s) ∧
            ∃ τ : Ω → ℝ≥0,
              (∀ ω : Ω, IsLeast {s : ℝ≥0 | (s : ℝ) ≤ T ∧
                M s ω = G (T - (s : ℝ)) (B x s ω)} (τ ω)) ∧
              Continuum.IsBrownianStopping (B x) τ ∧
              IsGreatest (Snell.attainable (B x) P G T)
                (∫ ω, G (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P) ∧
              ∀ τ' : Ω → ℝ≥0, Continuum.IsBrownianStopping (B x) τ' →
                (∀ ω : Ω, (τ' ω : ℝ) ≤ T) →
                (∫ ω, G (T - (τ' ω : ℝ)) (B x (τ' ω) ω) ∂P) =
                  Snell.snellValue (B x) P G T →
                ∀ᵐ ω ∂P, τ ω ≤ τ' ω

/-- The dimension-four paired local limit estimate (Lawler and Limic, Theorem 2.1.3,
Eq. (2.8)).  Assumed. -/
def PairedLocalCLTFour : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Site 4,
    |heatKernel 4 n x y + heatKernel 4 (n + 1) x y -
      8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) *
        Real.exp (-2 * (∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) / n)| ≤
      C / (n : ℝ) ^ 3

/-- The covariance form of the tightness criterion of Furlan and Mourrat, Theorem 2.30,
with the identification of `B^{-s,loc}_{2,2}` with `H^{-s}_loc`.  Assumed. -/
def ContinuumBesovTightness (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (d : ℕ) (β K : ℝ), 0 < β → β < (d : ℝ) → ∀ s : ℝ, β / 2 < s →
    ∀ (P : Measure Ω) [IsProbabilityMeasure P]
      (u : ℝ → Ω → Continuum.Space d → ℝ),
      (∀ R : ℝ, 1 ≤ R → ∀ ω : Ω,
        Measurable (fun y => u R ω y) ∧
          ∀ φ : Continuum.Space d → ℝ,
            Continuum.IsTestFn Set.univ φ →
              Integrable (fun y => u R ω y * φ y)) →
      (∀ R : ℝ, 1 ≤ R → ∀ y : Continuum.Space d,
        MemLp (fun ω => u R ω y) 2 P) →
      (∀ R : ℝ, 1 ≤ R → ∀ y : Continuum.Space d, ∫ ω, u R ω y ∂P = 0) →
      (∀ R : ℝ, 1 ≤ R → ∀ y y' : Continuum.Space d,
        |covariance (fun ω => u R ω y) (fun ω => u R ω y') P| ≤
          K * (1 + R * ‖y - y'‖) ^ (-β)) →
      Continuum.TightInNegSobolev d s P
        (fun R ω φ => R ^ (β / 2) *
          ∫ y : Continuum.Space d, u R ω y * φ y)

/-- The `ω`-paired defect at `y` between the kernel `g_t(·,y)` of the time-truncated
membrane field and the four-dimensional potential kernel `a(·,y)`. -/
noncomputable def membraneDefect (R : ℝ) (t : ℕ)
    (D : Set (Continuum.Space 4)) (w φ : Continuum.Space 4 → ℝ)
    (y : Site 4) : ℝ :=
  Continuum.omegaRep D w
    (Continuum.latticePairing R
      (fun x => greenTime 4 t x y - potentialKernel 4 x y)) φ

/-- The scaling limit of the four-dimensional discrete membrane field
(Cipriani, Hazra and Ruszel, Theorem 2; Cipriani, Dan and Hazra, Theorem 3.11).
Assumed. -/
def MembraneScalingLimitFour : Prop :=
  ∀ ν : Measure ℝ, ∀ _hprob : IsProbabilityMeasure ν, ∫ z, z ∂ν = 0 →
    0 < evariance id ν → evariance id ν < ⊤ →
    ∀ D : Set (Continuum.Space 4), Continuum.IsDomain D →
    ∀ w : Continuum.Space 4 → ℝ, Continuum.IsAveragingDensity D w →
    ∀ s : ℝ, 0 < s → ∀ T : ℝ → ℕ,
      (∀ φ : Continuum.Space 4 → ℝ, Continuum.IsTestFn D φ →
          Tendsto (fun R : ℝ => ∑' y : Site 4,
            ENNReal.ofReal (membraneDefect R (T R) D w φ y ^ 2))
            atTop (nhds 0)) →
      (∀ φ : Continuum.Space 4 → ℝ, Continuum.IsTestFn D φ →
          TendstoInDistribution
            (fun (R : ℝ) (σ : Site 4 → ℝ) =>
              Continuum.omegaRep D w
                (Continuum.latticePairing R
                  (membrane (scenery 4 σ) (T R))) φ)
            atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
            (gaussianReal 0 (Real.toNNReal
              (omegaMembraneCov4 D w (variance id ν) φ φ)))) ∧
        (∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
          centeredMassLaw 4 ν
              {σ | M < Continuum.negSobolevNorm 4 s D
                (Continuum.omegaRep D w
                  (Continuum.latticePairing R
                    (membrane (scenery 4 σ) (T R))))} ≤
            ENNReal.ofReal ε)

/-- Gaussian concentration for a Lipschitz functional (Borell; Tsirelson, Ibragimov
and Sudakov).  Assumed. -/
def GaussianLipschitzConcentration : Prop :=
  ∀ (ι : Type) (F : (ι → ℝ) → ℝ) (L : ℝ), 0 < L →
    Measurable F → Integrable F (gaussLaw ι) →
    (∀ (ω η : ι → ℝ) (M : ℝ), HasSum (fun i => (ω i - η i) ^ 2) M →
      |F ω - F η| ≤ L * Real.sqrt M) →
    ∀ t : ℝ, 0 ≤ t →
      (gaussLaw ι) {ω | ∫ η, F η ∂(gaussLaw ι) + t ≤ F ω}
        ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * L ^ 2)))

/-- The normal comparison inequality (Li and Shao, Corollary 2.1).  Assumed. -/
def NormalComparison : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (v : ℝ≥0), 0 < v →
      ∀ S : Matrix (Fin m) (Fin m) ℝ, S.PosSemidef →
        (∀ i, S i i = (v : ℝ)) → (∀ i j, 0 ≤ S i j) →
        ∀ b : Fin m → ℝ,
          |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
                  {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal -
              ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
            C * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
              S i j / (v : ℝ) *
                Real.exp (-(b i ^ 2 + b j ^ 2) /
                  (2 * (v : ℝ) * (1 + S i j / (v : ℝ))))

/-- The number of intersections of two paths, counted with multiplicity, in `ℝ≥0∞`. -/
noncomputable def interCount {d : ℕ} (X Y : ℕ → Site d) : ℝ≥0∞ :=
  ∑' p : ℕ × ℕ, Set.indicator {q : ℕ × ℕ | X q.1 = Y q.2} (fun _ => (1 : ℝ≥0∞)) p

/-- The second intersection estimate `eq:dgt4-intersection-second-moment` for two
independent simple random walks in `d ≥ 5` (Lawler, *Intersections of Random Walks*,
Theorem 3.3.2).  Assumed. -/
def IntersectionSecondMoment : Prop :=
  ∀ d : ℕ, 5 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : Site d,
        (∫⁻ X, ∫⁻ Y, interCount X Y ^ 2
            ∂(walkLaw d y) ∂(walkLaw d x)) ≤
          ENNReal.ofReal (C * (1 + latticeNorm (x - y)) ^ (4 - (d : ℝ)))

end External

end SandpileAudit
-- VOCABULARY-END

namespace SandpileAudit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Theorem 1.3(ii)(c) (`thm:main-explosion`). -/
theorem four_sobolev
    (hHeatKernel : External.HeatKernelBounds)
    (hVarScale : External.VarianceScale)
    (hBesov : External.ContinuumBesovTightness (Site 4 → ℝ))
    (hMembrane : External.MembraneScalingLimitFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : 0 < s) :
    Continuum.TightInNegSobolev 4 s (centeredMassLaw 4 ν)
        (fun (R : ℝ) (σ : Site 4 → ℝ) =>
          Continuum.latticePairing R
            (fun x => odometer σ ⌊T * R ^ 2⌋₊ x -
              meanOdometer (centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊)) ∧
      ∀ D : Set (Continuum.Space 4), Continuum.IsDomain D →
        ∀ w : Continuum.Space 4 → ℝ, Continuum.IsAveragingDensity D w →
          ∀ α : ℝ, 2 < α →
            (∀ φ : Continuum.Space 4 → ℝ, Continuum.IsTestFn D φ →
                TendstoInDistribution
                  (fun (R : ℝ) (σ : Site 4 → ℝ) =>
                    Continuum.omegaRep D w
                      (Continuum.latticePairing R
                        (fun x => odometer σ ⌊R ^ α⌋₊ x -
                          meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
                  atTop (id : ℝ → ℝ) (fun _ => centeredMassLaw 4 ν)
                  (gaussianReal 0 (Real.toNNReal
                    (Continuum.omegaRep D w
                      (fun φ' => Continuum.omegaRep D w
                        (Continuum.membraneCov4 (variance id ν) φ') φ) φ)))) ∧
              ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
                centeredMassLaw 4 ν
                    {σ | M < Continuum.negSobolevNorm 4 s D
                      (Continuum.omegaRep D w
                        (Continuum.latticePairing R
                          (fun x => odometer σ ⌊R ^ α⌋₊ x -
                            meanOdometer (centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
                  ENNReal.ofReal ε := by
  sorry

end SandpileAudit
