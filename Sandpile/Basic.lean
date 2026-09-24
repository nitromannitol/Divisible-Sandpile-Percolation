/-
The divisible sandpile of Levine and Peres on `ℤ^d`, as the paper defines it
(`sandpile.tex`, Section 1): the initial mass at a site is `σ(x)`, a site with
mass above one keeps one unit and shares the excess equally with its `2d`
neighbours, and the finite-time odometer obeys

  `u_{t+1}(x) = ((σ(x) - 1)/(2d) + (1/(2d)) ∑_{y ∼ x} u_t(y))₊`,   `u_0 = 0`.

How the paper's objects are modelled here:

- Sites, the lattice and the neighbour sum come from `LatticeProb.Site`.
- The odometer takes real values.  `u_t` increases in `t`, so the odometer
  limit `u_∞` is its supremum, taken in `ℝ≥0∞` so that an exploding site has a
  value rather than a junk one.
- The toppled set is `{x : 0 < u_∞ x}`.
-/
import LatticeProb.Site
import LatticeProb.IID

open scoped ENNReal

namespace Sandpile

export LatticeProb (Site unit lattice nbrSum HasInfiniteComponent)

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
  LatticeProb.iidLaw d μ

end Sandpile
