import Sandpile.Basic
import LatticeProb.Walk.LatticeGreen

/-!
# Simple random walk, its kernels, and the optimal-stopping vocabulary

Simple random walk on `ℤ^d` and the optimal-stopping vocabulary of `sandpile.tex`, Section 1
(`ssec:notation`) and Section 2 (`sec:rw-rep`).

How the paper's objects are modelled here:

- `heatKernel d k x y` is `p_k(x, y)`, defined by the averaging recursion; it needs no path
  space. `greenTime` is `g_t(x, y) = ∑_{k<t} p_k(x, y)` and `green` is `G(x, y) = ∑_k p_k(x,
  y)`. In dimensions one and two the last series diverges and the `tsum` takes its junk value
  zero; every statement that mentions `green` fixes `d ≥ 5`.
- `killedKernel D k x y` is `P_x(X_k = y, k < τ_D)`, again by a recursion: killing is the
  indicator of `D` in front of each step.
- The walk itself is a measure on path space `ℕ → Site d`: the increments are i.i.d. uniform on
  the `2d` unit vectors and `walkPath` accumulates them. This is the object the optimal-stopping
  statements need.
- A stopping time is a function of the path whose value at `k` is determined by the first `k + 1`
  positions. `stoppingSup n x F` is the supremum of `E_x F(τ, X)` over stopping times bounded by
  `n`; `F` sees the whole path, so both `sup_τ E_x ∑_{k<τ} ζ(X_k)` and `sup_τ E_x[-V_{t-τ}(X_τ)]`
  are instances. The supremum is an `sSup` over a set of reals which is nonempty (take `τ = 0`)
  and, for a fixed scenery, bounded, since only finitely many sites are reached.
-/

open MeasureTheory
open scoped ENNReal

namespace Sandpile

/-! ### The heat kernel and the Green kernels -/

/-- The `k`-step transition probability `p_k(x, y)` of simple random walk.
Reuses `LatticeProb.LocalCLT.heatKernel`, to which this is definitionally
equal (same recursion, `Site d` is `LatticeProb.Site d`). -/
noncomputable abbrev heatKernel (d : ℕ) : ℕ → Site d → Site d → ℝ :=
  LatticeProb.LocalCLT.heatKernel d

/-- The finite-time Green kernel `g_t(x, y) = ∑_{k<t} p_k(x, y)`.
Reuses `LatticeProb.greenTime`. -/
noncomputable abbrev greenTime (d : ℕ) (t : ℕ) (x y : Site d) : ℝ :=
  LatticeProb.greenTime d t x y

/-- The Green function `G(x, y) = ∑_{k≥0} p_k(x, y)`.  Transient dimensions only:
for `d ≤ 2` the series diverges and this takes the junk value zero. -/
noncomputable def green (d : ℕ) (x y : Site d) : ℝ := ∑' k : ℕ, heatKernel d k x y

/-- `P_x(X_k = y, k < τ_D)`, the transition kernel of the walk killed on
leaving `D`. -/
noncomputable def killedKernel {d : ℕ} (D : Set (Site d)) : ℕ → Site d → Site d → ℝ
  | 0 => fun x y => D.indicator (fun z => if z = y then (1 : ℝ) else 0) x
  | k + 1 => fun x y => D.indicator (fun z =>
      (∑ i : Fin d,
        (killedKernel D k (z + unit i) y + killedKernel D k (z - unit i) y)) / (2 * d)) x

/-- The killed finite-time Green kernel `g_t^D(x, y)`. -/
noncomputable def killedGreenTime {d : ℕ} (D : Set (Site d)) (t : ℕ) (x y : Site d) : ℝ :=
  ∑ k ∈ Finset.range t, killedKernel D k x y

/-- The killed Green kernel `g^D(x, y)`. -/
noncomputable def killedGreen {d : ℕ} (D : Set (Site d)) (x y : Site d) : ℝ :=
  ∑' k : ℕ, killedKernel D k x y

/-! ### The walk on path space -/

/-- The law of one increment of the walk: uniform on the `2d` unit vectors. -/
noncomputable def stepLaw (d : ℕ) : Measure (Site d) := LatticeProb.instructionLaw (0 : Site d)

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

/-- The exit time `τ_D = inf{k ≥ 0 : X_k ∉ D}`, as a value in `ℕ∞` so that a
path which never leaves `D` is not given a junk finite value. -/
noncomputable def exitTime {d : ℕ} (D : Set (Site d)) (X : ℕ → Site d) : ℕ∞ :=
  sInf {k : ℕ∞ | ∃ n : ℕ, (k : ℕ∞) = n ∧ X n ∉ D}

/-- The supremum of `E_x F(τ, X)` over stopping times `τ ≤ n`. -/
noncomputable def stoppingSup {d : ℕ} (n : ℕ) (x : Site d)
    (F : ℕ → (ℕ → Site d) → ℝ) : ℝ :=
  sSup {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
    a = ∫ X, F (τ X) X ∂(walkLaw d x)}

/-! ### The scenery and the fields built from it -/

/-- The scenery `ζ = (σ - 1) / (2d)` of `eq:mass-excess-notation`. -/
noncomputable def scenery (d : ℕ) (σ : Site d → ℝ) (x : Site d) : ℝ := (σ x - 1) / (2 * d)

/-- The averaging operator `Pf(x) = (2d)^{-1} ∑_{y ∼ x} f(y)`. -/
noncomputable def avg {d : ℕ} (f : Site d → ℝ) : Site d → ℝ := LatticeProb.walkOp f

/-- `S_n = ∑_{k<n} ζ(X_k)`, the scenery sum along the walk. -/
noncomputable def sceneryPartialSum {d : ℕ} (ζ : Site d → ℝ) (n : ℕ) (X : ℕ → Site d) : ℝ :=
  ∑ k ∈ Finset.range n, ζ (X k)

/-- `v_n(x) = sup_{τ ≤ n} E_x S_τ`, the optimal-stopping value of `thm:RW`. -/
noncomputable def stoppingValue {d : ℕ} (ζ : Site d → ℝ) (n : ℕ) (x : Site d) : ℝ :=
  stoppingSup n x (sceneryPartialSum ζ)

/-- The localized value `u_t^D(x) = sup_{τ ≤ t} E_x ∑_{k < τ ∧ τ_D} ζ(X_k)` of
`eq:localized-odometer`, and `0` off `D`. -/
noncomputable def localizedOdometer {d : ℕ} (D : Set (Site d)) (ζ : Site d → ℝ)
    (t : ℕ) (x : Site d) : ℝ :=
  D.indicator (fun z => stoppingSup t z
    (fun k X => ∑ j ∈ Finset.range k,
      Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j)) x

/-- The odometer written in the scenery: `u_{n+1}(x) = (ζ(x) + P u_n(x))₊`. -/
noncomputable def odometerOf {d : ℕ} (ζ : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (ζ x + avg (odometerOf ζ n) x)

/-- The membrane field `V_n` of `eq:membrane-recursion`: the odometer recursion
with the reflection removed. -/
noncomputable def membrane {d : ℕ} (ζ : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => ζ x + avg (membrane ζ n) x

end Sandpile
