/-
Lemma of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3923-3931`
(label `lem:d4-finite-range-lower-bound`):

  "For every $z\in\Z^4$,
   \[
     \mathcal B_{r,A_{\rm ex}r^2}(z)+Y_r(z)\leq u_{(A_{\rm ex}+1)r^2}(z)\, .
   \]
   Moreover, $\mathcal B_{r,A_{\rm ex}r^2}(z)+Y_r(z)$ is measurable with
   respect to the scenery in $Q(z,(A_{\rm loc}+3)r)$, for all large $r$."

The statement is a pathwise statement about a fixed scenery together with a
measurability statement about the map from the scenery, so no law appears.

Modelling.  The objects of the running text above the lemma
(`sandpile.tex:3861-3877`) are transcribed as `def`s:

- `frCube x L` is `Q(x,L) = {y ∈ ℤ⁴ : max_i |y_i - x_i| ≤ L}`
  (`sandpile.tex:680-682`); the radius is real, since `A_loc r` and
  `(A_loc+3)r` are.
- `frGreenFieldTime r N ζ z` is the finite-time killed Green field
  `𝓑_{r,N}(z) = ∑_{u∈ℤ⁴} g_N^{Q(0,r)}(0,u) ζ(z+u)` (`sandpile.tex:3863-3866`),
  with `g_N^D` the killed kernel `Sandpile.killedGreenTime` of
  `eq:killed-walk-notation`.  The sum is a `tsum` and no junk value is reached:
  `g_N^{Q(0,r)}(0,·)` vanishes off the finite set `Q(0,r)`, so the family is
  finitely supported.
- `frExitValue A_ex A_loc r ζ z` is
  `Y_r(z) = E_z[1_{{τ_{Q(z,r)} ≤ A_ex r²}} u_{r²}^{Q(X_{τ},A_loc r)}(X_{τ}) | ζ]`
  (`sandpile.tex:3869-3877`), an integral against `Sandpile.walkLaw 4 z`, the
  law of simple random walk started at `z`, with `u^D_t` the localized value
  `Sandpile.localizedOdometer` of `eq:localized-odometer`.  Conditioning on the
  scenery is exactly this: the scenery is a parameter and the integral is over
  the walk only.  As in `lem:localization-killing`, `exitTime` has type `ℕ∞`,
  the event `{τ ≤ A_ex r²}` is written in `ℕ∞`, and the walk is evaluated at
  `(exitTime …).toNat`; the integrand is a `Set.indicator` of that event, so on
  its complement, where `toNat` may take the junk value `0`, the value is
  multiplied by zero and never read.

`A_loc ≥ 1` is real and `A_ex ≥ 1` is a natural number, as the paper fixes
them, and both are bound before everything else, as the paper fixes them before
the lemma.  The odometer is `Sandpile.odometerOf ζ`, the odometer written in
the scenery.

Measurability with respect to the scenery in a box is measurability for the
comap sigma-algebra of the restriction map `ζ ↦ ζ|_{Q(z,(A_loc+3)r)}`, that is,
the smallest sigma-algebra making the scenery values inside that box
measurable.  "For all large `r`" is `∀ᶠ r in atTop`; the first clause carries
no largeness, matching the paper, which states it for every `z`.
-/
import Sandpile.Support.FiniteRange

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

/-- `Q(x,L) = {y ∈ ℤ⁴ : max_i |y_i - x_i| ≤ L}` (`sandpile.tex:680-682`). -/
def frCube (x : Site 4) (L : ℝ) : Set (Site 4) :=
  {y | ∀ i : Fin 4, |((y i : ℝ) - (x i : ℝ))| ≤ L}

/-- The finite-time killed Green field
`𝓑_{r,N}(z) = ∑_{u∈ℤ⁴} g_N^{Q(0,r)}(0,u) ζ(z+u)` (`sandpile.tex:3858-3861`). -/
noncomputable def frGreenFieldTime (r N : ℕ) (ζ : Site 4 → ℝ) (z : Site 4) : ℝ :=
  ∑' u : Site 4, killedGreenTime (frCube 0 (r : ℝ)) N 0 u * ζ (z + u)

/-- `Y_r(z) = E_z[1_{{τ_{Q(z,r)} ≤ A_ex r²}} u_{r²}^{Q(X_τ,A_loc r)}(X_τ) | ζ]`
(`sandpile.tex:3864-3872`). -/
noncomputable def frExitValue (Aex : ℕ) (Aloc : ℝ) (r : ℕ) (ζ : Site 4 → ℝ)
    (z : Site 4) : ℝ :=
  ∫ X, Set.indicator
      {X : ℕ → Site 4 | exitTime (frCube z (r : ℝ)) X ≤ ((Aex * r ^ 2 : ℕ) : ℕ∞)}
      (fun X => localizedOdometer
        (frCube (X (exitTime (frCube z (r : ℝ)) X).toNat) (Aloc * r)) ζ (r ^ 2)
        (X (exitTime (frCube z (r : ℝ)) X).toNat)) X
    ∂(walkLaw 4 z)

end Sandpile

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_finite_range_lower_bound
    (Aloc : ℝ) (hAloc : 1 ≤ Aloc) (Aex : ℕ) (hAex : 1 ≤ Aex) :
    (∀ (ζ : Sandpile.Site 4 → ℝ) (r : ℕ) (z : Sandpile.Site 4),
        Sandpile.frGreenFieldTime r (Aex * r ^ 2) ζ z +
            Sandpile.frExitValue Aex Aloc r ζ z ≤
          Sandpile.odometerOf ζ ((Aex + 1) * r ^ 2) z) ∧
      (∀ᶠ r : ℕ in atTop, ∀ z : Sandpile.Site 4,
        Measurable[MeasurableSpace.comap
            (fun ζ : Sandpile.Site 4 → ℝ =>
              Set.restrict (Sandpile.frCube z ((Aloc + 3) * r)) ζ) inferInstance]
          (fun ζ : Sandpile.Site 4 → ℝ =>
            Sandpile.frGreenFieldTime r (Aex * r ^ 2) ζ z +
              Sandpile.frExitValue Aex Aloc r ζ z))
-- FROZEN-STATEMENT-END
:= by
  have _horizon_pos : 0 < Aex := hAex
  have hg : ∀ (ζ : Sandpile.Site 4 → ℝ) (r N : ℕ) (z : Sandpile.Site 4),
      Sandpile.frGreenFieldTime r N ζ z =
        Sandpile.killedGreenPair (Sandpile.frCube z r) N ζ z := by
    intro ζ r N z
    have hD : {w : Sandpile.Site 4 | w + z ∈ Sandpile.frCube z r} =
        Sandpile.frCube 0 r := by
      ext w
      simp [Sandpile.frCube, Int.cast_add]
    simpa only [hD, Sandpile.frGreenFieldTime] using
      Sandpile.tsum_killedGreenTime_shift (Sandpile.frCube z r) N z ζ
  have he : ∀ (ζ : Sandpile.Site 4 → ℝ) (r : ℕ) (z : Sandpile.Site 4),
      Sandpile.frExitValue Aex Aloc r ζ z =
        ∫ X, Sandpile.localizedExitPayoff (Sandpile.frCube z r) (Aex * r ^ 2)
          (fun y => Sandpile.frCube y (Aloc * r)) (r ^ 2) ζ X ∂Sandpile.walkLaw 4 z := by
    intro ζ r z
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun X =>
      (Sandpile.localizedExitPayoff_eq_indicator (Sandpile.frCube z r) (Aex * r ^ 2)
        (fun y => Sandpile.frCube y (Aloc * r)) (r ^ 2) ζ X).symm
  constructor
  · intro ζ r z
    rw [hg, he, Nat.add_mul, one_mul]
    exact Sandpile.killedGreenPair_add_localizedExit_le (by norm_num) z
      (Sandpile.frCube z r) (Aex * r ^ 2) (r ^ 2)
      (fun y => Sandpile.frCube y (Aloc * r)) ζ
  · filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    intro z
    have hfun : (fun ζ : Sandpile.Site 4 → ℝ =>
        Sandpile.frGreenFieldTime r (Aex * r ^ 2) ζ z + Sandpile.frExitValue Aex Aloc r ζ z) =
      fun ζ => Sandpile.killedGreenPair (Sandpile.frCube z r) (Aex * r ^ 2) ζ z +
        ∫ X, Sandpile.localizedExitPayoff (Sandpile.frCube z r) (Aex * r ^ 2)
          (fun y => Sandpile.frCube y (Aloc * r)) (r ^ 2) ζ X ∂Sandpile.walkLaw 4 z := by
      funext ζ
      rw [hg, he]
    rw [hfun]
    exact Sandpile.cube_killed_continuation_measurable (by norm_num) z
      (Aex * r ^ 2) (r ^ 2) Aloc hAloc r hr
