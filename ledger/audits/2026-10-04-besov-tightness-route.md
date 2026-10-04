# Route to `Sandpile.External.ContinuumBesovTightness` (Furlan–Mourrat tightness criterion)

Status note for the discharge of `Sandpile.External.ContinuumBesovTightness`
(`~/lean/Divisible-Sandpile-Percolation/Sandpile/External/ContinuumBesovTightness.lean`, frozen).
The target is Furlan–Mourrat, *A tightness criterion for random fields, with application to the
Ising model*, AIHP 53 (2017), Theorem 2.30 at `p = q = 2`.  **It is not reachable as a single
bounded Lean proof**: the analytic core is a Riesz/Bessel-potential Fourier estimate that Mathlib
does not have, and the only in-repo precedents stop one step short of it.  This file records what is
proved, the precise route, and the exact missing lemmas with signatures.

Repository: `~/lean/Lattice-Probability`, branch `rectangle-ergodic-reduction` (not switched).
The frozen target lives in the sibling repo `~/lean/Divisible-Sandpile-Percolation`; the shared
library `LatticeProb` supplies the Sobolev vocabulary it re-exports.

## 0. The frozen target and its consumer

`Sandpile.External.ContinuumBesovTightness Ω : Prop` (frozen) is: for `0 < β < d`, `K`, `s > β/2`,
a probability space `(Ω, P)` and a field `u : ℝ → Ω → Space d → ℝ` that is mean-zero, pointwise
`MemLp 2`, and has covariance decay

```
|Cov(u R · y, u R · y')| ≤ K * (1 + R * ‖y - y'‖) ^ (-β),
```

the rescaled pairings

```
F R ω φ = R ^ (β / 2) * ∫ y, u R ω y * φ y
```

are tight in `H^{-s}_loc(ℝ^d)`, i.e. `Sandpile.Continuum.TightInNegSobolev d s P F`:

```
∀ D, IsDomain D → ∀ ε > 0, ∃ M ≠ ⊤, ∀ R ≥ 1,
  P {ω | M < negSobolevNorm d s D (F R ω)} ≤ ENNReal.ofReal ε.
```

`Space d` is `EuclideanSpace ℝ (Fin d)`, `IsTestFn D φ` is `φ ∈ C_c^∞(D)`,
`sobolevNormSq d s φ = ∫⁻ ξ, (1 + (2π‖ξ‖)²)^s ‖𝓕φ(ξ)‖²`, and
`negSobolevNorm d s D F = sSup {|F φ| : IsTestFn D φ, sobolevNormSq d s φ ≤ 1}` — definitions
re-exported by `Sandpile.Continuum.Sobolev` from `LatticeProb.Sobolev`
(`LatticeProb/Analysis/Sobolev/Defs.lean:30,34,46`).

Consumer: `Sandpile.Frozen.sobolev_tightness` (`Sandpile/Frozen/SobolevTightness.lean`) takes it
as `hBesov` and proves the lattice-to-continuum embedding step; it is cited as an explicit
hypothesis (`hBesov`) in 25 files.  `Sandpile/Support/TightWeightedMembrane.lean:360,445,487`
uses it to get `TightInNegSobolev` for the weighted membrane / odometer fluctuation fields.

## 1. Why a bounded proof is not reachable

* **Mathlib has no Besov / Littlewood–Paley / Riesz-potential content.**
  `rg -il besov` over `.lake/packages/mathlib/Mathlib` → 0 files;
  `rg -il "littlewood|paley"` → 0; `rg -in "rieszPotential|RieszPotential"` → 0.
* **Mathlib's Fourier-side Sobolev layer stops at tempered distributions.**
  `Mathlib/Analysis/Distribution/Sobolev.lean` has `TemperedDistribution.besselPotential`
  (line 71), `memSobolev_besselPotential_iff` (196), `MemSobolev.fourier_memL1` (241),
  `MemSobolev.mono` (298).  These are distribution-level multiplier identities; there is **no**
  function-valued Bessel-kernel asymptotic and **no** Fourier-to-double-integral representation of
  the covariance kernel.  Plancherel for Schwartz maps is available
  (`SchwartzMap.integral_norm_sq_fourier`, `SchwartzMap.integral_inner_fourier_fourier`,
  `MeasureTheory.Lp.inner_fourier_eq`) and is what the partial work below uses.
* **`LatticeProb` has no tightness criterion of this type.**  Its `Sobolev` directory
  (`Analysis/Sobolev/`) has the negative-Sobolev norm, its algebra, and a *tightness-transfer*
  lemma gated behind the still-open `LatticeProb.External.RellichKondrachovNegSobolev`
  (`Compact.lean`, `DualNet.lean`, `Tight.lean`, `TightTransfer.lean`).  The transfer runs the
  *opposite* way: it turns an already-tight `H^{-s₀}` family into an `H^{-s}` bound on a finite net
  of pairings, for `s₀ < s`.  The frozen criterion is the missing input that would feed it, not a
  consequence of it.  `LatticeProb` also has no `TightInNegSobolev` predicate and no `u R y`
  random-field bridge; only `Sandpile.Continuum` defines those.
* **The one genuinely hard step** is promoting the pointwise (fixed-`φ`) second-moment bound to a
  bound uniform over the whole `H^s(D)` unit ball.  This is a real Riesz/Bessel-potential estimate,
  not a lemma lookup: the covariance bound `(1 + R‖z‖)^{-β}` with `β < d` is exactly a rescaled
  Riesz kernel, and its spectral symbol is `~ R^{-β} ‖ξ‖^{β-d}`; integrating it against the
  `H^s` weight `(1+‖ξ‖²)^{-s}` converges precisely when `β > 0` at `ξ = 0` and `s > β/2` at
  `ξ = ∞`.

## 2. What is already proved and portable

A sibling worktree (`~/work/opus/luna-sand-besov`) produced
`Sandpile/External/ContinuumBesovTightnessProved.lean` (compiles clean, no `sorry`).  It does not
prove the frozen target; it proves the elementary half of the argument and isolates the analytic
gap.  The results are self-contained and can be ported to LatticeProb unchanged (they use only
`Space d`, `Bornology.IsBounded`, `MeasurableSet`, and Ball integrals):

* `aux_besov_ball_integral_bound` (line 49): for `0 < β < d`, `T ≥ 0`, `R ≥ 1`,
  ```
  R ^ β * ∫ z in Metric.ball 0 T, (1 + R * ‖z‖) ^ (-β)
    ≤ d * (volume (ball 0 1)).toReal * (T ^ (d - β) / (d - β)).
  ```
  Route: `MeasureTheory.integral_fun_norm_addHaar` (polar coordinates), then
  `(1 + Ry)^{-β} ≤ (Ry)^{-β}` and `integral_rpow`; `β < d` is used once, for convergence at `0`.
* `aux_besov_second_moment_integral` (line 165): for `0 < β < d` and `D` bounded measurable,
  `∃ C > 0, ∀ R ≥ 1, R ^ β * ∫ y in D, ∫ y' in D, (1 + R * ‖y - y'‖)^{-β} ≤ C`.
  This is the pure-calculus fact that keeps the *rescaled* second moment uniform in `R`.
* `aux_besov_cauchy_schwarz_unit_ball` / `..._sq` (lines 298, 348): the finite-index
  Cauchy–Schwarz identity `sSup{|Σ a i b i| : Σ w i a i² ≤ 1}² ≤ Σ b i²/w i`.
* `aux_besov_continuous_cauchy_schwarz_unit_ball_sq` (line 376): the Fourier-side version: if
  `F φ = Re ∫ ξ, b ξ * conj(𝓕φ ξ)` and `∫⁻ ξ (1+4π²‖ξ‖²)^{-s} ‖b ξ‖² ≤ B`, then
  `(negSobolevNorm d s D F)² ≤ B`.  This is proved with `ENNReal.lintegral_mul_le_Lp_mul_Lq`,
  Schwartz Fourier regularity, and Plancherel; it needs no basis expansion.
* `aux_besov_uniform_second_moment_from_spectral_bound` (line 575): the Tonelli assembly, taking
  the weighted spectral bound `∫⁻ ω ∫⁻ ξ (1+4π²‖ξ‖²)^{-s}‖b R ω ξ‖² ≤ C` as hypothesis and
  concluding `∫⁻ ω (negSobolevNorm d s D (F R ω))² ≤ C`, uniformly in `R`.

Together these reduce the frozen theorem to **one** missing analytic declaration (Section 3), plus
one Lean-side measurability issue (Section 4).

## 3. The precise missing lemmas

### M1a — covariance-to-spectrum (the blocker)

The covariance decay must be converted into the weighted spectral bound for the field's Fourier
multiplier `b R ω`.  The real-space covariance `c_R(z) = Cov(u R y, u R (y+z))` satisfies
`|c_R(z)| ≤ K (1 + R‖z‖)^{-β}`, i.e. `c_R` is a (positive-definite) rescaled Riesz kernel.  Its
spectral measure `μ_R = 𝓕 c_R` must satisfy, uniformly in `R ≥ 1`,

```
R ^ β * ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (-s)) ∂μ_R ≤ C.
```

The cleanest Lean-shaped sufficient form is the Bessel-kernel estimate.  Mathlib names the
multiplier but not the function-valued kernel; the needed declaration is essentially

```lean
/-- Function-valued Bessel potential kernel: the inverse Fourier transform `G` of
`ξ ↦ (1 + (2π‖ξ‖)²)^(-s)` is integrable and satisfies a uniform bound with the correct
small-`z` behaviour.  For `2 * s < d` this is `‖z‖ ^ (2 * s - d)`; for `2 * s ≥ d` it is `1`.
Both regimes are covered by the exponent `min (2 * s - d) 0` together with exponential decay. -/
theorem besselKernel_bound (d : ℕ) (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ G : Space d → ℝ,
      (∀ ξ : Space d, 𝓕 (fun z => (G z : ℂ)) ξ =
        1 / (1 + (2 * Real.pi * ‖ξ‖) ^ 2 : ℂ) ^ s) ∧
      Integrable G ∧
      ∀ z : Space d, |G z| ≤ C * (1 + ‖z‖) ^ (min (2 * s - d) 0) * Real.exp (-‖z‖)
```

With M1a in hand, the covariance bound gives the spectral bound by
`∫ (1+4π²‖ξ‖²)^{-s} μ_R(dξ) = ∫ G(z) c_R(z) dz` (Plancherel for the positive measure `μ_R`) and
`R^β ∫ G(z) (1+R‖z‖)^{-β} dz = O(1)`:

```lean
/-- The rescaled Bessel pairing of the covariance decay is uniform in `R ≥ 1`.
    `β / 2 < s` is exactly the convergence condition. -/
theorem exists_bessel_covariance_integral_le (d : ℕ) (β s : ℝ)
    (hβ : 0 < β) (hs : β / 2 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R →
      R ^ β * ∫ z : Space d, besselKernel d s z * (1 + R * ‖z‖) ^ (-β) ≤ C
```

Scaling check (why `s > β/2`), for `2 * s < d`: with `z = w/R` the pairing is
`R^{β-d} ∫ G(w/R)(1+‖w‖)^{-β} dw`; on `‖w‖ ≲ R`, `G(w/R) ≈ R^{d-2s}‖w‖^{2s-d}`, and
`R^{β-2s} ∫_{1}^{R} r^{2s-β-1} dr ≈ R^{β-2s} R^{2s-β} = O(1)`.  For `2 * s ≥ d` the near-`0`
bound `|G| ≤ C` gives `∫_{‖z‖ ≤ 1/R} G ≤ C R^{-d}` and `R^{β-d} ≤ 1` because `β < d`; the same
`∫_{1/R}^{1} r^{d-1-β}` bound applies on `1/R ≤ ‖z‖ ≤ 1`.  A sign error here is easy; the
`2s = β` boundary produces the divergent `log R`, which is why the hypothesis is strict.

Exact gap: Mathlib has `TemperedDistribution.besselPotential` but neither the function-valued
kernel `G` with its `min (2*s-d) 0` small-`z` bound nor the Plancherel identity for a positive
measure `μ_R` whose Fourier transform is only known to be *dominated* by the Riesz kernel.  There is
no `rieszPotential`/`besselKernel` declaration anywhere in Mathlib or LatticeProb.

### M1b — uniform second moment over the `H^s` unit ball

Once M1a gives `E|F R · φ|² ≤ C (1+4π²‖ξ‖²)^s`-weighted bound, the sup over the unit ball is
`E‖F R ·‖²_{H^{-s}} ≤ C`, uniformly in `R`.  This is the shape of
`aux_besov_uniform_second_moment_from_spectral_bound` above; only the spectral hypothesis is
missing.

### M1c — measurability of the norm map, and countable-sup reduction

`negSobolevNorm` is an `sSup` over the *uncountable* set of test functions.  The hypotheses of the
frozen statement give only pointwise measurability of `u R · y`, not joint measurability of
`ω ↦ negSobolevNorm d s D (F R ω)`, so the event `{ω | M < negSobolevNorm …}` is not a priori
measurable and Markov's inequality cannot be applied to it directly.  A proof must either:

* add separability of `C_c^∞(D)` under `‖·‖_{H^s}` and a countable dense subset `ψ_n`,
  `‖F‖_{H^{-s}} = sup_n |F ψ_n|` a.e., with `ω ↦ F R ω ψ_n` measurable; or
* prove the measurability of the norm itself from the field's measurability (a
  `MeasurableSpace`/`Sup` interchange, not in Mathlib for this shape).

This is a genuine Lean-only gap, separate from the analysis, and it is the reason a future
attempt should either strengthen the frozen hypotheses or prove a countable-density lemma.

### M1d — Markov assembly

Given M1b and M1c, tightness is one line: for `ε > 0` set `M = ENNReal.ofReal (Real.sqrt (C / ε))`
(or any `M` with `C/M² ≤ ε`), `M ≠ ⊤`, then Chebyshev gives
`P {M < ‖F R‖} ≤ E‖F R‖² / M² ≤ ε`, for every `R ≥ 1` simultaneously.  No new mathematics; it only
needs `M1c`.

## 4. The route, end to end

1. Fix `d, β, K, s` with `0 < β < d`, `s > β/2`, a domain `D`, and `ε > 0`.
2. For a fixed bounded test function `φ`: `F R ω φ = R^{β/2} ∫ u R ω y φ y`; expand
   `E|F R · φ|² = R^β ∫∫ c_R(y-y') φ(y) φ(y') dy dy'` and bound by
   `K R^β ‖φ‖_∞² ∫∫ (1+R‖y-y'‖)^{-β} ≤ C ‖φ‖_∞²` using `aux_besov_second_moment_integral`.
   (This bound is not uniform in the unit ball — `‖φ‖_∞` is not controlled by `‖φ‖_{H^s}` for
   small `s` — so it is only a sanity step.)
3. Apply M1a to replace `‖φ‖_∞` by the `H^s` weight: `E|F R · φ|² ≤ C sobolevNormSq d s φ`.
4. Use `aux_besov_continuous_cauchy_schwarz_unit_ball_sq` to take the sup over the unit ball,
   obtaining `E (negSobolevNorm d s D (F R ·))² ≤ C`, uniformly in `R`, provided the field is
   represented by a Fourier multiplier `b R ω` as in the frozen hypotheses (the covariance is
   positive-definite, so `b` exists; constructing it is part of M1a).
5. Resolve measurability (M1c), then conclude by Markov (M1d).

The only step that is not a routine consequence of the pieces above is 3 (M1a); steps 4 and 5 are
already in the sibling file or are bookkeeping, and step 2 is already proved.

## 5. If attempting this in LatticeProb

The natural home is a new `LatticeProb/Prob/ContinuumBesovTightness.lean`, but note two structural facts:

* `LatticeProb/lakefile.lean` requires only Mathlib, so `Sandpile.*` is **not importable** from this
  repository.  A file under `LatticeProb/` can therefore only prove the LatticeProb analogue of
  the criterion (defining its own `TightInNegSobolev`); discharging the frozen
  `Sandpile.External.ContinuumBesovTightness` itself needs a bridge file in the Sandpile repo (the
  pattern of `scratch/audit-lclt-latprob-ds3/BridgeSandpile.lean`).
* `LatticeProb` does not define `TightInNegSobolev`; either add it (mirroring
  `Sandpile/Continuum/Membrane.lean:50`) or keep the proof in `Sandpile`/a bridge file that
  imports both trees.
* Port `aux_besov_ball_integral_bound`, `aux_besov_second_moment_integral`, and
  `aux_besov_continuous_cauchy_schwarz_unit_ball_sq` verbatim; all three compile in the shared
  vocabulary (`Space d = EuclideanSpace ℝ (Fin d)`, `volume`, `Metric.ball`,
  `ENNReal.lintegral_mul_le_Lp_mul_Lq`).
* The new content is exactly M1a plus the measurability lemma M1c.  A clean first commit would be
  M1a as a standalone `besselKernel_bound` and the `exists_bessel_covariance_integral_le`
  corollary, both independent of the rest and reusable for `RellichKondrachovNegSobolev` and the
  Gaussian-log-Sobolev external.

## 6. Search record (exact names checked)

* Mathlib present and usable: `TemperedDistribution.besselPotential` (`Analysis/Distribution/
  Sobolev.lean:71`), `memSobolev_besselPotential_iff` (:196), `MemSobolev.fourier_memL1` (:241),
  `MemSobolev.mono` (:298), `SchwartzMap.integral_norm_sq_fourier`,
  `SchwartzMap.integral_inner_fourier_fourier`, `MeasureTheory.Lp.inner_fourier_eq`,
  `MeasureTheory.integral_fun_norm_addHaar`, `MeasureTheory.integral_rpow`.
* Mathlib absent: any `Besov`, `LittlewoodPaley`, `rieszPotential`/`RieszKernel`, and any
  function-valued Bessel-kernel asymptotic.  `rg` over Mathlib returns zero hits for each.
* LatticeProb present: `LatticeProb.Sobolev.{IsTestFn,sobolevNormSq,negSobolevNorm,IsDomain}`
  (`Analysis/Sobolev/Defs.lean`), `negSobolevNorm_anti`/`_smul_le`/`_add_le`/`_le_of_abs_le`/
  `_sub_le` (`Analysis/Sobolev/Basic.lean:26,37,55,77,88`), `abs_apply_le_negSobolevNorm`
  (`AbsApply.lean:11`), `negSobolevNorm_le_sup_add` (`DualNet.lean:13`),
  `negSobolevNorm_le_finset_sup_add` (`Compact.lean:14`), `tight_transfer`
  (`TightTransfer.lean:13`), `tight_of_tight_anti` (`Tight.lean`).
* LatticeProb absent: `TightInNegSobolev`, any Besov space, any Riesz/Bessel function kernel.

## 7. Dead end recorded

Do **not** route through `LatticeProb.External.RellichKondrachovNegSobolev` /
`Sandpile.External.RellichKondrachovNegSobolev`: that is a separate open node, and the net/compact
transfer it gates runs in the wrong direction for this criterion (it consumes tightness rather
than producing it).  The three commissioned rounds on it recorded a real obstruction
(`~/fleet/requests/opus-to-ds-lib.md`, REQ-8).  The frozen target must be attacked directly at the
fixed `s`, which is what M1a–M1d do.

## 8. Conclusion

`Sandpile.External.ContinuumBesovTightness` is **not proved** and is not reachable by a bounded
Lean effort.  The elementary reduction is complete and portable (Section 2); the single missing
analytic declaration is the function-valued Bessel/Riesz kernel estimate with its
`R^{β}`-uniform pairing (M1a), and there is a separate measurability obligation (M1c) arising from
the `sSup` definition of `negSobolevNorm`.  The smallest honest next deliverable is
`besselKernel_bound` plus `exists_bessel_covariance_integral_le`; everything else follows by the
already-proved Cauchy–Schwarz/Tonelli steps.
