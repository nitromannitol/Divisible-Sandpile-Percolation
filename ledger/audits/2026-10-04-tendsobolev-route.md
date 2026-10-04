# Route — `Sandpile.Continuum.TendstoInNegSobolev` (external-debt bridge)

Repo `~/lean/Divisible-Sandpile-Percolation`. Read-only audit plus route. No Lean file and no
manifest state was changed. `git` was not run. Read against the pinned dependency
`.lake/packages/lattice-probability` (the checkout `~/lean/Lattice-Probability` is ahead).

## 0. Verdict

**PARTIAL (route only; no bounded proof).** The shared library now supplies the `H^{-s}` space and
the compactness / order-transfer core, and its names are already consumed by the paper repository,
so the *modelling* bridge is supported. A closed Lean proof of the full Cramér–Wold / Prokhorov
bridge is **not** available this shift, for two independent reasons: (a) the a priori moment
criterion (Furlan–Mourrat) is still absent; (b) Mathlib and the library have no topology and no
Prokhorov theorem on the negative-Sobolev dual. Exact missing lemmas in §4.

## 1. The definition and its uses

`Sandpile.Continuum.TendstoInNegSobolev` is a **`def … : Prop`**, not a frozen External node:
`Sandpile/Continuum/Membrane.lean:59-66`.

```
def TendstoInNegSobolev (d : ℕ) (s : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℝ → Ω → (Space d → ℝ) → ℝ) (K : (Space d → ℝ) → (Space d → ℝ) → ℝ) : Prop :=
  (∀ φ, IsTestFn Set.univ φ →
      TendstoInDistribution (fun R ω => F R ω φ) atTop (id : ℝ → ℝ) (fun _ => P)
        (gaussianReal 0 (Real.toNNReal (K φ φ)))) ∧
    TightInNegSobolev d s P F
```

with `TightInNegSobolev` at `Membrane.lean:50-57`,

```
def TightInNegSobolev … : Prop :=
  ∀ D, IsDomain D → ∀ ε, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R, 1 ≤ R →
    P {ω | M < negSobolevNorm d s D (F R ω)} ≤ ENNReal.ofReal ε
```

and `negSobolevNorm` re-exported from the library at `Sandpile/Continuum/Sobolev.lean:32`
(`export LatticeProb.Sobolev (IsTestFn sobolevNormSq negSobolevNorm IsDomain)`).

The EXTERNALS row is the source of the "unproved bridge" label:

> `Sandpile.Continuum.TendstoInNegSobolev` — convergence in `H^{-s}_loc(ℝ^d)` … recorded as
> convergence in distribution of every pairing plus tightness of the `H^{-s}(D)` norms | not
> literature; Mathlib 4.32 has no Sobolev spaces, so the paper's weak convergence is recorded
> through the Cramér–Wold equivalent pair, which is itself an unproved bridge here | 9 …
> unproved bridge; needs `H^{-s}(D)` as a space and the Cramér–Wold argument

**Uses** (`grep -rn "TendstoInNegSobolev" Sandpile/`): it is only ever a *conclusion*, never a
hypothesis. Frozen conclusions: `Sandpile/Frozen/HighSobolevLimit.lean:38,52` (`thm:main-explosion`
(iii)(c)), `HighNonconvergence.lean:65` (negation), `DGT4DiffusiveMembrane.lean:102`,
`DGT4ManyLimits.lean:47`, `WeightedMembraneLimit.lean:62`; supporting assemblies
`Sandpile/Support/ManyLStep3Build.lean:82,115`, `ManyLStep3.lean:134,155`, `ManyLSubseq.lean:193`,
`ManyLMembrane.lean:54`, `ManyLManyLimits.lean:52,73`, `ExplHighSobolev.lean`, `ContNonconvergence.lean:58`,
and the main-theorem wrappers `Sandpile/MainTheorems.lean:322,336,378`. The tightness-only sibling
`TightInNegSobolev` is concluded by `Sandpile/Frozen/FourSobolev.lean:65`, `D4DiffusiveTightness.lean:56`,
`DGT4LinearizationFromSurvival.lean:149`, `SobolevTightness.lean:88`. Every one of these carries
`hBesov : Sandpile.External.ContinuumBesovTightness` (or `hRK`), so the bridge is a faithfulness
issue, not a load-bearing hypothesis.

## 2. Library API available now (`grep`-verified, pinned dependency)

Namespace `LatticeProb.Sobolev` (`LatticeProb/Analysis/Sobolev/`):

| name | file:line | role |
|---|---|---|
| `Space`, `IsTestFn`, `sobolevNormSq`, `negSobolevNorm`, `IsDomain` | `Defs.lean:27-56` | the `H^{-s}` space |
| `sobolevNormSq_mono`, `negSobolevNorm_anti` | `Basic.lean:15,26` | `s₀ ≤ s → negSobolevNorm s ≤ negSobolevNorm s₀` |
| `negSobolevNorm_smul_le`, `negSobolevNorm_add_le`, `negSobolevNorm_le_of_abs_le`, `negSobolevNorm_sub_le` | `Basic.lean:37,55,77,88` | algebraic control |
| `abs_apply_le_negSobolevNorm` | `AbsApply.lean:11` | `\|F φ\| ≤ η · ‖F‖` when `‖φ‖_{H^s}² ≤ η²` (pairing continuity) |
| `sobolevNormSq_const_mul`, `IsTestFn.const_mul`, `IsTestFn.sub` | `Scaling.lean:13`, `TestFn.lean:9`, `TestFnSub.lean:9` | scaling / closure of test functions |
| `weight_le` | `Weight.lean:11` | high-frequency weight comparison |
| `negSobolevNorm_le_finset_sup_add` | `Compact.lean:14` | RK upgrade (needs `hRK`) |
| `negSobolevNorm_le_sup_add` | `DualNet.lean:13` | the dual-net bound |
| `tight_transfer` | `TightTransfer.lean:13` | weak-norm tail bound + RK ⇒ strong norm ≤ finite pairings + η |
| `tight_of_tight_anti` | `Tight.lean:15` | tightness in `H^{-s₀}` ⇒ tightness in `H^{-s}`, `s₀ < s` |

Parallel (older) copy `LatticeProb.NegSobolev` in `LatticeProb/Analysis/NegSobolev.lean` (`negSobolevNorm`,
`sobolevNormSq`, `IsTestFn`, `IsDomain`, plus `negSobolevNorm_le`, `negSobolevNorm_mono_domain`,
`negSobolevNorm_le_of_le`, `negSobolevNorm_sublevel_subset`); it is not the copy the paper repo
consumes.

Sandpile-side bridge already in place: `Sandpile/Support/Dgt4ANegSobolevBridge.lean:26`
`negSobolevNorm_eq_latticeProb : Sandpile.Continuum.negSobolevNorm d s D F
= LatticeProb.Sobolev.negSobolevNorm d s D F` by `rfl`, so the library machinery is consumable in
the paper's vocabulary; `Sandpile/Support/Dgt4ALinNegSobolev.lean:118` already reimplements the
dual-net upgrade (`negSobolevNorm_le_sup_add_sub`) from `LatticeProb.Analysis.Sobolev.DualNet`, and
`:352` `tendsto_negSobolevNorm_zero_of_linearization` applies it.

Related library bridge material, but for *other* topologies: `LatticeProb/WeakLimit.lean:79`
`exists_weak_limit` (Prokhorov for `ℝ`), and `LatticeProb/Prob/FddTight.lean:383`
`tendsto_integral_of_fdd_of_equicontinuous'` (Cramér–Wold for `C(K)`, `K` compact metric).

## 3. Refute-first analysis

* **The tightness clause at order `s` is not the hard part.** `negSobolevNorm_anti` gives
  `negSobolevNorm d s ≤ negSobolevNorm₀` for `s₀ ≤ s`, hence the tail set `{M < negSobolevNorm s}`
  is contained in `{M < negSobolevNorm s₀}` and `tight_of_tight_anti` transfers tightness upward.
  So `TightInNegSobolev d s` follows from tightness at any `s₀ ≤ s`. This is exactly the
  order-transfer the library now provides, and it is **not** what was missing.
* **`tight_transfer` does not manufacture tightness.** Its hypothesis is an a priori weak-norm
  bound `μ{ω | 1 < negSobolevNorm d s₀ D (F ω)} ≤ ofReal η`; it consumes that bound. The missing
  input is a bound of `negSobolevNorm d s₀` (e.g. `s₀ = β/2`) off a small set, from the covariance
  decay. That is the Furlan–Mourrat Theorem 2.30 moment criterion, i.e. exactly the content of
  `Sandpile.External.ContinuumBesovTightness` (`Sandpile/External/ContinuumBesovTightness.lean:63`).
  So `tight_transfer` cannot discharge `ContinuumBesovTightness` (nor `TendstoInNegSobolev`).
* **The Cramér–Wold / Prokhorov bridge has no topology to run on.** The definition asserts a pair
  of conditions in place of "weak convergence in `H^{-s}_loc`". Turning the pair into a statement
  about laws on a dual space needs (i) a topology (the `H^{-s}_loc` Fréchet topology generated by
  the seminorms `negSobolevNorm d s D`, `D` over a countable base of bounded domains) and (ii)
  Prokhorov / Cramér–Wold on that dual. Mathlib has `MeasureTheory.IsTightMeasureSet` and
  Prokhorov for Polish spaces, and the library has `exists_weak_limit` for `ℝ` and the `C(K)`
  Cramér–Wold of `FddTight.lean`; neither is stated for a negative-Sobolev dual. The pairing
  continuity (`abs_apply_le_negSobolevNorm`) only gives the easy forward direction.

Net: the library closes the *technical compactness core* and the *order transfer*; it does not
close the moment criterion and does not have the dual topology. No bounded proof exists today.

## 4. Precise route and exact missing lemmas

**Route (shortest honest path).**

1. Prove the a priori weak-norm bound from the covariance hypothesis (Furlan–Mourrat, `p = q = 2`):
   for a field `u R ω y` on `ℝ^d` with `|Cov(u R · y, u R · y')| ≤ K (1 + R‖y−y'‖)^{-β}`, show that
   there is `s₀ < s` and, for every `D`, `ε`, an `M` with
   `P{ω | M < negSobolevNorm d s₀ D (fun φ => R^{β/2} ∫ u R ω y φ y)} ≤ ofReal ε` uniformly in
   `1 ≤ R`. (For `s > β/2` take `s₀ = β/2`.)
2. Upgrade to `TightInNegSobolev d s` with `LatticeProb.Sobolev.tight_of_tight_anti`.
3. Add the pairing convergence already proved in the repo (the `TendstoInDistribution` clause),
   giving `TendstoInNegSobolev`.
4. For the modelling bridge, add the dual topology and Cramér–Wold/Prokhorov so that the pair is
   equivalent to weak convergence in `H^{-s}_loc`. (Independent of 1–3; a faithfulness result.)

**Missing lemmas (exact statements to add; §2 names are grep-verified).**

* **(M1) Furlan–Mourrat moment criterion.** The single genuinely hard gap and the only reason
  `Sandpile.External.ContinuumBesovTightness` is still assumed. Target shape (a `theorem`, in the
  sandpile repo or library):

  ```
  theorem tightInNegSobolev_of_covariance {Ω} [MeasurableSpace Ω] (d : ℕ) {β K : ℝ}
      (hβ0 : 0 < β) (hβd : β < d) (P : Measure Ω) [IsProbabilityMeasure P]
      (u : ℝ → Ω → Space d → ℝ)
      (hmem : ∀ R ≥ 1, ∀ y, MemLp (fun ω => u R ω y) 2 P)
      (hcov : ∀ R ≥ 1, ∀ y y', |covariance (fun ω => u R ω y) (fun ω => u R ω y') P|
          ≤ K * (1 + R * ‖y - y'‖) ^ (-β)) :
      ∀ s, β / 2 < s → TightInNegSobolev d s P
        (fun R ω φ => R ^ (β / 2) * ∫ y, u R ω y * φ y)
  ```

  Reduces to a bound on `∫⁻ ω, (negSobolevNorm d s₀ D (·))`-type quantities via the moment `p = 2`
  condition; this is the step the paper attributes to Furlan–Mourrat Theorem 2.30 and does not
  prove. Nothing in the library currently approximates it (grep finds no `Furlan`, `Besov`, or
  covariance-to-`negSobolevNorm` theorem).
* **(M2) Cramér–Wold/Prokhorov on the negative-Sobolev dual.** Needed only for the faithfulness
  bridge, not for the paper's proofs. Missing Mathlib/LatticeProb ingredients:
  a. a `TopologicalSpace` / pseudo-metric on `(Space d → ℝ) → ℝ` from the seminorms
     `fun F => negSobolevNorm d s D F` over a countable cofinal family of `D` (no such instance in
     either repo);
  b. `MeasureTheory.IsTightMeasureSet` for that dual and a Prokhorov theorem producing a limit law
     (the library's `LatticeProb.WeakLimit.exists_weak_limit` is only for `ℝ`);
  c. a Cramér–Wold theorem for that dual (the library's `FddTight.tendsto_integral_of_fdd_of_equicontinuous'`
     is only for `C(K)`), using `abs_apply_le_negSobolevNorm` for pairing continuity and
     `tight_transfer`/`negSobolevNorm_le_finset_sup_add` to reduce a bounded continuous functional
     of the dual to finitely many pairings.
* **(M3) Naming cleanup (bounded).** `LatticeProb.NegSobolev` and `LatticeProb.Sobolev` are parallel
  copies; a one-line `rfl` bridge between them (in the style of
  `Sandpile.Support.negSobolevNorm_eq_latticeProb`) would make the EXTERNALS row's reference to
  `LatticeProb/Analysis/NegSobolev.lean` resolve to the `tight_transfer` copy. Provable, but does
  not move the bridge.

## 5. Machine evidence

Name survey and use survey are by `grep -rn` against `Sandpile/` and the pinned
`.lake/packages/lattice-probability/LatticeProb/`; the definition and bridge bodies were read in
full (`Sandpile/Continuum/Membrane.lean`, `Sandpile/Continuum/Sobolev.lean`,
`Sandpile/External/ContinuumBesovTightness.lean`, `Sandpile/Support/Dgt4ANegSobolevBridge.lean`,
`Sandpile/Support/Dgt4ALinNegSobolev.lean`, `Sandpile/Frozen/SobolevTightness.lean` and the
library `Analysis/Sobolev/*.lean`). No `sorry`, `axiom`, or unresolved node is involved; the gap is
a missing theorem, not an inconsistency. No scratch Lean file accompanies this report because no
bounded proof was found.
