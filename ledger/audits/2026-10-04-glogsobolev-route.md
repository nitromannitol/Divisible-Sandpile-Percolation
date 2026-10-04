# Route: discharge `LatticeProb.GaussianLogSobolev n` (Gaussian log-Sobolev, general `n`)

Status: **not discharged; no bounded proof attempted.** `gaussianLogSobolev_zero` (and
`gaussianHerbstBound_zero`) are proved in `LatticeProb/External/GaussianLogSobolev.lean`. This file
records the precise route, the existing infrastructure, and the exact missing lemmas. Do not treat
the Prop as proved.

Work target if reachable: a new file `LatticeProb/Prob/GaussianLogSobolev.lean`, namespace
`LatticeProb`, containing the general-`n` proofs and (recommended) the bounded Herbst implication.
Nothing in `LatticeProb/External/` is touched.

## Target (frozen)

`LatticeProb.GaussianLogSobolev n` (`LatticeProb/External/GaussianLogSobolev.lean`):

```
∀ h : (Fin n → ℝ) → ℝ, (∀ x, 0 < h x) →
  Integrable h γ → Integrable (fun x => h x * Real.log (h x)) γ →
  (∫ x, h x ∂γ = 1) →
  ∀ C : NNReal, LipschitzWith C (fun x => Real.log (h x)) →
  ∫ x, h x * Real.log (h x) ∂γ ≤ (C : ℝ) ^ 2 / 2
```

with `γ = Measure.pi fun _ : Fin n => gaussianReal 0 1`. The companion
`LatticeProb.GaussianHerbstBound n` is the exponential-moment form consumed by
`LatticeProb.gaussian_lipschitz_concentration` (`LatticeProb/Prob/GaussianHerbst.lean`). The
README (`README.md:48-53`) explicitly lists both as *cited and never proved here*, so discharging
either changes that status.

## Existing infrastructure

LatticeProb:

* `gaussianLogSobolev_zero`, `gaussianHerbstBound_zero` — the `n = 0` cases (single point).
* `LatticeProb.gaussian_lipschitz_concentration`, `LatticeProb.measure_ge_le_of_mgf_bound`,
  `LatticeProb.integrable_exp_lipschitz_gaussian`
  (`LatticeProb/Prob/GaussianConcentration.lean`, `GaussianHerbst.lean`) — the Chernoff step and
  the integrability of `exp (λ (f - ∫f))` for Lipschitz `f`.
* `LatticeProb.isProbabilityMeasure_pi_gaussianReal`, `LatticeProb.map_perm_pi_gaussianReal`.
* Relative entropy / KL machinery: `InformationTheory.klDiv`,
  `InformationTheory.klDiv_compProd_eq_add` (the chain rule),
  `LatticeProb.klDiv_map_measurableEquiv`, `LatticeProb.klDiv_prod_right`,
  `LatticeProb.klDiv_gaussianReal_shift`, `LatticeProb.klDiv_pi_gaussianReal`,
  `LatticeProb.llr_gaussianReal_eq`, `LatticeProb.integral_llr_gaussianReal`,
  `LatticeProb.integral_sub_log_integral_exp_le_of_klDiv_le` (Pinsker file).
* Gaussian kernels and integrals: `ProbabilityTheory.gaussianReal`, `.gaussianPDFReal`,
  `integrable_exp_mul_gaussianReal`, `LatticeProb.gaussianPDFReal_sq`,
  `LatticeProb.integrable_gaussianPDFReal_sq`, `LatticeProb.integral_gaussianPDFReal_sq`,
  `LatticeProb.gaussianReal_Iic_eq`.
* Product structure: `measurePreserving_piFinSuccAbove`, `MeasurableEquiv.piFinSuccAbove`,
  `ProbabilityTheory.Kernel`, `MeasureTheory.Measure.compProd`.

Mathlib:

* `InformationTheory.klDiv` is the only entropy-type functional; **there is no `entropy`**.
* `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, `…_of_lip` (differentiation under the
  integral), `antitoneOn_of_deriv_nonpos`, `monotoneOn_of_deriv_nonneg`, `ConvexOn`.
* `Real.hasDerivAt_log`, `Real.exp_le_exp`, `Real.add_one_le_exp`.
* **Absent:** any Ornstein–Uhlenbeck / Mehler semigroup, any carré-du-champ / `Γ₂` machinery, any
  log-Sobolev or Poincaré inequality, any entropy tensorization, and the a.e. chain rule for
  Lipschitz functions in the form needed below.

## Mathematical route

### Route 1 (recommended): standard LSI + Herbst form + tensorization

**(A) One-dimensional standard Gaussian LSI.**
```
theorem gaussian_lsi_oneDim :
  ∀ f : ℝ → ℝ, Integrable (fun x => f x ^ 2) (gaussianReal 0 1) →
    Integrable (fun x => (deriv f x) ^ 2) (gaussianReal 0 1) →
    ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂(gaussianReal 0 1)
      - (∫ x, f x ^ 2 ∂(gaussianReal 0 1))
          * Real.log (∫ x, f x ^ 2 ∂(gaussianReal 0 1))
    ≤ 2 * ∫ x, (deriv f x) ^ 2 ∂(gaussianReal 0 1)
```
The classical proof is the Ornstein–Uhlenbeck semigroup and the Bakry–Émery `Γ₂` criterion:
* `P_t f x = ∫ z, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2*t)) * z)
  ∂(gaussianReal 0 1)`;
* `∂_t P_t f = L P_t f` with `L f = deriv (deriv f) - x * deriv f`;
* `∂_x P_t f = Real.exp (-t) * P_t (deriv f)` (Mehler);
* integration by parts gives `d/dt ∫ (P_t f)² dγ = -2 ∫ (P_t (deriv f))² dγ`;
* the `exp(-t)` in the Mehler derivative gives the extra curvature term,
  `d/dt ∫ (P_t (deriv f))² dγ = -2 ∫ (P_t (deriv²f))² dγ - 2 ∫ (P_t (deriv f))² dγ`, hence
  `∫ (P_t (deriv f))² dγ ≤ Real.exp (-2*t) ∫ (deriv f)² dγ`;
* the de Bruijn identity `Ent(P_t f²) = ∫_t^∞ 2 ∫ (P_s (deriv f))² dγ ds` plus `P_t f² → (∫f²)`
  gives the constant `2`.

**(B) Herbst form from the standard LSI.**
For `h > 0` with `log h` `C`-Lipschitz, set `f = √h`. Then `f² = h`, and the a.e. chain rule gives
`|∇f| ≤ (C/2) f`, so `∫ |∇f|² ≤ (C²/4) ∫ h = C²/4`, and `Ent(h) ≤ 2 · C²/4 = C²/2`. This is a
Lipschitz-to-gradient comparison, formalizable either by Rademacher a.e. differentiability of
`log h` or by a smooth approximation argument (`f = √(h + ε)` and let `ε ↓ 0`).

**(C) Tensorization of entropy from `1` to `n`.**
For `γ_n = γ_{n-1} ⊗ γ_1` and `h > 0` with `∫ h dγ_n = 1`,
```
Ent_{γ_n}(h) ≤ ∫ Ent_{γ_1}(h(x, ·)) dγ_{n-1}(x) + Ent_{γ_{n-1}}(H),  H(x) = ∫ h(x,y) dγ_1(y).
```
This is the chain rule for `klDiv` (`InformationTheory.klDiv_compProd_eq_add`) applied to
`P = h · γ_n` and `Q = γ_n`: identify `P_X = H · γ_{n-1}` and the conditional `P_{Y|X}`. Iterating
and applying (A)+(B) coordinatewise yields `GaussianLogSobolev n`.

### Route 2: direct `n`-dimensional OU semigroup

Skip (C); use the Mehler kernel in `n` dimensions and the same `Γ₂` computation. Shorter
mathematically (no disintegration) but needs `n`-dimensional Fréchet derivatives and the
`n`-dimensional heat equation; comparable formal cost to (A) plus a gradient layer.

### Route 3 (rejected)

Bobkov's isoperimetric proof, Brascamp–Lieb, and optimal transport all give the LSI but rest on
deeper results (Gaussian isoperimetry, Prekopa–Leindler, Monge–Ampère) that are not in Mathlib.

## Bounded first step: the Herbst argument (`GaussianLogSobolev n → GaussianHerbstBound n`)

This is independent of (A)–(C) and is the recommended concrete advance: it removes the
`GaussianHerbstBound` hypothesis from `gaussian_lipschitz_concentration`, leaving the LSI as the
single cited input.

```
theorem gaussianLogSobolev_implies_herbst (n : ℕ) (hLSI : GaussianLogSobolev n) :
    GaussianHerbstBound n
```
Proof: fix `f`, `L`, `lam > 0`, `m = ∫ f dγ`, `F lam = ∫ exp (lam * (f - m)) dγ`,
`G lam = Real.log (F lam)`. The LSI applied to `h_lam = exp (lam (f - m)) / F lam` (positive,
mean one, `log` Lipschitz with constant `lam * L`) gives
```
lam * G' lam - G lam ≤ lam ^ 2 * L ^ 2 / 2.
```
Then `psi lam = (G lam - lam ^ 2 * L ^ 2 / 2) / lam` satisfies `psi' ≤ 0` on `(0, ∞)` and
`lim_{lam→0+} psi lam = G'(0) = 0` (since `F 0 = 1` and `F'(0) = ∫ (f - m) dγ = 0`), so
`G lam ≤ lam ^ 2 * L ^ 2 / 2`, i.e. `F lam ≤ Real.exp (lam ^ 2 * L ^ 2 / 2)`. The ODE step uses
`antitoneOn_of_deriv_nonpos` on `Ioi 0` together with the limit at `0`. The differentiation of
`F` uses `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the dominating integrable
function `abs (f - m) * exp (Λ * abs (f - m))` on `lam ∈ [0, Λ]`; `f` Lipschitz gives
`|f - m| ≤ |f 0| + |m| + L |x|` and `LatticeProb.integrable_exp_lipschitz_gaussian` supplies the
exponential integrability. Estimated 150–350 lines; no missing library lemma beyond the
integrability of `|f - m| * exp (Λ |f - m|)` (provable from the existing
`integrable_exp_lip`/`integrable_exp_lipschitz_gaussian` pattern).

## Exact missing lemmas (dependency order)

New file `LatticeProb/Prob/GaussianLogSobolev.lean` unless noted. Names to be grep-verified first.

1. `LatticeProb.ouSemigroup (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ` and
   `LatticeProb.ouSemigroup_apply` (the Mehler formula above). Requires `0 ≤ t`.
2. `LatticeProb.ouSemigroup_heat`: `HasDerivAt (fun t => ouSemigroup t f x) (L (ouSemigroup t f) x) t`
   for `t > 0`, with `L f = fun x => deriv (deriv f) x - x * deriv f x`.
3. `LatticeProb.ouSemigroup_deriv`: `deriv (ouSemigroup t f) x = Real.exp (-t) * ouSemigroup t (deriv f) x`.
4. `LatticeProb.ouSemigroup_entropy_decay` and `LatticeProb.ouSemigroup_gamma_decay`:
   `deriv (fun t => ∫ x, ouSemigroup t f x ^ 2 ∂γ) t = -2 * ∫ x, ouSemigroup t (deriv f) x ^ 2 ∂γ`
   and
   `deriv (fun t => ∫ x, ouSemigroup t (deriv f) x ^ 2 ∂γ) t
      = -2 * ∫ x, (deriv (deriv (ouSemigroup t f))) x ^ 2 ∂γ
        - 2 * ∫ x, ouSemigroup t (deriv f) x ^ 2 ∂γ`.
   These are the Γ₂ identities; they are where the two integrations by parts enter.
5. `LatticeProb.gaussian_lsi_oneDim` — item (A); assembly of 1–4 with the de Bruijn identity and
   `P_t f → ∫f`.
6. `LatticeProb.entropy_tensorization` — item (C), from `InformationTheory.klDiv_compProd_eq_add`
   plus the identification of the disintegration and the equality
   `InformationTheory.klDiv (h • γ_n) γ_n = ∫ x, h x * Real.log (h x) ∂γ_n` for `∫h = 1`.
7. `LatticeProb.gaussian_lsi_entropy (n)`: `Ent_{γ_n}(f²) ≤ 2 ∫ |∇f|² dγ_n`, from 5 and 6.
8. `LatticeProb.gaussian_lipschitz_to_gradient`: the a.e. chain rule `|∇√h| ≤ (C/2)√h` when
   `LipschitzWith C (log h)` (item (B); optionally bypassed by proving the Herbst form directly
   from 5).
9. `LatticeProb.gaussianLogSobolev (n)` — the target, from 7 and 8.

Recommended bounded sub-target (independent of 1–9):
`LatticeProb.gaussianLogSobolev_implies_herbst` (Section above), using only the LSI hypothesis.

## Alternatives considered and why rejected

* **Direct 1D proof via Hermite expansion:** the entropy of a Hermite-expanded `f²` has no closed
  form; the Poincaré spectrum gives only Poincaré, not LSI.
* **Pinsker / KL comparison** (`LatticeProb.klDiv_*`): gives an upper bound on the entropy by
  `L²`-type quantities, not the LSI constant, and no Gaussian `Γ₂`.
* **Efron–Stein** (`LatticeProb.efron_stein`): a variance inequality; it gives Gaussian
  concentration only with a `sup`-type constant and does not yield the sharp LSI. It also does
  not see the `Lip(log h)` hypothesis.
* **Weakening the statement:** not allowed — the frozen `def` is fixed and `n = 0` is already
  specialised.

## Scope / risk

* Items 1–5 (the 1D OU/Bakry–Émery proof) are the large analysis project: the Mehler kernel,
  differentiating under the integral twice, two integrations by parts on `γ`, and an entropy
  Gronwall argument. Estimated 800–2000 lines; the heat-equation and Γ₂ identities are the risk.
* Item 6 (tensorization) is bounded but leans on disintegration / conditional kernels, which are
  a known formalisation pain point; a workable alternative is to state it only for `n = k+1` with
  the `piFinSuccAbove` split used in `klDiv_pi_gaussianReal` and iterate.
* Item 8 is a technical a.e.-differentiability step; the `ε ↓ 0` smooth-approximation route avoids
  invoking Rademacher and is likely cheaper.
* The Herbst implication (bounded sub-target) is independent and recommended as the first file to
  land; it is the only piece that can be finished without the OU semigroup.

The Gaussian LSI is the genuinely hard cited result; unlike the polygonal-topology and
Rellich–Kondrachov externals it has a concrete, well-understood proof route, but it is not a
bounded Lean step.
