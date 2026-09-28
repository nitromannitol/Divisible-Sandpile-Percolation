import Sandpile.External.HeatKernelBoundsProved
import Sandpile.Support.TightD4Covariance
import Sandpile.Support.TightNegSobolev

/-! # Diffusive Tightness in Dimension Four

Proposition of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3317-3324`
(label `prop:d4-diffusive-tightness`):

  "[Diffusive tightness in dimension four]  Suppose that
   $(\zeta(x))_{x\in\Z^4}$ are i.i.d.\ mean-zero variables with variance
   $\nu^2\in(0,\infty)$.  For every $T>0$ and $s>0$, the fields
   $\bigl(u_{\lfloor TR^2\rfloor}-\E u_{\lfloor TR^2\rfloor}(0)\bigr)^{(R)}$
   for $R\geq1$ are tight in $H^{-s}_{\rm loc}(\R^4)$."

Modelling.  The scenery `ζ` is carried by its one-site law `ν` and the field by
`centeredMassLaw 4 ν`, the law of `σ = 1 + 8ζ`, so `u_t` is
`Sandpile.odometer σ t` and `E u_t(0)` is `Sandpile.meanOdometer`.  The
hypotheses `0 < Var(ζ(0)) < ∞` are the paper's `\nu^2\in(0,\infty)`, written
with `evariance` in `ℝ≥0∞` so that both halves are literal.  No exponential
moment is assumed: the paper's proof of this proposition uses only the
covariance bound `eq:odometer-covariance-bound`.

The embedded field `f^{(R)}` enters, as everywhere in the paper, only through
its pairings with test functions, so the random distribution
`\bigl(u_t-\E u_t(0)\bigr)^{(R)}` is the functional
`φ ↦ latticePairing R (u_t - E u_t(0)) φ`, and tightness in
`H^{-s}_{\rm loc}(\R^4)` is `Sandpile.Continuum.TightInNegSobolev`, which asks,
on every bounded domain, for a finite bound on the `H^{-s}(D)` norm that holds
with probability `1 - ε` uniformly over `R ≥ 1`.  The paper's `R ≥ 1` is the
`1 ≤ R` inside that definition, so `R` ranges over the reals, not the integers.
The time is `⌊T R²⌋` as a natural number, `Nat.floor`; for `T > 0` and `R ≥ 1`
this is the paper's floor, and no junk value is reached.

Cited inputs.  The proof reads the Gaussian upper bound `eq:rw-gaussian-upper`
through `hHeatKernel`, as the paper does, and it applies
`lem:sobolev-tightness`, whose own proof is the citation of the Furlan and
Mourrat criterion; standing convention R1 therefore also attaches that criterion,
`Sandpile.External.ContinuumBesovTightness`, on the space the proposition uses.
No other input is added.  With `ε` a small positive number below `s` and one,
the field `R^{-ε}(u_t - E u_t(0))` at `t = ⌊TR²⌋` has covariance at most
`K(1+|x-y|)^{-2ε}` uniformly in `R`, and the tightness lemma at `β = 2ε`
restores the factor `R^{β/2} = R^{ε}`, giving exactly the family of the
statement.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_diffusive_tightness
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site 4 → ℝ))
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : 0 < s) :
    Sandpile.Continuum.TightInNegSobolev 4 s (Sandpile.centeredMassLaw 4 ν)
      (fun (R : ℝ) (ω : Sandpile.Site 4 → ℝ) (φ : Sandpile.Continuum.Space 4 → ℝ) =>
        Sandpile.Continuum.latticePairing R
          (fun x => Sandpile.odometer ω ⌊T * R ^ 2⌋₊ x -
            Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊) φ)
-- FROZEN-STATEMENT-END
:= by
  have hHeatKernel : Sandpile.External.HeatKernelBounds := Sandpile.External.heatKernelBounds
  haveI := hprob
  have _hMeanZero := hmean
  have _hNondegenerate := hvar
  have hsq : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hsq2 : Integrable (fun z => z ^ 2) ν := by simpa using hsq.integrable_sq
  have hint : Integrable (id : ℝ → ℝ) ν := hsq.integrable (by norm_num)
  have hpos : Integrable (fun z => max z 0) ν := by
    refine hint.abs.mono' (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    rcases le_or_gt 0 z with hz | hz
    · rw [max_eq_left hz]
      simp
    · rw [max_eq_right (le_of_lt hz), abs_zero]
      simp
  set ε := min (s / 2) (1 / 2) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hεs : ε < s := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨K, hK, hcovbd⟩ :=
    Sandpile.Support.exists_d4_covariance_decay hHeatKernel ν hsq2 hpos T hT ε hε hε1
  set F : ℝ → (Sandpile.Site 4 → ℝ) → Sandpile.Site 4 → ℝ :=
    fun R ω x => R ^ (-ε) * (Sandpile.odometer ω ⌊T * R ^ 2⌋₊ x -
      Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊) with hF
  have hmemF : ∀ R : ℝ, 1 ≤ R → ∀ x : Sandpile.Site 4,
      MemLp (fun ω => F R ω x) 2 (Sandpile.centeredMassLaw 4 ν) := by
    intro R hR x
    exact ((Sandpile.Support.memLp_two_odometer ν hsq2 (by norm_num) ⌊T * R ^ 2⌋₊ x).sub
      (memLp_const _)).const_mul _
  have hmeanF : ∀ R : ℝ, 1 ≤ R → ∀ x : Sandpile.Site 4,
      ∫ ω, F R ω x ∂(Sandpile.centeredMassLaw 4 ν) = 0 := by
    intro R hR x
    have hix : Integrable (fun ω : Sandpile.Site 4 → ℝ =>
        Sandpile.odometer ω ⌊T * R ^ 2⌋₊ x) (Sandpile.centeredMassLaw 4 ν) :=
      Sandpile.Support.integrable_odometer ν hpos (by norm_num) _ x
    show ∫ ω, R ^ (-ε) * (Sandpile.odometer ω ⌊T * R ^ 2⌋₊ x -
      Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊)
        ∂(Sandpile.centeredMassLaw 4 ν) = 0
    rw [integral_const_mul, integral_sub hix (integrable_const _), integral_const,
      Sandpile.Support.integral_odometer_eq ν (by norm_num) _ x]
    simp
  have hmain := Sandpile.Frozen.sobolev_tightness 4 (2 * ε) K (by linarith)
    (by push_cast; linarith) hBesov (Sandpile.centeredMassLaw 4 ν) F hmemF hmeanF
    (fun R hR x y => hcovbd R hR x y) s (by linarith)
  refine Sandpile.Support.tight_congr_ge_one 4 s _ _ _ ?_ hmain
  intro R hR ω
  funext φ
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hexp : (2 * ε) / 2 = ε := by ring
  have hcancel : R ^ ε * R ^ (-ε) = 1 := by
    rw [← Real.rpow_add hR0]
    simp
  show R ^ ((2 * ε) / 2) * Sandpile.Continuum.latticePairing R (F R ω) φ = _
  rw [hexp, hF]
  rw [Sandpile.Support.latticePairing_const_mul R (R ^ (-ε))
    (fun x => Sandpile.odometer ω ⌊T * R ^ 2⌋₊ x -
      Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊) φ,
    ← mul_assoc, hcancel, one_mul]
