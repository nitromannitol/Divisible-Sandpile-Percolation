/-
Lemma of sandpile.tex, frozen.  `sandpile.tex:4909-4945`
(label `lem:dgt4-origin-frozen`):

  "Assume that $d\geq5$ and that the scenery is i.i.d., atomless, centered,
   and of finite positive variance.  For every $n\geq0$:
     $\{u_{n+1}(0)=0\}=\{-\zeta(0)>Pw_n(0)\}$,
     $(-\zeta(0)-Pu_n(0))_+=(-\zeta(0)-Pw_n(0))_+$,
     $\E u_{n+1}(0)-\E u_n(0)=\E(-\zeta(0)-Pw_n(0))_+$.
   If $\E|\zeta(0)|^p<\infty$ for some $p\geq2$, then
     $\frac{G(0,0)\E Pw_n(0)}{\E u_n(0)}\longrightarrow1$,
     $\sup_{n\geq0}\E|Pw_n(0)-\E Pw_n(0)|^p<\infty$.
   If, in addition, $\E e^{\theta_0|\zeta(0)|}<\infty$ for some $\theta_0>0$,
   then, for every
     $0<\lambda<\theta_0/\sup_{z\ne0}G(0,z)/G(0,0)$,
   there is $C(\lambda)<\infty$ such that for every $n,r\geq0$,
     $\P(Pw_n(0)-\E Pw_n(0)\leq-r)\leq C(\lambda)e^{-\lambda r}$."

Modelling decisions.

`w_n` is defined at `sandpile.tex:4829-4831`: "we introduce
$w_n\coloneqq u_n^{\Z^d\setminus\{0\}}$, the localized odometer
\eqref{eq:localized-odometer} with the walk killed on hitting the origin".  It
is `killedOdometer` below, `Sandpile.localizedOdometer` on the domain
`{x | x ≠ 0}`.  `Pw_n(0)` is `Sandpile.avg (killedOdometer ζ n) 0`, and
`Pu_n(0)` is `Sandpile.avg (Sandpile.odometer σ n) 0`.

The scenery is written in the mass normalization: the integration variable is
`σ` with law `Sandpile.centeredMassLaw d ν`, so `ζ = Sandpile.scenery d σ` has
one-site law `ν` and `u_n` is `Sandpile.odometer σ n`.  `E u_n(0)` is
`Sandpile.meanOdometer`.

The first two displayed identities are stated almost surely rather than
pointwise, because the proof (`sandpile.tex:4878-4880`, "Induction in $n$, using
monotonicity and atomlessness, gives the first two identities") uses
atomlessness to discard the tie `{-ζ(0) = Pw_n(0)}`, on which the paper's strict
inequality and the odometer recursion disagree.  The set identity is written as
an almost sure equivalence of the two membership conditions.  `(x)_+` is
`max 0 x`.

`E|ζ(0)|^p < ∞` is `Integrable (fun z => |z| ^ p) ν` with `p : ℝ` and rpow, and
`sup_{n≥0} E|·|^p < ∞` is an explicit finite bound valid for every `n`, which
avoids the junk value of an unbounded `sSup`.  The exponential-moment clause
repeats the `p`-moment hypothesis, since the paper's "in addition" adds to it.

`sup_{z≠0} G(0,z)/G(0,0)` is `greenRatioSup` below, an `iSup` over the subtype
of nonzero sites: the index type is nonempty and the values lie in `(0,1]`
because `G(0,z) ≤ G(0,0)`, so the `iSup` is not a junk value.  `C(λ)` is bound
after `λ`, as the paper's notation demands, and `r` ranges over the nonnegative
reals.  Probabilities are `ℝ≥0∞`-valued measures of the events, compared with
`ENNReal.ofReal` of the nonnegative right-hand side.
-/
import Sandpile.Support.OriginConcentration
import Sandpile.Law
import Sandpile.Walk
import Sandpile.External.GreenBoundsHigh

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Frozen.DGT4OriginFrozen

/-- `w_n := u_n^{ℤ^d ∖ {0}}` of `sandpile.tex:4824-4826`: "we introduce
$w_n\coloneqq u_n^{\Z^d\setminus\{0\}}$, the localized odometer
\eqref{eq:localized-odometer} with the walk killed on hitting the origin". -/
noncomputable def killedOdometer {d : ℕ} (ζ : Sandpile.Site d → ℝ) (n : ℕ) :
    Sandpile.Site d → ℝ :=
  Sandpile.localizedOdometer {x : Sandpile.Site d | x ≠ 0} ζ n

/-- `sup_{z≠0} G(0,z)/G(0,0)` of `sandpile.tex:4857-4860`, as a supremum over the
nonzero sites.  The values lie in `(0,1]`, so this is a genuine supremum. -/
noncomputable def greenRatioSup (d : ℕ) : ℝ :=
  ⨆ z : {z : Sandpile.Site d // z ≠ 0}, Sandpile.green d 0 (z : Sandpile.Site d) /
    Sandpile.green d 0 0

end Sandpile.Frozen.DGT4OriginFrozen

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_origin_frozen
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤) :
    (∀ n : ℕ,
        (∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
            (Sandpile.odometer σ (n + 1) 0 = 0 ↔
              Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
                  (Sandpile.scenery d σ) n) 0 < -Sandpile.scenery d σ 0)) ∧
          (∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
            max 0 (-Sandpile.scenery d σ 0 - Sandpile.avg (Sandpile.odometer σ n) 0) =
              max 0 (-Sandpile.scenery d σ 0 -
                Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
                  (Sandpile.scenery d σ) n) 0)) ∧
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n =
            ∫ σ, max 0 (-Sandpile.scenery d σ 0 -
                Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
                  (Sandpile.scenery d σ) n) 0) ∂(Sandpile.centeredMassLaw d ν)) ∧
      (∀ p : ℝ, 2 ≤ p → Integrable (fun z => |z| ^ p) ν →
        Tendsto (fun n : ℕ =>
            Sandpile.green d 0 0 *
              (∫ σ, Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
                  (Sandpile.scenery d σ) n) 0 ∂(Sandpile.centeredMassLaw d ν)) /
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n) atTop (𝓝 1) ∧
          ∃ M : ℝ, ∀ n : ℕ,
            ∫ σ, |Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
                  (Sandpile.scenery d σ) n) 0 -
                ∫ σ', Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
                  (Sandpile.scenery d σ') n) 0 ∂(Sandpile.centeredMassLaw d ν)| ^ p
              ∂(Sandpile.centeredMassLaw d ν) ≤ M) ∧
      (∀ p : ℝ, 2 ≤ p → Integrable (fun z => |z| ^ p) ν →
        ∀ θ₀ : ℝ, 0 < θ₀ → Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
          ∀ lam : ℝ, 0 < lam →
            lam < θ₀ / Sandpile.Frozen.DGT4OriginFrozen.greenRatioSup d →
            ∃ C : ℝ, ∀ (n : ℕ) (r : ℝ), 0 ≤ r →
              (Sandpile.centeredMassLaw d ν)
                  {σ | Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
                        (Sandpile.scenery d σ) n) 0 -
                      (∫ σ', Sandpile.avg (Sandpile.Frozen.DGT4OriginFrozen.killedOdometer
                        (Sandpile.scenery d σ') n) 0 ∂(Sandpile.centeredMassLaw d ν)) ≤ -r} ≤
                ENNReal.ofReal (C * Real.exp (-(lam * r))))
-- FROZEN-STATEMENT-END
:= by
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  have hd1 : 1 ≤ d := by omega
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hint : Integrable id ν := hLp.integrable (by norm_num)
  have hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z := by
    intro z hz
    have hv : 0 < variance (id : ℝ → ℝ) ν := ENNReal.toReal_pos hvar.ne' hvar'.ne
    rw [hz, variance_dirac] at hv
    exact (lt_irrefl 0) hv
  refine ⟨fun n => ?_, ?_, ?_⟩
  · exact Sandpile.origin_frozen_identities hd1 ν hatom hint hmean n
  · intro p hp hmom
    exact ⟨Sandpile.origin_frozen_mean_ratio hd ν hint hmean hnondeg,
      Sandpile.origin_frozen_moment_bound hGreenHigh hd ν hp hmom⟩
  · intro _ _ _ θ hθ hexp lam hlam hlt
    have hsup : Sandpile.Frozen.DGT4OriginFrozen.greenRatioSup d = LatticeProb.greenRatioSup d := by
      unfold Sandpile.Frozen.DGT4OriginFrozen.greenRatioSup LatticeProb.greenRatioSup
      congr 1
      funext z
      rw [Sandpile.green_origin_eq_srwGreenInf, Sandpile.green_origin_eq_srwGreenInf,
        LatticeProb.srwHitProb_eq_green_ratio (by omega)]
    rw [hsup] at hlt
    have hB : 0 < LatticeProb.greenRatioSup d := by
      by_contra hn
      have hb := div_nonpos_of_nonneg_of_nonpos hθ.le (le_of_not_gt hn)
      linarith
    have hgap : lam * LatticeProb.greenRatioSup d < θ := (lt_div_iff₀ hB).mp hlt
    obtain ⟨C, hC⟩ := Sandpile.origin_frozen_lower_tail hGreenHigh hd ν hθ hexp hB.le
      (fun z hz => LatticeProb.le_greenRatioSup (by omega) hz) hlam hgap
    exact ⟨C, fun n r _ => hC n r⟩
