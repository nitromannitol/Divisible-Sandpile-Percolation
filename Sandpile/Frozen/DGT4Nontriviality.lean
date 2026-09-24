/-
High-dimensional critical percolation theorem of sandpile.tex, frozen.
`sandpile.tex:6672-6694` (label `thm:dgt4-nontriviality`):

  "Fix $\nu_0>0$, $\theta_0>0$, and $K_0<\infty$. There are
   $b=b(d,\theta_0,K_0)>0$, $C=C(d,\theta_0,K_0)<\infty$,
   $c=c(d,\nu_0,\theta_0,K_0)>0$, and $t_0=t_0(d,\nu_0,\theta_0,K_0)<\infty$
   such that, for every mean-zero i.i.d.\ field $(\zeta(x))_{x\in\Z^d}$
   satisfying
   \[
     \Var(\zeta(0))\geq\nu_0^2\, ,\qquad \E e^{\theta_0|\zeta(0)|}\leq K_0\, ,
   \]
   and every $t\geq t_0$, the level set $\{x:u_t(x)>c(\log t)^{2/d}\}$
   contains an infinite nearest-neighbor component almost surely.
   Moreover, for every $t\geq t_0$,
   \[
     \P\left(Q(0,1)\leftrightarrow\infty
     \textup{ in }\{x:u_t(x)>\E u_t(0)/2\}\right)\geq 1-Ce^{-b\E u_t(0)}\, ."

The section fixes `d ≥ 5` (`sandpile.tex:4079`) and the standing hypotheses of
`sandpile.tex:4096-4108`: the scenery is i.i.d. with `E ζ(0) = 0` and
`0 < Var(ζ(0)) < ∞`.  The finiteness of the variance is implied by the
exponential moment but is recorded, as the section records it.
The dependence of the constants is transcribed by the quantifier order:
`b` and `C` depend on `d, θ₀, K₀` only, so they are bound after those and
before `ν₀`, while `c` and `t₀` also depend on `ν₀` and are bound after it; the
law `ν` is bound last, so all four constants are uniform over the class.
The scenery is the integration variable, with law `LatticeProb.iidLaw d ν`;
`u_t` is `Sandpile.odometerOf ζ t` and `E u_t(0)` is `meanOdometerOf d ν t`.
`Q(0,1)\leftrightarrow\infty` in a set `S` is read, as the proof reads it, as the
conjunction of `Q(0,1) ⊆ S` and the statement that the nearest-neighbour cluster
of the origin inside `S` is infinite; on the locally finite graph `ℤ^d` an
infinite cluster is exactly one that reaches every distance.
The first clause uses `Sandpile.HasInfiniteComponent`, which is the paper's
"contains an infinite nearest-neighbor component".
The probability bound is stated in `ℝ≥0∞`.  When `1 - Ce^{-b E u_t(0)}` is
negative, `ENNReal.ofReal` truncates it to `0` and the inequality is trivially
true, which is also the content of the paper's inequality in that regime, so
nothing is lost or gained.

The exponential-moment bound is stated together with the integrability of the
exponential, as the paper's `K₀ < ∞` requires: the Bochner integral of a
non-integrable nonnegative function is zero, so the bound alone would hold for
every law with no exponential moment.
-/
import Sandpile.Walk
import Sandpile.External.GreenBoundsHigh
import Sandpile.Support.AnnularPercolation
import Sandpile.Support.UniformTail
import Sandpile.Support.HeightLower

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Frozen.DGT4Nontriviality

/-- The box metric of `sandpile.tex:6366-6368`: "All distances in this
subsection are measured in the box metric used to define $Q(x,L)$; in
particular, $|x-y|$ below denotes this distance." -/
def boxDist {d : ℕ} (x y : Site d) : ℕ :=
  Finset.univ.sup fun i => (x i - y i).natAbs

/-- The box `Q(x,L)` of `sandpile.tex:680`:
`Q(x,L)\coloneqq \{y\in\Z^d:\max_{1\leq i\leq d}|y_i-x_i|\leq L\}`. -/
def boxAt {d : ℕ} (x : Site d) (L : ℝ) : Set (Site d) := {y | (boxDist y x : ℝ) ≤ L}

/-- `E u_t(0)`, the mean odometer at the origin for an i.i.d. scenery with
one-site law `ν`. -/
noncomputable def meanOdometerOf (d : ℕ) (ν : Measure ℝ) (t : ℕ) : ℝ :=
  ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)

end Sandpile.Frozen.DGT4Nontriviality

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_nontriviality
    (hBoundary : Sandpile.External.ExteriorBoundaryConnected)
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ ν₀ : ℝ, 0 < ν₀ →
      ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℕ, ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        evariance id ν < ⊤ → Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ t : ℕ, t₀ ≤ t →
          (∀ᵐ ζ ∂(LatticeProb.iidLaw d ν),
              Sandpile.HasInfiniteComponent
                {x | c * (Real.log t) ^ ((2 : ℝ) / d) < Sandpile.odometerOf ζ t x}) ∧
            ENNReal.ofReal (1 - C * Real.exp
                (-(b * Sandpile.Frozen.DGT4Nontriviality.meanOdometerOf d ν t))) ≤
              (LatticeProb.iidLaw d ν)
                {ζ | Sandpile.Frozen.DGT4Nontriviality.boxAt (0 : Sandpile.Site d) 1 ⊆
                      {x | Sandpile.Frozen.DGT4Nontriviality.meanOdometerOf d ν t / 2 <
                        Sandpile.odometerOf ζ t x} ∧
                    (LatticeProb.componentIn
                      {x | Sandpile.Frozen.DGT4Nontriviality.meanOdometerOf d ν t / 2 <
                        Sandpile.odometerOf ζ t x} (0 : Sandpile.Site d)).Infinite}
-- FROZEN-STATEMENT-END
:= by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨b, C, M, hb, hC, hM, hconn⟩ :=
    Sandpile.exists_odometer_origin_connection hBoundary hGreenHigh d hd θ₀ K₀ hθ₀
  refine ⟨b, C, hb, hC, ?_⟩
  intro ν₀ hν₀
  obtain ⟨a, q, ha, hq, hq1, htail⟩ := Sandpile.exists_uniform_left_tail ν₀ θ₀ K₀ hν₀ hθ₀
  obtain ⟨c₀, hc₀, t₁, hmeanlower⟩ := Sandpile.exists_mean_lower_uniform (d := d)
    (by omega) (by positivity) a q ha hq hq1
  let L := max M (Real.log (2 * C) / b)
  have hgrow : Tendsto (fun t : ℕ => c₀ * (Real.log t) ^ ((2 : ℝ) / d)) atTop atTop :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 2 / d)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop hc₀
  obtain ⟨t₂, ht₂⟩ := eventually_atTop.mp (hgrow.eventually_ge_atTop L)
  refine ⟨c₀ / 4, by positivity, max t₁ t₂, ?_⟩
  intro ν hν hmean hvarlow hvarfin hexp hK t ht
  letI := hν
  let m := ∫ ω, Sandpile.odometerOf ω t (0 : Sandpile.Site d) ∂(LatticeProb.iidLaw d ν)
  have hint := LatticeProb.integrable_id_of_exp_moment ν θ₀ hθ₀ hexp
  have hlow : c₀ * (Real.log t) ^ ((2 : ℝ) / d) ≤ m := hmeanlower ν hν hint hmean
    (htail ν hν hmean hvarlow hexp hK) t ((le_max_left _ _).trans ht)
  have hLm : L ≤ m := (ht₂ t ((le_max_right _ _).trans ht)).trans hlow
  have hmM : M ≤ m := (le_max_left _ _).trans hLm
  have hm1 : 1 ≤ m := hM.trans hmM
  have hvar : 0 < evariance id ν := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hν₀)).trans_le hvarlow
  have hcompl := hconn ν hν hmean hvar hvarfin hexp hK t hmM
  have hlower := Sandpile.origin_connection_lower_of_compl_le ν t (m / 2)
    (C * Real.exp (-(b * m))) (by positivity) hcompl
  have hlog : Real.log (2 * C) ≤ b * m := by
    have hh := (div_le_iff₀ hb).mp ((le_max_right _ _).trans hLm)
    linarith
  have hsmall : C * Real.exp (-(b * m)) ≤ (1 / 2 : ℝ) := by
    have hh := Real.exp_le_exp.mpr (neg_le_neg hlog)
    rw [Real.exp_neg (Real.log (2 * C)), Real.exp_log (by positivity : 0 < 2 * C)] at hh
    calc
      _ ≤ C * (2 * C)⁻¹ := mul_le_mul_of_nonneg_left hh hC.le
      _ = _ := by field_simp
  have hpos : 0 < (LatticeProb.iidLaw d ν) (Sandpile.odometerOriginConnectEvent (d := d) t (m / 2)) :=
    (ENNReal.ofReal_pos.mpr (by linarith : 0 < 1 - C * Real.exp (-(b * m)))).trans_le hlower
  have hperpos : 0 < (LatticeProb.iidLaw d ν)
      {ω | Sandpile.HasInfiniteComponent {x | m / 2 < Sandpile.odometerOf ω t x}} := by
    apply hpos.trans_le (measure_mono ?_)
    rintro ω ⟨hS, hi⟩
    refine ⟨0, hS ?_, hi⟩
    change (Sandpile.boxDist 0 0 : ℝ) ≤ 1
    simp [Sandpile.boxDist_self]
  have hae := Sandpile.ae_odometer_percolates_of_pos ν t (m / 2) hperpos
  refine ⟨?_, hlower⟩
  filter_upwards [hae] with ω hω
  apply Sandpile.hasInfiniteComponent_mono (T := {x | c₀ / 4 * (Real.log t) ^ ((2 : ℝ) / d) <
    Sandpile.odometerOf ω t x}) _ hω
  intro x hx
  have hlevel : c₀ / 4 * (Real.log t) ^ ((2 : ℝ) / d) ≤ m / 2 := by nlinarith
  exact hlevel.trans_lt hx
