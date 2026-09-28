import Sandpile.Walk
import Sandpile.External.GreenBoundsHigh
import Sandpile.Support.AnnularPercolation
import Sandpile.Support.UniformTail
import Sandpile.Support.HeightLower

/-!
# High-dimensional critical percolation, frozen

High-dimensional critical percolation theorem of `sandpile.tex`, frozen (`sandpile.tex:6699-6721`,
label `thm:dgt4-nontriviality`): fixing `ν₀ > 0`, `θ₀ > 0`, `K₀ < ∞` and `d ≥ 5`, there are
`b, C > 0` depending only on `d, θ₀, K₀`, and `c, t₀ > 0` also depending on `ν₀`, such that for
every mean-zero i.i.d. field with variance at least `ν₀²` and exponential moment at most `K₀`, and
every `t ≥ t₀`, the level set `{x : u_t(x) > c(log t)^{2/d}}` contains an infinite
nearest-neighbor component almost surely, and `P(Q(0,1) ↔ ∞ in {x : u_t(x) > E u_t(0)/2}) ≥
1 - C exp(-b E u_t(0))`. `boxDist` and `boxAt` transcribe the box metric and box of
`sandpile.tex:680` and `6366-6368`, `meanOdometerOf` is `E u_t(0)` for the scenery law
`LatticeProb.iidLaw d ν`, and the infinite-component clause uses `Sandpile.HasInfiniteComponent`;
the probability bound is stated on `ℝ≥0∞`, so `ENNReal.ofReal` truncates a negative right side to
`0` without loss.
-/

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
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
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
  have hpos : 0 <
      (LatticeProb.iidLaw d ν) (Sandpile.odometerOriginConnectEvent (d := d) t (m / 2)) :=
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
