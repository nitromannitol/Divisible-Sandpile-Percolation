/-
Cascade lemma of sandpile.tex, frozen.  `sandpile.tex:6570-6579`
(label `lem:dgt4-cascade`):

  "There are $b,C>0$ and $M<\infty$ such that, whenever $\E u_t(0)\geq M$, for
   every $n\geq0$,
   \[
     \sup_{x\in\Z^d}\P\bigl(A(x,64^n,\E u_t(0)/2)\bigr)
     \leq C\exp\{-b\E u_t(0)2^n\}\, ."

The standing hypotheses of Section `sec:dim5plus` (`sandpile.tex:4079`,
`sandpile.tex:4096-4108`) are in force: `d ≥ 5`, the scenery is i.i.d. with
`E ζ(0) = 0` and `0 < Var(ζ(0)) < ∞`, and `E e^{θ₀|ζ(0)|} ≤ K₀`.  The constants
`b, C, M` come from the pointwise concentration estimate
`eq:dgt4-pointwise-concentration` and from `lem:dgt4-level-shift-decoupling`,
whose constants depend only on `d, θ₀, K₀`; they are bound after those and
before the law `ν`, matching the dependence recorded in
`thm:dgt4-nontriviality`, where the same `b` and `C` appear as
`b(d,θ₀,K₀)` and `C(d,θ₀,K₀)`.
The event `A(x, L, s)` of `sandpile.tex:6416-6422` is transcribed below as
`lowCrossingEvent`; each frozen file carries its own copy.  The scale `64^n`
and the factor `2^n` are read as real numbers.
The threshold `E u_t(0) ≥ M` is a hypothesis on `t`, so `t` is bound before `n`,
as in the paper.
Probabilities are the `ℝ≥0∞`-valued measure of the event, so the supremum over
`x` is a supremum in a complete lattice and carries no junk value; the
right-hand side is nonnegative, so `ENNReal.ofReal` is exact.

The exponential-moment bound is stated together with the integrability of the
exponential, as the paper's `K₀ < ∞` requires: the Bochner integral of a
non-integrable nonnegative function is zero, so the bound alone would hold for
every law with no exponential moment.
-/
import Sandpile.Walk
import Sandpile.External.GreenBoundsHigh
import Sandpile.Support.CascadeRecurrence
import Sandpile.Support.CascadeScales
import Sandpile.Support.DoubleExponential

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Frozen.DGT4Cascade

/-- The box metric of `sandpile.tex:6366-6368`: "All distances in this
subsection are measured in the box metric used to define $Q(x,L)$; in
particular, $|x-y|$ below denotes this distance." -/
def boxDist {d : ℕ} (x y : Site d) : ℕ :=
  Finset.univ.sup fun i => (x i - y i).natAbs

/-- The box `Q(x,L)` of `sandpile.tex:680`:
`Q(x,L)\coloneqq \{y\in\Z^d:\max_{1\leq i\leq d}|y_i-x_i|\leq L\}`. -/
def boxAt {d : ℕ} (x : Site d) (L : ℝ) : Set (Site d) := {y | (boxDist y x : ℝ) ≤ L}

/-- The `∗`-lattice of `sandpile.tex:6368-6369`: "A set is $\ast$-connected if
it is connected by steps that change each coordinate by at most one." -/
def starLattice (d : ℕ) : SimpleGraph (Site d) where
  Adj x y := x ≠ y ∧ ∀ i, (x i - y i).natAbs ≤ 1
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun i => by have := h.2 i; omega⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The inner vertex boundary of `sandpile.tex:6409-6411`: "For a finite
$B\subset\Z^d$, write
$\partial_{\rm in}B\coloneqq\{y\in B:\text{there is }z\notin B\text{ with }z\sim y\}$
for its inner vertex boundary." -/
def innerBoundary {d : ℕ} (B : Set (Site d)) : Set (Site d) :=
  {y | y ∈ B ∧ ∃ z, z ∉ B ∧ (lattice d).Adj z y}

/-- `E u_t(0)`, the mean odometer at the origin for an i.i.d. scenery with
one-site law `ν`. -/
noncomputable def meanOdometerOf (d : ℕ) (ν : Measure ℝ) (t : ℕ) : ℝ :=
  ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)

/-- The event `A(x,L,s)` of `sandpile.tex:6411-6417`: "For $L\geq1$ and $s>0$,
let $A(x,L,s)$ be the event that there is a $\ast$-connected subset of
$\{y\in Q(x,2L):u_t(y)-\E u_t(0)\leq -s\}$ meeting both $Q(x,L)$ and
$\partial_{\rm in}Q(x,2L)$."  The real `m` stands for `E u_t(0)`. -/
def lowCrossingEvent {d : ℕ} (t : ℕ) (m : ℝ) (x : Site d) (L s : ℝ) :
    Set (Site d → ℝ) :=
  {ζ | ∃ T : Set (Site d),
      T ⊆ {y | y ∈ boxAt x (2 * L) ∧ Sandpile.odometerOf ζ t y - m ≤ -s} ∧
      ((starLattice d).induce T).Connected ∧
      (T ∩ boxAt x L).Nonempty ∧
      (T ∩ innerBoundary (boxAt x (2 * L))).Nonempty}

end Sandpile.Frozen.DGT4Cascade

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_cascade
    (d : ℕ) (hd : 5 ≤ d) (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ b C M : ℝ, 0 < b ∧ 0 < C ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ t : ℕ, M ≤ Sandpile.Frozen.DGT4Cascade.meanOdometerOf d ν t → ∀ n : ℕ,
        (⨆ x : Sandpile.Site d, (LatticeProb.iidLaw d ν)
            (Sandpile.Frozen.DGT4Cascade.lowCrossingEvent t
              (Sandpile.Frozen.DGT4Cascade.meanOdometerOf d ν t) x ((64 : ℝ) ^ n)
              (Sandpile.Frozen.DGT4Cascade.meanOdometerOf d ν t / 2))) ≤
          ENNReal.ofReal (C * Real.exp
            (-(b * Sandpile.Frozen.DGT4Cascade.meanOdometerOf d ν t * (2 : ℝ) ^ n)))
-- FROZEN-STATEMENT-END
:= by
  classical
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  obtain ⟨c, C, hc, hC, hstep⟩ := Sandpile.exists_annular_probability_step hGreenHigh d hd θ₀ K₀ hθ₀
  obtain ⟨c₀, C₀, hc₀, hC₀, hinit⟩ := Sandpile.exists_annular_probability_initial hGreenHigh d hd θ₀ K₀ hθ₀
  obtain ⟨b, η, M, hb, hη, hM, hsolve⟩ := Sandpile.exists_double_exponential_bound
    c₀ C₀ (c / 256) C ((64 : ℝ) ^ d) hc₀ hC₀ (by positivity) hC
    (one_le_pow₀ (by norm_num))
  refine ⟨b, η, M, hb, hη, ?_⟩
  intro ν hν hmean hvp hvf hexp hK t hm n
  haveI := hν
  let m := Sandpile.Frozen.DGT4Cascade.meanOdometerOf d ν t
  have hmM : M ≤ m := hm
  have hm1 : 1 ≤ m := hM.trans hmM
  have hm0 : 0 < m := by linarith
  let q := fun k : ℕ => Sandpile.annularProbability (d := d) ν t m
    ((64 : ℕ) ^ k) (Sandpile.cascadeLevel m k)
  have hq₀ : q 0 ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ * m))) := by
    simpa only [q, pow_zero, Sandpile.cascadeLevel_zero, m,
      Sandpile.Frozen.DGT4Cascade.meanOdometerOf,
      Sandpile.Frozen.DGT4LevelShiftDecoupling.meanOdometerOf] using hinit ν hν hexp hK t hm1
  have hqstep (k : ℕ) : q (k + 1) ≤ ENNReal.ofReal C * q k ^ 2 +
      ENNReal.ofReal (C * ((64 : ℝ) ^ d) ^ k * Real.exp (-(c / 256 * m * (2 : ℝ) ^ k))) := by
    have hh := hstep ν hν hmean hvp hvf hexp hK t ((64 : ℕ) ^ k)
      (one_le_pow₀ (by norm_num)) (Sandpile.cascadeLevel m (k + 1)) (Sandpile.cascadeShift m k)
      (Sandpile.cascadeShift_pos hm0 k) (Sandpile.cascade_level_gap hm0 k)
    rw [← pow_succ', Sandpile.cascadeLevel_succ_sub] at hh
    push_cast at hh
    have hpow : ((64 : ℝ) ^ k) ^ d = ((64 : ℝ) ^ d) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k d]
    have he := Sandpile.cascade_exponent_lower hd hm1 k
    have hexp : Real.exp (-(c * min
        (Sandpile.cascadeShift m k ^ 2 * ((64 : ℝ) ^ k) ^ ((d : ℝ) - 4))
        (Sandpile.cascadeShift m k * ((64 : ℝ) ^ k) ^ ((d : ℝ) - 2)))) ≤
        Real.exp (-(c / 256 * m * (2 : ℝ) ^ k)) := by
      apply Real.exp_le_exp.mpr
      have hx := mul_le_mul_of_nonneg_left he hc.le
      nlinarith
    refine hh.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    rw [hpow]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hfinal := hsolve m hmM q hq₀ hqstep n
  have hmono := Sandpile.annularProbability_antitone_level (d := d) ν t m ((64 : ℕ) ^ n)
    (Sandpile.cascadeLevel_bounds hm0.le n).2
  have hh := hmono.trans hfinal
  have hcross (x : Sandpile.Site d) (L s : ℝ) :
      Sandpile.Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m x L s =
        Sandpile.Frozen.DGT4Cascade.lowCrossingEvent t m x L s := rfl
  simpa only [Sandpile.annularProbability, Nat.cast_pow, Nat.cast_ofNat, hcross, m] using hh
