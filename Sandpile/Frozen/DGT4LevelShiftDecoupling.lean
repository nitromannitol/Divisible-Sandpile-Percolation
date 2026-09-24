/-
Level-shift decoupling lemma of sandpile.tex, frozen.  `sandpile.tex:6472-6486`
(label `lem:dgt4-level-shift-decoupling`):

  "There are $c>0$ and $C<\infty$ such that the following holds. Let
   $x_1,x_2\in\Z^d$, let $L,r\geq1$, and suppose
   \[
     \min_{\substack{z_1\in Q(x_1,2L)\\ z_2\in Q(x_2,2L)}} |z_1-z_2|\geq4r\, .
   \]
   Then, for every $s>2a>0$,
   \[
     \P\bigl(A(x_1,L,s)\cap A(x_2,L,s)\bigr)\leq
     \left[\sup_{z\in\Z^d}\P\bigl(A(z,L,s-2a)\bigr)\right]^2
     +CL^d\exp\{-c\min(a^2r^{d-4}, ar^{d-2})\}\, ."

The standing hypotheses of Section `sec:dim5plus` (`sandpile.tex:4079`,
`sandpile.tex:4096-4108`) are in force: `d ≥ 5`, the scenery is i.i.d. with
`E ζ(0) = 0` and `0 < Var(ζ(0)) < ∞`, and `E e^{θ₀|ζ(0)|} ≤ K₀`.  The constants
`c` and `C` come from `lem:dgt4-localization` and a count of the sites of a box,
so they depend only on `d, θ₀, K₀`; they are bound after those and before the
law `ν`.
The event `A(x, L, s)` of `sandpile.tex:6416-6422` is transcribed below as
`lowCrossingEvent`.  It depends on the time `t` and on the number `E u_t(0)`;
`t` is bound before `x₁, x₂` and the mean is supplied as `meanOdometerOf d ν t`,
so that the definition itself mentions no measure.
The minimum over the two boxes is written as a universally quantified lower
bound, which is the same statement and avoids the junk value of an infimum over
an empty set.
Probabilities are the `ℝ≥0∞`-valued measure of the event, so the supremum over
`z` is a supremum in a complete lattice and carries no junk value; the additive
error term is nonnegative, so `ENNReal.ofReal` is exact.  Each event is
measurable: `u_t` depends on finitely many coordinates and the crossing set may
be taken inside the finite box `Q(x, 2L)`.

The exponential-moment bound is stated together with the integrability of the
exponential, as the paper's `K₀ < ∞` requires: the Bochner integral of a
non-integrable nonnegative function is zero, so the bound alone would hold for
every law with no exponential moment.
-/
import Sandpile.Walk
import Sandpile.External.GreenBoundsHigh
import Sandpile.Support.LevelShift
import Sandpile.Support.RealBoxes

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Frozen.DGT4LevelShiftDecoupling

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

end Sandpile.Frozen.DGT4LevelShiftDecoupling

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_level_shift_decoupling
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → 0 < evariance id ν → evariance id ν < ⊤ →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      ∀ (t : ℕ) (x₁ x₂ : Sandpile.Site d) (L r : ℝ), 1 ≤ L → 1 ≤ r →
      (∀ z₁ ∈ Sandpile.Frozen.DGT4LevelShiftDecoupling.boxAt x₁ (2 * L),
        ∀ z₂ ∈ Sandpile.Frozen.DGT4LevelShiftDecoupling.boxAt x₂ (2 * L),
          4 * r ≤ (Sandpile.Frozen.DGT4LevelShiftDecoupling.boxDist z₁ z₂ : ℝ)) →
      ∀ s a : ℝ, 0 < a → 2 * a < s →
        (LatticeProb.iidLaw d ν)
            (Sandpile.Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t
                (Sandpile.Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t) x₁ L s ∩
              Sandpile.Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t
                (Sandpile.Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t) x₂ L s) ≤
          (⨆ z : Sandpile.Site d, (LatticeProb.iidLaw d ν)
              (Sandpile.Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t
                (Sandpile.Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t) z L
                (s - 2 * a))) ^ 2 +
            ENNReal.ofReal (C * L ^ d *
              Real.exp (-(c * min (a ^ 2 * r ^ ((d : ℝ) - 4)) (a * r ^ ((d : ℝ) - 2)))))
-- FROZEN-STATEMENT-END
:= by
  classical
  obtain ⟨c, hc, hdec⟩ := Sandpile.odometer_sublevel_decoupling hGreenHigh d hd θ₀ K₀ hθ₀
  refine ⟨c, 8 * (5 : ℝ) ^ d, hc, by positivity, ?_⟩
  intro ν hν hmean hvp hvf hexp hK t x₁ x₂ L r hL hr hsep s a ha _hs
  haveI := hν
  have hL₂ : 0 ≤ 2 * L := by linarith
  let K := fun x : Sandpile.Site d => Sandpile.realBoxFinset x (2 * L)
  let m := Sandpile.Frozen.DGT4LevelShiftDecoupling.meanOdometerOf d ν t
  let W := fun (x : Sandpile.Site d) (T : Set (Sandpile.Site d)) =>
    ((Sandpile.Frozen.DGT4LevelShiftDecoupling.starLattice d).induce T).Connected ∧
    (T ∩ Sandpile.Frozen.DGT4LevelShiftDecoupling.boxAt x L).Nonempty ∧
    (T ∩ Sandpile.Frozen.DGT4LevelShiftDecoupling.innerBoundary
      (Sandpile.Frozen.DGT4LevelShiftDecoupling.boxAt x (2 * L))).Nonempty
  have hcross (x : Sandpile.Site d) (q : ℝ) :
      Sandpile.sublevelWitnessEvent (K x : Set (Sandpile.Site d)) (W x)
        (fun ω y => Sandpile.odometerOf ω t y - m) q =
      Sandpile.Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m x L q := by
    ext ω
    constructor
    · rintro ⟨T, hT, hW, hval⟩
      refine ⟨T, fun y hy => ?_, hW.1, hW.2.1, hW.2.2⟩
      exact ⟨(Sandpile.mem_realBoxFinset hL₂).mp (hT hy), hval y hy⟩
    · rintro ⟨T, hT, hconn, hin, hout⟩
      refine ⟨T, fun y hy => ?_, ⟨hconn, hin, hout⟩, fun y hy => (hT hy).2⟩
      exact (Sandpile.mem_realBoxFinset hL₂).mpr (hT hy).1
  have hdisj : Disjoint
      (Sandpile.Frozen.DGT4Localization.thickening (K x₁) r)
      (Sandpile.Frozen.DGT4Localization.thickening (K x₂) r) := by
    apply Sandpile.disjoint_thickening_of_separated _ _ r (by linarith)
    intro z₁ hz₁ z₂ hz₂
    exact hsep z₁ ((Sandpile.mem_realBoxFinset hL₂).mp hz₁)
      z₂ ((Sandpile.mem_realBoxFinset hL₂).mp hz₂)
  let p : ℝ≥0∞ := ⨆ z : Sandpile.Site d, (LatticeProb.iidLaw d ν)
    (Sandpile.Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m z L (s - 2 * a))
  have hp : p ≤ 1 := iSup_le fun _ => prob_le_one
  have hbound (x : Sandpile.Site d) :
      (LatticeProb.iidLaw d ν) (Sandpile.sublevelWitnessEvent
        (K x : Set (Sandpile.Site d)) (W x) (fun ω y => Sandpile.odometerOf ω t y - m)
        (s - 2 * a)) ≤ p := by
    rw [hcross]
    exact le_iSup (fun z : Sandpile.Site d => (LatticeProb.iidLaw d ν)
      (Sandpile.Frozen.DGT4LevelShiftDecoupling.lowCrossingEvent t m z L (s - 2 * a))) x
  have hh := hdec ν hν hmean hvp hvf hexp hK (K x₁) (K x₂) r a hr ha hdisj
    t m (W x₁) (W x₂) s p hp (hbound x₁) (hbound x₂)
  rw [hcross, hcross] at hh
  refine hh.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hcard₁ := Sandpile.card_realBoxFinset_two_le x₁ hL
  have hcard₂ := Sandpile.card_realBoxFinset_two_le x₂ hL
  have hcK : 4 * (((K x₁).card : ℝ) + (K x₂).card) ≤ (8 * (5 : ℝ) ^ d) * L ^ d := by
    dsimp [K]
    nlinarith
  exact mul_le_mul_of_nonneg_right hcK (Real.exp_pos _).le
