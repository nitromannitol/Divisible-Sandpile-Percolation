import Sandpile.External.GreenBoundsHigh

/-!
# The second intersection moment of two independent random walks

`interCount` is the `ℝ≥0∞`-valued count of intersections of two paths,
`∑_{i,j} 1_{X_i=Y_j}`, kept infinite-valued so that two paths agreeing at infinitely many time
pairs are not rounded to a junk value.  `Sandpile.External.IntersectionSecondMoment` transcribes
the second intersection estimate of Lawler (*Intersections of Random Walks*, 1991, Theorem 3.3.2
and Proposition 3.2.1): in dimensions `d ≥ 5`, the second moment of the intersection count of two
independent simple random walks started at `x` and `y` is at most `C(1+|x-y|)^{4-d}`.  It is
proved unconditionally in `Sandpile.External.IntersectionSecondMomentProved`.
-/

open MeasureTheory
open scoped ENNReal

namespace Sandpile.External

/-- `I(X,Y) = ∑_{i,j\geq0}\one_{\{X_i=Y_j\}}`, the number of intersections of
two paths, counted with multiplicity in the pair of times and valued in `ℝ≥0∞`
so that an infinite count is not rounded to a junk value. -/
noncomputable def interCount {d : ℕ} (X Y : ℕ → Sandpile.Site d) : ℝ≥0∞ :=
  ∑' p : ℕ × ℕ, Set.indicator {q : ℕ × ℕ | X q.1 = Y q.2} (fun _ => (1 : ℝ≥0∞)) p

end Sandpile.External

-- No longer a frozen node's own file: the second intersection estimate is proved,
-- unconditionally, in `Sandpile.External.IntersectionSecondMomentProved`; this `Prop`'s
-- body is retained byte-for-byte as the statement that theorem discharges.
/-- The second intersection estimate `eq:dgt4-intersection-second-moment`
(`sandpile.tex:1318-1323`): in dimensions `d ≥ 5` the second moment of the
number of intersections of two independent simple random walks started at `x`
and `y` is at most `C(1+|x-y|)^{4-d}`.  Assumed, not proved. -/
def Sandpile.External.IntersectionSecondMoment : Prop :=
  ∀ d : ℕ, 5 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : Sandpile.Site d,
        (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2
            ∂(Sandpile.walkLaw d y) ∂(Sandpile.walkLaw d x)) ≤
          ENNReal.ofReal (C * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
