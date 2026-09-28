import Sandpile.Support.LinMeanGradient
import Sandpile.Support.LinStationary
import LatticeProb.Support.Fubini

/-!
# Joint measurability of the survival indicator, and the Fubini exchange it makes possible

Step 1 of `lem:dgt4-linearization-from-survival` (`sandpile.tex:5680-5695`) reads
the mean odometer gradient as `∑_{j<n} E_0[1_{X_j=z} P(S_{n,j}(X)=1 | X)]`, which
exchanges the integral over the scenery with the integral over path space. The
exchange needs the survival indicator to be measurable in the PAIR `(σ, X)`, and
that is what is proved here: `S_{n,j}` is the product over the first `j+1` times
of the indicators `1_{u_{n-i}(X_i) > 0}`, each of which is the indicator of a set
of pairs cut out by the jointly measurable function `(σ, X) ↦ u_t(X_i)`. The
lattice is countable, so that function is measurable by the same argument as for
the localized odometer in `Support/MeanLocalization.lean`.

Since the survival indicator takes values in `{0,1}`, the exchange itself is the
elementary Fubini theorem for a bounded jointly measurable function of two
probability spaces, which is stated separately.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The odometer along a path is jointly measurable in the mass field and the path. -/
theorem measurable_uncurry_odometer_path (t i : ℕ) :
    Measurable fun p : (Site d → ℝ) × (ℕ → Site d) => odometer p.1 t (p.2 i) := by
  have hpair : Measurable fun p : (Site d → ℝ) × (ℕ → Site d) => (p.1, p.2 i) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
  have hcount : Measurable fun q : (Site d → ℝ) × Site d => odometer q.1 t q.2 :=
    measurable_from_prod_countable_left fun z => measurable_odometer t z
  exact hcount.comp hpair

/-- **The survival indicator is jointly measurable.**  `S_{n,j}` of
`sandpile.tex:5443-5446` is a measurable function of the pair `(σ, X)`. -/
theorem measurable_uncurry_survival (n j : ℕ) :
    Measurable fun p : (Site d → ℝ) × (ℕ → Site d) =>
      Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer p.1 (n - r) (Y r)}
        (fun _ => (1 : ℝ)) p.2 := by
  classical
  have hrw : (fun p : (Site d → ℝ) × (ℕ → Site d) =>
      Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer p.1 (n - r) (Y r)}
        (fun _ => (1 : ℝ)) p.2)
      = fun p : (Site d → ℝ) × (ℕ → Site d) => ∏ i ∈ Finset.range (j + 1),
          (if 0 < odometer p.1 (n - i) (p.2 i) then (1 : ℝ) else 0) := by
    funext p
    exact indicator_forall_eq_prod p.1 n j p.2
  rw [hrw]
  refine Finset.measurable_prod _ fun i _ => ?_
  have hset : MeasurableSet
      {p : (Site d → ℝ) × (ℕ → Site d) | 0 < odometer p.1 (n - i) (p.2 i)} :=
    measurableSet_lt measurable_const (measurable_uncurry_odometer_path (n - i) i)
  exact Measurable.ite hset measurable_const measurable_const

/-- The survival indicator takes values in `[0,1]`. -/
theorem abs_survival_le_one (σ : Site d → ℝ) (n j : ℕ) (X : ℕ → Site d) :
    |Set.indicator {Y : ℕ → Site d | ∀ r ≤ j, 0 < odometer σ (n - r) (Y r)}
      (fun _ => (1 : ℝ)) X| ≤ 1 := by
  rw [Set.indicator_apply]
  split <;> simp

end Sandpile
