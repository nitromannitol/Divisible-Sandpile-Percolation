/-
The lattice side of the hypothesis `hQlim` of
`Sandpile.Support.heat_potential_fd_of_coeff`: the sums of squares of the
coefficients of the rescaled linear field, written as an exact double time sum
of transition probabilities.

The identity behind it is Fubini for the two walk times, with no error term:

  `∑_z g_k(x,z) g_{k'}(y,z) = ∑_{m<k} ∑_{n<k'} p_{m+n}(x,y)`,

the two-horizon form of `tsum_weightedKernel_mul_weightedKernel`.  The
coefficient `interpCoeff` is a finite combination, over the `2^d` corners of the
mesh cell and the two mesh times, of the rescaled truncated Green kernels, so
the doubled coefficient sum is the same finite combination of double time sums,
with the prefactor `R^{d-4}`.  What is left for the local central limit theorem
is then a statement about `R^{d-4} ∑_{m<⌊R^2 r⌋} ∑_{n<⌊R^2 r'⌋} p_{m+n}(x,y)`
alone, which `ssec:green-estimates` compares with the continuum double time
integral of `prop:dlt4-heat-potential-invariance`.
-/
import Sandpile.Support.ContWeightedCoeff
import Sandpile.Support.ContInterpSmall

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- **The doubled truncated Green kernel at two horizons is the double time sum
of transition probabilities.**  This is Fubini over the two walk times; the
two-horizon form of `tsum_weightedKernel_mul_weightedKernel`. -/
theorem tsum_greenTime_mul_greenTime (k k' : ℕ) (x y : Site d) :
    ∑' z : Site d, Sandpile.greenTime d k x z * Sandpile.greenTime d k' y z
      = ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k',
          Sandpile.heatKernel d (a + b) x y := by
  have hexp : ∀ z : Site d, Sandpile.greenTime d k x z * Sandpile.greenTime d k' y z
      = ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k',
          Sandpile.heatKernel d a x z * Sandpile.heatKernel d b y z := by
    intro z
    show (∑ a ∈ Finset.range k, Sandpile.heatKernel d a x z) *
      (∑ b ∈ Finset.range k', Sandpile.heatKernel d b y z) = _
    rw [Finset.sum_mul_sum]
  rw [tsum_congr hexp,
    Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.range k) =>
      summable_finsetSum (Finset.range k') fun b _ =>
        summable_heatKernel_mul a x (fun z => Sandpile.heatKernel d b y z))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Summable.tsum_finsetSum (fun b (_ : b ∈ Finset.range k') =>
    summable_heatKernel_mul a x (fun z => Sandpile.heatKernel d b y z))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hsy : ∀ z : Site d, Sandpile.heatKernel d a x z * Sandpile.heatKernel d b y z
      = Sandpile.heatKernel d a x z * Sandpile.heatKernel d b z y :=
    fun z => by rw [Sandpile.heatKernel_symm b y z]
  rw [tsum_congr hsy, tsum_heatKernel_mul_heatKernel a b x y]

/-- The multilinear interpolation weight of one corner of the mesh cell of `w`. -/
noncomputable def cornerWeight (d : ℕ) (R : ℝ) (w : Space d) (ε : Fin d → Bool) : ℝ :=
  ∏ i : Fin d, if ε i then R * w i - (⌊R * w i⌋ : ℝ)
    else 1 - (R * w i - (⌊R * w i⌋ : ℝ))

/-- The corner of the mesh cell of `w` indexed by `ε`. -/
noncomputable def cornerSite (d : ℕ) (R : ℝ) (w : Space d) (ε : Fin d → Bool) : Site d :=
  fun i => ⌊R * w i⌋ + if ε i then 1 else 0

theorem cornerSite_def (d : ℕ) (R : ℝ) (w : Space d) (ε : Fin d → Bool) :
    cornerSite d R w ε = fun i => ⌊R * w i⌋ + if ε i then 1 else 0 := rfl

/-- The weight of the later mesh time (`b = true`) and of the earlier one. -/
noncomputable def timeWeight (R r : ℝ) : Bool → ℝ
  | true => R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ)
  | false => 1 - (R ^ 2 * r - (⌊R ^ 2 * r⌋₊ : ℝ))

/-- The later and the earlier mesh time. -/
noncomputable def timeIndex (R r : ℝ) : Bool → ℕ
  | true => ⌊R ^ 2 * r⌋₊ + 1
  | false => ⌊R ^ 2 * r⌋₊

/-- The weight of one term of the interpolation: a corner and a mesh time. -/
noncomputable def interpTermWeight (d : ℕ) (R r : ℝ) (w : Space d)
    (p : (Fin d → Bool) × Bool) : ℝ :=
  cornerWeight d R w p.1 * timeWeight R r p.2

theorem interpCoeff_eq_sum (d : ℕ) (R r : ℝ) (w : Space d) (y : Site d) :
    interpCoeff d R r w y
      = ∑ p : (Fin d → Bool) × Bool, interpTermWeight d R r w p *
          (R ^ ((d : ℝ) / 2 - 2) *
            Sandpile.greenTime d (timeIndex R r p.2) (cornerSite d R w p.1) y) := by
  rw [interpCoeff, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Fintype.sum_bool]
  simp only [interpTermWeight, cornerWeight, cornerSite_def, timeWeight, timeIndex]
  ring

theorem tsum_interpCoeff_mul (d : ℕ) {R : ℝ} (hR : 0 < R) (r r' : ℝ) (w w' : Space d) :
    ∑' y : Site d, interpCoeff d R r w y * interpCoeff d R r' w' y
      = ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool,
          interpTermWeight d R r w p * interpTermWeight d R r' w' q *
            (R ^ ((d : ℝ) - 4) *
              ∑ m ∈ Finset.range (timeIndex R r p.2), ∑ n ∈ Finset.range (timeIndex R r' q.2),
                Sandpile.heatKernel d (m + n) (cornerSite d R w p.1) (cornerSite d R w' q.1)) := by
  have hpre : R ^ ((d : ℝ) / 2 - 2) * R ^ ((d : ℝ) / 2 - 2) = R ^ ((d : ℝ) - 4) := by
    rw [← Real.rpow_add hR]
    congr 1
    ring
  have hsum : ∀ p q : (Fin d → Bool) × Bool, Summable fun z : Site d =>
      interpTermWeight d R r w p * interpTermWeight d R r' w' q *
        (R ^ ((d : ℝ) - 4) *
          (Sandpile.greenTime d (timeIndex R r p.2) (cornerSite d R w p.1) z *
            Sandpile.greenTime d (timeIndex R r' q.2) (cornerSite d R w' q.1) z)) := by
    intro p q
    exact ((summable_greenTime_mul _ _ _).mul_left _).mul_left _
  have hpt : ∀ z : Site d, interpCoeff d R r w z * interpCoeff d R r' w' z
      = ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool,
          interpTermWeight d R r w p * interpTermWeight d R r' w' q *
            (R ^ ((d : ℝ) - 4) *
              (Sandpile.greenTime d (timeIndex R r p.2) (cornerSite d R w p.1) z *
                Sandpile.greenTime d (timeIndex R r' q.2) (cornerSite d R w' q.1) z)) := by
    intro z
    rw [interpCoeff_eq_sum d R r w z, interpCoeff_eq_sum d R r' w' z, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← hpre]
    ring
  rw [tsum_congr hpt,
    Summable.tsum_finsetSum (fun p (_ : p ∈ (Finset.univ : Finset ((Fin d → Bool) × Bool))) =>
      summable_finsetSum _ fun q _ => hsum p q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Summable.tsum_finsetSum (fun q (_ : q ∈ (Finset.univ : Finset ((Fin d → Bool) × Bool))) =>
    hsum p q)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [tsum_mul_left, tsum_mul_left, tsum_greenTime_mul_greenTime]

theorem interpCoeff_eq_zero_of_notMem (d : ℕ) (R r : ℝ) (w : Space d) {s : Finset (Site d)}
    (hs : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (cornerSite d R w ε) (⌊R ^ 2 * r⌋₊ + 1) ⊆ s)
    {z : Site d} (hz : z ∉ s) : interpCoeff d R r w z = 0 := by
  rw [interpCoeff_eq_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hg : Sandpile.greenTime d (timeIndex R r p.2) (cornerSite d R w p.1) z = 0 := by
    by_contra hne
    have hb := Sandpile.greenTime_support (timeIndex R r p.2) (cornerSite d R w p.1) hne
    have hb' : Sandpile.boxDist (cornerSite d R w p.1) z ≤ timeIndex R r p.2 := hb
    have hle : timeIndex R r p.2 ≤ ⌊R ^ 2 * r⌋₊ + 1 := by
      cases hp : p.2 <;> simp [timeIndex]
    exact hz (hs p.1 (Sandpile.mem_boxFinset (le_trans hb' hle)))
  rw [hg]
  ring

theorem sum_siteEnum_interpCoeff_mul (d : ℕ) (R r r' : ℝ) (w w' : Space d)
    {s : Finset (Site d)}
    (hs : ∀ ε : Fin d → Bool,
      Sandpile.boxFinset (cornerSite d R w ε) (⌊R ^ 2 * r⌋₊ + 1) ⊆ s) :
    ∑ k : Fin s.card, interpCoeff d R r w (siteEnum s k) * interpCoeff d R r' w' (siteEnum s k)
      = ∑' z : Site d, interpCoeff d R r w z * interpCoeff d R r' w' z := by
  rw [sum_siteEnum s fun z => interpCoeff d R r w z * interpCoeff d R r' w' z]
  refine (tsum_eq_sum fun z hz => ?_).symm
  rw [interpCoeff_eq_zero_of_notMem d R r w hs hz, zero_mul]

/-- **The sums of squares of the coefficients of the rescaled linear field, expanded
into the matrix of doubled coefficient sums.**  This is the left-hand side of the
hypothesis `hQlim` of `Sandpile.Support.heat_potential_fd_of_coeff`. -/
theorem sum_siteEnum_interp_sq (d : ℕ) (R : ℝ) {m : ℕ} (r : Fin m → ℝ) (w : Fin m → Space d)
    {s : Finset (Site d)}
    (hs : ∀ (i : Fin m) (ε : Fin d → Bool),
      Sandpile.boxFinset (cornerSite d R (w i) ε) (⌊R ^ 2 * r i⌋₊ + 1) ⊆ s)
    (t : Fin m → ℝ) :
    ∑ k : Fin s.card, (∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum s k)) ^ 2
      = ∑ i, ∑ j, t i * t j *
          ∑' z : Site d, interpCoeff d R (r i) (w i) z * interpCoeff d R (r j) (w j) z := by
  have hexp : ∀ k : Fin s.card, (∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum s k)) ^ 2
      = ∑ i, ∑ j, t i * t j * (interpCoeff d R (r i) (w i) (siteEnum s k) *
          interpCoeff d R (r j) (w j) (siteEnum s k)) := by
    intro k
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hexp k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, sum_siteEnum_interpCoeff_mul d R (r i) (r j) (w i) (w j) (hs i)]

/-- **The left-hand side of `hQlim` as a finite combination of double time sums of
transition probabilities.**  Nothing analytic is left in it: the interpolation
weights are explicit, and what the local central limit theorem has to control is the
single quantity `R^{d-4} ∑_{m<k} ∑_{n<k'} p_{m+n}(x,y)`. -/
theorem sum_interp_sq_eq (d : ℕ) {R : ℝ} (hR : 0 < R) (L : ℝ) {m : ℕ} (r : Fin m → ℝ)
    (w : Fin m → Space d) (hw : ∀ i, ‖w i‖ ≤ L) (t : Fin m → ℝ) :
    ∑ k : Fin (interpBox d R L r).card,
        (∑ i, t i * interpCoeff d R (r i) (w i) (siteEnum (interpBox d R L r) k)) ^ 2
      = ∑ i, ∑ j, t i * t j *
          ∑ p : (Fin d → Bool) × Bool, ∑ q : (Fin d → Bool) × Bool,
            interpTermWeight d R (r i) (w i) p * interpTermWeight d R (r j) (w j) q *
              (R ^ ((d : ℝ) - 4) *
                ∑ a ∈ Finset.range (timeIndex R (r i) p.2),
                  ∑ b ∈ Finset.range (timeIndex R (r j) q.2),
                    Sandpile.heatKernel d (a + b) (cornerSite d R (w i) p.1)
                      (cornerSite d R (w j) q.1)) := by
  have hs : ∀ (i : Fin m) (ε : Fin d → Bool),
      Sandpile.boxFinset (cornerSite d R (w i) ε) (⌊R ^ 2 * r i⌋₊ + 1)
        ⊆ interpBox d R L r := fun i ε => interp_box_subset_max R L r w hw i ε
  rw [sum_siteEnum_interp_sq d R r w hs t]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_interpCoeff_mul d hR (r i) (r j) (w i) (w j)]

/-- The two time weights of one mesh point sum to one. -/
theorem sum_timeWeight (R r : ℝ) : ∑ b : Bool, timeWeight R r b = 1 := by
  rw [Fintype.sum_bool]
  simp only [timeWeight]
  ring

/-- The two time weights are nonnegative. -/
theorem timeWeight_nonneg {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (b : Bool) :
    0 ≤ timeWeight R r b := by
  obtain ⟨h0, h1⟩ := interp_time_weight_mem hR hr
  cases b <;> simp only [timeWeight] <;> linarith

/-- The multilinear interpolation weights of one mesh cell sum to one. -/
theorem sum_cornerWeight (d : ℕ) (R : ℝ) (w : Space d) :
    ∑ ε : Fin d → Bool, cornerWeight d R w ε = 1 :=
  sum_interp_weights d (fun i => R * w i - (⌊R * w i⌋ : ℝ))

/-- The multilinear interpolation weights are nonnegative. -/
theorem cornerWeight_nonneg (d : ℕ) (R : ℝ) (w : Space d) (ε : Fin d → Bool) :
    0 ≤ cornerWeight d R w ε := by
  refine Finset.prod_nonneg fun i _ => ?_
  have h1 : ((⌊R * w i⌋ : ℤ) : ℝ) ≤ R * w i := Int.floor_le _
  have h2 : R * w i < ((⌊R * w i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  split <;> linarith

/-- **The weights of the interpolation are a probability vector.**  Over the `2^d`
corners of the mesh cell and the two mesh times they are nonnegative and sum to one,
so the coefficient of the rescaled linear field is a convex combination of rescaled
truncated Green kernels, and the doubled coefficient sum is the matching convex
combination of double time sums. -/
theorem sum_interpTermWeight (d : ℕ) (R r : ℝ) (w : Space d) :
    ∑ p : (Fin d → Bool) × Bool, interpTermWeight d R r w p = 1 := by
  rw [Fintype.sum_prod_type]
  have h : ∀ ε : Fin d → Bool, ∑ b : Bool, interpTermWeight d R r w (ε, b)
      = cornerWeight d R w ε := by
    intro ε
    show ∑ b : Bool, cornerWeight d R w ε * timeWeight R r b = cornerWeight d R w ε
    rw [← Finset.mul_sum, sum_timeWeight, mul_one]
  rw [Finset.sum_congr rfl fun ε _ => h ε, sum_cornerWeight]

theorem interpTermWeight_nonneg {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (d : ℕ) (w : Space d)
    (p : (Fin d → Bool) × Bool) : 0 ≤ interpTermWeight d R r w p :=
  mul_nonneg (cornerWeight_nonneg d R w p.1) (timeWeight_nonneg hR hr p.2)

end Sandpile.Support
