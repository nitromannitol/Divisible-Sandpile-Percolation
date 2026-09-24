/-
The polynomially weighted envelope of the interpolated rescaled field, uniform in
the scale: for every accuracy there is an amplitude `K`, the same for every
scale, such that with that probability the field is bounded by `K(1+|y|)` on the
whole of `[0,T] × ℝ^d`.

This is the field half of the cutoff error of `sandpile.tex:1908-1921`, which
asks for "at most a fixed power of the radius, with summable failure
probabilities" on dyadic annuli.  The power is one and the failure probabilities
are summable because the box tail of `exists_box_tail` has the moment exponent
`p` as its tail exponent, and the boxes of side two centred at the points of the
lattice cover the space with multiplicity one: a shell of sup-radius `n` carries
at most `(2n+1)^d` of them, each failing with probability at most a constant
times `(1+n)^{-p}`, and `p > d+1` makes the sum finite.
-/
import Sandpile.Support.MainExplBoxTail
import Sandpile.Support.IncrementBall

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile.Frozen.HeatPotentialInvariance

variable {d : ℕ}

/-- The weight of the sup-radius `n` shell of the lattice: its cardinality against the tail
exponent. -/
theorem summable_shell_weight (d : ℕ) {p : ℝ} (hp : (d : ℝ) + 1 < p) :
    Summable (fun n : ℕ => (2 * (n : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ (-p)) := by
  have hbase : ∀ n : ℕ, (0:ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hcomp : ∀ n : ℕ, (2 * (n : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ (-p)
      ≤ (3 : ℝ) ^ d * ((n : ℝ) + 1) ^ ((d : ℝ) - p) := by
    intro n
    have h1 : (2 * (n : ℝ) + 1) ^ d ≤ (3 : ℝ) ^ d * ((n : ℝ) + 1) ^ d := by
      rw [← mul_pow]
      have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact pow_le_pow_left₀ (by positivity) (by linarith) d
    have h2 : ((n : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ (-p) = ((n : ℝ) + 1) ^ ((d : ℝ) - p) := by
      rw [← Real.rpow_natCast ((n : ℝ) + 1) d, ← Real.rpow_add (hbase n), sub_eq_add_neg]
    calc (2 * (n : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ (-p)
        ≤ ((3 : ℝ) ^ d * ((n : ℝ) + 1) ^ d) * ((n : ℝ) + 1) ^ (-p) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (hbase n).le _)
      _ = (3 : ℝ) ^ d * (((n : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ (-p)) := by ring
      _ = (3 : ℝ) ^ d * ((n : ℝ) + 1) ^ ((d : ℝ) - p) := by rw [h2]
  refine Summable.of_nonneg_of_le (fun n => by positivity) hcomp ?_
  refine Summable.mul_left _ ?_
  have hq : (1:ℝ) < p - (d : ℝ) := by linarith
  have hbasesum : Summable (fun n : ℕ => (((n : ℝ)) ^ (p - (d : ℝ)))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hq
  have hshift := hbasesum.comp_injective (add_left_injective 1)
  refine hshift.congr ?_
  intro n
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
  simp only [Function.comp_apply, hcast]
  rw [← Real.rpow_neg (hbase n).le, neg_sub]

/-- The point of `ℝ^d` at a lattice site. -/
noncomputable def latticePoint (v : Site d) : Sandpile.Continuum.Space d :=
  WithLp.toLp 2 (fun i : Fin d => ((v i : ℤ) : ℝ))

/-- The sup-radius `n` shell of the lattice, as a finset. -/
noncomputable def shellFinset (d : ℕ) (n : ℕ) : Finset (Site d) :=
  (boxFinset (0 : Site d) n).filter (fun v => boxDist (0 : Site d) v = n)

theorem mem_shellFinset (v : Site d) : v ∈ shellFinset d (boxDist (0 : Site d) v) := by
  classical
  refine Finset.mem_filter.mpr ⟨mem_boxFinset le_rfl, rfl⟩

theorem card_shellFinset_le (d n : ℕ) : (shellFinset d n).card ≤ (2 * n + 1) ^ d := by
  classical
  calc (shellFinset d n).card ≤ (boxFinset (0 : Site d) n).card := Finset.card_filter_le _ _
    _ = (2 * n + 1) ^ d := card_boxFinset _ _

/-- **The polynomially weighted envelope of the interpolated field, uniform in the scale.**
For every accuracy there is one amplitude `K`, the same at every scale, with which the field
is bounded by `K(1+|y|)` on the whole of `[0,T] × ℝ^d` outside an event of that probability. -/
theorem exists_global_envelope
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (p : ℝ) (hp : 2 ≤ p)
    (hpd : (d : ℝ) + 1 < p)
    (hq : ((d : ℝ) + 1) < p * min (1 - (d : ℝ) / 4) ((1 - θ) / 4))
    (T : ℝ) (hT : 0 ≤ T)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hint : Integrable (fun z => |z| ^ p) ν)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R →
      Sandpile.centeredMassLaw d ν
          {σ | ∃ r ∈ Set.Icc (0:ℝ) T, ∃ w : Sandpile.Continuum.Space d,
            K * (1 + ‖w‖) < |linInterp d R (Sandpile.scenery d σ) r w|}
        ≤ ENNReal.ofReal δ := by
  classical
  obtain ⟨B, hB0, hB⟩ := exists_box_tail hHK hd hd3 hθ0 hθ1 p hp hq T 1 hT zero_le_one ν
    hmean hint
  have hp0 : (0:ℝ) < p := by linarith
  have hsum := summable_shell_weight d hpd
  set S : ℝ := ∑' n : ℕ, (2 * (n : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ (-p) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by positivity
  set K₀ : ℝ := (B ^ p * S / δ + 1) ^ (1/p) with hK0def
  have hK00 : 0 < K₀ := Real.rpow_pos_of_pos (by positivity) _
  have hK0p : B ^ p * S / δ ≤ K₀ ^ p := by
    rw [hK0def, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    linarith
  have hK0pp : (0:ℝ) < K₀ ^ p := Real.rpow_pos_of_pos hK00 p
  refine ⟨3 * K₀, by positivity, ?_⟩
  intro R hR
  set E : Site d → Set (Site d → ℝ) := fun v =>
    {σ | ∃ u ∈ Set.Icc (boxLo d 1) (boxHi d T 1),
      K₀ * (1 + (boxDist (0 : Site d) v : ℝ)) < |piFieldAt d R (latticePoint v) u σ|} with hEdef
  have hcover : {σ : Site d → ℝ | ∃ r ∈ Set.Icc (0:ℝ) T, ∃ w : Sandpile.Continuum.Space d,
      3 * K₀ * (1 + ‖w‖) < |linInterp d R (Sandpile.scenery d σ) r w|}
      ⊆ ⋃ n : ℕ, ⋃ v ∈ shellFinset d n, E v := by
    rintro σ ⟨r, hr, w, hw⟩
    set v : Site d := fun i => ⌊w i⌋ with hvdef
    refine Set.mem_iUnion.mpr ⟨boxDist (0:Site d) v, Set.mem_iUnion₂.mpr ⟨v, mem_shellFinset v, ?_⟩⟩
    set u : Fin (d+1) → ℝ := Fin.cons r (fun j => w j - ((v j : ℤ) : ℝ)) with hudef
    have hfloor : ∀ j : Fin d, ((v j : ℤ) : ℝ) ≤ w j ∧ w j - 1 < ((v j : ℤ) : ℝ) := by
      intro j
      exact ⟨Int.floor_le (w j), by linarith [Int.lt_floor_add_one (w j)]⟩
    have hubox : u ∈ Set.Icc (boxLo d 1) (boxHi d T 1) := by
      refine (mem_box_iff T 1 u).mpr ⟨⟨?_, ?_⟩, fun j => ?_⟩
      · show (0:ℝ) ≤ r
        exact hr.1
      · show r ≤ T
        exact hr.2
      · have h := hfloor j
        constructor
        · show (-1:ℝ) ≤ w j - ((v j : ℤ) : ℝ)
          linarith [h.1]
        · show w j - ((v j : ℤ) : ℝ) ≤ 1
          linarith [h.2]
    have hval : piFieldAt d R (latticePoint v) u σ
        = linInterp d R (Sandpile.scenery d σ) r w := by
      have h1 : (ofPi (u + piShift (latticePoint v))).1 = r := by
        rw [ofPi_shift_fst]; rfl
      have h2 : (ofPi (u + piShift (latticePoint v))).2 = w := by
        ext j
        rw [ofPi_shift_snd]
        show u j.succ + ((v j : ℤ) : ℝ) = w j
        rw [hudef]
        simp only [Fin.cons_succ]
        ring
      rw [piFieldAt, piField, h1, h2]
    refine ⟨u, hubox, ?_⟩
    rw [hval]
    have hnv : (boxDist (0:Site d) v : ℝ) ≤ ‖w‖ + 2 := by
      have hN : boxDist (0:Site d) v ≤ ⌊‖w‖⌋₊ + 2 := by
        refine Finset.sup_le fun i _ => ?_
        have hwi : |w i| ≤ ‖w‖ := abs_coord_le_norm w i
        have hfl := hfloor i
        have hnw : ‖w‖ < (⌊‖w‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ‖w‖
        have habs : |((v i : ℤ) : ℝ)| ≤ ‖w‖ + 1 := by
          rw [abs_le]
          constructor
          · have := abs_le.mp hwi
            linarith [hfl.2, this.1]
          · have := abs_le.mp hwi
            linarith [hfl.1, this.2]
        have hcast : ((((0:Site d) i - v i).natAbs : ℕ) : ℝ) = |((v i : ℤ) : ℝ)| := by
          have : ((0:Site d) i - v i) = -(v i) := by simp
          rw [this, Int.natAbs_neg, Nat.cast_natAbs]
          simp
        have hlt : ((((0:Site d) i - v i).natAbs : ℕ) : ℝ) < ((⌊‖w‖⌋₊ + 2 : ℕ) : ℝ) := by
          rw [hcast]
          push_cast
          linarith
        exact_mod_cast le_of_lt (by exact_mod_cast hlt)
      calc (boxDist (0:Site d) v : ℝ) ≤ ((⌊‖w‖⌋₊ + 2 : ℕ) : ℝ) := by exact_mod_cast hN
        _ ≤ ‖w‖ + 2 := by push_cast; linarith [Nat.floor_le (norm_nonneg w)]
    have hstep : K₀ * (1 + (boxDist (0:Site d) v : ℝ)) ≤ 3 * K₀ * (1 + ‖w‖) := by
      have h0 : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
      nlinarith [hK00.le]
    linarith
  refine le_trans (measure_mono hcover) (le_trans (measure_iUnion_le _) ?_)
  set g : ℕ → ℝ := fun n => B ^ p / K₀ ^ p * ((2 * (n:ℝ) + 1) ^ d * ((n:ℝ) + 1) ^ (-p)) with hgdef
  have hterm : ∀ n : ℕ, Sandpile.centeredMassLaw d ν (⋃ v ∈ shellFinset d n, E v)
      ≤ ENNReal.ofReal (g n) := by
    intro n
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    have hpt : ∀ v ∈ shellFinset d n, Sandpile.centeredMassLaw d ν (E v)
        ≤ ENNReal.ofReal (B ^ p / K₀ ^ p * ((n:ℝ) + 1) ^ (-p)) := by
      intro v hv
      have hvn : boxDist (0:Site d) v = n := (Finset.mem_filter.mp hv).2
      have hΛ : 0 < K₀ * (1 + (n:ℝ)) := by positivity
      have h := hB R hR (latticePoint v) (K₀ * (1 + (boxDist (0:Site d) v : ℝ)))
        (by rw [hvn]; exact hΛ)
      refine le_trans h (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [hvn, Real.div_rpow hB0.le (by positivity), Real.mul_rpow hK00.le (by positivity)]
      rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1)]
      rw [div_mul_eq_div_div]
      rw [add_comm (1:ℝ) (n:ℝ)]
      field_simp
    calc ∑ v ∈ shellFinset d n, Sandpile.centeredMassLaw d ν (E v)
        ≤ ∑ _v ∈ shellFinset d n, ENNReal.ofReal (B ^ p / K₀ ^ p * ((n:ℝ) + 1) ^ (-p)) :=
          Finset.sum_le_sum hpt
      _ = (shellFinset d n).card • ENNReal.ofReal (B ^ p / K₀ ^ p * ((n:ℝ) + 1) ^ (-p)) := by
          rw [Finset.sum_const]
      _ ≤ ((2 * n + 1) ^ d) • ENNReal.ofReal (B ^ p / K₀ ^ p * ((n:ℝ) + 1) ^ (-p)) := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          exact mul_le_mul' (Nat.cast_le.mpr (card_shellFinset_le d n)) le_rfl
      _ = ENNReal.ofReal (g n) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            hgdef]
          congr 1
          push_cast
          ring
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  have hgsum : Summable g := hsum.mul_left _
  have hgnn : ∀ n, 0 ≤ g n := fun n => by
    rw [hgdef]; positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hgnn hgsum]
  refine ENNReal.ofReal_le_ofReal ?_
  have : ∑' n : ℕ, g n = B ^ p / K₀ ^ p * S := by
    rw [hgdef, hSdef]
    exact tsum_mul_left
  rw [this]
  rw [div_mul_eq_mul_div, div_le_iff₀ hK0pp]
  rw [div_le_iff₀ hδ] at hK0p
  nlinarith [hK0p]

end Sandpile.Support
