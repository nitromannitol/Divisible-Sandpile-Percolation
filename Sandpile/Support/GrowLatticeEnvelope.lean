import Sandpile.Support.GrowBoxTail
import Sandpile.Support.MainExplLattice

/-!
# An almost-sure linear envelope for the continuous potential

Runs a Borel-Cantelli argument over the shells of the integer lattice to show that the
continuous version of the Gaussian heat potential has, almost surely, a random linear envelope
on every strip `[0, T] × ℝ^d`. The construction covers `ℝ^d` by the unit boxes centred at the
points of `ℤ^d`, exactly as `Sandpile.Support.exists_global_envelope` covers it for the discrete
interpolated field, and reuses that module's combinatorics `shellFinset` and
`summable_shell_weight`. Because the potential's box tail `exists_potential_box_tail` is uniform
in the box's centre and carries no scale parameter, the amplitude of the Borel-Cantelli events
can be read off directly, with no need to solve for a threshold amplitude at a target accuracy
first.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- The continuous version, read as a function of the space point directly
(rather than its raw coordinates). -/
noncomputable def zField {ΩW : Type*} (Y : ℝ × (Fin d → ℝ) → ΩW → ℝ) (t : ℝ) (x : Space d)
    (ω : ΩW) : ℝ :=
  Y (t, fun i => x i) ω

/-- **The lattice event at radius `n` covers the growth event at amplitude `3n`.**
This is the shell decomposition of `Sandpile.Support.exists_global_envelope`,
transposed from the interpolated discrete field to the continuous potential. -/
theorem exists_ae_linear_envelope (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {T : ℝ} (hT : 0 < T) {ΩW : Type} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    (Y : ℝ × (Fin d → ℝ) → ΩW → ℝ) (hYmeas : ∀ z, Measurable (Y z))
    (hYmod : ∀ z : ℝ × (Fin d → ℝ), z.1 ∈ Set.Icc (0 : ℝ) T →
      Y z =ᵐ[PW] fun ω => gaussianPotential d ν2 W z.1 (WithLp.toLp 2 z.2) ω)
    (hYcont : ∀ ω, Continuous fun z => Y z ω) :
    ∀ᵐ ω ∂PW, ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Space d,
      |zField Y t x ω| ≤ C * (1 + ‖x‖) := by
  classical
  obtain ⟨B, hB0, hB⟩ := exists_potential_box_tail hd hd3 hν2 hT PW W hW Y hYmeas hYmod hYcont
  set p : ℝ := 8 * ((d : ℝ) + 2) with hpdef
  have hp0 : (0 : ℝ) < p := by rw [hpdef]; positivity
  have hpd : (d : ℝ) + 1 < p := by rw [hpdef]; have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d; linarith
  have hsum := summable_shell_weight d hpd
  set S : ℝ := ∑' n : ℕ, (2 * (n : ℝ) + 1) ^ d * ((n : ℝ) + 1) ^ (-p) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by positivity
  -- The Borel-Cantelli events, indexed by the amplitude `m`.
  set G : ℕ → Set ΩW := fun m =>
    {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, ∃ x : Space d,
      3 * ((m : ℝ) + 1) * (1 + ‖x‖) < |zField Y t x ω|} with hGdef
  set E : ℕ → Site d → Set ΩW := fun m v =>
    {ω | ∃ u ∈ Set.Icc (boxLo d 1) (boxHi d T 1),
      ((m : ℝ) + 1) * (1 + (boxDist (0 : Site d) v : ℝ)) < |piPotential Y (latticePoint v) u ω|}
    with hEdef
  have hcover : ∀ m : ℕ, G m ⊆ ⋃ n : ℕ, ⋃ v ∈ shellFinset d n, E m v := by
    intro m
    rintro ω ⟨t, ht, x, hx⟩
    set v : Site d := fun i => ⌊x i⌋ with hvdef
    refine Set.mem_iUnion.mpr ⟨boxDist (0 : Site d) v,
      Set.mem_iUnion₂.mpr ⟨v, mem_shellFinset v, ?_⟩⟩
    set u : Fin (d + 1) → ℝ := Fin.cons t (fun j => x j - ((v j : ℤ) : ℝ)) with hudef
    have hfloor : ∀ j : Fin d, ((v j : ℤ) : ℝ) ≤ x j ∧ x j - 1 < ((v j : ℤ) : ℝ) := by
      intro j
      exact ⟨Int.floor_le (x j), by linarith [Int.lt_floor_add_one (x j)]⟩
    have hubox : u ∈ Set.Icc (boxLo d 1) (boxHi d T 1) := by
      refine (mem_box_iff T 1 u).mpr ⟨⟨?_, ?_⟩, fun j => ?_⟩
      · show (0 : ℝ) ≤ t; exact ht.1
      · show t ≤ T; exact ht.2
      · have h := hfloor j
        constructor
        · show (-1 : ℝ) ≤ x j - ((v j : ℤ) : ℝ); linarith [h.1]
        · show x j - ((v j : ℤ) : ℝ) ≤ 1; linarith [h.2]
    have hval : piPotential Y (latticePoint v) u = zField Y t x := by
      funext ω
      show Y (u 0, fun j => u j.succ + latticePoint v j) ω = Y (t, fun i => x i) ω
      have h1 : u 0 = t := rfl
      have h2 : (fun j : Fin d => u j.succ + latticePoint v j) = fun i => x i := by
        funext j
        show (x j - ((v j : ℤ) : ℝ)) + latticePoint v j = x j
        have hlv : latticePoint v j = ((v j : ℤ) : ℝ) := rfl
        rw [hlv]; ring
      rw [h1, h2]
    refine ⟨u, hubox, ?_⟩
    rw [hval]
    have hnv : (boxDist (0 : Site d) v : ℝ) ≤ ‖x‖ + 2 := by
      have hN : boxDist (0 : Site d) v ≤ ⌊‖x‖⌋₊ + 2 := by
        refine Finset.sup_le fun i _ => ?_
        have hxi : |x i| ≤ ‖x‖ := abs_coord_le_norm x i
        have hfl := hfloor i
        have hnw : ‖x‖ < (⌊‖x‖⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ‖x‖
        have habs : |((v i : ℤ) : ℝ)| ≤ ‖x‖ + 1 := by
          rw [abs_le]
          constructor
          · have := abs_le.mp hxi; linarith [hfl.2, this.1]
          · have := abs_le.mp hxi; linarith [hfl.1, this.2]
        have hcast : ((((0 : Site d) i - v i).natAbs : ℕ) : ℝ) = |((v i : ℤ) : ℝ)| := by
          have hz : ((0 : Site d) i - v i) = -(v i) := by simp
          rw [hz, Int.natAbs_neg, Nat.cast_natAbs]; simp
        have hlt : ((((0 : Site d) i - v i).natAbs : ℕ) : ℝ) < ((⌊‖x‖⌋₊ + 2 : ℕ) : ℝ) := by
          rw [hcast]; push_cast; linarith
        exact_mod_cast le_of_lt (by exact_mod_cast hlt)
      calc (boxDist (0 : Site d) v : ℝ) ≤ ((⌊‖x‖⌋₊ + 2 : ℕ) : ℝ) := by exact_mod_cast hN
        _ ≤ ‖x‖ + 2 := by push_cast; linarith [Nat.floor_le (norm_nonneg x)]
    have hm1 : (0:ℝ) ≤ (m:ℝ) + 1 := by positivity
    nlinarith [hx, hnv, hm1, norm_nonneg x]
  have hterm : ∀ m n : ℕ, PW (⋃ v ∈ shellFinset d n, E m v)
      ≤ ENNReal.ofReal ((B / ((m : ℝ) + 1)) ^ p * ((2 * (n:ℝ) + 1) ^ d * ((n:ℝ)+1) ^ (-p))) := by
    intro m n
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    have hpt : ∀ v ∈ shellFinset d n, PW (E m v)
        ≤ ENNReal.ofReal ((B / ((m:ℝ)+1)) ^ p * ((n:ℝ)+1) ^ (-p)) := by
      intro v hv
      have hvn : boxDist (0 : Site d) v = n := (Finset.mem_filter.mp hv).2
      have hΛ : 0 < ((m:ℝ)+1) * (1 + (n:ℝ)) := by positivity
      have h := hB (latticePoint v) (((m:ℝ)+1) * (1 + (boxDist (0:Site d) v : ℝ)))
        (by rw [hvn]; exact hΛ)
      refine le_trans h (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [hvn, Real.div_rpow hB0.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
        Real.div_rpow hB0.le (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ (n:ℝ)+1),
        add_comm (1:ℝ) (n:ℝ), div_mul_eq_div_div, div_eq_mul_inv]
    calc ∑ v ∈ shellFinset d n, PW (E m v)
        ≤ ∑ _v ∈ shellFinset d n, ENNReal.ofReal ((B / ((m:ℝ)+1)) ^ p * ((n:ℝ)+1) ^ (-p)) :=
          Finset.sum_le_sum hpt
      _ = (shellFinset d n).card • ENNReal.ofReal ((B / ((m:ℝ)+1)) ^ p * ((n:ℝ)+1) ^ (-p)) := by
          rw [Finset.sum_const]
      _ ≤ ((2 * n + 1) ^ d) • ENNReal.ofReal ((B / ((m:ℝ)+1)) ^ p * ((n:ℝ)+1) ^ (-p)) := by
          rw [nsmul_eq_mul, nsmul_eq_mul]
          exact mul_le_mul' (Nat.cast_le.mpr (card_shellFinset_le d n)) le_rfl
      _ = ENNReal.ofReal ((B / ((m:ℝ)+1)) ^ p * ((2 * (n:ℝ) + 1) ^ d * ((n:ℝ)+1) ^ (-p))) := by
          rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; push_cast; ring
  have hGm : ∀ m : ℕ, PW (G m) ≤ ENNReal.ofReal ((B / ((m:ℝ)+1)) ^ p * S) := by
    intro m
    refine le_trans (measure_mono (hcover m)) (le_trans (measure_iUnion_le _) ?_)
    refine le_trans (ENNReal.tsum_le_tsum (hterm m)) ?_
    have hgnn : ∀ n : ℕ, (0:ℝ) ≤ (B / ((m:ℝ)+1)) ^ p * ((2*(n:ℝ)+1)^d * ((n:ℝ)+1)^(-p)) := by
      intro n; positivity
    rw [← ENNReal.ofReal_tsum_of_nonneg hgnn (hsum.mul_left _)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [hSdef, tsum_mul_left]
  have hGsum : ∑' m : ℕ, PW (G m) ≠ ⊤ := by
    have hbound : ∀ m : ℕ, PW (G m) ≤ ENNReal.ofReal (B ^ p * S / ((m:ℝ)+1) ^ p) := by
      intro m
      refine le_trans (hGm m) (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [Real.div_rpow hB0.le (by positivity)]; ring
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    have hpsum : Summable (fun m : ℕ => B ^ p * S / ((m:ℝ)+1) ^ p) := by
      apply Summable.mul_left
      have h1 : (1:ℝ) < p := by rw [hpdef]; have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d; linarith
      have h2 : Summable (fun m : ℕ => (((m:ℝ)+1) ^ p)⁻¹) := by
        have := Real.summable_nat_rpow_inv.mpr h1
        have hshift := this.comp_injective (add_left_injective 1)
        refine hshift.congr fun m => ?_
        have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
        simp only [Function.comp_apply, hcast]
      simpa [div_eq_mul_inv] using h2
    have := ENNReal.ofReal_tsum_of_nonneg
      (fun m => by positivity : ∀ m : ℕ, (0:ℝ) ≤ B ^ p * S / ((m:ℝ)+1) ^ p) hpsum
    rw [← this]
    exact ENNReal.ofReal_ne_top
  have hae := MeasureTheory.ae_eventually_notMem (μ := PW) hGsum
  filter_upwards [hae] with ω hω
  obtain ⟨m, hm⟩ := hω.exists
  refine ⟨3 * ((m:ℝ)+1), fun t ht x => ?_⟩
  by_contra hcon
  exact hm ⟨t, ht, x, not_le.mp hcon⟩

end Sandpile.Support
