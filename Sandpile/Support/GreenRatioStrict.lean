/-
The Green ratio of the simple random walk is STRICTLY less than one.

`LatticeProb.greenRatioSup d` is the paper's `ℓ₀ = sup_{x ≠ 0} G(0,x)/G(0,0)`.
The shared library proves `ℓ₀ ≤ 1`.  The band construction needs the strict
inequality, and needs it for a reason that is not cosmetic: the gap condition
between the tail rate and the exponential moment forces `ℓ₀ < ℓ₁ < 1`, so if the
ratio could equal one the band estimates would hold vacuously.

The proof is a maximum principle along a ray.  If the supremum were one, some
site off the origin would attain the value at the origin; harmonicity then
propagates that value along a coordinate ray, contradicting the decay of the
Green function at infinity.

Stated in the `LatticeProb` namespace, mentioning no object of this paper, so it
can move to the shared library unchanged when that library is next revised.
-/
import Sandpile.Support.Dgt4ABandConcentration

open Filter
open scoped Topology

namespace LatticeProb

/-- The paper's `ℓ₀ := sup_{x≠0} G(0,x)/G(0,0) < 1`, by the maximum principle along a ray. -/
theorem greenRatioSup_lt_one {d : ℕ} (hd : 3 ≤ d) : greenRatioSup d < 1 := by
  classical
  have hd0 : 0 < d := by omega
  set G := srwGreenInf d with hGdef
  have hG0 : 1 ≤ G 0 := one_le_srwGreenInf_origin hd
  have hG0pos : 0 < G 0 := lt_of_lt_of_le zero_lt_one hG0
  have hle : ∀ x, G x ≤ G 0 := by
    intro x
    have h := srwHitProb_le_one hd0 x
    rw [srwHitProb_eq_green_ratio hd, div_le_one hG0pos] at h
    exact h
  haveI := nonempty_nonzero_site hd0
  by_contra hcon
  have hge1 : 1 ≤ greenRatioSup d := not_lt.mp hcon
  -- decay
  obtain ⟨R, hR1, hR0⟩ := tendsto_srwGreenInf_zero hd (ε := G 0 / 2) (by positivity)
  have hR : ∀ x : Site d, R ≤ graphNorm x → G x ≤ G 0 / 2 := hR0
  have hfar : ∀ x : Site d, x ∉ boxFinset (0 : Site d) R → G x ≤ G 0 / 2 := fun x hx =>
    hR x (le_graphNorm_of_notMem_boxFinset hx)
  -- the sup is a max over the finite box
  set F : Finset (Site d) := (boxFinset (0 : Site d) R).filter (fun x => x ≠ 0) with hF
  have hsup : ∀ M : ℝ, (∀ z : Site d, z ≠ 0 → G z ≤ M) → greenRatioSup d ≤ M / G 0 := by
    intro M hM
    refine ciSup_le fun z => ?_
    rw [srwHitProb_eq_green_ratio hd]
    exact div_le_div_of_nonneg_right (hM z z.2) hG0pos.le
  have hstar : ∃ z : Site d, z ≠ 0 ∧ G z = G 0 := by
    by_cases hFne : F.Nonempty
    · obtain ⟨z, hzF, hzmax⟩ := Finset.exists_max_image F G hFne
      have hzne : z ≠ 0 := (Finset.mem_filter.mp hzF).2
      have hM : ∀ y : Site d, y ≠ 0 → G y ≤ max (G z) (G 0 / 2) := by
        intro y hy
        by_cases hyF : y ∈ F
        · exact (hzmax y hyF).trans (le_max_left _ _)
        · have : y ∉ boxFinset (0 : Site d) R := fun h => hyF (Finset.mem_filter.mpr ⟨h, hy⟩)
          exact (hfar y this).trans (le_max_right _ _)
      have h1 := (hge1.trans (hsup _ hM))
      rw [le_div_iff₀ hG0pos, one_mul] at h1
      have h2 : G 0 ≤ G z := by
        rcases le_max_iff.mp h1 with h | h
        · exact h
        · linarith
      exact ⟨z, hzne, le_antisymm (hle z) h2⟩
    · exfalso
      have hM : ∀ y : Site d, y ≠ 0 → G y ≤ G 0 / 2 := by
        intro y hy
        refine hfar y fun h => hFne ⟨y, Finset.mem_filter.mpr ⟨h, hy⟩⟩
      have h1 := hge1.trans (hsup _ hM)
      rw [le_div_iff₀ hG0pos] at h1
      linarith
  obtain ⟨z, hzne, hz⟩ := hstar
  -- harmonic propagation
  have hprop : ∀ x : Site d, x ≠ 0 → G x = G 0 → ∀ j : Fin d,
      G (x + unit j) = G 0 ∧ G (x - unit j) = G 0 := by
    intro x hx hxg
    have hharm := walkOp_srwGreenInf_of_ne hd hx
    rw [walkOp, div_eq_iff (by positivity)] at hharm
    change nbrSum G x = G x * (2 * (d : ℝ)) at hharm
    have hsum0 : ∑ j : Fin d, (2 * G 0 - (G (x + unit j) + G (x - unit j))) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have : nbrSum G x = ∑ j : Fin d, (G (x + unit j) + G (x - unit j)) := rfl
      rw [← this, hharm, hxg]
      ring
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ 2 * G 0 - (G (x + unit j) + G (x - unit j)) := fun j _ => by
      linarith [hle (x + unit j), hle (x - unit j)]
    intro j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 j (Finset.mem_univ j)
    constructor <;> linarith [hle (x + unit j), hle (x - unit j)]
  -- a coordinate in which `z` is nonzero, and a direction pointing away from the origin
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hzne
  have hi' : z i ≠ 0 := by simpa using hi
  -- the ray
  have hray : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → 0 < z i * ε → ∀ m : ℕ,
      G (z + Pi.single i (m * ε)) = G 0 := by
    intro ε hε hpos m
    induction m with
    | zero => simpa using hz
    | succ m ih =>
      have hne : z + Pi.single i ((m : ℤ) * ε) ≠ 0 := by
        intro h
        have := congrFun h i
        simp at this
        rcases hε with rfl | rfl <;> omega
      have := hprop _ hne ih i
      rcases hε with rfl | rfl
      · have e : z + Pi.single i (((m + 1 : ℕ) : ℤ) * 1) =
            z + Pi.single i ((m : ℤ) * 1) + unit i := by
          ext j
          by_cases hj : j = i
          · subst hj; simp [unit]; ring
          · simp [unit, hj]
        rw [e]; exact this.1
      · have e : z + Pi.single i (((m + 1 : ℕ) : ℤ) * (-1)) =
            z + Pi.single i ((m : ℤ) * (-1)) - unit i := by
          ext j
          by_cases hj : j = i
          · subst hj; simp [unit]; ring
          · simp [unit, hj]
        rw [e]; exact this.2
  -- choose the direction
  have hdir : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ 0 < z i * ε := by
    rcases lt_or_gt_of_ne hi' with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  obtain ⟨ε, hε, hpos⟩ := hdir
  have hy := hray ε hε hpos R
  -- far along the ray the Green function is small
  have hnorm : R ≤ graphNorm (z + Pi.single i ((R : ℤ) * ε)) := by
    set y : Site d := z + Pi.single i ((R : ℤ) * ε) with hydef
    have h1 : (y i).natAbs ≤ graphNorm y :=
      Finset.single_le_sum (f := fun j => (y j).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    refine le_trans ?_ h1
    rw [hydef]
    simp
    rcases hε with rfl | rfl <;> omega
  have := hR _ hnorm
  rw [hy] at this
  linarith

end LatticeProb
