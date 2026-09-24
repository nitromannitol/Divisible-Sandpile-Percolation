/-
Coarse indexing of a coordinate plane, preservation of reachability
and comparison of fine and coarse distances.
-/
import Sandpile.Support.CoarseBox
import Sandpile.Support.ClusterPath
import Sandpile.Support.StarCrossings

open Set

noncomputable section
namespace Sandpile

def coarsePlaneIndex (x : Site 4) (L : ℕ) (z : Site 4) : Site 2 :=
  ![(z 0 - x 0) / (L : ℤ), (z 1 - x 1) / (L : ℤ)]

lemma coarsePlaneIndex_coord (x : Site 4) (L : ℕ) (z : Site 4) (i : Fin 2) :
    coarsePlaneIndex x L z i =
      (z (Fin.castLE (by decide : 2 ≤ 4) i) - x (Fin.castLE (by decide : 2 ≤ 4) i)) / (L : ℤ) := by
  fin_cases i <;> simp [coarsePlaneIndex]

lemma mem_planeBox_coarsePlaneIndex (x : Site 4) (L : ℕ) (hL : 0 < L) (z : Site 4)
    (hplane : ∀ i : Fin 4, 2 ≤ (i : ℕ) → z i = x i) :
    z ∈ planeBox (coarsePlaneCenter x L (coarsePlaneIndex x L z)) L := by
  have hLint : (0 : ℤ) < L := by exact_mod_cast hL
  let u : Site 2 := ![(z 0 - x 0) % (L : ℤ), (z 1 - x 1) % (L : ℤ)]
  apply Finset.mem_image.mpr
  refine ⟨u, (mem_planeRectangle L L u).mpr ?_, ?_⟩
  · exact ⟨Int.emod_nonneg _ hLint.ne', (Int.emod_lt_of_pos _ hLint).le,
      Int.emod_nonneg _ hLint.ne', (Int.emod_lt_of_pos _ hLint).le⟩
  · funext i
    fin_cases i
    · change x 0 + (L : ℤ) * ((z 0 - x 0) / (L : ℤ)) + (z 0 - x 0) % (L : ℤ) = z 0
      have hh := Int.emod_add_mul_ediv (z 0 - x 0) (L : ℤ)
      omega
    · change x 1 + (L : ℤ) * ((z 1 - x 1) / (L : ℤ)) + (z 1 - x 1) % (L : ℤ) = z 1
      have hh := Int.emod_add_mul_ediv (z 1 - x 1) (L : ℤ)
      omega
    · exact (hplane 2 (by decide)).symm
    · exact (hplane 3 (by decide)).symm

lemma int_ediv_step {a b L : ℤ} (hL : 0 < L) (hab : |a - b| ≤ 1) :
    |a / L - b / L| ≤ 1 := by
  have hle (a b : ℤ) (hab : a ≤ b + 1) : a / L ≤ b / L + 1 := by
    by_contra hn
    have hq : b / L + 2 ≤ a / L := by omega
    have hmul := mul_le_mul_of_nonneg_left hq hL.le
    have ha := Int.emod_add_mul_ediv a L
    have hb := Int.emod_add_mul_ediv b L
    have ha0 := Int.emod_nonneg a hL.ne'
    have hbL := Int.emod_lt_of_pos b hL
    nlinarith
  have hh := abs_le.mp hab
  exact abs_le.mpr ⟨by linarith [hle b a (by linarith)], by linarith [hle a b (by linarith)]⟩

lemma coarsePlaneIndex_adj_or_eq (x : Site 4) (L : ℕ) (hL : 0 < L) {z w : Site 4}
    (hzw : starGraph.Adj z w) : coarsePlaneIndex x L z = coarsePlaneIndex x L w ∨
      (starLatticeGraph 2).Adj (coarsePlaneIndex x L z) (coarsePlaneIndex x L w) := by
  by_cases he : coarsePlaneIndex x L z = coarsePlaneIndex x L w
  · exact Or.inl he
  · refine Or.inr ⟨he, ?_⟩
    intro i
    rw [coarsePlaneIndex_coord, coarsePlaneIndex_coord]
    have hh := int_ediv_step (by exact_mod_cast hL : (0 : ℤ) < L)
      (show |(z (Fin.castLE (by decide : 2 ≤ 4) i) - x (Fin.castLE (by decide : 2 ≤ 4) i)) -
        (w (Fin.castLE (by decide : 2 ≤ 4) i) - x (Fin.castLE (by decide : 2 ≤ 4) i))| ≤ 1 by
        simpa only [sub_sub_sub_cancel_right] using hzw.2.1 (Fin.castLE (by decide : 2 ≤ 4) i))
    have hh' : ((((z (Fin.castLE (by decide : 2 ≤ 4) i) - x (Fin.castLE (by decide : 2 ≤ 4) i)) / (L : ℤ) -
        (w (Fin.castLE (by decide : 2 ≤ 4) i) - x (Fin.castLE (by decide : 2 ≤ 4) i)) / (L : ℤ)).natAbs : ℕ) : ℤ) ≤ 1 := by
      simpa only [Int.natCast_natAbs] using hh
    exact_mod_cast hh'

lemma coarsePlaneIndex_mem_rectangle {ϑ : ℝ} (hϑ : 0 ≤ ϑ) (x : Site 4) (r L : ℕ)
    (hL : 0 < L) {z : Site 4} (hz : z ∈ ballRect ϑ r x) :
    coarsePlaneIndex x L z ∈ planeRectangle ⌊ϑ * r⌋₊ r := by
  have hLint : (0 : ℤ) < L := by exact_mod_cast hL
  obtain ⟨hz0, hw0, hz1, hw1, _⟩ := hz
  apply (mem_planeRectangle _ _ _).mpr
  refine ⟨Int.ediv_nonneg hz0 hLint.le, ?_, Int.ediv_nonneg hz1 hLint.le, ?_⟩
  · change (z 0 - x 0) / (L : ℤ) ≤ (⌊ϑ * r⌋₊ : ℤ)
    rw [Int.natCast_floor_eq_floor (mul_nonneg hϑ (Nat.cast_nonneg r))]
    exact (Int.ediv_le_self (L : ℤ) hz0).trans hw0
  · exact (Int.ediv_le_self (L : ℤ) hz1).trans hw1

lemma reachable_image_of_adj_or_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : ∀ a b, G.Adj a b → f a = f b ∨ H.Adj (f a) (f b))
    {a b : V} (hab : G.Reachable a b) : H.Reachable (f a) (f b) := by
  rcases hab with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj p ih =>
    rcases hf a b hadj with he | he
    · rw [he]
      exact ih
    · exact he.reachable.trans ih

lemma boxDist_le_walk_length {d : ℕ} {G : SimpleGraph (Site d)}
    (hstep : ∀ a b, G.Adj a b → boxDist a b ≤ 1) {a b : Site d} (p : G.Walk a b) :
    boxDist a b ≤ p.length := by
  induction p with
  | nil => simp [boxDist_self]
  | @cons a b c hab p ih =>
    exact (boxDist_trans a b c).trans (by have := hstep a b hab; simpa only [SimpleGraph.Walk.length_cons] using (show boxDist a b + boxDist b c ≤ p.length + 1 by omega))

lemma boxDist_le_of_starLatticeGraph_adj {d : ℕ} {a b : Site d}
    (hab : (starLatticeGraph d).Adj a b) : boxDist a b ≤ 1 :=
  Finset.sup_le (fun i _ => hab.2 i)

lemma dist_le_of_boxDist_le {d : ℕ} {z w : Site d} {R : ℕ} (h : boxDist z w ≤ R) :
    dist z w ≤ (R : ℝ) := by
  apply (dist_pi_le_iff (Nat.cast_nonneg R)).mpr
  intro i
  rw [Int.dist_eq, abs_sub_comm]
  exact (boxDist_le_iff_real_coords z w R).mp h i

lemma boxDist_coarsePlaneCenter_le (x : Site 4) (L : ℕ) (a b : Site 2) :
    boxDist (coarsePlaneCenter x L a) (coarsePlaneCenter x L b) ≤ L * boxDist a b := by
  have hc (i : Fin 2) : |(b i : ℝ) - (a i : ℝ)| ≤ boxDist a b :=
    (boxDist_le_iff_real_coords a b (boxDist a b)).mp le_rfl i
  apply (boxDist_le_iff_real_coords _ _ _).mpr
  intro i
  fin_cases i
  · change |((x 0 + (L : ℤ) * b 0 : ℤ) : ℝ) - ((x 0 + (L : ℤ) * a 0 : ℤ) : ℝ)| ≤ (L * boxDist a b : ℕ)
    push_cast
    rw [show (x 0 : ℝ) + (L : ℝ) * (b 0 : ℝ) - ((x 0 : ℝ) + (L : ℝ) * (a 0 : ℝ)) =
      (L : ℝ) * ((b 0 : ℝ) - (a 0 : ℝ)) by ring, abs_mul, abs_of_nonneg (Nat.cast_nonneg L)]
    exact mul_le_mul_of_nonneg_left (hc 0) (Nat.cast_nonneg L)
  · change |((x 1 + (L : ℤ) * b 1 : ℤ) : ℝ) - ((x 1 + (L : ℤ) * a 1 : ℤ) : ℝ)| ≤ (L * boxDist a b : ℕ)
    push_cast
    rw [show (x 1 : ℝ) + (L : ℝ) * (b 1 : ℝ) - ((x 1 : ℝ) + (L : ℝ) * (a 1 : ℝ)) =
      (L : ℝ) * ((b 1 : ℝ) - (a 1 : ℝ)) by ring, abs_mul, abs_of_nonneg (Nat.cast_nonneg L)]
    exact mul_le_mul_of_nonneg_left (hc 1) (Nat.cast_nonneg L)
  · simp [coarsePlaneCenter, planeTranslate]
    positivity
  · simp [coarsePlaneCenter, planeTranslate]
    positivity

lemma dist_le_coarsePlaneIndex_distance (x : Site 4) (L : ℕ) (hL : 0 < L) (z w : Site 4)
    (hzplane : ∀ i : Fin 4, 2 ≤ (i : ℕ) → z i = x i)
    (hwplane : ∀ i : Fin 4, 2 ≤ (i : ℕ) → w i = x i) :
    dist z w ≤ ((boxDist (coarsePlaneIndex x L z) (coarsePlaneIndex x L w) : ℝ) + 2) * L := by
  let a := coarsePlaneIndex x L z
  let b := coarsePlaneIndex x L w
  let c := coarsePlaneCenter x L a
  let d := coarsePlaneCenter x L b
  have hz : dist z c ≤ (L : ℝ) := by
    rw [dist_comm]
    exact dist_le_of_boxDist_le (mem_boxFinset_iff.mp (planeBox_subset_boxFinset c L
      (mem_planeBox_coarsePlaneIndex x L hL z hzplane)))
  have hw : dist d w ≤ (L : ℝ) :=
    dist_le_of_boxDist_le (mem_boxFinset_iff.mp (planeBox_subset_boxFinset d L
      (mem_planeBox_coarsePlaneIndex x L hL w hwplane)))
  have hcd : dist c d ≤ (L : ℝ) * boxDist a b := by
    simpa only [Nat.cast_mul] using dist_le_of_boxDist_le (boxDist_coarsePlaneCenter_le x L a b)
  have hdist := dist_triangle z c w
  have hdist' := dist_triangle c d w
  change dist z w ≤ ((boxDist a b : ℝ) + 2) * L
  nlinarith

end Sandpile
