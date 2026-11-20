import Sandpile.External.RSW.VerticalStripSubpath
import Sandpile.External.RSW.QuasiCascadeCover

/-!
# KST subpaths in a strip

A path crossing the scale-`k` strip contains a scale-`k` KST subpath when the
portion in the strip stays inside the scale rectangle and reaches both target rows
only inside their central target intervals.
-/

namespace Sandpile.External.RSW

/-- Strip and target bounds yield a KST subpath of a larger KST path. -/
theorem hasKSTSubpath_of_strip_bounds {Q : Finset (Site 2)} {a b : Q}
    {p : (rectangleGraph Q).Walk a b} {m k : ℕ} (hp : IsKSTPath m p)
    (hk : 0 < k) (hkm : k ≤ m)
    (hbox : ∀ z ∈ p.support, -(k : ℤ) ≤ (z : Site 2) 1 →
      (z : Site 2) 1 ≤ k → (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k)
    (htarget : ∀ z ∈ p.support, (z : Site 2) 1 = k ∨ (z : Site 2) 1 = -(k : ℤ) →
      -((k / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (k / 12 : ℕ)) :
    HasKSTSubpath k p := by
  obtain ⟨c, d, q, hsub, hq, hc, hd, hstrip⟩ :=
    exists_vertical_strip_subpath p hp.1 (B := -(k : ℤ)) (T := k)
      (by omega) (by rw [hp.2.1]; exact_mod_cast hkm)
      (by rw [hp.2.2.1]; exact_mod_cast (neg_le_neg (show (k : ℤ) ≤ m by exact_mod_cast hkm)))
  have hcp := hsub.support_subset q.start_mem_support
  have hdp := hsub.support_subset q.end_mem_support
  have hct := htarget c hcp (Or.inl hc)
  have hdt := htarget d hdp (Or.inr hd)
  refine ⟨c, d, q, hsub, ⟨hq, hc, hd, hct.1, hct.2, hdt.1, hdt.2, ?_⟩⟩
  intro z hz
  exact hbox z (hsub.support_subset hz) (hstrip z hz).1 (hstrip z hz).2

end Sandpile.External.RSW
