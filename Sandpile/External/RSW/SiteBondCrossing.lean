import Sandpile.External.RSW.SiteBond
import Sandpile.Support.RectangleMonotonicity

/-!
# Site and bond crossings

For bonds opened by their endpoint sites, a nontrivial walk is bond-open exactly when all of
its vertices are open. Thus positive-width rectangle crossings agree under thresholding.
-/

open Set

namespace Sandpile.External.RSW

/-- A rectangle walk is bond-open when each of its edges is open. -/
def IsBondOpenWalk {Q : Finset (Site 2)} (ω : Sym2 (Site 2) → Bool) :
    {a b : Q} → (rectangleGraph Q).Walk a b → Prop
  | _, _, .nil => True
  | a, _, .cons (v := b) _ p => ω s((a : Site 2), (b : Site 2)) = true ∧ IsBondOpenWalk ω p

/-- The bond crossing event of a lattice rectangle. -/
def bondCrossingEvent (w h : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  {ω | ∃ (a b : planeRectangle w h) (p : (rectangleGraph (planeRectangle w h)).Walk a b),
    a ∈ rectangleLeft (planeRectangle w h) ∧ b ∈ rectangleRight (planeRectangle w h) ∧
      IsBondOpenWalk ω p}

/-- A site-induced bond-open walk with an open starting site is precisely a walk all of whose
vertices are open. -/
theorem isBondOpenWalk_siteBond_iff {Q : Finset (Site 2)} (σ : Site 2 → Bool)
    {a b : Q} (p : (rectangleGraph Q).Walk a b) :
    IsBondOpenWalk (siteBondConfig σ) p ∧ σ a = true ↔
      ∀ z ∈ p.support, σ z = true := by
  induction p with
  | nil => simp [IsBondOpenWalk]
  | @cons a b c hab p ih =>
    simp only [IsBondOpenWalk, siteBondConfig_mk, Bool.and_eq_true,
      SimpleGraph.Walk.support_cons, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    tauto

/-- On a nontrivial walk, the open bonds already force its starting site to be open. -/
theorem isBondOpenWalk_siteBond_iff_of_ne {Q : Finset (Site 2)} (σ : Site 2 → Bool)
    {a b : Q} (p : (rectangleGraph Q).Walk a b) (hab : a ≠ b) :
    IsBondOpenWalk (siteBondConfig σ) p ↔ ∀ z ∈ p.support, σ z = true := by
  constructor
  · intro hp
    have ha : σ a = true := by
      cases p with
      | nil => exact (hab rfl).elim
      | @cons a b c h p =>
        have he : (σ a && σ b) = true := hp.1
        simp only [Bool.and_eq_true] at he
        exact he.1
    exact (isBondOpenWalk_siteBond_iff σ p).mp ⟨hp, ha⟩
  · intro hp
    exact ((isBondOpenWalk_siteBond_iff σ p).mpr hp).1

/-- In a positive-width rectangle the field superlevel crossing event is the pullback of the
bond crossing event under thresholding followed by the site-to-bond map. -/
theorem planarCrossingEvent_eq_preimage_bondCrossingEvent (w h : ℕ) (hw : 0 < w)
    (level : ℝ) :
    planarCrossingEvent w h level =
      (siteBondConfig ∘ thresholdConfig level) ⁻¹' bondCrossingEvent w h := by
  ext F
  change level ≤ crossingValue (planeRectangle w h) (fun z => F z) ↔
    ∃ (a b : planeRectangle w h) (p : (rectangleGraph (planeRectangle w h)).Walk a b),
      a ∈ rectangleLeft (planeRectangle w h) ∧ b ∈ rectangleRight (planeRectangle w h) ∧
        IsBondOpenWalk (siteBondConfig (thresholdConfig level F)) p
  rw [le_crossingValue_iff_exists_walk (isLatticeRectangle_planeRectangle w h)
    (planeRectangle_nonempty w h)]
  constructor <;> rintro ⟨a, b, p, ha, hb, hp⟩
  · refine ⟨a, b, p, ha, hb, ?_⟩
    have hab : a ≠ b := by
      intro he
      have hleft := (mem_rectangleLeft_planeRectangle a).mp ha
      have hright := (mem_rectangleRight_planeRectangle b).mp hb
      rw [he] at hleft
      omega
    apply (isBondOpenWalk_siteBond_iff_of_ne (thresholdConfig level F) p hab).mpr
    intro z hz
    simpa [thresholdConfig] using hp z hz
  · refine ⟨a, b, p, ha, hb, ?_⟩
    have hab : a ≠ b := by
      intro he
      have hleft := (mem_rectangleLeft_planeRectangle a).mp ha
      have hright := (mem_rectangleRight_planeRectangle b).mp hb
      rw [he] at hleft
      omega
    have hopen := (isBondOpenWalk_siteBond_iff_of_ne (thresholdConfig level F) p hab).mp hp
    intro z hz
    simpa [thresholdConfig] using hopen z hz

end Sandpile.External.RSW
