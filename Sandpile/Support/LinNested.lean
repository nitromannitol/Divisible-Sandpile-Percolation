import Mathlib
import Sandpile.Frozen.DGT4LastVisits

/-!
# Only the last visit to a site matters

Only the last visit to a site matters, `sandpile.tex:5462-5467`: "These threshold events are
nested, so a path visiting `x` at times `r_1 < … < r_k` satisfies
`⋂_{ℓ} {J(x) ≤ E u_{n-r_ℓ-1}(0)} = {J(x) ≤ E u_{n-r_k-1}(0)}`; only the last visit to each site
matters."

The statement below is the deterministic content: for thresholds `b` that decrease along time,
asking `J(X_r) ≤ b_r` at every time `r ≤ j` is the same as asking it only at the times that are
last visits, which are the times where the indicator `I_{r,j}` of `lem:dgt4-weighted-last-visits`
equals one. The thresholds of the paper are `b_r = E u_{n-r-1}(0)`, decreasing in `r` because the
mean odometer increases in time.
-/

namespace Sandpile

/-- For a decreasing threshold family `b`, asking `J (X r) ≤ b r` at every `r ≤ j` is the same as
asking it only at the times `r ≤ j` that are last visits to `X r` before time `j`; the forward
direction is trivial, and the converse replaces `r` by the last time `m` at or after `r` (up to
`j`) that revisits the same point, using that `b m ≤ b r` since `b` decreases. -/
theorem forall_le_iff_lastVisit {α : Type*} [DecidableEq α] (j : ℕ) (X : ℕ → α) (b : ℕ → ℝ)
    (hb : ∀ r s : ℕ, r ≤ s → b s ≤ b r) (J : α → ℝ) :
    (∀ r, r ≤ j → J (X r) ≤ b r)
      ↔ (∀ r, r ≤ j → (∀ s : ℕ, r < s → s ≤ j → X r ≠ X s) → J (X r) ≤ b r) := by
  classical
  constructor
  · intro h r hr _
    exact h r hr
  · intro h r hr
    set T : Finset ℕ := (Finset.Icc r j).filter (fun s => X s = X r) with hT
    have hrT : r ∈ T := by
      simp only [hT, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, hr⟩, trivial⟩
    have hne : T.Nonempty := ⟨r, hrT⟩
    set m : ℕ := T.max' hne with hm
    have hmT : m ∈ T := T.max'_mem hne
    rw [hT, Finset.mem_filter, Finset.mem_Icc] at hmT
    obtain ⟨⟨hrm, hmj⟩, hXm⟩ := hmT
    have hlast : ∀ s : ℕ, m < s → s ≤ j → X m ≠ X s := by
      intro s hms hsj hXs
      have hsT : s ∈ T := by
        simp only [hT, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨le_trans hrm (le_of_lt hms), hsj⟩, by rw [← hXs, hXm]⟩
      exact absurd (T.le_max' s hsT) (not_le.mpr hms)
    have hJ := h m hmj hlast
    rw [hXm] at hJ
    exact le_trans hJ (hb r m hrm)

/-- The last-visit indicator of `lem:dgt4-weighted-last-visits` equals one
exactly on the times that are last visits. -/
theorem lastVisitIndicator_eq_one_iff {d : ℕ} (i j : ℕ) (X : ℕ → Site d) :
    Sandpile.Frozen.DGT4LastVisits.lastVisitIndicator i j X = 1
      ↔ ∀ s : ℕ, i < s → s ≤ j → X i ≠ X s := by
  classical
  constructor
  · intro h s hs1 hs2
    by_contra hc
    have hnot : X ∉ {Y : ℕ → Site d | ∀ r : ℕ, i < r → r ≤ j → Y i ≠ Y r} := by
      intro hmem
      exact hmem s hs1 hs2 hc
    rw [Sandpile.Frozen.DGT4LastVisits.lastVisitIndicator,
      Set.indicator_of_notMem hnot] at h
    exact zero_ne_one h
  · intro h
    have hmem : X ∈ {Y : ℕ → Site d | ∀ r : ℕ, i < r → r ≤ j → Y i ≠ Y r} := h
    rw [Sandpile.Frozen.DGT4LastVisits.lastVisitIndicator, Set.indicator_of_mem hmem]

/-- The paper's reduction to last visits, written with the indicator. -/
theorem forall_le_iff_lastVisitIndicator {d : ℕ} (j : ℕ) (X : ℕ → Site d) (b : ℕ → ℝ)
    (hb : ∀ r s : ℕ, r ≤ s → b s ≤ b r) (J : Site d → ℝ) :
    (∀ r, r ≤ j → J (X r) ≤ b r)
      ↔ ∀ r, r ≤ j → Sandpile.Frozen.DGT4LastVisits.lastVisitIndicator r j X = 1 →
          J (X r) ≤ b r := by
  rw [forall_le_iff_lastVisit j X b hb J]
  constructor
  · intro h r hr hind
    exact h r hr ((lastVisitIndicator_eq_one_iff r j X).mp hind)
  · intro h r hr hlast
    exact h r hr ((lastVisitIndicator_eq_one_iff r j X).mpr hlast)

end Sandpile
