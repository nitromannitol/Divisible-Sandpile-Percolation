/- First and last contact times for continuous real functions. -/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

open Set
namespace Sandpile.Support.CrossPathContact

theorem exists_first_contact {f : ℝ → ℝ} (hf : Continuous f)
    {a b c : ℝ} (hab : a ≤ b) (ha : f a ≤ c) (hb : c ≤ f b) :
    ∃ t ∈ Icc a b, f t = c ∧ ∀ u ∈ Icc a t, f u ≤ c := by
  have hne : (Icc a b ∩ f ⁻¹' {c}).Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab hf.continuousOn ⟨ha, hb⟩
    exact ⟨t, ht, he⟩
  obtain ⟨t, ht, hmin⟩ :=
    (isCompact_Icc.inter_right (isClosed_singleton.preimage hf)).exists_isMinOn hne
      continuous_id.continuousOn
  refine ⟨t, ht.1, ht.2, fun u hu => ?_⟩
  by_contra hgt
  have hgt : c < f u := lt_of_not_ge hgt
  obtain ⟨v, hv, hev⟩ := intermediate_value_Icc hu.1 hf.continuousOn ⟨ha, hgt.le⟩
  have htv : t ≤ v := hmin ⟨⟨hv.1, hv.2.trans (hu.2.trans ht.1.2)⟩, hev⟩
  have hvu : v = u := le_antisymm hv.2 (hu.2.trans htv)
  rw [hvu] at hev
  exact hgt.ne' hev

theorem exists_last_contact {f : ℝ → ℝ} (hf : Continuous f)
    {a b c : ℝ} (hab : a ≤ b) (ha : f a ≤ c) (hb : c ≤ f b) :
    ∃ t ∈ Icc a b, f t = c ∧ ∀ u ∈ Icc t b, c ≤ f u := by
  have hne : (Icc a b ∩ f ⁻¹' {c}).Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab hf.continuousOn ⟨ha, hb⟩
    exact ⟨t, ht, he⟩
  obtain ⟨t, ht, hmax⟩ :=
    (isCompact_Icc.inter_right (isClosed_singleton.preimage hf)).exists_isMaxOn hne
      continuous_id.continuousOn
  refine ⟨t, ht.1, ht.2, fun u hu => ?_⟩
  by_contra hlt
  have hlt : f u < c := lt_of_not_ge hlt
  obtain ⟨v, hv, hev⟩ := intermediate_value_Icc hu.2 hf.continuousOn ⟨hlt.le, hb⟩
  have hvt : v ≤ t := hmax ⟨⟨ht.1.1.trans (hu.1.trans hv.1), hv.2⟩, hev⟩
  have hvu : v = u := le_antisymm (hvt.trans hu.1) hv.1
  rw [hvu] at hev
  exact hlt.ne hev


end Sandpile.Support.CrossPathContact
