import JSP000933DiamondDomainDecode

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open OpenGraphForcing

variable {T : Type} {R : Rules (fun (_ : OmegaTwoIndex) => T)}

theorem exists_club_captures_domainTags_r119 (E : DiamondEncoder T)
    (hSmall : ∀ a : OmegaTwoIndex, Cardinal.mk (Before R a) ≤ ℵ₁) :
    ∃ C : Set OmegaTwoIndex, OrdinalClub C ∧
      ∀ a ∈ C, (ℵ₀ : Cardinal) < (omegaTwoOrdinal a).cof →
        ∀ j < a, ∀ q : Before R a, E.domainTag j (E.conditionCode q.1) < a := by
  classical
  have hCap (b : OmegaTwoIndex) : ∃ d : OmegaTwoIndex,
      ∀ j < b, ∀ q : Before R b, E.domainTag j (E.conditionCode q.1) < d := by
    let f (p : ↥(Set.Iio b) × Before R b) := E.domainTag p.1.1 (E.conditionCode p.2.1)
    let r (p : ↥(Set.Iio b) × Before R b) : ↥(Set.range f) := ⟨f p,Set.mem_range_self p⟩
    have hOnto : Function.Surjective r := by
      rintro ⟨_,⟨p,rfl⟩⟩
      exact ⟨p,rfl⟩
    have hCard : Cardinal.mk (↥(Set.Iio b) × Before R b) ≤ ℵ₁ := by
      rw [Cardinal.mk_prod,Cardinal.lift_id,Cardinal.lift_id,
        ← Cardinal.mul_eq_self Cardinal.isRegular_aleph_one.1]
      exact mul_le_mul' (mk_omegaTwo_properPrefix_le_alephOne_r97 b) (hSmall b)
    obtain ⟨d,hd⟩ := omegaTwo_smallSet_bounded_r108 (Set.range f)
      ((Cardinal.mk_le_of_surjective hOnto).trans hCard)
    exact ⟨d,fun j hj q => hd _ (Set.mem_range_self (f := f) ((⟨j,hj⟩,q) : ↥(Set.Iio b) × Before R b))⟩
  choose cap hTag using hCap
  refine ⟨stageClosedUnder cap,stageClosedUnder_isClub_r108 cap,fun a ha hcf j hj q => ?_⟩
  let S : Finset OmegaTwoIndex := insert j (support q.1)
  have hBelow (i : OmegaTwoIndex) (hi : i ∈ (S : Set OmegaTwoIndex)) : i < a := by
    change i ∈ insert j (support q.1) at hi
    rcases Finset.mem_insert.mp hi with rfl | hp
    · exact hj
    · exact q.2 i ((mem_support_r75 q.1 i).mp hp)
  obtain ⟨b,hba,hb⟩ := omegaTwo_countable_bounded_below_r109 a hcf _ S.finite_toSet.countable hBelow
  let pq : Before R b :=
    ⟨q.1,fun i hi => hb i (Finset.mem_insert_of_mem ((mem_support_r75 q.1 i).mpr hi))⟩
  exact (hTag b j (hb j (Finset.mem_insert_self ..)) pq).trans (ha b hba)

theorem exists_club_refines_two_and_floor_r119 {C D : Set OmegaTwoIndex}
    (hC : OrdinalClub C) (hD : OrdinalClub D) (floor : OmegaTwoIndex) :
    ∃ E : Set OmegaTwoIndex, OrdinalClub E ∧
      ∀ a ∈ E, (∃ i, i < a) → a ∈ C ∧ a ∈ D ∧ floor < a := by
  classical
  choose c hc hcC using hC.1
  choose d hd hdD using hD.1
  let f (i : OmegaTwoIndex) := max (c i) (max (d i) floor)
  refine ⟨stageClosedUnder f,stageClosedUnder_isClub_r108 f,fun a ha hne => ?_⟩
  have hCa : a ∈ C := hC.2 a hne (fun i hi =>
    ⟨c i,hc i,(le_max_left _ _).trans_lt (ha i hi),hcC i⟩)
  have hDa : a ∈ D := hD.2 a hne (fun i hi =>
    ⟨d i,hd i,((le_max_left _ _).trans (le_max_right _ _)).trans_lt (ha i hi),hdD i⟩)
  obtain ⟨i,hi⟩ := hne
  exact ⟨hCa,hDa,((le_max_right _ _).trans (le_max_right _ _)).trans_lt (ha i hi)⟩

def DiamondAtOmegaOne (guess : OmegaTwoIndex → Set OmegaTwoIndex) : Prop :=
  ∀ signal : Set OmegaTwoIndex, ∀ C : Set OmegaTwoIndex, OrdinalClub C →
    ∃ a ∈ C, (omegaTwoOrdinal a).cof = ℵ₁ ∧ CorrectTrace a (guess a) signal

end FiniteSupport
end JSP000933
