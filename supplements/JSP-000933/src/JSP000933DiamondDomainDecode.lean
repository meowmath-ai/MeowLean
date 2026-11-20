import JSP000933FixedDiamondEncoding

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion

variable {T : Type} {R : Rules (fun (_ : OmegaTwoIndex) => T)}

noncomputable def diamondSignal (E : DiamondEncoder T)
    (D : OmegaTwoIndex → RO (Condition R)) (color : OmegaTwoIndex) (p : Condition R) :
    Set OmegaTwoIndex :=
  {j | ∃ i : OmegaTwoIndex, ∃ q : Condition R,
    E.domainTag i (E.conditionCode q) = j ∧ imageCondition q ≤ D i} ∪
    {E.colorTag color,E.conditionTag (E.conditionCode p)}

theorem domainTag_mem_signal_r118 (E : DiamondEncoder T)
    (D : OmegaTwoIndex → RO (Condition R)) (color j : OmegaTwoIndex) (p q : Condition R) :
    E.domainTag j (E.conditionCode q) ∈ diamondSignal E D color p ↔ imageCondition q ≤ D j := by
  classical
  constructor
  · intro hm
    rcases hm with hd | hm
    · obtain ⟨i,r,ht,hr⟩ := hd
      have he := Sum.inl.inj (E.atom.injective ht)
      have hi : i = j := congrArg Prod.fst he
      have hq : r = q := E.conditionCode_injective_r117 (congrArg Prod.snd he)
      exact hi ▸ hq ▸ hr
    · rcases Set.mem_insert_iff.mp hm with he | hm
      · have h := E.atom.injective he
        cases h
      · have he := Set.mem_singleton_iff.mp hm
        have h := E.atom.injective he
        cases h
  · intro h
    exact Or.inl ⟨j,q,rfl,h⟩

theorem colorTag_mem_signal_r118 (E : DiamondEncoder T)
    (D : OmegaTwoIndex → RO (Condition R)) (color j : OmegaTwoIndex) (p : Condition R) :
    E.colorTag j ∈ diamondSignal E D color p ↔ j = color := by
  constructor
  · intro hm
    rcases hm with hd | hm
    · obtain ⟨i,r,ht,_⟩ := hd
      have h := E.atom.injective ht
      cases h
    · rcases Set.mem_insert_iff.mp hm with he | hm
      · exact Sum.inl.inj (Sum.inr.inj (E.atom.injective he))
      · have he := Set.mem_singleton_iff.mp hm
        have h := Sum.inr.inj (E.atom.injective he)
        cases h
  · rintro rfl
    exact Or.inr (Set.mem_insert _ _)

theorem conditionTag_mem_signal_r118 (E : DiamondEncoder T)
    (D : OmegaTwoIndex → RO (Condition R)) (color j : OmegaTwoIndex) (p : Condition R) :
    E.conditionTag j ∈ diamondSignal E D color p ↔ j = E.conditionCode p := by
  constructor
  · intro hm
    rcases hm with hd | hm
    · obtain ⟨i,r,ht,_⟩ := hd
      have h := E.atom.injective ht
      cases h
    · rcases Set.mem_insert_iff.mp hm with he | hm
      · have h := Sum.inr.inj (E.atom.injective he)
        cases h
      · exact Sum.inr.inj (Sum.inr.inj (E.atom.injective (Set.mem_singleton_iff.mp hm)))
  · rintro rfl
    exact Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _))

def CorrectTrace (a : OmegaTwoIndex) (guess signal : Set OmegaTwoIndex) : Prop :=
  ∀ z < a, z ∈ guess ↔ z ∈ signal

noncomputable def guessDomain (E : DiamondEncoder T) (a : OmegaTwoIndex)
    (guess : Set OmegaTwoIndex) (j : OmegaTwoIndex) : RO (Before R a) :=
  ⨆ q : {q : Before R a // E.domainTag j (E.conditionCode q.1) ∈ guess}, imageCondition q.1

theorem guessDomain_correct_r118 (E : DiamondEncoder T) (a : OmegaTwoIndex)
    (guess : Set OmegaTwoIndex) (D : OmegaTwoIndex → RO (Condition R))
    (color : OmegaTwoIndex) (p : Condition R) (j : OmegaTwoIndex)
    (small : RO (Before R a)) (hSmall : (wholeReduction a).boolPullback small = D j)
    (hCap : ∀ q : Before R a, E.domainTag j (E.conditionCode q.1) < a)
    (hG : CorrectTrace a guess (diamondSignal E D color p)) :
    guessDomain E a guess j = small := by
  have hMatch (q : Before R a) : E.domainTag j (E.conditionCode q.1) ∈ guess ↔ imageCondition q ≤ small := by
    rw [hG _ (hCap q),domainTag_mem_signal_r118]
    rw [← hSmall,← wholeReduction_basic_r100 a q]
    exact (wholeReduction a).boolPullback_le_iff_r90 _ _
  apply le_antisymm
  · exact iSup_le (fun q => (hMatch q.1).mp q.2)
  · rw [← basicConditions_join_r98 small]
    apply iSup_le
    intro q
    exact le_iSup (fun q : {q : Before R a // E.domainTag j (E.conditionCode q.1) ∈ guess} =>
      imageCondition q.1) ⟨q.1,(hMatch q.1).mpr q.2⟩

end FiniteSupport
end JSP000933
