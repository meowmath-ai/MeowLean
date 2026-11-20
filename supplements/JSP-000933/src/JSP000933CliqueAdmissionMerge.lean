import JSP000933IndexedDisjointSupports

namespace JSP000933
namespace CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B] [DecidableEq I]

theorem cliqueAdmitted_union_r155 (p : B) (d : I → B) (K : I → I → B)
    {s t : Finset I} {q : B}
    (hs : q ≤ cliqueAdmitted p d K s) (ht : q ≤ cliqueAdmitted p d K t)
    (cross : ∀ i ∈ s, ∀ j ∈ t, i ≠ j → q ≤ K i j ∧ q ≤ K j i) :
    q ≤ cliqueAdmitted p d K (s ∪ t) := by
  apply le_inf <;> apply le_iInf
  · rintro ⟨i,hi⟩
    rcases Finset.mem_union.mp hi with h | h
    · exact hs.trans (cliqueAdmitted_le_vertex_r121 p d K h)
    · exact ht.trans (cliqueAdmitted_le_vertex_r121 p d K h)
  · rintro ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,hne⟩
    rcases Finset.mem_union.mp hi with hsi | hti <;>
      rcases Finset.mem_union.mp hj with hsj | htj
    · exact hs.trans (cliqueAdmitted_le_edge_r121 p d K hsi hsj hne)
    · exact (cross i hsi j htj hne).1
    · exact (cross j hsj i hti hne.symm).2
    · exact ht.trans (cliqueAdmitted_le_edge_r121 p d K hti htj hne)

theorem cliqueAdmitted_restoreShared_r155 (p : B) (d : I → B) (K : I → I → B)
    {s t : Finset I} {c : I} {q : B} (hcs : c ∈ s) (hct : c ∈ t)
    (hs : q ≤ cliqueAdmitted p d K s) (ht : q ≤ cliqueAdmitted p d K t)
    (hSmall : q ≤ cliqueAdmitted p d K (s.erase c ∪ t.erase c)) :
    q ≤ cliqueAdmitted p d K (s ∪ t) := by
  apply cliqueAdmitted_union_r155 p d K hs ht
  intro i hi j hj hne
  by_cases hic : i = c
  · subst i
    exact ⟨ht.trans (cliqueAdmitted_le_edge_r121 p d K hct hj hne),
      ht.trans (cliqueAdmitted_le_edge_r121 p d K hj hct hne.symm)⟩
  · by_cases hjc : j = c
    · subst j
      exact ⟨hs.trans (cliqueAdmitted_le_edge_r121 p d K hi hcs hne),
        hs.trans (cliqueAdmitted_le_edge_r121 p d K hcs hi hne.symm)⟩
    · have hI := Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hic,hi⟩) :
          i ∈ s.erase c ∨ i ∈ t.erase c)
      have hJ := Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨hjc,hj⟩) :
          j ∈ s.erase c ∨ j ∈ t.erase c)
      exact ⟨hSmall.trans (cliqueAdmitted_le_edge_r121 p d K hI hJ hne),
        hSmall.trans (cliqueAdmitted_le_edge_r121 p d K hJ hI hne.symm)⟩

end CantorCodes
end JSP000933
