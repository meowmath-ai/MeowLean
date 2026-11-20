import JSP000933GuessedNoCoverStage

namespace JSP000933
namespace CantorCodes

open FiniteSupport BooleanTwoStep

variable {B I : Type} [CompleteBooleanAlgebra B] [DecidableEq I]

abbrev ReverseLabels (I : Type) := (Finset I)ᵒᵈ

noncomputable def cliqueAdmitted (p : B) (d : I → B) (K : I → I → B)
    (s : Finset I) : B :=
  (⨅ i : ↥s, p ⊓ d i.1) ⊓
  (⨅ q : {q : ↥s × ↥s // q.1.1 ≠ q.2.1}, K q.1.1.1 q.1.2.1)

theorem cliqueAdmitted_empty_r121 (p : B) (d : I → B) (K : I → I → B) :
    cliqueAdmitted p d K ∅ = ⊤ := by
  apply top_unique
  apply le_inf <;> apply le_iInf
  · intro i
    exact False.elim (Finset.notMem_empty i.1 i.2)
  · intro q
    exact False.elim (Finset.notMem_empty q.1.1.1 q.1.1.2)

theorem cliqueAdmitted_le_vertex_r121 (p : B) (d : I → B) (K : I → I → B)
    {s : Finset I} {i : I} (hi : i ∈ s) :
    cliqueAdmitted p d K s ≤ p ⊓ d i :=
  inf_le_left.trans (iInf_le (fun j : ↥s => p ⊓ d j.1) ⟨i,hi⟩)

theorem cliqueAdmitted_le_edge_r121 (p : B) (d : I → B) (K : I → I → B)
    {s : Finset I} {i j : I} (hi : i ∈ s) (hj : j ∈ s) (hne : i ≠ j) :
    cliqueAdmitted p d K s ≤ K i j :=
  inf_le_right.trans (iInf_le
    (fun q : {q : ↥s × ↥s // q.1.1 ≠ q.2.1} => K q.1.1.1 q.1.2.1)
    ⟨(⟨i,hi⟩,⟨j,hj⟩),hne⟩)

theorem cliqueAdmitted_singleton_r121 (p : B) (d : I → B) (K : I → I → B) (i : I) :
    cliqueAdmitted p d K {i} = p ⊓ d i := by
  apply le_antisymm (cliqueAdmitted_le_vertex_r121 p d K (Finset.mem_singleton_self _))
  apply le_inf <;> apply le_iInf
  · intro j
    rw [Finset.mem_singleton.mp j.2]
  · intro q
    exact False.elim (q.2 ((Finset.mem_singleton.mp q.1.1.2).trans
      (Finset.mem_singleton.mp q.1.2.2).symm))

theorem cliqueAdmitted_anti_r121 (p : B) (d : I → B) (K : I → I → B)
    {s t : Finset I} (hst : s ⊆ t) :
    cliqueAdmitted p d K t ≤ cliqueAdmitted p d K s := by
  apply le_inf <;> apply le_iInf
  · intro i
    exact cliqueAdmitted_le_vertex_r121 p d K (hst i.2)
  · intro q
    exact cliqueAdmitted_le_edge_r121 p d K (hst q.1.1.2) (hst q.1.2.2) q.2

noncomputable def cliqueLabelStage (p : B) (d : I → B) (K : I → I → B) :
    Stage B (ReverseLabels I) :=
  staticLabelStage (fun s => cliqueAdmitted p d K (OrderDual.ofDual s))

theorem cliqueLabelStage_comp_r121 (p : B) (d : I → B) (K : I → I → B)
    (s t : ReverseLabels I) :
    (cliqueLabelStage p d K).compVal s t =
      cliqueAdmitted p d K (OrderDual.ofDual s ∪ OrderDual.ofDual t) := by
  classical
  unfold Stage.compVal
  apply le_antisymm
  · apply iSup_le
    intro u
    change cliqueAdmitted p d K (OrderDual.ofDual u) ⊓
      ((if u ≤ s then ⊤ else ⊥) ⊓ (if u ≤ t then ⊤ else ⊥)) ≤ _
    by_cases hs : u ≤ s
    · by_cases ht : u ≤ t
      · exact inf_le_left.trans (cliqueAdmitted_anti_r121 p d K (Finset.union_subset hs ht))
      · simp [hs,ht]
    · simp [hs]
  · let u := OrderDual.toDual (OrderDual.ofDual s ∪ OrderDual.ofDual t)
    apply le_iSup_of_le u
    have hs : u ≤ s := Finset.subset_union_left
    have ht : u ≤ t := Finset.subset_union_right
    change cliqueAdmitted p d K (OrderDual.ofDual u) ≤
      cliqueAdmitted p d K (OrderDual.ofDual u) ⊓
      ((if u ≤ s then ⊤ else ⊥) ⊓ (if u ≤ t then ⊤ else ⊥))
    simp [hs,ht]

end CantorCodes
end JSP000933
