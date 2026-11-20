import JSP000933RelativeLowLast
import JSP000933RelativeCliquePoset

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing MarkedForcing

variable {B : Type} [CompleteBooleanAlgebra B]

def CardRelativeCCC (m : B) (D : OmegaOneIndex→B) (K : OmegaOneIndex→OmegaOneIndex→B)
    (n : ℕ) : Prop :=
  ∀ W : OmegaOneIndex→Finset OmegaOneIndex→B,
    (∀ i s,W i s≤cliqueAdmitted m D K s) →
    (∀ i s,s.card≠n→W i s=⊥) →
    (∀ i j,i<j→∀ s t,(W i s⊓W j t)⊓cliqueAdmitted m D K (s∪t)=⊥) →
    unboundedValue (rowLabelWeight W)=⊥

noncomputable def projectedLabelWeight (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (f : LabelCandidate→Finset OmegaOneIndex) (i : OmegaOneIndex) (a : Finset OmegaOneIndex) : B :=
  ⨆ s : {s : Finset OmegaOneIndex // f (i,s)=a},W i s.val

theorem projectedLabelWeight_rows_r455 (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (f : LabelCandidate→Finset OmegaOneIndex) :
    rowLabelWeight (projectedLabelWeight W f)=rowLabelWeight W := by
  funext i
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro s
    exact le_iSup _ s.val
  · apply iSup_le
    intro s
    exact le_iSup_of_le (f (i,s)) (le_iSup (fun t : {t : Finset OmegaOneIndex // f (i,t) = f (i,s)} => W i t.val) ⟨s,rfl⟩)

theorem projectedLabelWeight_pairs_zero_r455
    (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (f : LabelCandidate→Finset OmegaOneIndex) (Valid : Finset OmegaOneIndex→B)
    (h : ∀ i j,i<j→∀ s t,(W i s⊓W j t)⊓Valid (f (i,s)∪f (j,t))=⊥)
    (i j : OmegaOneIndex) (hij : i<j) (a b : Finset OmegaOneIndex) :
    (projectedLabelWeight W f i a⊓projectedLabelWeight W f j b)⊓Valid (a∪b)=⊥ := by
  apply le_bot_iff.mp
  simp only [projectedLabelWeight,iSup_inf_eq,inf_iSup_eq]
  apply iSup_le
  intro t
  apply iSup_le
  intro s
  have he : f (i,s.val) ∪ f (j,t.val) = a ∪ b := congrArg₂ (· ∪ ·) s.property t.property
  rw [← he]
  exact (h i j hij s.val t.val).le

theorem CardRelativeCCC.zero_r455 (m : B) (D : OmegaOneIndex→B)
    (K : OmegaOneIndex→OmegaOneIndex→B) :
    CardRelativeCCC m D K 0 := by
  intro W _ hSize hNo
  apply unboundedValue_of_disjoint_rows_r454
  intro i j hij
  apply disjoint_iff_inf_le.mpr
  simp only [rowLabelWeight,iSup_inf_iSup]
  apply iSup_le
  rintro ⟨s,t⟩
  by_cases hs : s.card=0
  · by_cases ht : t.card=0
    · have hs' : s=∅ := Finset.card_eq_zero.mp hs
      have ht' : t=∅ := Finset.card_eq_zero.mp ht
      subst s
      subst t
      simpa only [Finset.empty_union,cliqueAdmitted_empty_r121,inf_top_eq] using
        (hNo i j hij ∅ ∅).le
    · rw [hSize j t ht,inf_bot_eq]
  · rw [hSize i s hs,bot_inf_eq]

theorem relativeCCC_of_cardRelativeCCC_r455 (hB : BoundsCountableOmegaOneNames B)
    (m : B) (D : OmegaOneIndex→B) (K : OmegaOneIndex→OmegaOneIndex→B)
    (h : ∀ n,CardRelativeCCC m D K n) :
    ForcesRelativeCCC (relativeCliquePoset m D K) := by
  classical
  intro W hW hNo
  let V (n : ℕ) := restrictLabels W (fun x => x.2.card=n)
  have hRows : rowLabelWeight W=(fun i => ⨆ n,rowLabelWeight (V n) i) := by
    funext i
    apply le_antisymm
    · apply iSup_le
      intro s
      apply le_iSup_of_le s.card
      exact le_iSup_of_le s (by simp only [V,restrictLabels,ite_true,le_rfl])
    · apply iSup_le
      intro n
      apply iSup_le
      intro s
      exact (show V n i s≤W i s by unfold V restrictLabels; split <;> simp).trans (le_iSup _ s)
  change unboundedValue (rowLabelWeight W)=⊥
  rw [hRows,unboundedValue_countablePartition_r433 hB]
  apply le_bot_iff.mp
  apply iSup_le
  intro n
  apply Eq.le
  apply h n (V n)
  · intro i s
    exact (show V n i s≤W i s by unfold V restrictLabels; split <;> simp).trans (hW i s)
  · intro i s hn
    simp only [V,restrictLabels,ite_eq_right hn]
  · intro i j hij s t
    apply le_bot_iff.mp
    have h1 : V n i s≤W i s := by unfold V restrictLabels; split <;> simp
    have h2 : V n j t≤W j t := by unfold V restrictLabels; split <;> simp
    have hw := hNo i j hij s t
    rw [relativeClique_common_r437] at hw
    exact (inf_le_inf (inf_le_inf h1 h2) le_rfl).trans hw.le

end RelativeOCA
end JSP000933
