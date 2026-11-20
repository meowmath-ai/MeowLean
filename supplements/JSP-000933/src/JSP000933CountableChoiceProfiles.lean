import JSP000933PreparedProduct

namespace JSP000933
namespace BooleanCompletion

theorem exists_allChoiceProfiles_r411 {P : Type} [Preorder P] (hP : IsCountablyClosed P)
    {J : Type*} (p : P) (A : ℕ→J→RO P) (hA : ∀ n,imageCondition p≤⨆ j,A n j) :
    ∃ (q : P) (f : ℕ→J),q≤p ∧ ∀ n,imageCondition q≤A n (f n) := by
  classical
  let S := {q : P // q≤p}
  have hStep (n : ℕ) (r : S) : ∃ (s : S) (j : J),s.val≤r.val ∧ imageCondition s.val≤A n j := by
    obtain ⟨i,s,hs,ht⟩ := exists_stronger_below_indexedSup_r51 r.val (A n)
      ((imageCondition_mono_r50 r.property).trans (hA n))
    exact ⟨⟨s,hs.trans r.property⟩,i,hs,ht⟩
  choose next label hNext hV using hStep
  let states : ℕ→S := Nat.rec ⟨p,le_rfl⟩ next
  have hRec (n : ℕ) : states (n+1)=next n (states n) := rfl
  have hAnti : Antitone (fun n => (states n).val) := by
    apply antitone_nat_of_succ_le
    intro n
    change (states (n+1)).val≤(states n).val
    rw [hRec n]
    exact hNext n (states n)
  obtain ⟨q,hq⟩ := hP (fun n => (states n).val) hAnti
  refine ⟨q,fun n => label n (states n),(hq 0).trans (states 0).property,fun n => ?_⟩
  have h : q≤(next n (states n)).val := by
    simpa only [hRec n] using hq (n+1)
  exact (imageCondition_mono_r50 h).trans (hV n (states n))

end BooleanCompletion
end JSP000933
