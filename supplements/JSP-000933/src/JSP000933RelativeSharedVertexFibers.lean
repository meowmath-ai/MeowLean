import JSP000933RelativeRectangularPair

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem restrictLabels_vertex_rows_r461 (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (v : OmegaOneIndex) :
    rowLabelWeight (restrictLabels W (fun x => v∈x.2))=vertexFiber W v := by
  classical
  funext i
  apply le_antisymm
  · apply iSup_le
    intro s
    by_cases hs : v∈s
    · rw [restrictLabels, ite_eq_left hs]
      exact le_iSup (fun t : {s : Finset OmegaOneIndex // v∈s} => W i t.val) ⟨s,hs⟩
    · simp only [restrictLabels,ite_eq_right hs,bot_le]
  · apply iSup_le
    intro s
    apply le_iSup_of_le s.val
    simp only [restrictLabels,ite_eq_left s.property,le_rfl]

theorem sharedVertexFiber_bounded_r461 (m : B) (D : OmegaOneIndex→B)
    (K : OmegaOneIndex→OmegaOneIndex→B) {n : ℕ} (lower : CardRelativeCCC m D K n)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (hW : ∀ i s,W i s≤cliqueAdmitted m D K s)
    (hSize : ∀ i s,s.card≠n+1 → W i s=⊥)
    (hPairs : ∀ i j,i<j→∀ s t,(W i s⊓W j t)⊓cliqueAdmitted m D K (s∪t)=⊥)
    (v : OmegaOneIndex) :
    unboundedValue (vertexFiber W v)=⊥ := by
  classical
  let L := restrictLabels W (fun x => v∈x.2)
  let f (x : LabelCandidate) := x.2.erase v
  let A := cliqueAdmitted m D K
  have hL (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : L i s≤W i s := by
    unfold L restrictLabels
    split <;> simp
  have hNZ (i : OmegaOneIndex) (s : Finset OmegaOneIndex) (h : L i s≠⊥) : v∈s := by
    by_contra hn
    exact h (by simp only [L,restrictLabels,ite_eq_right hn])
  have hF : ∀ i s,projectedLabelWeight L f i s≤A s := by
    intro i s
    apply iSup_le
    intro t
    have hA : L i t.val ≤ A (f (i,t.val)) :=
      (hL i t.val).trans ((hW i t.val).trans
        (cliqueAdmitted_anti_r121 m D K (Finset.erase_subset v t.val)))
    exact hA.trans_eq (congrArg A t.property)
  have hS (i : OmegaOneIndex) (s : Finset OmegaOneIndex) (hs : s.card≠n) :
      projectedLabelWeight L f i s=⊥ := by
    apply le_bot_iff.mp
    apply iSup_le
    intro t
    by_contra hn
    have hP : L i t.val≠⊥ := fun he => hn he.le
    have hT : t.val.card=n+1 := by
      by_contra hn'
      exact hP (le_bot_iff.mp ((hL i t.val).trans_eq (hSize i t.val hn')))
    have hE : (f (i,t.val)).card=n := by
      change (t.val.erase v).card=n
      rw [Finset.card_erase_of_mem (hNZ i t.val hP),hT] <;> omega
    exact hs ((congrArg Finset.card t.property).symm.trans hE)
  have hP (i j : OmegaOneIndex) (hij : i<j) (s t : Finset OmegaOneIndex) :
      (L i s⊓L j t)⊓A (f (i,s)∪f (j,t))=⊥ := by
    let z := (L i s⊓L j t)⊓A (f (i,s)∪f (j,t))
    change z=⊥
    by_contra hz
    have hI : z≤L i s := inf_le_left.trans inf_le_left
    have hJ : z≤L j t := inf_le_left.trans inf_le_right
    have hs : v∈s := hNZ i s (fun he => hz (le_bot_iff.mp (hI.trans_eq he)))
    have ht : v∈t := hNZ j t (fun he => hz (le_bot_iff.mp (hJ.trans_eq he)))
    have hIW := hI.trans (hL i s)
    have hJW := hJ.trans (hL j t)
    have hR : z≤A (s∪t) :=
      cliqueAdmitted_restoreShared_r155 m D K hs ht (hIW.trans (hW i s))
        (hJW.trans (hW j t)) inf_le_right
    exact hz (le_bot_iff.mp ((le_inf (le_inf hIW hJW) hR).trans_eq (hPairs i j hij s t)))
  have h0 := lower (projectedLabelWeight L f) hF hS
    (fun i j hij s t => projectedLabelWeight_pairs_zero_r455 L f A hP i j hij s t)
  rw [projectedLabelWeight_rows_r455,restrictLabels_vertex_rows_r461] at h0
  exact h0

end RelativeOCA
end JSP000933
