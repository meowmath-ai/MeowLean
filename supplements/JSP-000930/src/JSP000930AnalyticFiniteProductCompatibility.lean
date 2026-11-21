import JSP000930CohenRetargetManyValues

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B] [Fintype I] {N : I → Type}

theorem rowProduct_commonRefinement_eq (Q : ∀ i,ValuedPoset B (N i))
    (p q : ∀ i,N i) :
    commonRefinementValue (rowProductQ Q) p q = ⨅ i, commonRefinementValue (Q i) (p i) (q i) := by
  let V := rowProductQ Q
  let L := commonRefinementValue V p q
  let R := ⨅ i,commonRefinementValue (Q i) (p i) (q i)
  apply le_antisymm
  · change L ≤ R
    apply iSup_le
    intro r
    apply le_iInf
    intro i
    exact (inf_le_inf (iInf_le _ i) (iInf_le _ i)).trans (le_iSup (fun t : N i => (Q i).refines t (p i) ⊓ (Q i).refines t (q i)) (r i))
  · change R ≤ L
    by_contra h
    let m := R ⊓ Lᶜ
    have hm : m ≠ ⊥ := fun he => h (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    let T (i : I) (a : B) :=
      ∃ r : N i,a ≤ (Q i).refines r (p i) ⊓ (Q i).refines r (q i)
    have hM (i : I) {a b : B} (hab : a ≤ b) : T i b → T i a := by
      rintro ⟨r,hr⟩
      exact ⟨r,hab.trans hr⟩
    obtain ⟨a,ha,haM,hA⟩ := exists_finitely_refined_marks T hM m hm (by
      intro i b hb hbM
      have hB : b ≤ commonRefinementValue (Q i) (p i) (q i) :=
        (hbM.trans inf_le_left).trans (iInf_le (fun j => commonRefinementValue (Q j) (p j) (q j)) i)
      obtain ⟨r,c,hc,hcB,hCr⟩ := exists_nonzero_below_choice_r135 b hb
        (fun r : N i => (Q i).refines r (p i) ⊓ (Q i).refines r (q i)) hB
      exact ⟨c,hc,hcB,r,hCr⟩)
    choose r hr using hA
    have hL : a ≤ L := le_iSup_of_le r (le_inf
      (le_iInf (fun i => (hr i).trans inf_le_left))
      (le_iInf (fun i => (hr i).trans inf_le_right)))
    exact ha (disjoint_compl_right.out _ hL (haM.trans inf_le_right))

end JSP000930.Negative
