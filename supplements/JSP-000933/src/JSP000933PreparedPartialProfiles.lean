import JSP000933PreparedShortProfiles

open Cardinal

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

theorem prepared_partialProfiles_bounded_r415 {I : Type} (hI : Cardinal.mk I<GroundContinuumSucc)
    (V : I→GroundContinuumSuccIndex→PreparedBA) (m : PreparedBA)
    (hFunc : ∀ i,Pairwise (fun a b => Disjoint (m⊓V i a) (m⊓V i b)))
    (p : CollapseBasicCondition) (q : SmallDiamondCondition)
    (hM : imageCondition ((p,q) : PreparedCondition)≤ m) :
    ∃ (s : SmallDiamondCondition) (b : GroundContinuumSuccIndex), s≤q ∧
      ∀ i j,b≤j → imageCondition ((p,s) : PreparedCondition)⊓V i j=⊥ := by
  let R (i : I) := ⨆ j,m⊓V i j
  let V' (i : I) (o : Option GroundContinuumSuccIndex) : PreparedBA :=
    match o with
    | none => (R i)ᶜ
    | some j => m⊓V i j
  let stamp (o : Option GroundContinuumSuccIndex) : GroundContinuumSuccIndex :=
    o.getD (continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos)
  have hFull (i : I) : (⨆ o,V' i o)=⊤ := by
    apply top_unique
    have h1 : R i≤⨆ o,V' i o := iSup_le (fun j => le_iSup (V' i) (some j))
    have h2 : (R i)ᶜ≤⨆ o,V' i o := le_iSup (V' i) none
    exact (sup_compl_eq_top (x := R i)).symm.trans_le (sup_le h1 h2)
  have hTot (i : I) : imageCondition ((p,q) : PreparedCondition)≤⨆ o,V' i o :=
    (hFull i).symm ▸ le_top
  obtain ⟨s,b,hs,hRows⟩ := prepared_totalProfiles_shortened_r404 hI stamp V' p q hTot
  let t := imageCondition ((p,s) : PreparedCondition)
  have hT : t≤ m := (imageCondition_mono_r50
    (show ((p,s) : PreparedCondition)≤(p,q) from ⟨le_rfl,hs⟩)).trans hM
  refine ⟨s,b,hs,fun i j hj => le_bot_iff.mp ?_⟩
  let r := t⊓V i j
  have hR : r≤ m⊓V i j := le_inf (inf_le_left.trans hT) inf_le_right
  change r≤⊥
  have hShort : r≤⨆ o : {o : Option GroundContinuumSuccIndex // stamp o<b}, V' i o.val :=
    inf_le_left.trans (hRows i)
  apply (le_inf le_rfl hShort).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro o
  rcases o with ⟨o,ho⟩
  cases o with
  | none =>
    exact disjoint_iff_inf_le.mp ((disjoint_compl_right :
      Disjoint (R i) (R i)ᶜ).mono_left (hR.trans (le_iSup (fun k => m ⊓ V i k) j)))
  | some k =>
    have hk : k<b := ho
    have hJK : j≠k := fun he => not_lt_of_ge hj (he.symm ▸ hk)
    exact disjoint_iff_inf_le.mp ((hFunc i hJK).mono_left hR)

end PreparedModel
end JSP000933
