import JSP000933PreparedCollapseEmbedding
import JSP000933PreparedSmallDiamondSimultaneous

open Cardinal

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

theorem smallBaseProducts_r404 {I : Type} (hI : Cardinal.mk I<GroundContinuumSucc)
    (p : CollapseBasicCondition) :
    Cardinal.mk (I×{q : CollapseBasicCondition // q≤p})<GroundContinuumSucc := by
  apply Order.lt_succ_iff.mpr
  rw [Cardinal.mk_prod]
  simp only [Cardinal.lift_id]
  calc
    _ ≤ (𝔠 : Cardinal)*𝔠 := mul_le_mul'
      (Order.lt_succ_iff.mp hI)
      ((Cardinal.mk_subtype_le (fun q : CollapseBasicCondition => q≤p)).trans
        basicValue_card_le_continuum_r401)
    _ = 𝔠 := Cardinal.continuum_mul_self

theorem prepared_totalProfiles_shortened_r404 {I J : Type}
    (hI : Cardinal.mk I<GroundContinuumSucc) (stamp : J→GroundContinuumSuccIndex)
    (V : I→J→PreparedBA) (p : CollapseBasicCondition) (q : SmallDiamondCondition)
    (hV : ∀ i,imageCondition ((p,q) : PreparedCondition)≤⨆ j,V i j) :
    ∃ (s : SmallDiamondCondition) (b : GroundContinuumSuccIndex), s≤q ∧
      ∀ i,imageCondition ((p,s) : PreparedCondition)≤⨆ j : {j : J // stamp j<b},V i j.val := by
  classical
  let Index := I×{r : CollapseBasicCondition // r≤p}
  let Q (i : Index) (t : SmallDiamondCondition) := ∃ (r : CollapseBasicCondition) (j : J),
    r≤ i.2.val ∧ imageCondition ((r,t) : PreparedCondition)≤V i.1 j
  have hDown (i : Index) {t u : SmallDiamondCondition} (htu : u≤t) (h : Q i t) : Q i u := by
    obtain ⟨r,j,hr,hj⟩ := h
    exact ⟨r,j,hr,(imageCondition_mono_r50
      (show ((r,u) : PreparedCondition)≤(r,t) from ⟨le_rfl,htu⟩)).trans hj⟩
  have hDense (i : Index) (t : SmallDiamondCondition) (ht : t≤q) : ∃ u≤t,Q i u := by
    have hPT : ((i.2.val,t) : PreparedCondition)≤(p,q) := ⟨i.2.property,ht⟩
    obtain ⟨j,new,hNew,hj⟩ := exists_stronger_below_indexedSup_r51
      ((i.2.val,t) : PreparedCondition) (V i.1)
      ((imageCondition_mono_r50 hPT).trans (hV i.1))
    exact ⟨new.2,hNew.2,new.1,j,hNew.1,hj⟩
  obtain ⟨s,hs,hAll⟩ := smallDiamond_simultaneous_wellOrder_r402
    (smallBaseProducts_r404 hI p) Q hDown q hDense
  have hWitness (i : Index) : ∃ (r : CollapseBasicCondition) (j : J),
      r≤ i.2.val ∧ imageCondition ((r,s) : PreparedCondition)≤V i.1 j := hAll i
  choose r j hr hj using hWitness
  obtain ⟨b,hb⟩ := continuumSuccIndex_family_bounded_r399
    (fun i : Index => stamp (j i)) (smallBaseProducts_r404 hI p)
  refine ⟨s,b,hs,fun i => ?_⟩
  apply productImage_le_of_dense_r403
  intro t ht
  let k : Index := (i,⟨t.1,ht.1⟩)
  have hRT : ((r k,t.2) : PreparedCondition)≤t := ⟨hr k,le_rfl⟩
  have hRS : ((r k,t.2) : PreparedCondition)≤(r k,s) := ⟨le_rfl,ht.2⟩
  exact ⟨(r k,t.2),hRT,le_iSup_of_le ⟨j k,hb k⟩
    ((imageCondition_mono_r50 hRS).trans (hj k))⟩

end PreparedModel
end JSP000933
