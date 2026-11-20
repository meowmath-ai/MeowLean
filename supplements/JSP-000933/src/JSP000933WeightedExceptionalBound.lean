import JSP000933BooleanClusterTransversality

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem exists_uncountable_fiber_r151 {A C : Type} [Countable C]
    (hA : ¬ Countable A) (f : A → C) :
    ∃ c : C, ¬ Countable {x : A // f x = c} := by
  classical
  by_contra h
  have hMany (c : C) : ({x : A | f x = c} : Set A).Countable := by
    by_contra hn
    exact h ⟨c,fun hc => hn (Set.countable_coe_iff.mp hc)⟩
  have hU : (Set.univ : Set A).Countable :=
    (Set.countable_iUnion hMany).mono (fun x _ => Set.mem_iUnion.mpr ⟨f x,rfl⟩)
  exact hA (Set.countable_univ_iff.mp hU)

def LowerStemPairs {n : ℕ} (K : Word × Word → B) (F : I → BooleanSample B n) : Prop :=
  ∀ {J : Type} (e : J → I), Function.Injective e → ¬ Countable J →
    ∀ u : J → B, (∀ j, u j ≠ ⊥ ∧ u j ≤ (F (e j)).weight) →
      ∃ j k, j ≠ k ∧ (u j ⊓ u k) ⊓ matchedValue K (F (e j)).stem (F (e k)).stem ≠ ⊥

theorem exists_high_clusterPiece_r151 {n : ℕ} (K : Word × Word → B)
    (F : I → BooleanSample B n) (hI : ¬ Countable I) (hWeight : ∀ i, (F i).weight ≠ ⊥)
    (last : I → OmegaOneIndex) (hLast : Function.Injective last) (cutoff : OmegaOneIndex)
    (lower : LowerStemPairs K F) :
    ∃ i, cutoff < last i ∧ ((F i).weight ⊓ weightedCluster K F (F i).stem (F i).tip) ≠ ⊥ := by
  classical
  by_contra hNo
  let Above : Set I := {i | cutoff < last i}
  let Low : Set OmegaOneIndex := Set.Iic cutoff
  have hLow : Low.Countable := by
    apply ((OmegaOneIndex_initial_countable_r61 cutoff).to_set.insert cutoff).mono
    intro j hj
    rcases lt_or_eq_of_le (show j ≤ cutoff from hj) with hh | hh
    · exact Set.mem_insert_of_mem _ hh
    · exact Set.mem_insert_iff.mpr (Or.inl hh)
  have hAbove : ¬ Countable (↥Above) := by
    intro ha
    have hUnion : (Set.univ : Set I).Countable :=
      ((Set.countable_coe_iff.mp ha).union (hLow.preimage hLast)).mono (fun i _ => by
        by_cases h : cutoff < last i
        · exact Or.inl h
        · exact Or.inr (le_of_not_gt h))
    exact hI (Set.countable_univ_iff.mp hUnion)
  have hEach (i : ↥Above) :
      ∃ U : Fin n → Word, ∃ V : Word, ∃ u : B, u ≠ ⊥ ∧ u ≤ (F i.1).weight ∧
        u ≤ stemCylinder (F i.1).stem U ∧ u ≤ cylinderValue (F i.1).tip V ∧
          u ≤ (weightedClusterHit K F (F i.1).stem U V)ᶜ := by
    have hBot : (F i.1).weight ⊓ weightedCluster K F (F i.1).stem (F i.1).tip = ⊥ := by
      by_contra hn
      exact hNo ⟨i.1,i.2,hn⟩
    have hFail : (F i.1).weight ≤ (weightedCluster K F (F i.1).stem (F i.1).tip)ᶜ :=
      le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hBot.le)
    rw [weightedCluster_compl_r143] at hFail
    let t (U : Fin n → Word) (V : Word) :=
      (stemCylinder (F i.1).stem U ⊓ cylinderValue (F i.1).tip V) ⊓
        (weightedClusterHit K F (F i.1).stem U V)ᶜ
    obtain ⟨U,b,hb,hbi,hbU⟩ := exists_nonzero_below_choice_r135 (F i.1).weight
      (hWeight i.1) (fun U => ⨆ V, t U V) hFail
    obtain ⟨V,u,hu,hub,huT⟩ := exists_nonzero_below_choice_r135 b hb (t U) hbU
    exact ⟨U,V,u,hu,hub.trans hbi,huT.trans (inf_le_left.trans inf_le_left),
      huT.trans (inf_le_left.trans inf_le_right),huT.trans inf_le_right⟩
  choose U V u hU using hEach
  let f (i : ↥Above) := (U i,V i)
  obtain ⟨W,hW⟩ := exists_uncountable_fiber_r151 hAbove f
  let E := {i : ↥Above // f i = W}
  let e (i : E) : I := i.1.1
  have he : Function.Injective e := fun _ _ h => Subtype.ext (Subtype.ext h)
  obtain ⟨i,j,hij,hNon⟩ := lower e he hW (fun i => u i.1)
    (fun i => ⟨(hU i.1).1,(hU i.1).2.1⟩)
  let c := (u i.1 ⊓ u j.1) ⊓ matchedValue K (F (e i)).stem (F (e j)).stem
  have hEq : f i.1 = f j.1 := i.2.trans j.2.symm
  have hStem : c ≤ stemCylinder (F (e j)).stem (U i.1) := by
    rw [show U i.1 = U j.1 from congrArg Prod.fst hEq]
    exact (inf_le_left.trans inf_le_right).trans (hU j.1).2.2.1
  have hTip : c ≤ cylinderValue (F (e j)).tip (V i.1) := by
    rw [show V i.1 = V j.1 from congrArg Prod.snd hEq]
    exact (inf_le_left.trans inf_le_right).trans (hU j.1).2.2.2.1
  have hIn : c ≤ weightedClusterHit K F (F (e i)).stem (U i.1) (V i.1) :=
    le_iSup_of_le (e j)
      (le_inf (le_inf ((inf_le_left.trans inf_le_right).trans (hU j.1).2.1) inf_le_right)
        (le_inf hStem hTip))
  have hOut : c ≤ (weightedClusterHit K F (F (e i)).stem (U i.1) (V i.1))ᶜ :=
    (inf_le_left.trans inf_le_left).trans (hU i.1).2.2.2.2
  exact hNon (le_bot_iff.mp ((le_inf hIn hOut).trans_eq (inf_compl_eq_bot')))

end CantorCodes
end JSP000933
