import JSP000933LocalCoverFailureReflection
import JSP000933RelativeUnboundedTransfer
import JSP000933ActualRelativeCliqueStage

namespace JSP000933
namespace ForcingTransport

open CantorCodes BooleanCompletion RelativeOCA MarkedForcing OpenGraphForcing

variable {B C : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

theorem relativeStage_clique_on_localized_mark
    {d : (ℕ→B)→B} {k : Word×Word→B} {m : B}
    (S : RelativeCliqueStageData d k m)
    (E : CompleteValueMap B C) (F : CompleteValueMap (TotalBA S.iterand) C)
    (hCoherent : ∀ b, F.toFun (baseEmbed S.iterand b)=E.toFun b)
    (hB : BoundsCountableOmegaOneNames C)
    (q : B) (hq : q≠⊥) (hqm : q≤ m)
    (D : (ℕ→C)→C) (K : Word×Word→C)
    (hD : ∀ x,E.toFun q⊓E.toFun (d x)≤D (E.toFun ∘ x))
    (hK : ∀ w,E.toFun q⊓E.toFun (k w)=E.toFun q⊓K w) :
    ∃ p : C, p≠⊥ ∧ p≤E.toFun q ∧ p≤weightedCliqueExistsValue D K := by
  let U := unboundedValue S.membership
  let x (i : OmegaOneIndex) := E.toFun ∘ S.points i
  let g (i : OmegaOneIndex) := F.toFun (S.membership i)
  let p := E.toFun q⊓F.toFun U
  have hp : p≠⊥ := by
    intro h
    have h' : F.toFun (U⊓baseEmbed S.iterand q)=F.toFun ⊥ := by
      rw [F.map_inf,hCoherent,F.map_bot,inf_comm]
      exact h
    have h'' := congrArg (supportProjection S.iterand) (F.injective h')
    rw [supportProjection_meet_base_r428,
      (supportProjection_zero_iff_r428 S.iterand _).mpr rfl] at h''
    have hQ : q ≤ supportProjection S.iterand U := hqm.trans S.unboundedSupport_r463
    exact hq (by rwa [inf_eq_right.mpr hQ] at h'')
  have hC (i j : OmegaOneIndex) :
      E.toFun q⊓E.toFun (colorValue k (S.points i) (S.points j))=
        E.toFun q⊓colorValue K (x i) (x j) := by
    rw [map_colorValue_r105]
    exact mask_colorCode_congr hK _ _
  have hG (i : OmegaOneIndex) : g i≤E.toFun (d (S.points i)) := by
    rw [←hCoherent]
    apply F.monotone
    apply (supportProjection_le_iff_r428 S.iterand _ _).mp
    rw [S.membership_support i]
    exact inf_le_right
  have hEdge (i j : OmegaOneIndex) (hij : i≠j) :
      g i⊓g j≤E.toFun (colorValue k (S.points i) (S.points j)) := by
    rw [←F.map_inf,←hCoherent]
    apply F.monotone
    exact S.membership_edge hij
  have hNotEq (i j : OmegaOneIndex) (hij : i≠j) :
      E.toFun q≤(realEqValue (x i) (x j))ᶜ := by
    change E.toFun q≤(realEqValue (fun n => E.toFun (S.points i n)) (fun n => E.toFun (S.points j n)))ᶜ
    rw [←map_realEqValue_r126 E (S.points i) (S.points j),←E.map_compl]
    have hBase : q ≤ (realEqValue (S.points i) (S.points j))ᶜ :=
      hqm.trans (le_compl_iff_disjoint_right.mpr (S.distinct i j hij))
    exact E.monotone hBase
  have hUnbounded : F.toFun U = unboundedValue g := by
    simp only [U,unboundedValue,aboveValue,F.map_iInf,F.map_iSup,g]
  refine ⟨p,hp,inf_le_left,?_⟩
  apply le_iSup_of_le x
  apply le_iSup_of_le g
  unfold weightedCliqueValue
  apply le_inf
  · apply le_iInf
    intro i
    apply (le_materialImp_iff_r126 _ _ _).mpr
    exact (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans (hG i))).trans (hD _)
  · apply le_inf
    · apply le_iInf
      intro j
      apply (le_materialImp_iff_r126 _ _ _).mpr
      have hq' : p⊓(g j.val.1⊓g j.val.2)≤E.toFun q := inf_le_left.trans inf_le_left
      exact le_inf ((le_inf hq' (inf_le_right.trans (hEdge _ _ j.property))).trans
        ((hC _ _).le.trans inf_le_right)) (hq'.trans (hNotEq _ _ j.property))
    · exact inf_le_right.trans (hUnbounded.trans_le (unbounded_le_noncountable hB g))

end ForcingTransport
end JSP000933
