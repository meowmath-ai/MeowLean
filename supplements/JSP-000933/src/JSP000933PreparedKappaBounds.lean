import JSP000933PreparedFiniteTraceEnum
import JSP000933PreparedShortProfiles

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel BooleanCompletion

def BoundsSmallKappaNames (B : Type) [CompleteBooleanAlgebra B] : Prop :=
  ∀ I : Type,Cardinal.mk I<GroundContinuumSucc → ∀ V : I→GroundContinuumSuccIndex→B,
    (⨅ i,⨆ j,V i j)≤⨆ b : GroundContinuumSuccIndex,
      ⨅ i,⨆ j : ↥(Set.Iio b),V i j.val

theorem actual_prepared_boundsSmallKappa_r473 : BoundsSmallKappaNames PreparedBA := by
  intro I hI V
  let m : PreparedBA := ⨅ i,⨆ j,V i j
  let w : PreparedBA := ⨆ b : GroundContinuumSuccIndex,⨅ i,⨆ j : ↥(Set.Iio b),V i j.val
  change m≤w
  by_contra hn
  have hN : m⊓wᶜ≠⊥ := fun he =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hN
  obtain ⟨q,b,hq,hV⟩ := prepared_totalProfiles_shortened_r404 hI id V p.1 p.2
    (fun i => hp.trans (inf_le_left.trans (iInf_le _ i)))
  let r : PreparedCondition := (p.1,q)
  have hr : r≤p := ⟨le_rfl,hq⟩
  have hW : imageCondition r≤w := le_iSup_of_le b (le_iInf hV)
  exact imageCondition_ne_bot_r50 r
    (disjoint_compl_right.out _ hW ((imageCondition_mono_r50 hr).trans (hp.trans inf_le_right)))

theorem uniform_smallKappa_cutoffs_r473 {B I : Type} [CompleteBooleanAlgebra B]
    (hB : BoundsSmallKappaNames B) (hI : Cardinal.mk I<GroundContinuumSucc)
    (m : B) (V : I→GroundContinuumSuccIndex→B)
    (hMono : ∀ i,Monotone (V i)) (hV : ∀ i,m≤⨆ b,V i b) :
    m≤⨆ b : GroundContinuumSuccIndex,⨅ i,V i b := by
  apply ((le_iInf hV).trans (hB I hI V)).trans
  apply iSup_le
  intro b
  apply le_iSup_of_le b
  apply le_iInf
  intro i
  apply (iInf_le _ i).trans
  exact iSup_le (fun c => hMono i c.property.le)

noncomputable def aboveKappaValue {B : Type} [CompleteBooleanAlgebra B]
    (w : GroundContinuumSuccIndex→B) (b : GroundContinuumSuccIndex) : B :=
  ⨆ i : {i : GroundContinuumSuccIndex // b< i},w i.val

noncomputable def unboundedKappaValue {B : Type} [CompleteBooleanAlgebra B]
    (w : GroundContinuumSuccIndex→B) : B :=
  ⨅ b : GroundContinuumSuccIndex,aboveKappaValue w b

end RelativeOCA
end JSP000933
