import JSP000933PreparedSmallTraceEnum
import JSP000933PreparedNameCodes

open Cardinal Flypitch

namespace JSP000933
namespace RelativeOCA

open PreparedModel OpenGraphForcing

theorem finiteTraces_continuumBound_r472 (I : Type) (hI : Cardinal.mk I≤𝔠) :
    Cardinal.mk (Finset (I×OmegaOneIndex))≤𝔠 := by
  classical
  have hP : Cardinal.mk (I×OmegaOneIndex)≤𝔠 := by
    rw [Cardinal.mk_prod,mk_OmegaOneIndex_r61]
    simp only [Cardinal.lift_id]
    exact Cardinal.mul_le_of_le Cardinal.aleph0_le_continuum hI Cardinal.aleph_one_le_continuum
  obtain ⟨e⟩ := (Cardinal.le_def (I×OmegaOneIndex) BaseGroundReals.Type).mp
    (hP.trans_eq baseGroundReals_type_card_r391.symm)
  let Code := {S : Set BaseGroundReals.Type // Cardinal.mk S≤ℵ₀}
  let F (s : Finset (I×OmegaOneIndex)) : Code :=
    ⟨Set.image e (s : Set (I×OmegaOneIndex)),
      Cardinal.mk_le_aleph0_iff.mpr ((s.finite_toSet.image e).countable.to_subtype)⟩
  have hF : Function.Injective F := by
    intro s t h
    have hEq : Set.image e (s : Set (I×OmegaOneIndex))=
        Set.image e (t : Set (I×OmegaOneIndex)) := congrArg Subtype.val h
    have one (s t : Finset (I×OmegaOneIndex))
        (h' : Set.image e (s : Set (I×OmegaOneIndex))=Set.image e (t : Set (I×OmegaOneIndex))) :
        s⊆t := by
      intro x hx
      have hm : e x∈Set.image e (s : Set (I×OmegaOneIndex)) := ⟨x,hx,rfl⟩
      rw [h'] at hm
      obtain ⟨y,hy,hey⟩ := hm
      exact (e.injective hey) ▸ hy
    exact le_antisymm (show s ≤ t from one s t hEq) (show t ≤ s from one t s hEq.symm)
  letI : Infinite BaseGroundReals.Type := Cardinal.infinite_iff.mpr (by
    rw [baseGroundReals_type_card_r391]
    exact Cardinal.aleph0_le_continuum)
  apply (Cardinal.mk_le_of_injective hF).trans
  apply (Cardinal.mk_bounded_set_le_of_infinite BaseGroundReals.Type ℵ₀).trans
  rw [baseGroundReals_type_card_r391,Cardinal.continuum_power_aleph0]

theorem prepared_mixedFiniteTraceEnum_r472 (I : Type) (hI : Cardinal.mk I≤𝔠) :
    Nonempty (MixedEnumeration OmegaOneIndex (Finset (I×OmegaOneIndex)) PreparedBA) :=
  prepared_smallMixedTraceEnum_r471 _ (finiteTraces_continuumBound_r472 I hI)

theorem prepared_mixedPrefixTraceEnum_r472 (a : GroundContinuumSuccIndex) :
    Nonempty (MixedEnumeration OmegaOneIndex (Finset (↥(Set.Iio a)×OmegaOneIndex)) PreparedBA) :=
  prepared_mixedFiniteTraceEnum_r472 _ (Order.lt_succ_iff.mp (continuumSuccInitial_card_lt_r406 a))

end RelativeOCA
end JSP000933
