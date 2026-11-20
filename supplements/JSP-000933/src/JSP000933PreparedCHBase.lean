import Flypitch4.Zfc
import Mathlib.SetTheory.Cardinal.Continuum

open Fol bSet Cardinal Flypitch
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

noncomputable abbrev CHBase := collapse_algebra.𝔹_collapse.{0}

noncomputable abbrev BaseOmegaOne : PSet.{0} := pSet_aleph1

abbrev BaseGroundReals : PSet.{0} := PSet.powerset PSet.omega

noncomputable abbrev BaseCollapseBasic : Type :=
  CollapsePoset BaseOmegaOne.Type BaseGroundReals.Type (Order.succ (ℵ₀ : Cardinal))

noncomputable def baseCollapseImage (q : BaseCollapseBasic) : CHBase := collapseInclusion q

theorem baseCollapse_denseOmegaClosed_r390 :
    DenseOmegaClosed (Set.range baseCollapseImage : Set CHBase) := by
  letI : Nonempty BaseGroundReals.Type := ⟨Set.univ⟩
  letI : Nonempty (BaseOmegaOne.Type → BaseGroundReals.Type) := ⟨fun _ => Classical.arbitrary _⟩
  exact principalOpens_denseOmegaClosed

theorem baseCollapse_top_CH_r390 : (⊤ : CHBase) ⊩[V CHBase] CH_f :=
  V_𝔹_collapse_models_CH

theorem baseCollapse_top_ZFC_CH_r390 :
    ((⊤ : CHBase) ⊩ₜ[V CHBase] ZFC) ∧ ((⊤ : CHBase) ⊩[V CHBase] CH_f) :=
  ⟨bSet_models_ZFC,baseCollapse_top_CH_r390⟩

theorem baseCollapse_checkedOmegaOne_r390 :
    (⊤ : CHBase) ≤ ((check BaseOmegaOne : bSet CHBase) =ᴮ (aleph_one (𝔹 := CHBase))) :=
  aleph_one_check_is_aleph_one_of_omega_lt collapse_algebra.omega_lt_aleph_one_collapse

theorem baseCollapse_checkedNatFunctions_r390 (y : PSet.{0}) :
    (⊤ : CHBase) ≤ (check (PSet.functions PSet.omega y) : bSet CHBase) =ᴮ
      functions bSet.omega (check y) :=
  collapse_algebra.check_functions_eq_functions y

theorem baseCollapse_actualEnumeration_r390 :
    (⊤ : CHBase) ≤
      is_func' (check BaseOmegaOne) (check BaseGroundReals) collapse_algebra.π ⊓
        is_surj (check BaseOmegaOne) (check BaseGroundReals) collapse_algebra.π :=
  collapse_algebra.π_spec'

end PreparedModel
end JSP000933
