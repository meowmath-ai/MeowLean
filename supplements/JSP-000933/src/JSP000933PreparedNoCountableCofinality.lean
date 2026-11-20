import JSP000933PreparedActualMarkedDiamond
import JSP000933CheckedOmegaUncountability

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

noncomputable def actualCofinalGraph {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (X Y G : bSet B) : B :=
  ⨅ a : bSet B,(a∈ᴮ Y)⟹(⨆ n : bSet B,(n∈ᴮ X)⊓
    (⨆ b : bSet B,(b∈ᴮ Y)⊓((pair n b∈ᴮ G)⊓(a∈ᴮ b))))

theorem prepared_noCountableCofinal_r422 (d : GroundContinuumSuccIndex) (hd : OmegaOneCofinalIndex d) :
    (⨆ G : bSet PreparedBA,is_func' bSet.omega (preparedOrdinalEntry d) G⊓
      actualCofinalGraph bSet.omega (preparedOrdinalEntry d) G)=⊥ := by
  classical
  let α := continuumSuccOrdinal d
  let y := PSet.ordinalMk α
  rw [preparedOrdinalEntry_asOrdinal_r416 d]
  apply le_bot_iff.mp
  apply iSup_le
  intro G
  let m : PreparedBA := is_func' bSet.omega (check y) G⊓actualCofinalGraph bSet.omega (check y) G
  change m≤⊥
  by_contra hm
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 m (fun he => hm he.le)
  let V (n : ℕ) (j : y.Type) : PreparedBA :=
    pair (check (PSet.omega.Func (ULift.up n))) (check (y.Func j))∈ᴮ G
  have hTot (n : ℕ) : imageCondition p≤⨆ j,V n j :=
    checkNatRows_total_r412 y G (imageCondition p) (hp.trans inf_le_left) n
  obtain ⟨q,f,hq,hV⟩ := exists_allChoiceProfiles_r411 preparedProduct_countablyClosed_r401 p V hTot
  let c := imageCondition q
  have hc : c≤ m := (imageCondition_mono_r50 hq).trans hp
  let jOrd (j : y.Type) : α.ToType := cast PSet.ordinalMk_type j
  let o (n : ℕ) := (jOrd (f n)).toOrd.val
  let β := ⨆ n,o n
  have hSmall : Cardinal.mk ℕ<α.cof := by
    change (continuumSuccOrdinal d).cof=ℵ₁ at hd
    change Cardinal.mk ℕ<(continuumSuccOrdinal d).cof
    rw [Cardinal.mk_nat,hd]
    exact PSet.omega_lt_aleph_one
  have hβ : β<α := Ordinal.iSup_lt_of_lt_cof hSmall (fun n => (jOrd (f n)).toOrd.property)
  let a : bSet PreparedBA := check (PSet.ordinalMk β)
  have ha : c≤a∈ᴮ check y := check_mem (prepOrdinalMk_mem_of_lt_r397 hβ)
  have hC : c≤⨆ n : bSet PreparedBA,(n∈ᴮ bSet.omega)⊓
      (⨆ b : bSet PreparedBA,(b∈ᴮ check y)⊓((pair n b∈ᴮ G)⊓(a∈ᴮ b))) :=
    (le_inf (hc.trans (inf_le_right.trans (iInf_le _ a))) ha).trans Lattice.bv_imp_elim
  have hE : B_ext (fun n : bSet PreparedBA => ⨆ b : bSet PreparedBA,
      (b∈ᴮ check y)⊓((pair n b∈ᴮ G)⊓(a∈ᴮ b))) :=
    B_ext_iSup (h := fun b => B_ext_inf B_ext_const (B_ext_inf B_ext_pair_mem_left B_ext_const))
  rw [← bounded_exists (h_congr := hE)] at hC
  have hBot : c≤⊥ := by
    apply (le_inf le_rfl hC).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro n'
    simp only [bSet.omega,check_bval_top,top_inf_eq,check_func]
    let n := (check_cast n' : PSet.omega.Type).down
    let x : bSet PreparedBA := check (PSet.omega.Func (ULift.up n))
    change c⊓(⨆ b : bSet PreparedBA,(b∈ᴮ check y)⊓((pair x b∈ᴮ G)⊓(a∈ᴮ b)))≤⊥
    have hB : B_ext (fun b : bSet PreparedBA => (pair x b∈ᴮ G)⊓(a∈ᴮ b)) :=
      B_ext_inf B_ext_pair_mem_right B_ext_mem_right
    rw [← bounded_exists (h_congr := hB),inf_iSup_eq]
    apply iSup_le
    intro j'
    simp only [check_bval_top,top_inf_eq,check_func]
    let j : y.Type := check_cast j'
    let w : bSet PreparedBA := check (y.Func j)
    let z : bSet PreparedBA := check (y.Func (f n))
    let v := c⊓((pair x w∈ᴮ G)⊓(a∈ᴮ w))
    change v≤⊥
    have hEq : v≤z=ᴮ w := eq_of_is_func_of_eq
      (inf_le_left.trans (hc.trans (inf_le_left.trans inf_le_left))) bv_refl
      (inf_le_left.trans (hV n)) (inf_le_right.trans inf_le_left)
    have hA : v≤a∈ᴮ z := subst_congr_mem_right' (hEq.trans_eq bv_eq_symm)
      (inf_le_right.trans inf_le_right)
    have hz : z=check (PSet.ordinalMk (o n)) := by
      unfold z o jOrd y
      rw [ordinalMk_func_eq_r396]
    rw [hz] at hA
    exact check_not_mem (groundOrd_not_mem_of_not_lt_r418 (not_lt_of_ge (Ordinal.le_iSup o n))) hA
  exact imageCondition_ne_bot_r50 q (le_bot_iff.mp hBot)

end PreparedModel
end JSP000933
