import JSP000933PreparedCollapseSize
import Mathlib.SetTheory.Cardinal.Regular

open Cardinal Flypitch

namespace JSP000933
namespace PreparedModel

noncomputable abbrev GroundContinuumSucc : Cardinal := Order.succ (𝔠 : Cardinal)

noncomputable abbrev GroundContinuumSuccIndex : Type := GroundContinuumSucc.ord.ToType

noncomputable def continuumSuccOrdinal (i : GroundContinuumSuccIndex) : Ordinal :=
  ((Ordinal.ToType.mk (o := GroundContinuumSucc.ord)).symm i).val

theorem continuumSuccOrdinal_lt_r392 (i : GroundContinuumSuccIndex) :
    continuumSuccOrdinal i<GroundContinuumSucc.ord :=
  ((Ordinal.ToType.mk (o := GroundContinuumSucc.ord)).symm i).property

theorem groundContinuumSucc_regular_r392 : GroundContinuumSucc.IsRegular :=
  Cardinal.isRegular_succ Cardinal.aleph0_le_continuum

theorem baseCollapse_disjointFamily_card_r392 {I : Type} (f : I → CHBase)
    (hF : ∀ i, f i≠⊥) (hD : Pairwise (fun i j => Disjoint (f i) (f j))) : Cardinal.mk I≤𝔠 := by
  classical
  have hBasic (i : I) : ∃ a : BaseCollapseBasic, baseCollapseImage a≤f i := by
    obtain ⟨v,hv,hvf⟩ := baseCollapse_denseOmegaClosed_r390.1.2 (f i) (bot_lt_iff_ne_bot.mpr (hF i))
    obtain ⟨a,ha⟩ := hv
    exact ⟨a,by simpa only [ha] using hvf⟩
  choose a ha using hBasic
  have haInj : Function.Injective a := by
    intro i j he
    by_contra hn
    have h1 : baseCollapseImage (a i)≤f i := ha i
    have h2 : baseCollapseImage (a i)≤f j := by simpa only [he] using ha j
    exact baseCollapse_denseOmegaClosed_r390.1.1
      ⟨a i,(hD hn).out (baseCollapseImage (a i)) h1 h2⟩
  exact (Cardinal.mk_le_of_injective haInj).trans baseCollapseBasic_card_le_continuum_r391

theorem baseCollapse_shortArrays_bounded_r392 {I : Type} (hI : Cardinal.mk I<GroundContinuumSucc)
    (q : CHBase) (v : I → GroundContinuumSuccIndex → CHBase)
    (hV : ∀ i, Pairwise (fun j k => Disjoint (q⊓v i j) (q⊓v i k))) :
    ∃ β : Ordinal, β<GroundContinuumSucc.ord ∧
      ∀ i j, β≤continuumSuccOrdinal j → q⊓v i j=⊥ := by
  classical
  let S (i : I) := {j : GroundContinuumSuccIndex // q⊓v i j≠⊥}
  have hS (i : I) : Cardinal.mk (S i)≤𝔠 :=
    baseCollapse_disjointFamily_card_r392 (fun j : S i => q⊓v i j.val)
      (fun j => j.property) (fun j k h => hV i (fun he => h (Subtype.ext he)))
  have hEmb (i : I) : Nonempty (S i ↪ BaseGroundReals.Type) :=
    (Cardinal.le_def _ _).mp ((hS i).trans_eq baseGroundReals_type_card_r391.symm)
  let E (i : I) := Classical.choice (hEmb i)
  let encode (a : Σ i, S i) : I×BaseGroundReals.Type := (a.1,E a.1 a.2)
  have hEnc : Function.Injective encode := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    have hi : i=j := congrArg Prod.fst he
    subst j
    have hb : a=b := (E i).injective (congrArg Prod.snd he)
    subst b
    rfl
  have hDom : Cardinal.mk (Σ i, S i)≤𝔠 := by
    apply (Cardinal.mk_le_of_injective hEnc).trans
    rw [Cardinal.mk_prod,baseGroundReals_type_card_r391]
    simp only [Cardinal.lift_id]
    exact (mul_le_mul_left (Order.lt_succ_iff.mp hI) _).trans_eq Cardinal.continuum_mul_self
  let α (a : Σ i, S i) := continuumSuccOrdinal a.2.val
  have hRegular := groundContinuumSucc_regular_r392
  have hD : Cardinal.mk (Σ i, S i)<GroundContinuumSucc.ord.cof := by
    rw [hRegular.cof_ord]
    exact (Order.lt_succ_iff.mpr hDom)
  have hSup : (⨆ a, α a)<GroundContinuumSucc.ord :=
    Ordinal.iSup_lt_of_lt_cof hD (fun a => continuumSuccOrdinal_lt_r392 a.2.val)
  let β := (⨆ a, α a)+1
  have hβ : β<GroundContinuumSucc.ord := (Cardinal.isSuccLimit_ord hRegular.1).add_one_lt hSup
  refine ⟨β,hβ,?_⟩
  intro i j hj
  by_contra hn
  let a : Σ i, S i := ⟨i,⟨j,hn⟩⟩
  have ha : continuumSuccOrdinal j≤⨆ a, α a := Ordinal.le_iSup α a
  have hLT : (⨆ a, α a)<β := Order.lt_add_one_iff.mpr le_rfl
  exact not_lt_of_ge hj (ha.trans_lt hLT)

end PreparedModel
end JSP000933
