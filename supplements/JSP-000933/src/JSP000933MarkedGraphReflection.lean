import JSP000933TwoPointCoverWitness
import JSP000933SaturatedDomainBridge

namespace JSP000933
namespace ForcingTransport

open CantorCodes BooleanCompletion

variable {B C I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

theorem transport_le_iff (F : CompleteValueMap B C) {x y : B} :
    F.toFun x≤F.toFun y ↔ x≤y :=
  ⟨F.reflect_le_r93,fun h => F.monotone h⟩

theorem mask_colorCode_congr
    {m : C} {a b : Word×Word→C} (h : ∀ w,m⊓a w=m⊓b w) (x y : ℕ→C) :
    m⊓colorValue a x y=m⊓colorValue b x y :=
  mask_iSup_congr_r126 (fun w => mask_inf_congr_r126 (h w) rfl)

theorem saturatedDomain_ge_row (x : I→ℕ→B) (d : I→B) (i : I) :
    d i ≤ saturatedDomain x d (x i) := by
  apply le_iSup_of_le i
  rw [realEqValue_refl_r127,inf_top_eq]

theorem saturatedDomain_lifts_under
    (F : CompleteValueMap B C) (m : C) (D : (ℕ→C)→C) (hD : RealTestExt D)
    (x : I→ℕ→B) (d : I→B) (X : I→ℕ→C)
    (hBits : ∀ i n,m⊓F.toFun (x i n)=m⊓X i n)
    (hDom : ∀ i,m⊓F.toFun (d i)≤D (X i)) (y : ℕ→B) :
    m⊓F.toFun (saturatedDomain x d y)≤D (F.toFun ∘ y) := by
  rw [map_saturatedDomain_r127,saturatedDomain,inf_iSup_eq]
  apply iSup_le
  intro i
  let r := m⊓(F.toFun (d i)⊓realEqValue (F.toFun ∘ y) (F.toFun ∘ x i))
  have h1 : r ≤ realEqValue (F.toFun ∘ y) (F.toFun ∘ x i) := inf_le_right.trans inf_le_right
  have h2 : r ≤ realEqValue (F.toFun ∘ x i) (X i) :=
    inf_le_left.trans ((le_realEqValue_iff_r126 _ _ _).mpr (hBits i))
  have h3 : r ≤ realEqValue (F.toFun ∘ y) (X i) :=
    (le_inf h1 h2).trans (realEqValue_trans_r127 _ _ _)
  have h4 : r≤D (X i) := (le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans (hDom i)
  exact (le_inf le_rfl h4).trans ((hD r _ _ h3).ge.trans inf_le_right)

theorem graph_valid_lifts_down
    (F : CompleteValueMap B C) (q : B)
    (D : (ℕ→C)→C) (K : Word×Word→C)
    (d : (ℕ→B)→B) (k : Word×Word→B)
    (hD : ∀ x,F.toFun q⊓F.toFun (d x)≤D (F.toFun ∘ x))
    (hCode : ∀ w,F.toFun q⊓F.toFun (k w)=F.toFun q⊓K w)
    (hIrr : ∀ x,F.toFun q⊓D x≤(colorValue K x x)ᶜ)
    (hSym : ∀ x y,(F.toFun q⊓(D x⊓D y))⊓colorValue K x y≤colorValue K y x) :
    (∀ x,q⊓d x≤(colorValue k x x)ᶜ) ∧
      ∀ x y,(q⊓(d x⊓d y))⊓colorValue k x y≤colorValue k y x := by
  have hC (x y : ℕ→B) :
      F.toFun q⊓F.toFun (colorValue k x y)=
        F.toFun q⊓colorValue K (F.toFun ∘ x) (F.toFun ∘ y) := by
    rw [map_colorValue_r105]
    exact mask_colorCode_congr hCode _ _
  constructor
  · intro x
    apply F.reflect_le_r93
    rw [F.map_inf,F.map_compl]
    have hLe : F.toFun q⊓F.toFun (d x)≤
        F.toFun q⊓(colorValue K (F.toFun ∘ x) (F.toFun ∘ x))ᶜ := by
      exact le_inf inf_le_left ((le_inf inf_le_left (hD x)).trans (hIrr _))
    exact hLe.trans ((mask_compl_congr_r126 (hC x x)).ge.trans inf_le_right)
  · intro x y
    apply F.reflect_le_r93
    rw [F.map_inf,F.map_inf,F.map_inf]
    let a := (F.toFun q⊓(F.toFun (d x)⊓F.toFun (d y)))⊓F.toFun (colorValue k x y)
    have hA : a≤F.toFun q := inf_le_left.trans inf_le_left
    have hDx : a≤D (F.toFun ∘ x) := (le_inf hA
      (inf_le_left.trans (inf_le_right.trans inf_le_left))).trans (hD x)
    have hDy : a≤D (F.toFun ∘ y) := (le_inf hA
      (inf_le_left.trans (inf_le_right.trans inf_le_right))).trans (hD y)
    have hCol : a≤colorValue K (F.toFun ∘ x) (F.toFun ∘ y) :=
      (le_inf hA inf_le_right).trans ((hC x y).le.trans inf_le_right)
    have hRev := (le_inf (le_inf hA (le_inf hDx hDy)) hCol).trans (hSym _ _)
    exact (le_inf hA hRev).trans ((hC y x).ge.trans inf_le_right)

end ForcingTransport
end JSP000933
