import JSP000930NegativeTransportedCohenPalette
import JSP000930ActualMixedFreshPalettes
import JSP000930NamedDistanceCongruence

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.BooleanAnalysis JSP000930.Negative JSP000930.MixedPalettes
open JSP000933.BooleanCompletion JSP000933.OpenGraphForcing

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

theorem transported_actualMixedPalette_cutOn (M : Label B) (n : ℕ)
    (F : CompleteValueMap (StageCohenBA B) C) :
    ((actualMixedPalette M n).map F).CutOn (⊤ : C) := by
  simpa only [F.map_top] using ComplexBits.map_cutOn F (actualMixedPalette_cutOn M n)

theorem transported_actualMixedPalette_eq_on (M : Label B) (n : ℕ) (r : OmegaOneIndex)
    (F : CompleteValueMap (StageCohenBA B) C) :
    F.toFun ((stageCohenMap B).toFun (M.value r)) ≤
      ((actualMixedPalette M n).map F).name =ᴮ ((paletteBits (B := B) r n).map F).name := by
  simpa only [ComplexBits.map_nameEq] using F.monotone (actualMixedPalette_equal_on M n r)

private theorem replace_avoiding_palette_on {x y f g : ComplexBits C} {m : C}
    (hx : x.CutOn m) (hf : f.CutOn m) (hg : g.CutOn m)
    (hfg : m ≤ f.name =ᴮ g.name) {ε : ℚ} (he : 0 ≤ ε)
    (h : m ≤ distanceLe x g ε ⊓ (g.name =ᴮ y.name)ᶜ) :
    m ≤ distanceLe x f ε ⊓ (f.name =ᴮ y.name)ᶜ := by
  refine le_inf (distanceLe_congr_right930 hx hg hf (bSet.bv_symm hfg) he
    (h.trans inf_le_left)) ?_
  apply le_compl_iff_disjoint_right.mpr
  rw [disjoint_iff_inf_le]
  have hEq : m ⊓ (f.name =ᴮ y.name) ≤ g.name =ᴮ y.name :=
    bSet.bv_trans (bSet.bv_symm (inf_le_left.trans hfg)) inf_le_right
  exact (le_inf hEq (inf_le_left.trans (h.trans inf_le_right))).trans_eq (inf_compl_self _)

theorem transported_actualMixedPalette_avoiding (M : Label B)
    (F : CompleteValueMap (StageCohenBA B) C) :
    AvoidingPalette (fun n => (actualMixedPalette M n).map F) := by
  intro x y p hx hy ε he
  let w (r : OmegaOneIndex) := F.toFun ((stageCohenMap B).toFun (M.value r))
  let h (n : ℕ) := (actualMixedPalette M n).map F
  have hCover : (⨆ r,w r) = (⊤ : C) := by
    unfold w
    rw [← F.map_iSup,← (stageCohenMap B).map_iSup,M.covers,(stageCohenMap B).map_top,F.map_top]
  have hp : p ≤ p ⊓ (⨆ r,w r) := by rw [hCover,inf_top_eq]
  apply hp.trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro r
  let u (n : ℕ) := (paletteBits (B := B) r n).map F
  let q := p ⊓ w r
  have hxQ : x.CutOn q := cutOn_mono930 hx inf_le_left
  have hyQ : y.CutOn q := cutOn_mono930 hy inf_le_left
  have hOld : q ≤ ⨆ n, distanceLe x (u n) ε ⊓ ((u n).name =ᴮ y.name)ᶜ :=
    transported_cohen_avoiding_palette F r x y q hxQ hyQ ε he
  change q ≤ ⨆ n,distanceLe x (h n) ε ⊓ ((h n).name =ᴮ y.name)ᶜ
  apply (le_inf le_rfl hOld).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro n
  let m := q ⊓ (distanceLe x (u n) ε ⊓ ((u n).name =ᴮ y.name)ᶜ)
  have hf := cutOn_mono930 (transported_actualMixedPalette_cutOn M n F) (le_top : m ≤ ⊤)
  have hg := cutOn_mono930 (transported_cohen_palette_cutOn F r n) (le_top : m ≤ ⊤)
  have hfg : m ≤ (h n).name =ᴮ (u n).name :=
    (inf_le_left.trans inf_le_right).trans (transported_actualMixedPalette_eq_on M n r F)
  exact le_iSup_of_le n (replace_avoiding_palette_on (cutOn_mono930 hxQ inf_le_left)
    hf hg hfg he.le inf_le_right)

theorem transported_actualMixedPalette_dense (M : Label B)
    (F : CompleteValueMap (StageCohenBA B) C) :
    DensePalette (fun n => (actualMixedPalette M n).map F) :=
  avoidingPalette_dense (transported_actualMixedPalette_avoiding M F)

end JSP000930.Negative.Cohen
