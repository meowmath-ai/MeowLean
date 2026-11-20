import JSP000933BooleanEnumerations
import JSP000933BooleanNamedClique

open scoped Flypitch Cardinal
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open BooleanCompletion OpenGraphForcing

noncomputable instance completion_nontrivialCompleteBooleanAlgebra_r73
    {P : Type*} [Preorder P] [Nonempty P] : NontrivialCompleteBooleanAlgebra (RO P) where
  toCompleteBooleanAlgebra := inferInstance
  bot_lt_top :=
    (bot_lt_iff_ne_bot.mpr (imageCondition_ne_bot_r50 (Classical.choice ‹Nonempty P›))).trans_le le_top

instance cliqueCondition_nonempty_r73 {X : Type} {K : Set (X × X)} {Y : OmegaOneIndex → X} :
    Nonempty (CliqueCondition K Y) :=
  ⟨⟨∅,by
    intro i hi
    exact False.elim (Finset.notMem_empty i hi)⟩⟩

noncomputable def cliqueName {X : Type} (K : Set (X × X)) (Y : OmegaOneIndex → X)
    (embed : X → RealCode) : bSet (RO (CliqueCondition K Y)) :=
  familyName (fun i => realCheckName (embed (Y i))) (cliqueBit K Y)

noncomputable def cliqueGroundGraph {X : Type} (K : Set (X × X)) (Y : OmegaOneIndex → X)
    (embed : X → RealCode) : bSet (RO (CliqueCondition K Y)) :=
  groundEdgeName (fun i => realCheckName (embed (Y i))) (fun i j => (Y i,Y j) ∈ K)

noncomputable def hasOmegaEnumeration {B : Type*} [NontrivialCompleteBooleanAlgebra B]
    (s : bSet B) : B :=
  ⨆ f : bSet B, bSet.is_func f ⊓ bSet.is_surj bSet.omega s f

theorem exists_CH_namedUncountableClique_r73 {X : Type}
    [TopologicalSpace X] [SecondCountableTopology X] (K : Set (X × X))
    (hK : IsOpen K) (hSym : ∀ x y, (x,y) ∈ K → (y,x) ∈ K)
    (hIrr : ∀ x, (x,x) ∉ K) (hChrom : UncountablyChromatic K)
    (embed : X → RealCode) (hEmbed : Function.Injective embed) (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ Y : OmegaOneIndex → X, Function.Injective Y ∧
      BooleanCCC (RO (CliqueCondition K Y)) ∧
      nameIsClique (cliqueName K Y embed) (cliqueGroundGraph K Y embed) = ⊤ ∧
      (∀ i : OmegaOneIndex,
        (realCheckName (embed (Y i)) : bSet (RO (CliqueCondition K Y))) ⊆ᴮ bSet.omega = ⊤) ∧
      ∃ p : CliqueCondition K Y, imageCondition p ≤ (hasOmegaEnumeration (cliqueName K Y embed))ᶜ := by
  obtain ⟨Y,hY,hCCC,hd,p,hp⟩ := exists_CH_BooleanClique_stage_r69 hK hSym hIrr hChrom embed hEmbed CH
  have ha (i j : OmegaOneIndex) (hij : i ≠ j) :
      ((realCheckName (embed (Y i)) : bSet (RO (CliqueCondition K Y))) =ᴮ realCheckName (embed (Y j))) = ⊥ :=
    realCheckName_eq_bot_of_ne_r72 (fun he => hij (hY (hEmbed he)))
  have hCount : hasOmegaEnumeration (cliqueName K Y embed) ≤ countableCoverageValue (cliqueBit K Y) :=
    bSet_countableValue_le_matrixValue_r71 (fun i => realCheckName (embed (Y i))) ha (cliqueBit K Y)
  exact ⟨Y,hY,hCCC,familyName_isClique_r72 _ _ _ hd,
    fun i => realCheckName_subset_omega_r72 (embed (Y i)),p,hp.trans (compl_le_compl hCount)⟩

end BooleanNames
end JSP000933
