import JSP000933ActualBranchDiagonalCutoff

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def neatBranchLabeling : ℕ ↪ Word :=
  ⟨neatBlockLabel,neatBlockLabel_injective⟩

noncomputable def namedBranchCrossDomain (G : bSet B) : (ℕ → B) → B :=
  concreteCrossDomain neatBranchLabeling G branchCapExtra

theorem namedBranchCrossDomain_ext_r266 (G : bSet B) : RealTestExt (namedBranchCrossDomain G) :=
  concreteCrossDomain_ext_r260 neatBranchLabeling G branchCapExtra branchCapExtra_ext_r264

structure ActualBranchCrossingData (G : bSet B) (k : ℕ → ℕ) (p : B) where
  cover : ℕ → CoverCode B
  good : ∀ j, p≤goodCoverValue id (namedBranchCrossDomain G)
    (concreteCrossColorTable neatBranchLabeling (k j)) (cover j)
  samples : ∀ j, ClosedCoverSamples (namedBranchCrossDomain G) (cover j) p
  support : SampleSlot → ℕ → B
  supportGood : ∀ j l u, p⊓closedSamplePresent (namedBranchCrossDomain G) (cover j) l u ≤
    bitsBelowValue (crossCap ((samples j).nameFor l u)) (actualBranchBits (support (j,l,u)))

theorem exists_actualBranchCrossingData_r266 (G : bSet B) (k : ℕ → ℕ) (hk : ∀ j, k j≠0)
    {p : B} (F : CoherentSelectedIso B p) (hOCA : p≤namedCantorOCAValue B)
    (hG : p≤actualPreserveReflectValue G) (hF : ∀ x, p≤graphPairBits G false x (F.toName x)) :
    Nonempty (ActualBranchCrossingData G k p) := by
  classical
  obtain ⟨C,hC⟩ := actualOCA_allBudget_crossing_covers_r262 G neatBranchLabeling k hk
    branchCapExtra branchCapExtra_ext_r264 F hOCA hG hF
  let D := namedBranchCrossDomain G
  let S (j : ℕ) : ClosedCoverSamples D (C j) p :=
    Classical.choice (closedCover_has_actualSamples_r261 D (namedBranchCrossDomain_ext_r266 G) (C j) p)
  have hExist (z : SampleSlot) : ∃ x : ℕ → B,
      p⊓closedSamplePresent D (C z.1) z.2.1 z.2.2 ≤
      bitsBelowValue (crossCap ((S z.1).nameFor z.2.1 z.2.2)) (actualBranchBits x) := by
    have h := (S z.1).qualified z.2.1 z.2.2
    have hExtra : p⊓closedSamplePresent D (C z.1) z.2.1 z.2.2 ≤
        branchCapExtra (crossCap ((S z.1).nameFor z.2.1 z.2.2)) :=
      h.trans (inf_le_left.trans (show D _≤branchCapExtra (crossCap _) from inf_le_left))
    exact exists_actualBranch_support_r264 _ hExtra
  choose Br hBr using hExist
  exact ⟨⟨C,hC,S,Br,fun j l u => hBr (j,l,u)⟩⟩

noncomputable def ActualBranchCrossingData.freshCap {G : bSet B} {k : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G k p) : ℕ → B :=
  actualBranchBits (actualFreshBranch T.support)

theorem ActualBranchCrossingData.freshLarge_r266 {G : bSet B} {k : ℕ → ℕ} {p : B}
    (T : ActualBranchCrossingData G k p) : (⊤ : B)≤actualLongBlockLarge T.freshCap :=
  actualBranch_large_r264 (actualFreshBranch T.support)

theorem ActualBranchCrossingData.avoidance_r266 {G : bSet B} {k : ℕ → ℕ} {p q : B}
    (T : ActualBranchCrossingData G k p) (j l : ℕ) (u : Word) (x : ℕ → B) (hq : q≤p)
    (hX : q≤namedBranchCrossDomain G x) (hC : q≤ClosedMember (T.cover j) l x) (hU : q≤cylinderValue x u)
    (m : ℕ) (hm : shortBranchCut (Encodable.encode ((j,l,u) : SampleSlot))≤ m) :
    q⊓(crossCap ((T.samples j).nameFor l u) m⊓T.freshCap m)≤⊥ := by
  have hOcc : q≤closedSamplePresent (namedBranchCrossDomain G) (T.cover j) l u :=
    le_iSup_of_le x (le_inf hX (le_inf hC hU))
  exact actualFreshBranch_avoids_supportCap_r265 T.support (j,l,u) _
    ((le_inf hq hOcc).trans (T.supportGood j l u)) m hm

end SetLanguage
end JSP000933
