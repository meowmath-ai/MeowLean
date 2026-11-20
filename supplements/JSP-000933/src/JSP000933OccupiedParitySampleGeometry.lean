import JSP000933ActualSampleTreeTests

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bitsBelowValue_of_pointwise_r272 {a b : ℕ → B} {p : B} (h : ∀ m, a m≤b m) :
    p≤bitsBelowValue a b := by
  unfold bitsBelowValue
  apply le_iInf
  intro m
  change p≤(a m)ᶜ⊔b m
  exact (le_materialImp_iff_r126 p _ _).mpr (inf_le_right.trans (h m))

theorem ActualBranchCrossingData.slotSample_qualifies_r272
    {G : bSet B} {ks : ℕ → ℕ} {p q : B} (T : ActualBranchCrossingData G ks p)
    (j l : ℕ) (u : Word) (hp : q≤p)
    (hOcc : q≤closedSamplePresent (namedBranchCrossDomain G) (T.cover j) l u) :
    q≤closedSampleTest (namedBranchCrossDomain G) (T.cover j) l u ((T.samples j).nameFor l u) :=
  (le_inf hp hOcc).trans ((T.samples j).qualified l u)

theorem ActualBranchCrossingData.occupiedParitySample_beforePrefix_r272
    {G : bSet B} {ks : ℕ → ℕ} {p q : B} (T : ActualBranchCrossingData G ks p)
    (j l k : ℕ) (b : Bool) (u : Word) (hl : l≤k) (hPar : k%2≠colorParity b)
    (hu : u.length=4*actualSampleCut j k) (hp : q≤p)
    (hOcc : q≤closedSamplePresent (namedBranchCrossDomain G) (T.cover j) l u) :
    q≤afterCutDisjointValue (crossCap ((T.samples j).nameFor l u))
      (actualParityCap T.freshCap j b) (actualSampleCut j k) := by
  refine afterCutDisjointValue_intro_r268 (fun m hm => ?_)
  by_cases h : m<actualSampleCut j (k+1)
  · have hBand := actualBand_at_r268 j k m hm h
    simp only [actualParityCap,hBand,ite_eq_right hPar,inf_bot_eq,le_rfl]
  · have hCut := (actualSampleCut_lookahead_r267 j k l u hl hu).trans (Nat.le_of_not_gt h)
    have hAway := actualFreshBranch_avoids_supportCap_r265 T.support (j,l,u) _
      ((le_inf hp hOcc).trans (T.supportGood j l u)) m hCut
    exact (le_inf inf_le_left (le_inf (inf_le_right.trans inf_le_left)
      ((inf_le_right.trans inf_le_right).trans (actualParityCap_le_r268 T.freshCap j b m)))).trans hAway

theorem ActualBranchCrossingData.occupiedParitySample_incomp_r272
    {G : bSet B} {ks : ℕ → ℕ} {p q : B} (T : ActualBranchCrossingData G ks p)
    (j l : ℕ) (b : Bool) (u : Word) (hp : q≤p)
    (hOcc : q≤closedSamplePresent (namedBranchCrossDomain G) (T.cover j) l u) :
    q≤actualIncompCaps neatBranchLabeling (actualParityCap T.freshCap j b)
      (crossCap ((T.samples j).nameFor l u)) := by
  let s : SampleSlot := (j,l,u)
  let i := Encodable.encode s
  let X := actualFreshBranch T.support
  let A := actualParityCap T.freshCap j b
  let C := crossCap ((T.samples j).nameFor l u)
  have hOpp : q≤bitEq (X i) (T.support s i)ᶜ :=
    (le_bitEq_iff_r126 _ _ _).mpr
      (congrArg (fun x : B => q⊓x) (actualFreshBranch_at_slot_r265 T.support s))
  have hA : q≤bitsBelowValue A (actualBranchBits X) :=
    bitsBelowValue_of_pointwise_r272 (actualParityCap_le_r268 _ _ _)
  have hC : q≤bitsBelowValue C (actualBranchBits (T.support s)) :=
    (le_inf hp hOcc).trans (T.supportGood j l u)
  have hUnbA : q≤actualUnboundedCap A := le_top.trans (actualParityCap_unbounded_r268 X j b)
  have hQual := T.slotSample_qualifies_r272 j l u hp hOcc
  have hUnbC : q≤actualUnboundedCap C :=
    hQual.trans (inf_le_left.trans ((show namedBranchCrossDomain G _ ≤ branchCapExtra C from inf_le_left).trans inf_le_left))
  exact opposedBranches_unboundedCaps_incomp_r269 X (T.support s) A C i hOpp hA hC hUnbA hUnbC

end SetLanguage
end JSP000933
