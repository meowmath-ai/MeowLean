import JSP000930ActualWorkingNameTransport

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

noncomputable def actualSurvivorRow (a r : GroundContinuumSuccIndex) :=
  supportedSymbolicQ (actualWorkingInputs a).site (actualWetzelRowPalette a r) (WorkingDomain a)

noncomputable def actualSurvivorProduct (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) :=
  rowProductQ (fun r : s => actualSurvivorRow a r.val)

theorem actualSurvivorRow_self (a : GroundContinuumSuccIndex) :
    actualSurvivorRow a a = (actualWorkingInputs a).row a := by
  unfold actualSurvivorRow WetzelWorkInputs.row
  rw [actualWorkingInputs_palette_eq]

private theorem noAllowedPins {J : Type} {A : J→Prop} (hA : ∀ j,¬A j)
    (t : SymbolicTrace J) (h : SymbolicAt A t) : t.pins = [] := by
  cases he : t.pins with
  | nil => rfl
  | cons p l =>
    have hp : p ∈ t.pins := he.symm ▸ List.mem_cons_self
    exact (hA p.1 (h p.1 (List.mem_map.mpr ⟨p,hp,rfl⟩))).elim

def zeroPinCode {J : Type} {A : J → Prop} (t : SupportedSymbolic J A) :
    Option (List (ℚ×ℚ) × ℕ × ℚ) :=
  t.val.map (fun p => (p.seed,p.radius,p.budget))

theorem zeroPinCode_injective {J : Type} {A : J → Prop} (hA : ∀ j,¬A j) :
    Function.Injective (zeroPinCode (A := A)) := by
  rintro ⟨p,hp⟩ ⟨q,hq⟩ he
  apply Subtype.ext
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some q => cases he
  | some p =>
    cases q with
    | none => cases he
    | some q =>
      have hP : p.pins = [] := noAllowedPins hA p hp
      have hQ : q.pins = [] := noAllowedPins hA q hq
      have hh : (p.seed,p.radius,p.budget) = (q.seed,q.radius,q.budget) := Option.some.inj he
      cases p with
      | mk ps pp pr pb _ _ =>
        cases q with
        | mk qs qp qr qb _ _ =>
          change (ps,pr,pb) = (qs,qr,qb) at hh
          change pp=[] at hP
          change qp=[] at hQ
          subst pp
          subst qp
          have h₁ : ps=qs := congrArg Prod.fst hh
          have h₂ : pr=qr := congrArg (fun x => x.2.1) hh
          have h₃ : pb=qb := congrArg (fun x => x.2.2) hh
          subst qs
          subst qr
          subst qb
          rfl

theorem actualFirstWorkingPrefix_projectedCCC :
    ProjectedAntichainCCC (prefixMaskRealization actualWetzelTail
      (wetzel_bot_lt_work firstGroundWetzelStage)).project :=
  actualBulkPrefix_projectedCCC actualWetzelRest

theorem actualWorkingPrefix_boundsOmegaOne (a : GroundContinuumSuccIndex)
    (h : ProjectedAntichainCCC (prefixMaskRealization actualWetzelTail (wetzel_bot_lt_work a)).project) :
    BoundsCountableOmegaOneNames (ActualWorkBA a) :=
  rowBounds_ofIso ((nativeWetzelPrefixPull actualWetzelRest (wetzel_bot_lt_work a)).trans
    (wetzelHistoryChart actualWetzelRest (wetzelWorkStage a)).symm)
    (prepared_relativeCCC_boundsOmegaOne (nativeWetzelPrefixQ_relativeCCC actualWetzelRest _ h))

theorem actualFirstWorkingPrefix_jointCCC (s : Finset GroundContinuumSuccIndex) :
    ForcesRelativeCCC (actualSurvivorProduct firstGroundWetzelStage s) := by
  letI : Countable (SupportedSymbolic GroundContinuumSuccIndex (WorkingDomain firstGroundWetzelStage)) :=
    Function.Injective.countable (zeroPinCode_injective (fun j => (firstGroundWetzelStage_le j).not_gt))
  exact relativeCCC_countable_carrier
    (actualWorkingPrefix_boundsOmegaOne _ actualFirstWorkingPrefix_projectedCCC) _

end JSP000930.Negative
