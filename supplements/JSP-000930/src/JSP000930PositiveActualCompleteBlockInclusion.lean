import JSP000930PositiveMarkedCohenProjection
import JSP000930PositiveCompleteCohenProjection

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B X : Type} [CompleteBooleanAlgebra B]

abbrev CohenBlockBA (B : Type) [CompleteBooleanAlgebra B] (S : Set X) :=
  RO (BlockTotal B S)

theorem restrict_of_supported_le {S : Set X} (p : Trace X) (hs : Supported p S) :
    (restrict p S).1 ≤ p := by
  change Extends (restrict p S).1.1 p.1
  exact ⟨fun x hx => (restrict_mem_dom p S x).mpr ⟨hx,hs x hx⟩,
    fun x hx => restrict_bit_eq p S x hx (hs x hx)⟩

theorem restrict_total_of_supported_le {S : Set X} (q : BlockTotal B S) :
    restrictTotal q.1 S ≤ q := by
  change (restrictTotal q.1 S).1 ≤ q.1
  exact (cohen_total_le_iff _ _).mpr ⟨le_rfl,restrict_of_supported_le q.1.trace q.2⟩

theorem supported_le_restrict_total {S : Set X} (q : BlockTotal B S) :
    q ≤ restrictTotal q.1 S := by
  change q.1 ≤ (restrictTotal q.1 S).1
  exact (cohen_total_le_iff _ _).mpr ⟨le_rfl,le_restrict q.1.trace S⟩

noncomputable def cohenBlockProjection (B : Type) [CompleteBooleanAlgebra B]
    (S : Set X) : ForcingProjection (CohenTotal B X) (BlockTotal B S) where
  toFun p := restrictTotal p S
  mono := by
    intro p q hpq
    exact restrictTotal_mono S hpq
  liftBelow := by
    intro p q hq
    obtain ⟨r,hr,hqr⟩ := lift_stronger_total_block p S q hq
    exact ⟨r,hr,(show restrictTotal r S ≤ restrictTotal q.1 S from
      restrictTotal_mono S hqr).trans (restrict_total_of_supported_le q)⟩

noncomputable def blockEmbed (B : Type) [CompleteBooleanAlgebra B] (S : Set X) :
    CohenBlockBA B S → CohenBA B X :=
  (cohenBlockProjection B S).pull

theorem blockEmbed_injective (S : Set X) :
    Function.Injective (blockEmbed B S) :=
  (cohenBlockProjection B S).pull_injective_of_weak_surj fun q =>
    ⟨q.1,restrict_total_of_supported_le q,supported_le_restrict_total q⟩

theorem blockEmbed_general_iSup (S : Set X) {I : Type*} (f : I → CohenBlockBA B S) :
    blockEmbed B S (⨆ i, f i) = ⨆ i, blockEmbed B S (f i) :=
  (cohenBlockProjection B S).pull_iSup f

theorem blockEmbed_compl (S : Set X) (a : CohenBlockBA B S) :
    blockEmbed B S aᶜ = (blockEmbed B S a)ᶜ :=
  (cohenBlockProjection B S).pull_compl a

theorem blockEmbed_inf (S : Set X) (a b : CohenBlockBA B S) :
    blockEmbed B S (a ⊓ b) = blockEmbed B S a ⊓ blockEmbed B S b :=
  (cohenBlockProjection B S).pull_inf a b

theorem blockEmbed_top (S : Set X) :
    blockEmbed B S ⊤ = ⊤ := (cohenBlockProjection B S).pull_top

end JSP000930.Positive.Cohen
