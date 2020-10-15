Require Import Rel.Definitions.
Require Import Rel.BasicFacts.
Set Implicit Arguments.

Section section_compat_tm_val.
Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅).

Lemma compat_tm_val n v₁ v₂ :
n ⊨ ⟦ Ξ Γ ⊢ v₁ ≼ˡᵒᵍᵥ v₂ : T ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ v₁ ≼ˡᵒᵍ v₂ : T # E ⟧.
Proof.
intro Hv.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
iespecialize Hv.
ispecialize Hv ; [ eassumption | ].
ispecialize Hv ; [ eassumption | ].
ispecialize Hv ; [ eassumption | ].
ispecialize Hv ; [ eassumption | ].
simpl.
apply 𝓥_in_𝓣.
apply Hv.
Qed.

Lemma compat_ktx_hole n :
n ⊨ ⟦ Ξ Γ ⊢ ktx_hole ≼ˡᵒᵍ ktx_hole : T # E ⇢ T # E ⟧.
Proof.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.

iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro t₁ ; iintro t₂ ; iintro Ht.
apply Ht.
Qed.

End section_compat_tm_val.
