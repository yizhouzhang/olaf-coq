Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.Monotone.
Set Implicit Arguments.

Section section_compat_md_tm.

Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (T : ty ∅ EV LV ∅) (σ : ms ∅ EV LV ∅) (ℓ : lbl LV ∅).
Context (m₁ m₂ : md EV LV (inc V) ∅).

Lemma compat_md_tm n :
n ⊨ ⟦ Ξ (env_ext Γ T) ⊢ m₁ ≼ˡᵒᵍₘ m₂ : σ ^ ℓ ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (md_tm m₁) ≼ˡᵒᵍₘ (md_tm m₂) : (ms_tm T σ) ^ ℓ ⟧.
Proof.
intro Hm.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
simpl 𝓜_Fun.
repeat ieexists ; repeat isplit ; [ auto | ].

iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro v₁ ; iintro v₂ ; iintro Hv.
ispecialize Hm ξ₁' ; ispecialize Hm ξ₂' ;
ispecialize Hm δ₁ ; ispecialize Hm δ₂ ; ispecialize Hm δ ;
ispecialize Hm ρ₁ ; ispecialize Hm ρ₂ ; ispecialize Hm ρ.
ispecialize Hm (env_ext γ₁ v₁) ; ispecialize Hm (env_ext γ₂ v₂).
ispecialize Hm.
{ iintro_prop ; eapply 𝜩_monotone ; eauto. }
ispecialize Hm.
{ eapply δ_is_closed_monotone ; eauto. }
ispecialize Hm.
{ iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto. }
ispecialize Hm.
{ iintro x ; destruct x as [ | x ] ; simpl.
  - apply Hv.
  - iespecialize Hγ ; eapply 𝓥_monotone ; eauto.
}

repeat erewrite V_bind_bind_md ; try apply Hm.
{ intro x ; destruct x ; simpl ; [ crush | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}
{ intro x ; destruct x ; simpl ; [ crush | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}
Qed.

End section_compat_md_tm.
