Require Import UFO.Lang.Static.
Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.Monotone.
Set Implicit Arguments.

Section section_compat_md_res.

Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (σ : ms ∅ EV (inc LV) ∅) (ℓ : lbl LV ∅) (m₁ m₂ : md EV (inc LV) V ∅).
Context (X : var).
Context (Ta Tb : ty ∅ EV LV ∅) (Ea Eb : eff ∅ EV LV ∅) (t₁ t₂ : tm EV LV (inc V) ∅).
Context (BindsX : binds X (Tb, Eb) Ξ).

Lemma compat_md_res n :
n ⊨ ⟦ Ξ (env_ext Γ (ty_cont Ta (ef_lbl (lbl_id (lid_f X)) :: Ea) Tb Eb)) ⊢ t₁ ≼ˡᵒᵍ t₂ : Tb # Eb ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (md_res t₁) ≼ˡᵒᵍₘ (md_res t₂) : (ms_res Ta Ea) ^ (lbl_id (lid_f X)) ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
simpl 𝓜_Fun.
rewrite BindsX.
apply get_some_inv in BindsX as HX.

repeat ieexists ; repeat isplit ; [ auto | auto | ].
iintro_later.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro K₁ ; iintro K₂ ; iintro HK.
erewrite <- I_iff_elim_M ; [ | apply fold_𝓥𝓤_in_𝓣 ].

ispecialize Ht ξ₁' ; ispecialize Ht ξ₂' ;
ispecialize Ht δ₁ ; ispecialize Ht δ₂ ; ispecialize Ht δ ;
ispecialize Ht ρ₁ ; ispecialize Ht ρ₂ ; ispecialize Ht ρ.
ispecialize Ht (env_ext γ₁ K₁) ;
ispecialize Ht (env_ext γ₂ K₂).
ispecialize Ht.
{ iintro_prop ; eapply 𝜩_monotone ; eauto. }
ispecialize Ht.
{ eapply δ_is_closed_monotone ; eauto. }
ispecialize Ht.
{ iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto. }
ispecialize Ht.
{ iintro x ; destruct x as [ | x ] ; simpl.
  + rewrite BindsX.
    repeat ieexists ; isplit ; [ auto | ].
    eapply I_iff_elim_M ; [ | apply HK ].
    apply 𝓚_Fun_nonexpansive ; repeat iintro.
    - auto_contr.
    - apply fold_𝓥𝓤_in_𝓣.
  + iespecialize Hγ ; eapply 𝓥_monotone ; eauto.
}

repeat erewrite V_bind_bind_tm ; try apply Ht.
{ intro x ; destruct x ; simpl ; [ crush | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}
{ intro x ; destruct x ; simpl ; [ crush | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; reflexivity.
}
Qed.

End section_compat_md_res.
