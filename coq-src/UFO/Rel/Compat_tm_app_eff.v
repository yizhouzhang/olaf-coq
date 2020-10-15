Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.BasicFacts.
Require Import UFO.Rel.Monotone.
Require Import UFO.Rel.Compat_bind_EV.
Require Import UFO.Util.Subset.
Require Import UFO.Util.Postfix.
Set Implicit Arguments.

Section section_ccompat_tm_app_eff.

Context (n : nat).
Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (σ : ms ∅ (inc EV) LV ∅) (ℓ : lbl LV ∅) (E E' : eff ∅ EV LV ∅).
Context (ξ₁ ξ₂ : list var).
Context (Hξ : n ⊨ (𝜩 Ξ ξ₁ ξ₂)ᵢ).
Context (Hδ : n ⊨ δ_is_closed ξ₁ ξ₂ δ).
Context (Hρ₁ρ₂ : n ⊨ (ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂)ᵢ).

Lemma ccompat_tm_app_eff (t₁ t₂ : tm0) :
n ⊨ 𝓣⟦ Ξ ⊢ (ty_ms (ms_ev σ) ℓ) # E' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ →
n ⊨ 𝓣⟦ Ξ ⊢ (ty_ms (EV_subst_ms E σ) ℓ) # E' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (tm_app_eff t₁ (subst_eff δ₁ ρ₁ E))
    (tm_app_eff t₂ (subst_eff δ₂ ρ₂ E)).
Proof.
intro Ht.
change (tm_app_eff t₁ (subst_eff δ₁ ρ₁ E))
with (ktx_plug (ktx_app_eff ktx_hole (subst_eff δ₁ ρ₁ E)) t₁).
change (tm_app_eff t₂ (subst_eff δ₂ ρ₂ E))
with (ktx_plug (ktx_app_eff ktx_hole (subst_eff δ₂ ρ₂ E)) t₂).
eapply plug0 ; simpl ; eauto using postfix_refl.
clear t₁ t₂ Ht.

iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro v₁ ; iintro v₂ ; iintro Hv ; simpl.
destruct v₁ as [ | | | m₁ [ | X₁ ] | m₁ [ | X₁ ] ], v₂ as [ | | | m₂ [ | X₂ ] | m₂ [ | X₂ ] ] ; simpl 𝓥_Fun in Hv ;
idestruct Hv as m₁' Hv ; idestruct Hv as m₂' Hv ;
idestruct Hv as X₁' Hv ; idestruct Hv as X₂' Hv ;
idestruct Hv as Hv Hr ; ielim_prop Hv ; destruct Hv as [Hv₁ Hv₂] ;
inversion Hv₁ ; inversion Hv₂ ; clear Hv₁ Hv₂ ; subst m₁' m₂' X₁' X₂'.

idestruct Hr as HX₁X₂ Hr ; idestruct Hr as m₁' Hr ; idestruct Hr as m₂' Hr ;
idestruct Hr as Hm Hr ; ielim_prop Hm ; destruct Hm ; subst m₁ m₂.
eapply 𝓣_step_r ; [ apply step_app_eff | ].
eapply 𝓣_step_l ; [ apply step_app_eff | ].
iintro_later.
apply 𝓥_in_𝓣.
simpl 𝓥_Fun.
repeat ieexists ; repeat isplit ; [ iintro_prop ; crush | assumption | ].

ielim_vars Hr ; [ | apply postfix_refl | apply postfix_refl ].
ispecialize Hr (subst_eff δ₁ ρ₁ E).
ispecialize Hr (subst_eff δ₂ ρ₂ E).
ispecialize Hr (𝓤⟦ Ξ ⊢ E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ).
ispecialize Hr.
{ do 5 iintro ; iintro L₁ ; iintro L₂ ; iintro.
  iintro_prop ; assert (L₁ \c from_list ξ₁ ∧ L₂ \c from_list ξ₂) as HL₁L₂.
  - eapply 𝓤_is_closed ; eauto.
  - clear - Hξ₁' Hξ₂' HL₁L₂ ; destruct HL₁L₂ ; split ;
    eauto using subset_trans, postfix_is_subset.
}

replace Ξ with (EV_subst_XEnv E (EV_shift_XEnv Ξ))
by (erewrite EV_bind_map_XEnv, EV_bind_XEnv_id, EV_map_XEnv_id ; crush).
erewrite <- I_iff_elim_M ; [ apply Hr | ].
apply EV_bind_𝓜.
+ intro α ; destruct α as [ | α ] ; simpl ; crush.
+ intro α ; destruct α as [ | α ] ; simpl ; crush.
+ iintro α ; destruct α as [ | α ] ; simpl.
  - erewrite EV_bind_map_XEnv, EV_bind_XEnv_id, EV_map_XEnv_id ; try reflexivity.
    repeat iintro ; apply auto_contr_id.
  - repeat iintro.
    isplit ; iintro H ; [ ileft | idestruct H as H H ] ; crush.
Qed.

End section_ccompat_tm_app_eff.

Section section_compat_tm_app_eff.
Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (σ : ms ∅ (inc EV) LV ∅) (ℓ : lbl LV ∅) (E E' : eff ∅ EV LV ∅).

Lemma compat_tm_app_eff n t₁ t₂ :
n ⊨ ⟦ Ξ Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : (ty_ms (ms_ev σ) ℓ) # E' ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (tm_app_eff t₁ E) ≼ˡᵒᵍ (tm_app_eff t₂ E) :
      (ty_ms (EV_subst_ms E σ) ℓ) # E' ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
simpl subst_tm.
apply ccompat_tm_app_eff ; try assumption.

iespecialize Ht ; repeat (ispecialize Ht ; [ eassumption | ]).
apply Ht.
Qed.

Lemma compat_ktx_app_eff n T_hole E_hole K₁ K₂ :
n ⊨ ⟦ Ξ Γ ⊢ K₁ ≼ˡᵒᵍ K₂ :
      T_hole # E_hole ⇢ (ty_ms (ms_ev σ) ℓ) # E' ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (ktx_app_eff K₁ E) ≼ˡᵒᵍ (ktx_app_eff K₂ E) :
      T_hole # E_hole ⇢ (ty_ms (EV_subst_ms E σ) ℓ) # E' ⟧.
Proof.
intro HK.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro t₁ ; iintro t₂ ; iintro Ht.
iespecialize HK.
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ispecialize HK ; [ eassumption | ].
ielim_vars HK ; [ | eassumption | eassumption ].
iespecialize HK.
ispecialize HK ; [ eassumption | ].
simpl ktx_plug.
apply ccompat_tm_app_eff ; try apply HK.
- iintro_prop ; eapply 𝜩_monotone ; eauto.
- eapply δ_is_closed_monotone ; eauto.
- iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto.
Qed.

End section_compat_tm_app_eff.
