Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Lang.Static.
Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.BasicFacts.
Require Import UFO.Rel.Monotone.
Require Import UFO.Rel.Compat_bind_LV.
Require Import UFO.Util.Subset.
Require Import UFO.Util.Postfix.
Set Implicit Arguments.

Section section_ccompat_tm_app_lbl.
Context (n : nat).
Context (EV LV : Set).
Context (Ξ : XEnv EV LV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : LV → lbl0) (ρ : LV → IRel 𝓣_Sig).
Context (σ : ms ∅ EV (inc LV) ∅) (ℓ ℓ' : lbl LV ∅) (E : eff ∅ EV LV ∅).
Context (Wf_ℓ : wf_lbl Ξ ℓ).
Context (ξ₁ ξ₂ : list var).
Context (t₁ t₂ : tm0).
Context (Hξ : n ⊨ (𝜩 Ξ ξ₁ ξ₂)ᵢ).
Context (Hρ₁ρ₂ : n ⊨ (ρ₁ρ₂_are_closed ξ₁ ξ₂ ρ₁ ρ₂)ᵢ).

Lemma ccompat_tm_app_lbl :
n ⊨ 𝓣⟦ Ξ ⊢ (ty_ms (ms_lv σ) ℓ') # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ →
n ⊨ 𝓣⟦ Ξ ⊢ (ty_ms (LV_subst_ms ℓ σ) ℓ') # E ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (tm_app_lbl t₁ (LV_bind_lbl ρ₁ ℓ))
    (tm_app_lbl t₂ (LV_bind_lbl ρ₂ ℓ)).
Proof.
intro Ht.
change (tm_app_lbl t₁ (LV_bind_lbl ρ₁ ℓ))
with (ktx_plug (ktx_app_lbl ktx_hole (LV_bind_lbl ρ₁ ℓ)) t₁).
change (tm_app_lbl t₂ (LV_bind_lbl ρ₂ ℓ))
with (ktx_plug (ktx_app_lbl ktx_hole (LV_bind_lbl ρ₂ ℓ)) t₂).
eapply plug0 ; simpl ; eauto using postfix_refl.
clear t₁ t₂ Ht.

iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro v₁ ; iintro v₂ ; iintro Hv ; simpl.
destruct v₁ as [ | | | m₁ [ | X₁' ] | m₁ [ | X₁' ] ], v₂ as [ | | | m₂ [ | X₂' ] | m₂ [ | X₂' ] ] ; simpl 𝓥_Fun in Hv ;
idestruct Hv as m₁' Hv ; idestruct Hv as m₂' Hv ;
idestruct Hv as X₁'' Hv ; idestruct Hv as X₂'' Hv ;
idestruct Hv as Hv Hr ; ielim_prop Hv ; destruct Hv as [Hv₁ Hv₂] ;
inversion Hv₁ ; inversion Hv₂ ; clear Hv₁ Hv₂ ; subst m₁' m₂' X₁'' X₂''.

idestruct Hr as HX₁'X₂' Hr ; idestruct Hr as m₁' Hr ; idestruct Hr as m₂' Hr ;
idestruct Hr as Hm Hr ; ielim_prop Hm ; destruct Hm ; subst m₁ m₂.
eapply 𝓣_step_r ; [ apply step_app_lbl | ].
eapply 𝓣_step_l ; [ apply step_app_lbl | ].
iintro_later.
apply 𝓥_in_𝓣.
simpl 𝓥_Fun.
repeat ieexists ; repeat isplit ; [ iintro_prop ; crush | apply HX₁'X₂' | ].
clear HX₁'X₂'.

ielim_vars Hr ; [ | apply postfix_refl | apply postfix_refl ].
destruct (LV_bind_lbl ρ₁ ℓ) as [ | [ | X₁ ] ] eqn:HX₁ ; [ auto | auto | ].
destruct (LV_bind_lbl ρ₂ ℓ) as [ | [ | X₂ ] ] eqn:HX₂ ; [ auto | auto | ].
ispecialize Hr X₁.
ispecialize Hr X₂.
ispecialize Hr (𝓣𝓵⟦ Ξ ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ).

ispecialize Hr.
{ clear Hr.
  apply postfix_is_subset in Hξ₁' ; apply postfix_is_subset in Hξ₂'.
  destruct ℓ as [ α | [ | X ] ] ; [ | auto | ] ; simpl in HX₁, HX₂.
  + ielim_prop Hρ₁ρ₂ ; specialize (Hρ₁ρ₂ α) ; rewrite HX₁, HX₂ in Hρ₁ρ₂.
    iintro_prop ; split.
    - destruct (Hρ₁ρ₂ X₁) as [? _] ; auto.
    - destruct (Hρ₁ρ₂ X₂) as [_ ?] ; auto.
  + inversion HX₁ ; inversion HX₂ ; subst X₁ X₂.
    inversion Wf_ℓ ; subst.
    ielim_prop Hξ ; destruct Hξ as [Hξ₁ Hξ₂].
    iintro_prop ; crush.
}

replace Ξ with (LV_subst_XEnv ℓ (LV_shift_XEnv Ξ))
by (erewrite LV_bind_map_XEnv, LV_bind_XEnv_id, LV_map_XEnv_id ; crush).
replace ℓ' with (LV_subst_lbl ℓ (LV_shift_lbl ℓ'))
by (erewrite LV_bind_map_lbl, LV_bind_lbl_id, LV_map_lbl_id ; crush).
erewrite <- I_iff_elim_M ; [ apply Hr | clear Hr ].
apply LV_bind_𝓜.
+ crush.
+ crush.
+ iintro α ; destruct α as [ | α ] ; repeat iintro ; simpl.
  - erewrite LV_bind_map_XEnv, LV_map_XEnv_id, LV_bind_XEnv_id ;
    try reflexivity ; try auto_contr.
  - auto_contr.
+ erewrite LV_bind_map_XEnv, LV_map_XEnv_id, LV_bind_XEnv_id ; try reflexivity.
  intro α ; destruct α as [ | α ] ; simpl ; [ assumption | constructor ].
Qed.

End section_ccompat_tm_app_lbl.


Section section_compat_tm_app_lbl.
Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (σ : ms ∅ EV (inc LV) ∅) (ℓ ℓ' : lbl LV ∅) (E : eff ∅ EV LV ∅).
Context (Wf_ℓ : wf_lbl Ξ ℓ).

Lemma compat_tm_app_lbl n t₁ t₂ :
n ⊨ ⟦ Ξ Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : (ty_ms (ms_lv σ) ℓ') # E ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (tm_app_lbl t₁ ℓ) ≼ˡᵒᵍ (tm_app_lbl t₂ ℓ) :
      (ty_ms (LV_subst_ms ℓ σ) ℓ') # E ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
simpl subst_tm.
apply ccompat_tm_app_lbl ; try assumption.

iespecialize Ht ; repeat (ispecialize Ht ; [ eassumption | ]).
apply Ht.
Qed.

Lemma compat_ktx_app_lbl n T_hole E_hole K₁ K₂ :
n ⊨ ⟦ Ξ Γ ⊢ K₁ ≼ˡᵒᵍ K₂ :
      T_hole # E_hole ⇢ (ty_ms (ms_lv σ) ℓ') # E ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (ktx_app_lbl K₁ ℓ) ≼ˡᵒᵍ (ktx_app_lbl K₂ ℓ) :
      T_hole # E_hole ⇢ (ty_ms (LV_subst_ms ℓ σ) ℓ') # E ⟧.
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
apply ccompat_tm_app_lbl ; try apply HK.
- assumption.
- iintro_prop ; eapply 𝜩_monotone ; eauto.
- iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto.
Qed.

End section_compat_tm_app_lbl.
