Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.Monotone.
Require Import UFO.Rel.Compat_map.
Require Import UFO.Util.Subset.
Require Import UFO.Util.Postfix.
Set Implicit Arguments.

Section section_compat_md_lv.

Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (σ : ms ∅ EV (inc LV) ∅) (ℓ : lbl LV ∅).
Context (m₁ m₂ : md EV (inc LV) V ∅).

Hint Resolve subset_trans.

Lemma compat_md_lv n :
n ⊨ ⟦ (LV_shift_XEnv Ξ) (LV_shift_ty ∘ Γ) ⊢ m₁ ≼ˡᵒᵍₘ m₂ : σ ^ (LV_shift_lbl ℓ) ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (md_lv m₁) ≼ˡᵒᵍₘ (md_lv m₂) : (ms_lv σ) ^ ℓ ⟧.
Proof.
intro Hm.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
simpl 𝓜_Fun.
repeat ieexists ; repeat isplit ; [ crush | ].
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
iintro X₁ ; iintro X₂ ; iintro φ ; iintro HX₁X₂.
ispecialize Hm ξ₁' ; ispecialize Hm ξ₂'.
ispecialize Hm δ₁ ; ispecialize Hm δ₂ ; ispecialize Hm δ.
ispecialize Hm (env_ext ρ₁ (lbl_id (lid_f X₁))) ;
ispecialize Hm (env_ext ρ₂ (lbl_id (lid_f X₂))) ;
ispecialize Hm (env_ext ρ φ).
iespecialize Hm.
ispecialize Hm.
{ iintro_prop ; ielim_prop Hξ ; unfold 𝜩 ; rewrite LV_map_XEnv_dom.
  eapply 𝜩_monotone ; eauto.
}
ispecialize Hm.
{ eapply δ_is_closed_monotone ; eauto. }
ispecialize Hm.
{ iintro_prop ; intros α X ; destruct α as [ | α ] ; simpl.
  + ielim_prop HX₁X₂ ; destruct HX₁X₂.
    split ; let H := fresh in (intro H ; inversion H) ; subst ; auto.
  + apply postfix_is_subset in Hξ₁' ; apply postfix_is_subset in Hξ₂'.
    ielim_prop Hρ ; specialize (Hρ α X) ; crush.
}
ispecialize Hm.
{ iintro x ; ispecialize Hγ x.
  apply 𝓥_monotone with (ξ₁ := ξ₁) (ξ₂ := ξ₂) ; [auto|auto| ].
  erewrite <- I_iff_elim_M ; [ exact Hγ | apply LV_map_𝓥 ].
  - crush.
  - crush.
  - repeat iintro ; apply auto_contr_id.
}

clear - Hm.
repeat erewrite <- LV_V_bind_md, <- EV_LV_bind_md, LV_bind_bind_md ; try apply Hm.
{ intro α ; destruct α ; simpl ; [ crush | ].
  erewrite LV_bind_map_lbl, LV_map_lbl_id, LV_bind_lbl_id ; reflexivity.
}
{ intro ; erewrite LV_bind_map_eff, LV_map_eff_id, LV_bind_eff_id ; reflexivity. }
{ intro ; erewrite LV_bind_map_val, LV_map_val_id, LV_bind_val_id ; reflexivity. }
{ intro α ; destruct α ; simpl ; [ crush | ].
  erewrite LV_bind_map_lbl, LV_map_lbl_id, LV_bind_lbl_id ; reflexivity.
}
{ intro ; erewrite LV_bind_map_eff, LV_map_eff_id, LV_bind_eff_id ; reflexivity. }
{ intro ; erewrite LV_bind_map_val, LV_map_val_id, LV_bind_val_id ; reflexivity. }
Qed.

End section_compat_md_lv.
