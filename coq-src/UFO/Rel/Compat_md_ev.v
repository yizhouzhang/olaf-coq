Require Import UFO.Lang.BindingsFacts.
Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.Monotone.
Require Import UFO.Rel.Compat_map.
Require Import UFO.Util.Subset.
Require Import UFO.Util.Postfix.
Set Implicit Arguments.

Section section_compat_md_ev.

Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).
Context (σ : ms ∅ (inc EV) LV ∅) (ℓ : lbl LV ∅).
Context (m₁ m₂ : md (inc EV) LV V ∅).

Hint Resolve subset_trans.

Lemma compat_md_ev n :
n ⊨ ⟦ (EV_shift_XEnv Ξ) (EV_shift_ty ∘ Γ) ⊢ m₁ ≼ˡᵒᵍₘ m₂ : σ ^ ℓ ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (md_ev m₁) ≼ˡᵒᵍₘ (md_ev m₂) : (ms_ev σ) ^ ℓ ⟧.
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
iintro E₁ ; iintro E₂ ; iintro φ ; iintro Hφ.
ispecialize Hm ξ₁' ; ispecialize Hm ξ₂'.
ispecialize Hm (env_ext δ₁ E₁) ; ispecialize Hm (env_ext δ₂ E₂) ;
ispecialize Hm (env_ext δ φ).
iespecialize Hm.
ispecialize Hm.
{ iintro_prop ; ielim_prop Hξ ; unfold 𝜩 ; rewrite EV_map_XEnv_dom.
  eapply 𝜩_monotone ; eauto.
}
ispecialize Hm.
{ clear - Hδ Hφ Hξ₁' Hξ₂'.
  iintro α ; destruct α as [ | α ] ; simpl ; [ crush | ].
  repeat iintro ; iespecialize Hδ ; ispecialize Hδ ; [ eassumption | ].
  apply postfix_is_subset in Hξ₁' ; apply postfix_is_subset in Hξ₂'.
  ielim_prop Hδ ; destruct Hδ ; split ; eauto.
}
ispecialize Hm.
{ iintro_prop ; eapply ρ₁ρ₂_are_closed_monotone ; eauto. }
ispecialize Hm.
{ iintro x ; ispecialize Hγ x.
  apply 𝓥_monotone with (ξ₁ := ξ₁) (ξ₂ := ξ₂) ; [auto|auto| ].
  erewrite <- I_iff_elim_M ; [ exact Hγ | apply EV_map_𝓥 ].
  - crush.
  - crush.
  - repeat iintro ; apply auto_contr_id.
}

clear - Hm.
repeat erewrite <- EV_V_bind_md, EV_bind_bind_md ; try apply Hm.
{ intro α ; destruct α ; simpl ; [ crush | ].
  erewrite EV_bind_map_eff, EV_map_eff_id, EV_bind_eff_id ; reflexivity.
}
{ intro ; erewrite EV_bind_map_val, EV_map_val_id, EV_bind_val_id ; reflexivity. }
{ intro α ; destruct α ; simpl ; [ crush | ].
  erewrite EV_bind_map_eff, EV_map_eff_id, EV_bind_eff_id ; reflexivity.
}
{ intro ; erewrite EV_bind_map_val, EV_map_val_id, EV_bind_val_id ; reflexivity. }
Qed.

End section_compat_md_ev.
