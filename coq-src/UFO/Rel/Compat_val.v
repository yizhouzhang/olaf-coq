Require Import Lang.BindingsFacts.
Require Import Lang.Sig.
Require Import Lang.SigFacts.
Require Import Rel.Definitions.
Set Implicit Arguments.

Section section_compat_val.

Context (EV LV V : Set).
Context (Ξ : XEnv EV LV).
Context (Γ : V → ty ∅ EV LV ∅).

Lemma compat_val_unit n :
n ⊨ ⟦ Ξ Γ ⊢ val_unit ≼ˡᵒᵍᵥ val_unit : 𝟙 ⟧.
Proof.
repeat iintro ; crush.
Qed.

Lemma compat_val_var n x :
n ⊨ ⟦ Ξ Γ ⊢ (val_var x) ≼ˡᵒᵍᵥ (val_var x) : (Γ x) ⟧.
Proof.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
iespecialize Hγ ; apply Hγ.
Qed.

Lemma compat_val_md n m₁ m₂ σ X :
n ⊨ ⟦ Ξ Γ ⊢ m₁ ≼ˡᵒᵍₘ m₂ : σ ^ (lbl_id (lid_f X)) ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (val_md m₁ (lid_f X)) ≼ˡᵒᵍᵥ (val_md m₂ (lid_f X)) :
      ty_ms σ (lbl_id (lid_f X)) ⟧.
Proof.
intro H.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
iespecialize H.
ispecialize H ; [ eassumption | ].
ispecialize H ; [ eassumption | ].
ispecialize H ; [ eassumption | ].
ispecialize H ; [ eassumption | ].
simpl 𝓥_Fun ; repeat ieexists ; repeat isplit.
* iintro_prop ; crush.
* iintro_prop ; crush.
* apply H.
Qed.

Lemma compat_val_fix n m₁ m₂ N X :
n ⊨ ▷ ⟦ Ξ (env_ext Γ (ty_it N (lbl_id (lid_f X)))) ⊢ m₁ ≼ˡᵒᵍₘ m₂ : (it_msig N) ^ (lbl_id (lid_f X)) ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (val_fix m₁ (lid_f X)) ≼ˡᵒᵍᵥ (val_fix m₂ (lid_f X)) :
      ty_it N (lbl_id (lid_f X)) ⟧.
Proof.
intro H.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
loeb_induction LöbIH.
apply I_later_forall_down in H ; ispecialize H ξ₁ ;
apply I_later_forall_down in H ; ispecialize H ξ₂.
apply I_later_forall_down in H ; ispecialize H δ₁ ;
apply I_later_forall_down in H ; ispecialize H δ₂ ;
apply I_later_forall_down in H ; ispecialize H δ.
apply I_later_forall_down in H ; ispecialize H ρ₁ ;
apply I_later_forall_down in H ; ispecialize H ρ₂ ;
apply I_later_forall_down in H ; ispecialize H ρ.
apply I_later_forall_down in H ; ispecialize H (
  env_ext γ₁ (subst_val δ₁ ρ₁ γ₁ (val_fix m₁ (lid_f X)))
).
apply I_later_forall_down in H ; ispecialize H (
  env_ext γ₂ (subst_val δ₂ ρ₂ γ₂ (val_fix m₂ (lid_f X)))
).
apply I_later_arrow_down in H ; ispecialize H.
{ iintro_later ; eassumption. }
apply I_later_arrow_down in H ; ispecialize H.
{ iintro_later ; eassumption. }
apply I_later_arrow_down in H ; ispecialize H.
{ iintro_later ; eassumption. }
apply I_later_arrow_down in H ; ispecialize H.
{
  later_shift.
  iintro x ; destruct x as [ | x ]  ; simpl 𝜞 ; simpl env_ext.
  + apply LöbIH.
  + iespecialize Hγ ; apply Hγ.
}

clear - H.
simpl 𝓥_Fun.
repeat ieexists ; repeat isplit ; [ auto | auto | ].
later_shift.
apply 𝓥_roll ; simpl 𝓥_Fun.
repeat ieexists ; repeat isplit ; [ auto | auto | ].
simpl subst_md in H.
repeat erewrite V_bind_bind_md.
{ apply H. }
{
  intro x ; destruct x as [|x] ; simpl ; [ auto | ].
  erewrite V_bind_map_val, V_map_val_id, V_bind_val_id ; crush.
}
{
  intro x ; destruct x as [|x] ; simpl ; [ auto | ].
  erewrite V_bind_map_val, V_map_val_id, V_bind_val_id ; crush.
}
Qed.

Lemma compat_val_ktx n K₁ K₂ Ta Ea Tb Eb  :
n ⊨ ⟦ Ξ Γ ⊢ K₁ ≼ˡᵒᵍ K₂ : Ta # Ea ⇢ Tb # Eb ⟧ →
n ⊨ ⟦ Ξ Γ ⊢ (val_cont K₁) ≼ˡᵒᵍᵥ (val_cont K₂) : ty_cont Ta Ea Tb Eb ⟧.
Proof.
intro H.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro Hδ ; iintro Hρ ; iintro Hγ.
iespecialize H.
ispecialize H ; [ eassumption | ].
ispecialize H ; [ eassumption | ].
ispecialize H ; [ eassumption | ].
ispecialize H ; [ eassumption | ].
simpl 𝓥_Fun ; repeat ieexists ; repeat isplit.
* iintro_prop ; crush.
* apply H.
Qed.

End section_compat_val.
