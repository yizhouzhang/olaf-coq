Require Import UFO.Util.Postfix.
Require Import UFO.Util.Subset.
Require Import UFO.Util.FromList.
Require Import Relation_Operators.
Require Import UFO.Lang.Syntax.
Require Import UFO.Lang.Bindings.
Require Import UFO.Lang.Operational.
Require Import UFO.Lang.Sim.
Require Import UFO.Lang.SimFacts.
Require Import UFO.Lang.Xs.
Require Import UFO.Lang.XsFacts.
Set Implicit Arguments.

Lemma step_n_to_step_refl_tran n cfg₁ cfg₂ :
step_n n cfg₁ cfg₂ → step_refl_tran cfg₁ cfg₂.
Proof.
induction 1 ; simpl.
+ constructor.
+ econstructor ; eauto.
Qed.

Lemma step_refl_tran_to_step_n cfg₁ cfg₂ :
step_refl_tran cfg₁ cfg₂ → ∃ n, step_n n cfg₁ cfg₂.
Proof.
induction 1 as [ | ? ? ? ? ? [n ?] ].
+ exists 0 ; constructor.
+ exists (S n) ; econstructor ; eauto.
Qed.

Section section_step_monotone.

Hint Constructors postfix.

Lemma step_monotone_config_aux :
∀ c₁ c₂, step c₁ c₂ →
∀ ξ₁ ξ₂ t₁ t₂, c₁ = ⟨ξ₁, t₁⟩ → c₂ = ⟨ξ₂, t₂⟩ →
postfix ξ₁ ξ₂.
Proof.
induction 1 ; intros ; crush ; eauto.
Qed.

Lemma step_monotone_config ξ₁ ξ₂ t₁ t₂ :
step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
postfix ξ₁ ξ₂.
Proof.
intro ; eapply step_monotone_config_aux ; eauto.
Qed.

Hint Extern 0 => match goal with
| [H : step ⟨_, _⟩ ⟨_, _⟩ |- _] => eapply step_monotone_config in H
end.

Hint Resolve postfix_trans.

Lemma step_tran_monotone_config_aux :
∀ c₁ c₂, step_tran c₁ c₂ →
∀ ξ₁ ξ₂ t₁ t₂, c₁ = ⟨ξ₁, t₁⟩ → c₂ = ⟨ξ₂, t₂⟩ →
postfix ξ₁ ξ₂.
Proof.
induction 1 as [ | ? [ξ₁' t₁'] ? ? ? IH ] ; intros ; subst.
+ eauto.
+ eauto.
Qed.

Lemma step_tran_monotone_config ξ₁ ξ₂ t₁ t₂ :
step_tran ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
postfix ξ₁ ξ₂.
Proof.
intro ; eapply step_tran_monotone_config_aux ; eauto.
Qed.

Lemma step_refl_tran_monotone_config_aux :
∀ c₁ c₂, step_refl_tran c₁ c₂ →
∀ ξ₁ ξ₂ t₁ t₂, c₁ = ⟨ξ₁, t₁⟩ → c₂ = ⟨ξ₂, t₂⟩ →
postfix ξ₁ ξ₂.
Proof.
induction 1 as [ | ? [ξ₁' t₁'] ? ? ? IH ] ; intros ; subst.
+ crush.
+ eauto.
Qed.

Lemma step_refl_tran_monotone_config ξ₁ ξ₂ t₁ t₂ :
step_refl_tran ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
postfix ξ₁ ξ₂.
Proof.
intro ; eapply step_refl_tran_monotone_config_aux ; eauto.
Qed.

End section_step_monotone.

Section section_ktx_congruence.

Hint Constructors step.

Fixpoint ktx_congruence ξ₁ ξ₂ t₁ t₂ (K : ktx0) :
step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ → step ⟨ξ₁, ktx_plug K t₁⟩ ⟨ξ₂, ktx_plug K t₂⟩.
Proof.
destruct K ; crush.
Qed.

Local Lemma ktx_tran_congruence_aux:
∀ c₁ c₂, step_tran c₁ c₂ →
∀ ξ₁ ξ₂ t₁ t₂, c₁ = ⟨ξ₁, t₁⟩ → c₂ = ⟨ξ₂, t₂⟩ →
∀ K, step_tran ⟨ξ₁, ktx_plug K t₁⟩ ⟨ξ₂, ktx_plug K t₂⟩.
Proof.
induction 1 as [ | ? [ξ' t'] ? ? ? IH ] ; intros ; subst.
+ apply t1n_step.
  apply ktx_congruence.
  assumption.
+ eapply t1n_trans.
  - apply ktx_congruence.
    eassumption.
  - apply IH ; crush.
Qed.

Lemma ktx_tran_congruence:
∀ ξ₁ ξ₂ t₁ t₂, step_tran ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
∀ K, step_tran ⟨ξ₁, ktx_plug K t₁⟩ ⟨ξ₂, ktx_plug K t₂⟩.
Proof.
intros ; eapply ktx_tran_congruence_aux ; eauto.
Qed.

Local Lemma ktx_refl_tran_congruence_aux:
∀ c₁ c₂, step_refl_tran c₁ c₂ →
∀ ξ₁ ξ₂ t₁ t₂, c₁ = ⟨ξ₁, t₁⟩ → c₂ = ⟨ξ₂, t₂⟩ →
∀ K, step_refl_tran ⟨ξ₁, ktx_plug K t₁⟩ ⟨ξ₂, ktx_plug K t₂⟩.
Proof.
induction 1 as [ | ? [ξ' t'] ? ? ? IH ] ; intros ; subst.
+ match goal with
  | [ H : ⟨_, _⟩ = ⟨_, _⟩ |- _ ] => inversion H ; clear H ; subst
  end.
  apply rt1n_refl.
+ eapply rt1n_trans.
  - apply ktx_congruence.
    eassumption.
  - apply IH ; crush.
Qed.

Lemma ktx_refl_tran_congruence:
∀ ξ₁ ξ₂ t₁ t₂, step_refl_tran ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
∀ K, step_refl_tran ⟨ξ₁, ktx_plug K t₁⟩ ⟨ξ₂, ktx_plug K t₂⟩.
Proof.
intros ; eapply ktx_refl_tran_congruence_aux ; eauto.
Qed.

End section_ktx_congruence.

Section section_ktx_comp.
Context (EV HV V L : Set).

Lemma ktx_plug_comp
(K J : ktx EV HV V L) (t : tm EV HV V L) :
ktx_plug K (ktx_plug J t) = ktx_plug (ktx_comp K J) t.
Proof.
induction K ; simpl ; crush.
Qed.

Lemma tunnels_ktx_comp (X : var) (K J : ktx EV HV V L) :
tunnels X K →
tunnels X J →
tunnels X (ktx_comp K J).
Proof.
induction K ; crush.
Qed.

End section_ktx_comp.

Fixpoint L_map_ktx_plug
(EV LV V L L' : Set) (f : L → L')
(K : ktx EV LV V L) (t : tm EV LV V L) {struct K} :
L_map_tm f (ktx_plug K t) =
ktx_plug (L_map_ktx f K) (L_map_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.

Fixpoint LV_map_ktx_plug
(EV LV LV' V L : Set) (f : LV → lbl LV' L)
(K : ktx EV LV V L) (t : tm EV LV V L) {struct K} :
LV_map_tm f (ktx_plug K t) =
ktx_plug (LV_map_ktx f K) (LV_map_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.

Fixpoint EV_map_ktx_plug
(EV EV' LV V L : Set) (f : EV → eff ∅ EV' LV L)
(K : ktx EV LV V L) (t : tm EV LV V L) {struct K} :
EV_map_tm f (ktx_plug K t) =
ktx_plug (EV_map_ktx f K) (EV_map_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.

Fixpoint V_map_ktx_plug
(EV LV V V' L : Set) (f : V → val EV LV V' L)
(K : ktx EV LV V L) (t : tm EV LV V L) {struct K} :
V_map_tm f (ktx_plug K t) =
ktx_plug (V_map_ktx f K) (V_map_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.

Fixpoint L_bind_ktx_plug
(EV LV V L L' : Set) (f : L → lid L')
(K : ktx EV LV V L) (t : tm EV LV V L) {struct K} :
L_bind_tm f (ktx_plug K t) =
ktx_plug (L_bind_ktx f K) (L_bind_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.

Fixpoint LV_bind_ktx_plug
(EV LV LV' V L : Set) (f : LV → lbl LV' L)
(K : ktx EV LV V L) (t : tm EV LV V L) {struct K} :
LV_bind_tm f (ktx_plug K t) =
ktx_plug (LV_bind_ktx f K) (LV_bind_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.

Fixpoint EV_bind_ktx_plug
(EV EV' LV V L : Set) (f : EV → eff ∅ EV' LV L)
(K : ktx EV LV V L) (t : tm EV LV V L) {struct K} :
EV_bind_tm f (ktx_plug K t) =
ktx_plug (EV_bind_ktx f K) (EV_bind_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.

Fixpoint V_bind_ktx_plug
(EV LV V V' L : Set) (f : V → val EV LV V' L)
(K : ktx EV LV V L) (t : tm EV LV V L) {struct K} :
V_bind_tm f (ktx_plug K t) =
ktx_plug (V_bind_ktx f K) (V_bind_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.


Section sectoin_stuck_term_facts.

Local Ltac auto_stuck := repeat match goal with
| [ H : step ⟨_, tm_val _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_let _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_throw _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_app_eff _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_app_lbl _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_app_tm _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, ⬇ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, ⇩ _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, ⇧ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_op _⟩ _ |- _ ] => inversion H ; subst ; clear H

| [ H : ktx_plug ?K _ = tm_val _ |- _ ] =>
  destruct K ; discriminate
| [ H : tm_val _ = ktx_plug ?K _ |- _ ] =>
  destruct K ; discriminate

| [ H : tm_op _ = tm_op _ |- _ ] => inversion H ; subst ; clear H
| [ H : ⇧ _ = ⇧ _ |- _ ] => inversion H ; subst ; clear H
| [ H : ⇩ _ _ = ⇩ _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_let _ _ = tm_let _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_throw _ _ = tm_throw _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_app_eff _ _ = tm_app_eff _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_app_lbl _ _ = tm_app_lbl _ _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_app_tm _ _ = tm_app_tm _ _ |- _ ] => inversion H ; subst ; clear H
end.

Lemma ktx_plug_up_val_unique EV LV V L (K1 : ktx EV LV V L) t1 X1 K2 t2 X2 :
ktx_plug K1 (⇧ (tm_val (val_md (md_res t1) (lid_f X1)))) =
ktx_plug K2 (⇧ (tm_val (val_md (md_res t2) (lid_f X2)))) →
K1 = K2 ∧ t1 = t2 ∧ X1 = X2.
Proof.
generalize K2 ; clear K2.
induction K1 ; simpl ; intros K2 H.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck ; crush.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck.
  match goal with
  | [ H : ktx_plug _ _ = ktx_plug _ _ |- _ ] => apply IHK1 in H
  end ; crush.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck.
  match goal with
  | [ H : ktx_plug _ _ = ktx_plug _ _ |- _ ] => apply IHK1 in H
  end ; crush.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck.
  match goal with
  | [ H : ktx_plug _ _ = ktx_plug _ _ |- _ ] => apply IHK1 in H
  end ; crush.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck.
  match goal with
  | [ H : ktx_plug _ _ = ktx_plug _ _ |- _ ] => apply IHK1 in H
  end ; crush.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck.
  match goal with
  | [ H : ktx_plug _ _ = ktx_plug _ _ |- _ ] => apply IHK1 in H
  end ; crush.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck.
  match goal with
  | [ H : ktx_plug _ _ = ktx_plug _ _ |- _ ] => apply IHK1 in H
  end ; crush.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck.
  match goal with
  | [ H : ktx_plug _ _ = ktx_plug _ _ |- _ ] => apply IHK1 in H
  end ; crush.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck.
  match goal with
  | [ H : ktx_plug _ _ = ktx_plug _ _ |- _ ] => apply IHK1 in H
  end ; crush.
+ destruct K2 ; simpl in H ; try discriminate ; auto_stuck.
  match goal with
  | [ H : ktx_plug _ _ = ktx_plug _ _ |- _ ] => apply IHK1 in H
  end ; crush.
Qed.

Fixpoint ktx_plug_up_val_is_stuck ξ ξ' t' K r X
(Step : step ⟨ξ, ktx_plug K (⇧ (val_md (md_res r) (lid_f X)))⟩ ⟨ξ', t'⟩)
(Tunnel : tunnels X K) {struct K} :
False.
Proof.
destruct K ; simpl in Step, Tunnel.
+ inversion Step ; subst ; clear Step.
  auto_stuck.
+ inversion Step ; subst ; clear Step.
  - auto_stuck.
  - eapply ktx_plug_up_val_is_stuck ; eauto.
+ inversion Step ; subst ; clear Step.
  eapply ktx_plug_up_val_is_stuck ; eauto.
+ destruct Tunnel.
  inversion Step ; subst ; clear Step.
  - auto_stuck.
  - match goal with
    | [ H : ktx_plug _ (⇧ (tm_val _))  = ktx_plug _ (⇧ (tm_val _)) |- _ ] =>
      apply ktx_plug_up_val_unique in H
    end.
    crush.
  - eapply ktx_plug_up_val_is_stuck ; eauto.
+ inversion Step ; subst ; clear Step.
  - auto_stuck.
  - eapply ktx_plug_up_val_is_stuck ; eauto.
+ inversion Step ; subst ; clear Step.
  - auto_stuck.
  - eapply ktx_plug_up_val_is_stuck ; eauto.
+ inversion Step ; subst ; clear Step.
  - auto_stuck.
  - eapply ktx_plug_up_val_is_stuck ; eauto.
+ inversion Step ; subst ; clear Step.
  - auto_stuck.
  - eapply ktx_plug_up_val_is_stuck ; eauto.
+ inversion Step ; subst ; clear Step.
  - auto_stuck.
  - eapply ktx_plug_up_val_is_stuck ; eauto.
  - auto_stuck.
+ inversion Step ; subst ; clear Step.
  - auto_stuck.
  - auto_stuck.
  - eapply ktx_plug_up_val_is_stuck ; eauto.
Qed.

End sectoin_stuck_term_facts.


Section section_sim_operational.

Import TLC.LibList.

Lemma sim_tunnels ξ ξ' EV LV V L (K K' : ktx EV LV V L) X X' :
ktx_sim ξ ξ' K K' →
var_sim ξ ξ' X X' →
tunnels X K →
noduplicates ξ' →
tunnels X' K'.
Proof.
induction 1 as [ | | | ? ? ? ? K K' Y Y' ? ? HY | | | | | | ] ; simpl ;
intros HX Tunnel NoDup.
+ crush.
+ crush.
+ crush.
+ split ; [ crush | ].
  intro ; subst.
  destruct Tunnel as [ _ H' ] ; apply H'.
  clear - HX HY NoDup.
  destruct HX as [nX [NX NX']].
  destruct HY as [nY [NY NX'2]].
  assert (nX = nY) ; [ eauto using noduplicates_Nth_same_inv | subst nY ].
  eauto using Nth_functional.
+ crush.
+ crush.
+ crush.
+ crush.
+ crush.
+ crush.
Qed.

Hint Constructors lid_sim lbl_sim ef_sim eff_sim ty_sim ms_sim.
Hint Constructors md_sim ktx_sim val_sim tm_sim.

Lemma ktx_plug_sim ξ ξ' EV LV V L (K K' : ktx EV LV V L) t t' :
ktx_sim ξ ξ' K K' → tm_sim ξ ξ' t t' → tm_sim ξ ξ' (ktx_plug K t) (ktx_plug K' t').
Proof.
induction 1 ; crush.
Qed.

Lemma ktx_plug_sim_l_inv EV LV V L : ∀ K (s : tm EV LV V L) t' ξ ξ',
tm_sim ξ ξ' (ktx_plug K s) t' →
∃ K' s', t' = ktx_plug K' s' ∧ ktx_sim ξ ξ' K K' ∧ tm_sim ξ ξ' s s'.
Proof.
induction K ; simpl ; intros ? ? ? ? H ; inversion H ; subst ; clear H.
+ repeat exists ; crush.
+ repeat exists ; crush.
+ repeat exists ; crush.
+ repeat exists ; crush.
+ repeat exists ; crush.
+ repeat exists ; crush.
+ repeat exists ; crush.
+ repeat exists ; crush.
+ repeat exists ; crush.
+ repeat exists ; crush.
+ match goal with
  | [ H : tm_sim _ _ (ktx_plug K _) _ |- _ ] =>
    eapply IHK in H ; destruct H as [? [? [? [? ?]]]] ; subst
  end.
  eexists (ktx_op _) ; eexists ; crush.
+ match goal with
  | [ H : tm_sim _ _ (ktx_plug K _) _ |- _ ] =>
    eapply IHK in H ; destruct H as [? [? [? [? ?]]]] ; subst
  end.
  eexists (ktx_up _) ; eexists ; crush.
+ match goal with
  | [ H : tm_sim _ _ (ktx_plug K _) _ |- _ ] =>
    eapply IHK in H ; destruct H as [? [? [? [? ?]]]] ; subst
  end.
  eexists (ktx_down _ _) ; eexists ; crush.
+ match goal with
  | [ H : tm_sim _ _ (ktx_plug K _) _ |- _ ] =>
    eapply IHK in H ; destruct H as [? [? [? [? ?]]]] ; subst
  end.
  eexists (ktx_let _ _) ; eexists ; crush.
+ match goal with
  | [ H : tm_sim _ _ (ktx_plug K _) _ |- _ ] =>
    eapply IHK in H ; destruct H as [? [? [? [? ?]]]] ; subst
  end.
  eexists (ktx_throw _ _) ; eexists ; crush.
+ match goal with
  | [ H : tm_sim _ _ (ktx_plug K _) _ |- _ ] =>
    eapply IHK in H ; destruct H as [? [? [? [? ?]]]] ; subst
  end.
  eexists (ktx_app_eff _ _) ; eexists ; crush.
+ match goal with
  | [ H : tm_sim _ _ (ktx_plug K _) _ |- _ ] =>
    eapply IHK in H ; destruct H as [? [? [? [? ?]]]] ; subst
  end.
  eexists (ktx_app_lbl _ _) ; eexists ; crush.
+ match goal with
  | [ H : tm_sim _ _ (ktx_plug K _) _ |- _ ] =>
    eapply IHK in H ; destruct H as [? [? [? [? ?]]]] ; subst
  end.
  eexists (ktx_app_tm1 _ _) ; eexists ; crush.
+ repeat match goal with
  | [ H : tm_sim _ _ (tm_val _) _ |- _ ] =>
    inversion H ; subst ; clear H
  | [ H : tm_sim _ _ (ktx_plug K _) _ |- _ ] =>
    eapply IHK in H ; destruct H as [? [? [? [? ?]]]] ; subst
  end.
  eexists (ktx_app_tm2 _ _) ; eexists ; crush.
Qed.

Ltac solve_sim := repeat match goal with
| [ H : tm_sim _ _ (tm_val _ ) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (tm_let _ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (tm_throw _ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (tm_app_eff _ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (tm_app_lbl _ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (tm_app_tm _ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (⬇ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (⇩ _ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (⇧ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (tm_op _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ _ (tm_val _ ) |- _ ] => inversion H ; subst ; clear H
| [ H : tm_sim _ _ (ktx_plug _ _) _ |- _ ] =>
  apply ktx_plug_sim_l_inv in H ; destruct H as [? [? [? [? ?]]]] ; subst

| [ H : val_sim _ _ (val_md _ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : val_sim _ _ (val_fix _ _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : val_sim _ _ (val_cont _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : md_sim _ _ (md_ev _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : md_sim _ _ (md_lv _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : md_sim _ _ (md_tm _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : md_sim _ _ (md_res _) _ |- _ ] => inversion H ; subst ; clear H
| [ H : lid_sim _ _ (lid_f _) _ |- _ ] => inversion H ; subst ; clear H

| [ H : step ⟨_, tm_val _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_let _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_throw _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_app_eff _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_app_lbl _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_app_tm _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, ⬇ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, ⇩ _ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, ⇧ _⟩ _ |- _ ] => inversion H ; subst ; clear H
| [ H : step ⟨_, tm_op _⟩ _ |- _ ] => inversion H ; subst ; clear H

| [ H : ktx_plug ?K _ = tm_val _ |- _ ] => destruct K ; discriminate
| [ H : tm_val _ = ktx_plug ?K _ |- _ ] => destruct K ; discriminate

| [ H : ktx_plug _ (⇧ (tm_val (val_md (md_res _) _))) =
        ktx_plug _ (⇧ (tm_val (val_md (md_res _) _))) |- _ ] =>
  apply ktx_plug_up_val_unique in H ; destruct H as [? [? ?]]
end.

Hint Resolve var_sim_future lid_sim_future lbl_sim_future eff_sim_future ty_sim_future.
Hint Resolve md_sim_future ktx_sim_future val_sim_future tm_sim_future.

Hint Resolve V_bind_tm_sim L_bind_tm_sim EV_bind_md_sim LV_bind_md_sim V_bind_md_sim.

Hint Resolve ktx_plug_sim.

Hint Constructors step.

Lemma step_preserves_sim
cfg₁ cfg₂ (H₁ : step cfg₁ cfg₂) :
∀ ξ₁ t₁ ξ₂ t₂ (Hcfg₁ : cfg₁ = ⟨ξ₁, t₁⟩) (Hcfg₂ : cfg₂ = ⟨ξ₂, t₂⟩)
ξ₁' t₁'
(NoDup_ξ₁ : noduplicates ξ₁)
(NoDup_ξ₁' : noduplicates ξ₁')
(Hsim : tm_sim ξ₁ ξ₁' t₁ t₁')
ξ₂' t₂'
(H₂ : step ⟨ξ₁', t₁'⟩ ⟨ξ₂', t₂'⟩),
tm_sim ξ₂ ξ₂' t₂ t₂' ∧
((ξ₂ = ξ₁ ∧ ξ₂' = ξ₁') ∨ (∃ X X', ξ₂ = X :: ξ₁ ∧ ξ₂' = X' :: ξ₁')).
Proof.
induction H₁ ; intros ; inversion Hcfg₁ ; inversion Hcfg₂ ; clear Hcfg₁ Hcfg₂ ; subst.
+ solve_sim ; crush.
+ solve_sim ; crush.
+ solve_sim ; crush.
+ solve_sim ; crush.
+ solve_sim ; crush.
+ solve_sim ; crush.
+ solve_sim ; split.
  - constructor ; [ exists 0 ; crush | ].
    apply L_bind_tm_sim ; [ | eauto 6 ].
    intro x ; destruct x ; simpl ; [ | crush ].
    constructor ; exists 0 ; crush.
  - right ; eauto.
+ solve_sim ; crush.
+ solve_sim.
  - crush.
  - exfalso.
    eauto using ktx_plug_up_val_is_stuck, sim_tunnels.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try eassumption ; destruct H as [? ?]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try eassumption ; destruct H as [? ?]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try eassumption ; destruct H as [? ?]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try eassumption ; destruct H as [? ?]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try eassumption ; destruct H as [? ?]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try eassumption ; destruct H as [? ?]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try eassumption ; destruct H as [? ?]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try eassumption ; destruct H as [? ?]
  end.
  eauto.
+ solve_sim.
  - exfalso.
    match goal with
    | [ H : tm_sim _ _ _ (ktx_plug K (⇧ _)) |- _ ] =>
      apply tm_sim_sym in H ; apply ktx_plug_sim_l_inv in H ;
      destruct H as [?[?[?[??]]]] ; subst
    end.
    solve_sim.
    eauto using ktx_plug_up_val_is_stuck, sim_tunnels.
  - match goal with
    | [ H : tm_sim _ _ t₁ _ |- _ ] =>
      eapply IHH₁ in H ; try reflexivity ; try eassumption ; destruct H as [? ?]
    end.
    eauto.
Qed.

Lemma sim_preserves_step
cfg₁ cfg₂ (H₁ : step cfg₁ cfg₂) :
∀ ξ₁ t₁ ξ₂ t₂ (Hcfg₁ : cfg₁ = ⟨ξ₁, t₁⟩) (Hcfg₂ : cfg₂ = ⟨ξ₂, t₂⟩)
ξ₁' t₁'
(NoDup_ξ₁ : noduplicates ξ₁)
(NoDup_ξ₁' : noduplicates ξ₁')
(Hsim : tm_sim ξ₁ ξ₁' t₁ t₁'),
∃ ξ₂' t₂', step ⟨ξ₁', t₁'⟩ ⟨ξ₂', t₂'⟩.
Proof.
induction H₁ ; intros ; inversion Hcfg₁ ; inversion Hcfg₂ ; clear Hcfg₁ Hcfg₂ ; subst.
+ solve_sim ; eauto.
+ solve_sim ; eauto.
+ solve_sim ; eauto.
+ solve_sim ; eauto.
+ solve_sim ; eauto.
+ solve_sim ; eauto.
+ pick_fresh_gen (from_list ξ₁') X'.
  solve_sim ; eauto.
+ solve_sim ; eauto.
+ solve_sim.
  eexists ; eexists.
  match goal with
  | [ H1 : var_sim ?ξ ?ξ' ?X ?X'1,
      H2 : var_sim ?ξ ?ξ' ?X ?X'2,
      NoDup : noduplicates ?ξ' |- _ ] =>
    specialize H1 as H1' ; specialize H2 as H2' ;
    destruct H1 as [n1 [? ?]] ; destruct H2 as [n2 [? ?]] ;
    assert (n1 = n2) ; [ eauto using noduplicates_Nth_same_inv | ] ;
    assert (X'1 = X'2) ; [ subst ; eauto using Nth_functional | ]
  end.
  subst ; constructor.
  eauto using sim_tunnels.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try assumption ;
    destruct H as [? [? ?]]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try assumption ;
    destruct H as [? [? ?]]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try assumption ;
    destruct H as [? [? ?]]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try assumption ;
    destruct H as [? [? ?]]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try assumption ;
    destruct H as [? [? ?]]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try assumption ;
    destruct H as [? [? ?]]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try assumption ;
    destruct H as [? [? ?]]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try assumption ;
    destruct H as [? [? ?]]
  end.
  eauto.
+ solve_sim.
  match goal with
  | [ H : tm_sim _ _ t₁ _ |- _ ] =>
    eapply IHH₁ in H ; try reflexivity ; try assumption ;
    destruct H as [? [? ?]]
  end.
  eauto.
Qed.

End section_sim_operational.


Section section_step_vars.

Import TLC.LibList.

Hint Rewrite <- from_list_spec.

Lemma step_preserves_noduplicates :
∀ c₁ c₂, step c₁ c₂ → ∀ ξ₁ ξ₂ t₁ t₂, c₁ = ⟨ξ₁, t₁⟩ → c₂ = ⟨ξ₂, t₂⟩ →
noduplicates ξ₁ → noduplicates ξ₂.
Proof.
induction 1 ; intros ? ? ? ? Cfg₁ Cfg₂ NoDup ;
inversion Cfg₁ ; inversion Cfg₂ ; subst ; clear Cfg₁ Cfg₂ ; eauto.
constructors ; crush.
Qed.

Hint Extern 1 => match goal with
| [ H : _ \u _ \c _ |- _ ] => apply union_subset_inv in H ; destruct H
| [ H : step ⟨ ?ξ, _ ⟩ ⟨ ?ξ', _ ⟩ |- _ \c from_list ?ξ' ] =>
  assert (from_list ξ ⊆ from_list ξ') ; [
    apply postfix_is_subset ; apply (step_monotone_config H) |
  ]
end.

Hint Resolve subset_refl subset_union_l subset_union_r.

Lemma step_preserves_closedness :
∀ c₁ c₂, step c₁ c₂ → ∀ ξ₁ ξ₂ t₁ t₂, c₁ = ⟨ξ₁, t₁⟩ → c₂ = ⟨ξ₂, t₂⟩ →
Xs_tm t₁ \c from_list ξ₁ → Xs_tm t₂ \c from_list ξ₂.
Proof.
induction 1 ; intros ? ? ? ? Cfg₁ Cfg₂ Closed ;
inversion Cfg₁ ; inversion Cfg₂ ; subst ; clear Cfg₁ Cfg₂ ; simpl in Closed |- *.
+ eapply subset_trans ; [ | exact Closed ].
  eapply subset_trans ; [ apply V_bind_tm_Xs with (B := Xs_val v) ; auto | ].
  rewrite union_comm ; auto.
+ rewrite Xs_ktx_plug ; auto.
+ eapply subset_trans ; [ | exact Closed ].
  apply union_subset.
  - eapply subset_trans ; [ apply V_bind_md_Xs with (B := Xs_val (val_fix m ι)) ; auto | ].
    auto using union_subset.
  - auto.
+ eapply subset_trans ; [ | exact Closed ].
  apply union_subset.
  - eapply subset_trans ; [ apply EV_bind_md_Xs with (B := Xs_eff E) ; auto | ].
    auto using union_subset.
  - auto.
+ eapply subset_trans ; [ | exact Closed ].
  apply union_subset.
  - eapply subset_trans ; [ apply LV_bind_md_Xs with (B := Xs_lbl ℓ) ; auto | ].
    auto using union_subset.
  - auto.
+ eapply subset_trans ; [ | exact Closed ].
  apply union_subset.
  - eapply subset_trans ; [ apply V_bind_md_Xs with (B := Xs_val v) ; auto | ].
    auto using union_subset.
  - auto.
+ rewrite from_list_cons.
  apply union_subset ; [ | auto ].
  eapply subset_trans with (F := \{X} \u Xs_tm t).
  - eapply subset_trans ; [ apply L_bind_tm_Xs with (B := \{X}) ; auto | ].
    apply union_subset ; auto.
  - apply union_subset ; auto.
+ auto.
+ rewrite Xs_ktx_plug in Closed ; simpl in Closed.
  eapply subset_trans ; [ | exact Closed ].
  eapply subset_trans ; [ apply V_bind_tm_Xs with (B := Xs_ktx K \u \{X}) | ].
  - destruct x ; auto.
  - rewrite (union_assoc (Xs_tm t)), (union_comm (Xs_tm t)), <- (union_assoc (Xs_ktx K)).
    auto.
+ simpl ; apply union_subset ; eauto using subset_trans.
+ simpl ; apply union_subset ; eauto using subset_trans.
+ simpl ; apply union_subset ; eauto using subset_trans.
+ simpl ; apply union_subset ; eauto using subset_trans.
+ simpl ; apply union_subset ; eauto using subset_trans.
+ simpl ; apply union_subset ; eauto using subset_trans.
+ eauto.
+ eauto.
+ simpl ; apply union_subset ; eauto using subset_trans.
Qed.

End section_step_vars.
