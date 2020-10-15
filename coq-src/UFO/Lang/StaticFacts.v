Require Import Lang.Syntax.
Require Import Lang.Bindings.
Require Import Lang.Static.
Require Import Lang.Sig.
Require Import Lang.SigFacts.
Require Import Lang.BindingsFacts.
Require Import Setoid.
Require Import FunctionalExtensionality. (* TODO: don't really need extensionality *)
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

(** * Facts about the preorders on effects and types *)

Section section_eff_facts.
Context (EP EV LV L : Set).

Lemma se_transitive (E₁ E₂ E₃ : eff EP EV LV L) : se E₁ E₂ → se E₂ E₃ → se E₁ E₃.
Proof.
auto.
Qed.

Lemma se_reflexive (E : eff EP EV LV L) : se E E.
Proof.
auto.
Qed.

Instance se_PreOrder : PreOrder (fun E₁ E₂ => se E₁ E₂) := {
  PreOrder_Reflexive  := @se_reflexive ;
  PreOrder_Transitive := @se_transitive ;
}.

Lemma se_nil (E : eff EP EV LV L) : se [] E.
Proof.
induction E ; crush.
Qed.

Lemma se_cons_l (e : ef EP EV LV L) E1 E2 : se (e :: E1) E2 -> se E1 E2.
Proof.
crush.
Qed.

Lemma se_cons_r (e : ef EP EV LV L) E1 E2 : se E1 E2 -> se E1 (e :: E2).
Proof.
crush.
Qed.

Lemma se_app_l (E1 E2 : eff EP EV LV L) : se E1 (E1 ++ E2).
Proof.
crush.
Qed.

Lemma se_app_r (E1 E2 : eff EP EV LV L) : se E2 (E1 ++ E2).
Proof.
crush.
Qed.

Lemma se_app (E1 E2 E : eff EP EV LV L) : se E1 E -> se E2 E -> se (E1 ++ E2) E.
Proof.
Hint Rewrite in_app_iff.
crush.
Qed.

End section_eff_facts.


Section section_ty_facts.

Hint Constructors st ss.
Hint Resolve se_reflexive.

Lemma st_transitive EP EV LV L (T₁ T₂ T₃ : ty EP EV LV L) : st T₁ T₂ → st T₂ T₃ → st T₁ T₃.
Proof.
eauto.
Qed.

Lemma ss_transitive EP EV LV L (σ₁ σ₂ σ₃ : ms EP EV LV L) : ss σ₁ σ₂ → ss σ₂ σ₃ → ss σ₁ σ₃.
Proof.
eauto.
Qed.

Fixpoint
st_reflexive EP EV LV L (T : ty EP EV LV L) {struct T} : st T T
with
ss_reflexive EP EV LV L (σ : ms EP EV LV L) {struct σ} : ss σ σ
.
Proof.
{
  destruct T ; simpl.
  + apply st_unit.
  + apply st_cont ; auto.
  + apply st_it ; auto.
  + apply st_ms ; auto.
}
{
  destruct σ ; simpl.
  + apply ss_eff ; auto.
  + apply ss_lbl ; auto.
  + apply ss_tm ; auto.
  + apply ss_res ; auto.
}
Qed.

Instance st_PreOrder EP EV LV L : PreOrder (@st EP EV LV L) := {
  PreOrder_Reflexive  := @st_reflexive EP EV LV L;
  PreOrder_Transitive := @st_transitive EP EV LV L;
}.

Instance ss_PreOrder EP EV LV L : PreOrder (@ss EP EV LV L) := {
  PreOrder_Reflexive  := @ss_reflexive EP EV LV L;
  PreOrder_Transitive := @ss_transitive EP EV LV L;
}.

End section_ty_facts.


(** * Facts about label environments *)

Section section_wf_XEnv.

Hint Rewrite concat_empty_r concat_assoc.
Hint Rewrite notin_singleton notin_union dom_empty dom_concat dom_single.
Hint Extern 0 => match goal with
| [ H : empty = _ & _ ~ _ |- _ ] => apply empty_push_inv in H ; crush
| [ H : _ & _ ~ _ = _ & _ ~ _ |- _ ] => apply eq_push_inv in H ; crush
end.

Lemma ok_concat_indom_l EV LV (Ξ Ξ' : XEnv EV LV) :
ok (Ξ & Ξ') → ∀ X, X ∈ dom Ξ → X ∉ dom Ξ'.
Proof.
intros ok_ΞΞ' X HX.
induction Ξ' using env_ind ; [crush|].
rewrite concat_assoc in ok_ΞΞ'.
inversion ok_ΞΞ' ; crush.
Qed.

Lemma wf_XEnv_ok EV LV (Ξ : XEnv EV LV) :
wf_XEnv Ξ → ok Ξ.
Proof.
induction 1 ; constructor ; crush.
Qed.

Lemma wf_XEnv_concat_inv_l EV LV (Ξ Ξ' : XEnv EV LV) :
wf_XEnv (Ξ & Ξ') → wf_XEnv Ξ.
Proof.
induction Ξ' as [ | Ξ'' X [??] ] using env_ind ; [crush|].
rewrite concat_assoc.
inversion 1 ; crush.
Qed.

End section_wf_XEnv.


(** * Facts about well-formedness under weakening *)

Section section_weaken_wf.

Hint Rewrite dom_concat in_union.

Lemma weaken_wf_lbl
EV LV (Ξ Ξ' : XEnv EV LV) l :
wf_lbl Ξ l → wf_lbl (Ξ & Ξ') l.
Proof.
destruct 1 ; constructor ; crush.
Qed.

Hint Resolve weaken_wf_lbl.

Lemma weaken_wf_ef
EP EV LV (Ξ Ξ' : XEnv EV LV) (e : ef EP EV LV ∅) :
wf_ef Ξ e → wf_ef (Ξ & Ξ') e.
Proof.
destruct 1 ; constructor ; crush.
Qed.

Hint Resolve weaken_wf_ef.

Lemma weaken_wf_eff
EP EV LV (Ξ Ξ' : XEnv EV LV) (E : eff EP EV LV ∅) :
wf_eff Ξ E → wf_eff (Ξ & Ξ') E.
Proof.
induction 1 ; constructor ; crush.
Qed.

Hint Resolve weaken_wf_eff.
Hint Rewrite EV_map_XEnv_concat LV_map_XEnv_concat.

Lemma weaken_wf_it
EP EV LV (Ξ Ξ' : XEnv EV LV) κ (N : it EP EV LV ∅ κ) :
wf_it Ξ N → wf_it (Ξ & Ξ') N.
Proof.
induction 1 ; constructor ; crush.
Qed.

Hint Resolve weaken_wf_it.

Fixpoint
weaken_wf_ty
EP EV LV (Ξ Ξ' : XEnv EV LV) (T : ty EP EV LV ∅)
(H : wf_ty Ξ T) :
wf_ty (Ξ & Ξ') T
with
weaken_wf_ms
EP EV LV (Ξ Ξ' : XEnv EV LV) (σ : ms EP EV LV ∅)
(H : wf_ms Ξ σ) :
wf_ms (Ξ & Ξ') σ
.
Proof.
+ destruct H ; constructor ; crush.
+ destruct H ; constructor ; crush.
Qed.

Hint Resolve weaken_wf_ty.

Corollary weaken_wf_Γ
EV LV V (Ξ Ξ' : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅) :
wf_Γ Ξ Γ → wf_Γ (Ξ & Ξ') Γ.
Proof.
intros_all ; crush.
Qed.

End section_weaken_wf.


Section section_EV_map_wf.

Hint Rewrite EV_map_XEnv_dom.

Lemma EV_map_wf_lbl EV EV' LV
(f : EV → EV') (Ξ : XEnv EV LV)
(ℓ : lbl LV ∅) :
wf_lbl Ξ ℓ → wf_lbl (EV_map_XEnv f Ξ) ℓ.
Proof.
destruct 1 ; constructor ; crush.
Qed.

Hint Resolve EV_map_wf_lbl.

Lemma EV_map_wf_ef EP EV EV' LV
(f : EV → EV') (Ξ : XEnv EV LV)
(ε : ef EP EV LV ∅) :
wf_ef Ξ ε → wf_ef (EV_map_XEnv f Ξ) (EV_map_ef f ε).
Proof.
destruct 1 ; constructor ; crush.
Qed.

Hint Resolve EV_map_wf_ef.

Lemma EV_map_wf_eff EP EV EV' LV
(f : EV → EV') (Ξ : XEnv EV LV)
(E : eff EP EV LV ∅) :
wf_eff Ξ E → wf_eff (EV_map_XEnv f Ξ) (EV_map_eff f E).
Proof.
induction 1 ; constructor ; crush.
Qed.

Hint Resolve EV_map_wf_eff.

Lemma EV_map_wf_it EP EV EV' LV
(f : EV → EV') (Ξ : XEnv EV LV)
κ (N : it EP EV LV ∅ κ) :
wf_it Ξ N → wf_it (EV_map_XEnv f Ξ) (EV_map_it f N).
Proof.
induction 1 ; constructor ; crush.
Qed.

Hint Resolve EV_map_wf_it.

Fixpoint
EV_map_wf_ty EP EV EV' LV
(f : EV → EV') (Ξ : XEnv EV LV)
(T : ty EP EV LV ∅)
(Q : wf_ty Ξ T) :
wf_ty (EV_map_XEnv f Ξ) (EV_map_ty f T)
with
EV_map_wf_ms EP EV EV' LV
(f : EV → EV') (Ξ : XEnv EV LV)
(σ : ms EP EV LV ∅)
(Q : wf_ms Ξ σ) :
wf_ms (EV_map_XEnv f Ξ) (EV_map_ms f σ)
.
Proof.
+ destruct Q ; simpl ; constructor ; crush.
+ destruct Q ; simpl.
  - constructor.
    eapply EV_map_wf_ms in Q.
    erewrite EV_map_map_XEnv in Q|-* ; [eauto|crush|crush].
  - constructor.
    rewrite <- EV_LV_map_XEnv ; crush.
  - constructor ; crush.
  - constructor ; crush.
Qed.

Hint Resolve EV_map_wf_ty.
Hint Rewrite EV_map_XEnv_empty EV_map_XEnv_concat EV_map_XEnv_single.

Lemma EV_map_wf_XEnv EV EV' LV
(f : EV → EV') (Ξ : XEnv EV LV) :
wf_XEnv Ξ → wf_XEnv (EV_map_XEnv f Ξ).
Proof.
induction 1 ; crush ; constructor ; crush.
Qed.

Lemma EV_map_wf_Γ EV EV' LV V
(f : EV → EV') (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅) :
wf_Γ Ξ Γ → wf_Γ (EV_shift_XEnv Ξ) (EV_shift_ty ∘ Γ).
Proof.
intros_all; auto.
Qed.

End section_EV_map_wf.


Section section_LV_map_wf.

Hint Rewrite LV_map_XEnv_dom.

Lemma LV_map_wf_lbl EV LV LV'
(f : LV → LV') (Ξ : XEnv EV LV)
(ℓ : lbl LV ∅)
(Wf_ℓ : wf_lbl Ξ ℓ) :
wf_lbl (LV_map_XEnv f Ξ) (LV_map_lbl f ℓ).
Proof.
destruct Wf_ℓ ; constructor ; crush.
Qed.

Hint Resolve LV_map_wf_lbl.

Lemma LV_map_wf_ef EP EV LV LV'
(f : LV → LV') (Ξ : XEnv EV LV)
(ε : ef EP EV LV ∅)
(Wf_ε : wf_ef Ξ ε) :
wf_ef (LV_map_XEnv f Ξ) (LV_map_ef f ε).
Proof.
destruct Wf_ε ; constructor ; crush.
Qed.

Hint Resolve LV_map_wf_ef.

Fixpoint LV_map_wf_eff EP EV LV LV'
(f : LV → LV') (Ξ : XEnv EV LV)
(E : eff EP EV LV ∅)
(Wf_E : wf_eff Ξ E) :
wf_eff (LV_map_XEnv f Ξ) (LV_map_eff f E).
Proof.
destruct Wf_E ; simpl ; constructor ; crush.
Qed.

Hint Resolve LV_map_wf_eff.

Fixpoint LV_map_wf_it EP EV LV LV'
(f : LV → LV') (Ξ : XEnv EV LV)
κ (N : it EP EV LV ∅ κ)
(Wf_N : wf_it Ξ N) :
wf_it (LV_map_XEnv f Ξ) (LV_map_it f N).
Proof.
destruct Wf_N ; simpl ; constructor ; crush.
Qed.

Hint Resolve LV_map_wf_it.

Fixpoint
LV_map_wf_ty
EP EV LV LV'
(f : LV → LV') (Ξ : XEnv EV LV)
(T : ty EP EV LV ∅)
(Q : wf_ty Ξ T) :
wf_ty (LV_map_XEnv f Ξ) (LV_map_ty f T)
with
LV_map_wf_ms
EP EV LV LV'
(f : LV → LV') (Ξ : XEnv EV LV)
(σ : ms EP EV LV ∅)
(Q : wf_ms Ξ σ) :
wf_ms (LV_map_XEnv f Ξ) (LV_map_ms f σ)
.
Proof.
+ destruct Q ; simpl ; constructor ; crush.
+ destruct Q ; simpl.
  - constructor.
    rewrite EV_LV_map_XEnv ; crush.
  - constructor.
    eapply LV_map_wf_ms in Q.
    erewrite LV_map_map_XEnv in Q|-* ; [eauto|crush|crush].
  - constructor ; crush.
  - constructor ; crush.
Qed.

Hint Resolve LV_map_wf_ty.
Hint Rewrite LV_map_XEnv_empty LV_map_XEnv_concat LV_map_XEnv_single.

Lemma LV_map_wf_XEnv EV LV LV'
(f : LV → LV') (Ξ : XEnv EV LV) :
wf_XEnv Ξ → wf_XEnv (LV_map_XEnv f Ξ).
Proof.
induction 1 ; crush ; constructor ; crush.
Qed.

Lemma LV_map_wf_Γ EV LV LV' V
(f : LV → LV') (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅) :
wf_Γ Ξ Γ → wf_Γ (LV_shift_XEnv Ξ) (LV_shift_ty ∘ Γ).
Proof.
intros_all; auto.
Qed.

End section_LV_map_wf.


Section section_XLEnv_inv.

Hint Rewrite dom_concat dom_single in_union in_singleton.

Fixpoint XLEnv_inv_substituion_ok
EV LV L Ξ (Π : LEnv EV LV L) f
(H : XLEnv Ξ Π f) {struct H} :
∀ β, ∃ X, f β = lid_f X ∧ X ∈ dom Ξ.
Proof.
destruct H as [ | ? ? ? ? ? ? ? H ] ; intro β.
+ destruct β.
+ destruct β as [ | β ] ; simpl.
  - eexists ; crush.
  - destruct (f β) as [ | Y ] eqn:H' ; [ auto | ].
    exists ; split ; [ reflexivity | ].
    apply XLEnv_inv_substituion_ok with (β := β) in H ; destruct H as [?[??]].
    rewrite H' in H.
    crush.
Qed.

Fixpoint XLEnv_inv_wf_XEnv
EV LV L Ξ (Π : LEnv EV LV L) f
(H : XLEnv Ξ Π f) {struct H} :
wf_XEnv Ξ.
Proof.
destruct H as [ | ? ? ? ? ? ? ? H ] ; simpl.
+ constructor.
+ constructor ; eauto.
Qed.

End section_XLEnv_inv.


Section section_ok_wf.

Fixpoint LEnv_lookup_inv_binds
EV LV L Ξ (Π : LEnv EV LV L) f X β T E
(Lookup : LEnv_lookup β Π = (T, E))
(EQ_β : f β = lid_f X)
(H : XLEnv Ξ Π f) {struct H} :
binds X (L_bind_ty f T, L_bind_eff f E) Ξ.
Proof.
destruct H as [ | ??????? H] ; simpl ; [auto|].
destruct β as [|β] ; simpl in *.
+ inversion EQ_β ; inversion Lookup ; subst.
  unshelve erewrite L_bind_map_ty, L_bind_map_eff, L_map_ty_id, L_map_eff_id ; auto.
  - intro ; erewrite L_map_lid_id ; auto.
  - intro ; erewrite L_map_lid_id ; auto.
+ destruct (LEnv_lookup β Π) eqn:Lookup'.
  inversion Lookup ; subst.
  eapply LEnv_lookup_inv_binds in H ; try eassumption.
  apply get_some_inv in H as H'.
  apply binds_concat_left.
  - unshelve erewrite L_bind_map_ty, L_bind_map_eff, L_map_ty_id, L_map_eff_id ; eauto.
    * intro ; erewrite L_map_lid_id ; auto.
    * intro ; erewrite L_map_lid_id ; auto.
  - rewrite dom_single, notin_singleton.
    intro ; subst ; auto.
Qed.

Fixpoint LV_map_XLEnv
EV LV L LV' (f : LV → LV')
Ξ (Π : LEnv EV LV L) g
(H : XLEnv Ξ Π g) :
XLEnv (LV_map_XEnv f Ξ) (LV_map_LEnv f Π) g.
Proof.
destruct H as [ | ? ? ? ? ? ? ? H ] ; simpl.
+ rewrite LV_map_XEnv_empty ; constructor.
+ rewrite LV_map_XEnv_concat, LV_map_XEnv_single.
  rewrite <- L_bind_LV_map_ty, <- L_bind_LV_map_eff.
  constructor.
  - auto.
  - rewrite LV_map_XEnv_dom ; auto.
  - rewrite L_bind_LV_map_ty.
    apply LV_map_wf_ty ; auto.
  - rewrite L_bind_LV_map_eff.
    apply LV_map_wf_eff ; auto.
Qed.

Fixpoint EV_map_XLEnv
EV LV L EV' (f : EV → EV')
Ξ (Π : LEnv EV LV L) g
(H : XLEnv Ξ Π g) :
XLEnv (EV_map_XEnv f Ξ) (EV_map_LEnv f Π) g.
Proof.
destruct H as [ | ? ? ? ? ? ? ? H ] ; simpl.
+ rewrite EV_map_XEnv_empty ; constructor.
+ rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  rewrite <- L_bind_EV_map_ty, <- L_bind_EV_map_eff.
  constructor.
  - auto.
  - rewrite EV_map_XEnv_dom ; auto.
  - rewrite L_bind_EV_map_ty.
    apply EV_map_wf_ty ; auto.
  - rewrite L_bind_EV_map_eff.
    apply EV_map_wf_eff ; auto.
Qed.

Lemma L_bind_In
EP EV LV L L' (f : L → lid L') :
∀ e (E : eff EP EV LV L) (H : In e E),
In (L_bind_ef f e) (L_bind_eff f E).
Proof.
induction E ; crush.
Qed.

Hint Resolve L_bind_In.

Lemma L_bind_se
EP EV LV L L' (f : L → lid L') :
∀ (E1 E2 : eff EP EV LV L) (H : se E1 E2),
se (L_bind_eff f E1) (L_bind_eff f E2).
Proof.
induction E1 ; crush.
Qed.

Hint Resolve L_bind_se.

Fixpoint
subty_st
EV LV L (f : L → lid0)
(T1 T2 : ty ∅ EV LV L)
(H : subty T1 T2) :
st (L_bind_ty f T1) (L_bind_ty f T2)
with
subms_ss
EV LV L (f : L → lid0)
(σ1 σ2 : ms ∅ EV LV L)
(H : subms σ1 σ2) :
ss (L_bind_ms f σ1) (L_bind_ms f σ2)
.
Proof.
+ destruct H ; simpl.
  - constructor.
  - constructor ; eauto.
  - constructor.
  - constructor ; auto.
  - econstructor ; eauto.
+ destruct H ; simpl.
  - constructor ; auto.
  - constructor ; auto.
  - constructor ; auto.
  - constructor ; eauto.
  - econstructor ; eauto.
Qed.

Hint Resolve subty_st subms_ss.

Hint Constructors wf_lbl wf_ef wf_eff wf_it wf_ms wf_ty.
Hint Constructors wf_md wf_ktx wf_val wf_tm.

Lemma ok_wf_lbl
EV LV L (Π : LEnv EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
(ℓ : lbl LV L) (H : ok_lbl Π ℓ) :
wf_lbl Ξ (L_bind_lbl f ℓ).
Proof.
destruct H ; simpl.
+ eapply XLEnv_inv_substituion_ok in Q ; crush.
+ crush.
Qed.

Hint Resolve ok_wf_lbl.

Lemma ok_wf_ef
EV LV L (Π : LEnv EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
(ε : ef ∅ EV LV L) (H : ok_ef Π ε) :
wf_ef Ξ (L_bind_ef f ε).
Proof.
destruct H ; simpl ; eauto.
Qed.

Hint Resolve ok_wf_ef.

Lemma ok_wf_eff
EV LV L (Π : LEnv EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
(E : eff ∅ EV LV L) (H : ok_eff Π E) :
wf_eff Ξ (L_bind_eff f E).
Proof.
induction H ; simpl ; eauto.
Qed.

Hint Resolve ok_wf_eff.

Lemma ok_wf_it
EV LV L (Π : LEnv EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
κ (N : it ∅ EV LV L κ) (H : ok_it Π N) :
wf_it Ξ (L_bind_it f N).
Proof.
induction H ; simpl ; eauto.
Qed.

Hint Resolve ok_wf_it.

Hint Resolve EV_map_XLEnv LV_map_XLEnv.

Fixpoint
ok_wf_ty
EV LV L (Π : LEnv EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
(T : ty ∅ EV LV L) (H : ok_ty Π T) :
wf_ty Ξ (L_bind_ty f T)
with
ok_wf_ms
EV LV L (Π : LEnv EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
(σ : ms ∅ EV LV L) (H : ok_ms Π σ) :
wf_ms Ξ (L_bind_ms f σ)
.
Proof.
+ destruct H ; simpl ; eauto 6.
+ destruct H ; simpl ; eauto.
Qed.

Hint Resolve ok_wf_ty.
Hint Resolve ok_wf_ms.

Fixpoint
ok_wf_md
EV LV V L (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
(m : md EV LV V L) σ β (H : ok_md Π Γ m σ β) :
∃ X, f β = lid_f X ∧
wf_md Ξ ((L_bind_ty f) ∘ Γ) (L_bind_md f m) (L_bind_ms f σ) X
with
ok_wf_ktx
EV LV V L (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
(K : ktx EV LV V L) T E T' E' (H : ok_ktx Π Γ K T E T' E') :
wf_ktx Ξ ((L_bind_ty f) ∘ Γ) (L_bind_ktx f K)
  (L_bind_ty f T) (L_bind_eff f E)
  (L_bind_ty f T') (L_bind_eff f E')
with
ok_wf_val
EV LV V L (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
(v : val EV LV V L) T (H : ok_val Π Γ v T) :
wf_val Ξ ((L_bind_ty f) ∘ Γ) (L_bind_val f v) (L_bind_ty f T)
with
ok_wf_tm
EV LV V L (Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
Ξ f (Q : XLEnv Ξ Π f)
(t : tm EV LV V L) T E (H : ok_tm Π Γ t T E) :
wf_tm Ξ ((L_bind_ty f) ∘ Γ) (L_bind_tm f t) (L_bind_ty f T) (L_bind_eff f E)
.
Proof.
+ destruct (f β) as [ | X ] eqn:EQ_β ; simpl ; [auto|].
  eexists ; split ; [reflexivity|].
  destruct H as [ ??? H' | ??? H' | ????? H' |
    ? T E ? T' E' Lookup ???? H' ] ; simpl.
  - constructor.
    eapply ok_wf_md in H' ; [ | eauto ].
    destruct H' as [Y [EQ_β' H']].
    rewrite EQ_β' in EQ_β ; inversion EQ_β ; subst Y.
    clear - H'.
    match goal with
    | [ H : wf_md ?Ξ ?Γ ?m ?σ ?X |- wf_md ?Ξ ?Γ' ?m ?σ ?X ] =>
      replace Γ' with Γ ; [ exact H |]
    end.
    unfold compose ; extensionality x ; rewrite L_bind_EV_map_ty ; auto.
  - constructor.
    eapply ok_wf_md in H' ; [ | eauto ].
    destruct H' as [Y [EQ_β' H']].
    rewrite EQ_β' in EQ_β ; inversion EQ_β ; subst Y.
    match goal with
    | [ H : wf_md ?Ξ ?Γ ?m ?σ ?X |- wf_md ?Ξ ?Γ' ?m ?σ ?X ] =>
      replace Γ' with Γ ; [ exact H |]
    end.
    unfold compose ; extensionality x ; rewrite L_bind_LV_map_ty ; auto.
  - constructor ; [ eauto | ].
    eapply ok_wf_md in H' ; [ | eauto ].
    destruct H' as [Y [EQ_β' H']].
    rewrite EQ_β' in EQ_β ; inversion EQ_β ; subst Y.
    match goal with
    | [ H : wf_md ?Ξ ?Γ ?m ?σ ?X |- wf_md ?Ξ ?Γ' ?m ?σ ?X ] =>
      replace Γ' with Γ ; [ exact H | extensionality x ; auto ]
    end.
  - eapply wf_md_res with (Tb := L_bind_ty f T') (Eb := L_bind_eff f E') ; eauto.
    * clear - Q EQ_β Lookup.
      eapply LEnv_lookup_inv_binds ; eauto.
    * eapply ok_wf_tm in H' ; [ | eauto ].
      match goal with
      | [ H : wf_tm ?Ξ ?Γ ?t ?T ?E |- wf_tm ?Ξ ?Γ' ?t ?T ?E ] =>
        replace Γ' with Γ ; [ exact H | extensionality x ; auto ]
      end.
+ destruct H as [ | ?????? H' | ??????? H' | ???????? H' | ???????? H' | ???????? H' |
    ???????? H' | ???????? H' | ????????? H' ] ; simpl.
  - constructor ; eauto.
  - eapply ok_wf_ktx in H' ; [|eauto].
    rewrite L_bind_it_msig.
    econstructor ; eauto.
  - eapply ok_wf_ktx in H' ; [|eauto].
    rewrite <- L_bind_eff_app ; econstructor ; eauto.
  - eapply ok_wf_ktx in H' ; [|eauto].
    erewrite <- EV_L_bind_ms ; [econstructor|] ; eauto.
  - eapply ok_wf_ktx in H' ; [|eauto].
    erewrite <- LV_L_bind_ms ; [econstructor|] ; eauto.
  - eapply ok_wf_ktx in H' ; [|eauto].
    econstructor ; eauto.
  - eapply ok_wf_val in H' ; [|eauto].
    econstructor ; eauto.
  - eapply ok_wf_ktx in H' ; [|eauto].
    econstructor ; eauto.
  - eapply ok_wf_tm in H' ; [|eauto].
    econstructor ; eauto.
    match goal with
    | [ H : wf_tm ?Ξ ?Γ ?t ?T ?E |- wf_tm ?Ξ ?Γ' ?t ?T ?E ] =>
      replace Γ' with Γ ; [ exact H | extensionality x ; auto ]
    end.
+ destruct H as [ | | ? ? ? H' | ? ? ? H' | ? ? ? ? ? H' ] ; simpl.
  - constructor.
  - constructor.
  - eapply ok_wf_md in H' ; [|eauto].
    destruct H' as [X [Hfβ H']] ; rewrite Hfβ.
    constructor.
    * rewrite L_bind_it_msig in H'.
      match goal with
      | [ H : wf_md ?Ξ ?Γ ?m ?σ ?X |- wf_md ?Ξ ?Γ' ?m ?σ ?X ] =>
        replace Γ' with Γ ; [ exact H |]
      end.
      extensionality x ; crush.
    * eauto.
    * apply XLEnv_inv_substituion_ok with (β := β) in Q.
      crush.
  - eapply ok_wf_md in H' ; [|eauto].
    destruct H' as [? [Hfβ ?]] ; rewrite Hfβ.
    constructor ; auto.
  - eapply ok_wf_ktx in H' ; [|eauto].
    constructor ; auto.
+ destruct H as [ ?? H'| ????? H' | ????? H' | ?????? H' H'' | ???? H' | ????? H' |
    ? T E OK_T OK_E H' | ?????? H' H'' | ?????? H' H'' | ?????? H' ] ; simpl.
  - eapply ok_wf_val in H' ; [|eauto].
    constructor ; auto.
  - eapply ok_wf_tm in H' ; [|eauto].
    erewrite <- EV_L_bind_ms ; [econstructor|] ; eauto.
  - eapply ok_wf_tm in H' ; [|eauto].
    erewrite <- LV_L_bind_ms ; [econstructor|] ; eauto.
  - eapply ok_wf_tm in H' ; [|eauto].
    eapply ok_wf_tm in H'' ; [|eauto].
    econstructor ; eauto.
  - eapply ok_wf_tm in H' ; [|eauto].
    rewrite L_bind_it_msig.
    econstructor ; eauto.
  - eapply ok_wf_tm in H' ; [|eauto].
    rewrite <- L_bind_eff_app.
    constructor ; auto.
  - econstructor ; [ eauto | eauto | ].
    intros X FrX.
    eapply ok_wf_tm
      with (Ξ := Ξ & X ~ (L_bind_ty f T, L_bind_eff f E)) (f := env_ext f (lid_f X))
      in H' ; [ | constructor ; eauto ].
    simpl L_bind_eff in H'.
    unshelve erewrite L_bind_map_ty, L_map_ty_id in H' ; eauto.
    unshelve erewrite L_bind_map_eff, L_map_eff_id in H' ; eauto.
    erewrite L_bind_bind_tm with (g := env_ext f (lid_f X)).
    match goal with
    | [ H : wf_tm ?Ξ ?Γ ?t ?T ?E |- wf_tm ?Ξ ?Γ' ?t ?T ?E ] =>
      replace Γ' with Γ ; [ exact H | ]
    end.
    { extensionality x ; unfold compose.
      unshelve erewrite L_bind_map_ty, L_map_ty_id ; eauto.
      intro ; erewrite L_map_lid_id ; eauto.
    }
    { intro α ; destruct α ; simpl ; [auto|].
      unshelve erewrite L_bind_map_lid, L_map_lid_id, L_bind_lid_id ; auto.
    }
    { intro ; erewrite L_map_lid_id ; auto. }
    { intro ; erewrite L_map_lid_id ; auto. }
  - econstructor.
    * eapply ok_wf_tm in H' ; eauto.
    * eapply ok_wf_tm in H'' ; eauto.
  - econstructor.
    * eapply ok_wf_ty ; eauto.
    * eapply ok_wf_tm in H' ; eauto.
    * eapply ok_wf_tm in H'' ; eauto.
      match goal with
      | [ H : wf_tm ?Ξ ?Γ ?t ?T ?E |- wf_tm ?Ξ ?Γ' ?t ?T ?E ] =>
        replace Γ' with Γ ; [ exact H | extensionality x ; auto ]
      end.
  - econstructor ; eauto.
Qed.

End section_ok_wf.


Lemma binds_wf EV LV (Ξ : XEnv EV LV) X T E :
wf_XEnv Ξ → binds X (T, E) Ξ → wf_ty Ξ T ∧ wf_eff Ξ E.
Proof.
induction 1 as [ | ? ? ? ? ? IH ] ; simpl.
+ intro BindsX ; apply binds_empty_inv in BindsX ; contradict BindsX.
+ intro BindsX.
  apply binds_concat_inv in BindsX.
  destruct BindsX as [BindsX | BindsX].
  - apply binds_single_inv in BindsX.
    destruct BindsX as [ HX HTE ].
    apply eq_sym in HX ; apply eq_sym in HTE.
    inversion HTE ; clear HTE ; subst.
    split ; [ apply weaken_wf_ty | apply weaken_wf_eff ] ; assumption.
  - destruct BindsX as [HX BindsX].
    specialize (IH BindsX).
    destruct IH.
    split ; [ apply weaken_wf_ty | apply weaken_wf_eff ] ; assumption.
Qed.
