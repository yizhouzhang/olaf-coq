Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.Compatability.
Require Import UFO.Lang.Static.
Require Import UFO.Lang.StaticFacts.

Implicit Types EV LV V L : Set.

(** Step-indexed parametricity, using a locally nameless rep of label identifiers *)
Section section_SI_LN_parametricity.

Local Fact wf_ext_Γ
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅) S :
wf_Γ Ξ Γ → wf_ty Ξ S → wf_Γ Ξ (env_ext Γ S).
Proof.
intros_all ; crush.
Qed.

Hint Resolve wf_ext_Γ wf_XEnv_cons weaken_wf_Γ.
Hint Resolve EV_map_wf_XEnv EV_map_wf_Γ.
Hint Resolve LV_map_wf_XEnv LV_map_wf_Γ.
Hint Constructors wf_ty wf_eff wf_ef wf_lbl.

Fixpoint
SI_LN_parametricity_md
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅)
(Wf_Ξ : wf_XEnv Ξ) (Wf_Γ : wf_Γ Ξ Γ)
m σ X (Wf_m : wf_md Ξ Γ m σ X)
n {struct Wf_m} :
n ⊨ ⟦ Ξ Γ ⊢ m ≼ˡᵒᵍₘ m : σ ^ (lbl_id (lid_f X)) ⟧
with
SI_LN_parametricity_ktx
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅)
(Wf_Ξ : wf_XEnv Ξ) (Wf_Γ : wf_Γ Ξ Γ)
K Ta Ea Tb Eb (Wf_K : wf_ktx Ξ Γ K Ta Ea Tb Eb)
n {struct Wf_K} :
n ⊨ ⟦ Ξ Γ ⊢ K ≼ˡᵒᵍ K : Ta # Ea ⇢ Tb # Eb ⟧
with
SI_LN_parametricity_val
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅)
(Wf_Ξ : wf_XEnv Ξ) (Wf_Γ : wf_Γ Ξ Γ)
v T (Wf_v : wf_val Ξ Γ v T)
n {struct Wf_v} :
n ⊨ ⟦ Ξ Γ ⊢ v ≼ˡᵒᵍᵥ v : T ⟧
with
SI_LN_parametricity_tm
EV LV V (Ξ : XEnv EV LV) (Γ : V → ty ∅ EV LV ∅)
(Wf_Ξ : wf_XEnv Ξ) (Wf_Γ : wf_Γ Ξ Γ)
t T E (Wf_t : wf_tm Ξ Γ t T E)
n {struct Wf_t} :
n ⊨ ⟦ Ξ Γ ⊢ t ≼ˡᵒᵍ t : T # E ⟧
.
Proof.
+ destruct Wf_m.
  - apply compat_md_ev.
    apply SI_LN_parametricity_md ; eauto.
  - apply compat_md_lv.
    apply SI_LN_parametricity_md ; eauto.
  - apply compat_md_tm.
    apply SI_LN_parametricity_md ; auto.
  - eapply compat_md_res.
    * eauto.
    * apply get_some_inv in H as H'.
      apply SI_LN_parametricity_tm ; auto 6.
+ destruct Wf_K.
  - apply compat_ktx_hole.
  - apply compat_ktx_op.
    apply SI_LN_parametricity_ktx ; auto.
  - apply compat_ktx_up.
    apply SI_LN_parametricity_ktx ; auto.
  - apply compat_ktx_app_eff.
    apply SI_LN_parametricity_ktx ; auto.
  - apply compat_ktx_app_lbl.
    * auto.
    * apply SI_LN_parametricity_ktx ; auto.
  - eapply compat_ktx_app_tm1.
    * apply SI_LN_parametricity_ktx ; eauto.
    * apply SI_LN_parametricity_tm ; auto.
  - eapply compat_ktx_app_tm2.
    * apply SI_LN_parametricity_ktx ; eauto.
    * apply SI_LN_parametricity_val ; auto.
  - eapply compat_ktx_throw.
    * apply SI_LN_parametricity_ktx ; eauto.
    * apply SI_LN_parametricity_tm ; auto.
  - eapply compat_ktx_let.
    * apply SI_LN_parametricity_ktx ; eauto.
    * apply SI_LN_parametricity_tm ; auto.
+ destruct Wf_v.
  - apply compat_val_unit.
  - apply compat_val_var.
  - apply compat_val_fix.
    iintro_later.
    apply SI_LN_parametricity_md ; try assumption.
    intro x ; destruct x as [|x] ; simpl ; [ | crush ].
    repeat constructor ; assumption.
  - apply compat_val_md.
    apply SI_LN_parametricity_md ; auto.
  - apply compat_val_ktx ; auto.
+ destruct Wf_t.
  - apply compat_tm_val ; auto.
  - apply compat_tm_app_eff ; auto.
  - apply compat_tm_app_lbl ; auto.
  - eapply compat_tm_app_tm.
    * apply SI_LN_parametricity_tm ; eauto.
    * apply SI_LN_parametricity_tm ; eauto.
  - apply compat_tm_op ; auto.
  - apply compat_tm_up ; auto.
  - apply compat_tm_down with (B := B \u dom Ξ) ; try assumption.
    intros ; eapply SI_LN_parametricity_tm ; eauto.
  - eapply compat_tm_throw.
    * apply SI_LN_parametricity_tm ; eauto.
    * apply SI_LN_parametricity_tm ; auto.
  - eapply compat_tm_let.
    * apply SI_LN_parametricity_tm ; eauto.
    * apply SI_LN_parametricity_tm ; auto.
  - eapply compat_sub.
    * eauto.
    * eauto.
    * apply SI_LN_parametricity_tm ; auto.
Qed.

End section_SI_LN_parametricity.

(** Parametricity, using a locally nameless rep of label identifiers *)
Section section_LN_parametricity.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (Γ : V → ty ∅ EV HV ∅).
Context (WF_Ξ : wf_XEnv Ξ).
Context (WF_Γ : wf_Γ Ξ Γ).

Hint Resolve SI_LN_parametricity_tm SI_LN_parametricity_val
  SI_LN_parametricity_ktx SI_LN_parametricity_md.

Theorem LN_parametricity_tm
t T E (WF_t : wf_tm Ξ Γ t T E) :
⊨ ⟦ Ξ Γ ⊢ t ≼ˡᵒᵍ t : T # E ⟧.
Proof.
intro ; auto.
Qed.

Theorem LN_parametricity_eq_tm
t T E (WF_t : wf_tm Ξ Γ t T E) :
⊨ ⟦ Ξ Γ ⊢ t ≈ˡᵒᵍ t : T # E ⟧.
Proof.
intro ; isplit ; auto.
Qed.

Theorem LN_parametricity_ktx
K Ta Ea Tb Eb (WF_K : wf_ktx Ξ Γ K Ta Ea Tb Eb) :
⊨ ⟦ Ξ Γ ⊢ K ≼ˡᵒᵍ K : Ta # Ea ⇢ Tb # Eb ⟧.
Proof.
intro ; auto.
Qed.

Theorem LN_parametricity_val
v T (WF_v : wf_val Ξ Γ v T) :
⊨ ⟦ Ξ Γ ⊢ v ≼ˡᵒᵍᵥ v : T ⟧.
Proof.
intro ; auto.
Qed.

Theorem LN_parametricity_md
m σ X (Wf_m : wf_md Ξ Γ m σ X) :
⊨ ⟦ Ξ Γ ⊢ m ≼ˡᵒᵍₘ m : σ ^ (lbl_id (lid_f X)) ⟧.
Proof.
intro ; auto.
Qed.

End section_LN_parametricity.


(** Step-indexed parametricity, using a de Bruijn rep of label identifiers *)
Section section_SI_DB_parametricity.
Context (EV LV V L : Set).
Context (Π : LEnv EV LV L).
Context (Γ : V → ty ∅ EV LV L).
Context (OK_Γ : ok_Γ Π Γ).
Context (n : nat).

Hint Resolve XLEnv_inv_wf_XEnv.
Hint Resolve ok_wf_ty.

Corollary SI_DB_parametricity_tm
t T E (OK_t : ok_tm Π Γ t T E) :
n ⊨ 【 Π Γ ⊢ t ≼ˡᵒᵍ t : T # E 】.
Proof.
iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ ; simpl.
apply SI_LN_parametricity_tm.
+ eauto.
+ intro x ; eauto.
+ eapply ok_wf_tm in OK_t ; eauto.
Qed.

Corollary SI_DB_parametricity_ktx
K Ta Ea Tb Eb (OK_K : ok_ktx Π Γ K Ta Ea Tb Eb) :
n ⊨ 【 Π Γ ⊢ K ≼ˡᵒᵍ K : Ta # Ea ⇢ Tb # Eb 】.
Proof.
iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ ; simpl.
apply SI_LN_parametricity_ktx.
+ eauto.
+ intro x ; eauto.
+ eapply ok_wf_ktx in OK_K ; eauto.
Qed.

Corollary SI_DB_parametricity_val
v T (OK_v : ok_val Π Γ v T) :
n ⊨ 【 Π Γ ⊢ v ≼ˡᵒᵍᵥ v : T 】.
Proof.
iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ ; simpl.
apply SI_LN_parametricity_val.
+ eauto.
+ intro x ; eauto.
+ eapply ok_wf_val in OK_v ; eauto.
Qed.

Corollary SI_DB_parametricity_md
m σ β (OK_m : ok_md Π Γ m σ β) :
n ⊨ 【 Π Γ ⊢ m ≼ˡᵒᵍₘ m : σ ^ (lbl_id (lid_b β)) 】.
Proof.
iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ ; simpl.
destruct (f β) as [|X] eqn:EQ_fβ ; [auto|].
apply SI_LN_parametricity_md.
+ eauto.
+ intro x ; eauto.
+ eapply ok_wf_md in OK_m ; [|eauto] ; crush.
Qed.

End section_SI_DB_parametricity.

(** Parametricity, using a de Bruijn rep of label identifiers *)
Section section_DB_parametricity.
Context (EV LV V L : Set).
Context (Π : LEnv EV LV L).
Context (Γ : V → ty ∅ EV LV L).
Context (OK_Γ : ok_Γ Π Γ).

Hint Resolve SI_DB_parametricity_tm SI_DB_parametricity_val
  SI_DB_parametricity_ktx SI_DB_parametricity_md.

Theorem DB_parametricity_tm
t T E (OK_t : ok_tm Π Γ t T E) :
⊨ 【 Π Γ ⊢ t ≼ˡᵒᵍ t : T # E 】.
Proof.
intro ; auto.
Qed.

Theorem DB_parametricity_eq_tm
t T E (OK_t : ok_tm Π Γ t T E) :
⊨ 【 Π Γ ⊢ t ≈ˡᵒᵍ t : T # E 】.
Proof.
intro ; isplit ; auto.
Qed.

Theorem DB_parametricity_ktx
K Ta Ea Tb Eb (OK_K : ok_ktx Π Γ K Ta Ea Tb Eb) :
⊨ 【 Π Γ ⊢ K ≼ˡᵒᵍ K : Ta # Ea ⇢ Tb # Eb 】.
Proof.
intro ; auto.
Qed.

Theorem DB_parametricity_val
v T (OK_v : ok_val Π Γ v T) :
⊨ 【 Π Γ ⊢ v ≼ˡᵒᵍᵥ v : T 】.
Proof.
intro ; auto.
Qed.

Theorem DB_parametricity_md
m σ β (OK_m : ok_md Π Γ m σ β) :
⊨ 【 Π Γ ⊢ m ≼ˡᵒᵍₘ m : σ ^ (lbl_id (lid_b β)) 】.
Proof.
intro ; auto.
Qed.

End section_DB_parametricity.
