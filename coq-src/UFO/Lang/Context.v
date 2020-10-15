Require Import UFO.Lang.Syntax.
Require Import UFO.Lang.Bindings.
Require Import UFO.Lang.Static.
Require Import UFO.Lang.Operational.
Require Import UFO.Lang.Xs.
Require Import UFO.Lang.Sig.
Set Implicit Arguments.

Implicit Types EV LV V L : Set.

(**
  C ::= ... | D[λk. [•]]
  D ::= C[νX. [•]] | D[Λα. [•]] | D[Λβ. [•]] | D[λx. [•]]
*)
Inductive
ctx : Set → Set → Set → Set → Type :=
| ctx_top : ctx ∅ ∅ ∅ ∅
| ctx_md : ∀ EV LV V L, dtx EV LV V L → ctx EV LV (inc V) L
| ctx_op : ∀ EV LV V L, ctx EV LV V L → ctx EV LV V L
| ctx_up : ∀ EV LV V L, ctx EV LV V L → ctx EV LV V L
| ctx_Down : ∀ EV LV V L, ctx EV LV V L → ctx EV LV V (inc L)
| ctx_let1 : ∀ EV LV V L, ctx EV LV V L → tm EV LV (inc V) L → ctx EV LV V L
| ctx_let2 : ∀ EV LV V L, ctx EV LV V L → tm EV LV V L → ctx EV LV (inc V) L
| ctx_throw1 : ∀ EV LV V L, ctx EV LV V L → tm EV LV V L → ctx EV LV V L
| ctx_throw2 : ∀ EV LV V L, ctx EV LV V L → tm EV LV V L → ctx EV LV V L
| ctx_app_eff : ∀ EV LV V L, ctx EV LV V L → eff ∅ EV LV L → ctx EV LV V L
| ctx_app_lbl : ∀ EV LV V L, ctx EV LV V L → lbl LV L → ctx EV LV V L
| ctx_app_tm1 : ∀ EV LV V L, ctx EV LV V L → tm EV LV V L → ctx EV LV V L
| ctx_app_tm2 : ∀ EV LV V L, ctx EV LV V L → tm EV LV V L → ctx EV LV V L
with
dtx : Set → Set → Set → Set → Type :=
| dtx_ctx : ∀ EV LV V L, ctx EV LV V L → L → dtx EV LV V L
| dtx_eff : ∀ EV LV V L, dtx EV LV V L → dtx (inc EV) LV V L
| dtx_lbl : ∀ EV LV V L, dtx EV LV V L → dtx EV (inc LV) V L
| dtx_tm :  ∀ EV LV V L, dtx EV LV V L → dtx EV LV (inc V) L
.

Fixpoint
ctx_plug EV LV V L (C : ctx EV LV V L) (t : tm EV LV V L) {struct C} : tm0
with
dtx_plug EV LV V L (D : dtx EV LV V L) (m : md EV LV V L) {struct D} : tm0.
Proof.
{
destruct C as [ | ? ? ? ? D | ? ? ? ? C | ? ? ? ? C | ? ? ? ? C | ? ? ? ? C r | ? ? ? ? C s |
  ? ? ? ? C s | ? ? ? ? C k | ? ? ? ? C E | ? ? ? ? C ℓ | ? ? ? ? C s | ? ? ? ? C f ].
+ refine t.
+ refine (dtx_plug _ _ _ _ D (md_res t)).
+ refine (ctx_plug _ _ _ _ C (tm_op t)).
+ refine (ctx_plug _ _ _ _ C (⇧ t)).
+ refine (ctx_plug _ _ _ _ C (⬇ t)).
+ refine (ctx_plug _ _ _ _ C (tm_let t r)).
+ refine (ctx_plug _ _ _ _ C (tm_let s t)).
+ refine (ctx_plug _ _ _ _ C (tm_throw t s)).
+ refine (ctx_plug _ _ _ _ C (tm_throw k t)).
+ refine (ctx_plug _ _ _ _ C (tm_app_eff t E)).
+ refine (ctx_plug _ _ _ _ C (tm_app_lbl t ℓ)).
+ refine (ctx_plug _ _ _ _ C (tm_app_tm t s)).
+ refine (ctx_plug _ _ _ _ C (tm_app_tm f t)).
}
{
destruct D as [ ? ? ? ? C β | ? ? ? ? D | ? ? ? ? D | ? ? ? ? D ].
+ refine (ctx_plug _ _ _ _ C (val_md m (lid_b β))).
+ refine (dtx_plug _ _ _ _ D (md_ev m)).
+ refine (dtx_plug _ _ _ _ D (md_lv m)).
+ refine (dtx_plug _ _ _ _ D (md_tm m)).
}
Defined.

Fixpoint
Xs_ctx EV LV V L (C : ctx EV LV V L) : vars
with
Xs_dtx EV LV V L (D : dtx EV LV V L) : vars.
Proof.
{
destruct C as [ | ? ? ? ? D | ? ? ? ? C | ? ? ? ? C | ? ? ? ? C | ? ? ? ? C r | ? ? ? ? C s |
  ? ? ? ? C s | ? ? ? ? C k | ? ? ? ? C E | ? ? ? ? C ℓ | ? ? ? ? C s | ? ? ? ? C f ].
+ refine \{}.
+ refine (Xs_dtx _ _ _ _ D).
+ refine (Xs_ctx _ _ _ _ C).
+ refine (Xs_ctx _ _ _ _ C).
+ refine (Xs_ctx _ _ _ _ C).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm r).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm s).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm s).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm k).
+ refine (Xs_ctx _ _ _ _ C \u Xs_eff E).
+ refine (Xs_ctx _ _ _ _ C \u Xs_lbl ℓ).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm s).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm f).
}
{
destruct D as [ ? ? ? ? C β | ? ? ? ? D | ? ? ? ? D | ? ? ? ? D ].
+ refine (Xs_ctx _ _ _ _ C).
+ refine (Xs_dtx _ _ _ _ D).
+ refine (Xs_dtx _ _ _ _ D).
+ refine (Xs_dtx _ _ _ _ D).
}
Defined.

Section section_Xs_ctx_plug.
Hint Rewrite union_empty_l union_empty_r union_assoc.

Hint Extern 1 => match goal with
| [ |- ?A \u ?B \u ?C = (?A \u ?C) \u ?B ] => rewrite union_comm_assoc, union_comm
end.

Fixpoint
Xs_ctx_plug EV LV V L (C : ctx EV LV V L) t :
Xs_tm (ctx_plug C t) = Xs_ctx C \u Xs_tm t
with
Xs_dtx_plug EV LV V L (D : dtx EV LV V L) m :
Xs_tm (dtx_plug D m) = Xs_dtx D \u Xs_md m.
Proof.
{ destruct C ; simpl ; crush. }
{ destruct D ; simpl ; crush. }
Qed.

End section_Xs_ctx_plug.

Inductive
ok_ctx :
∀ EV LV V L, ctx EV LV V L → (V → ty ∅ EV LV L) → (LEnv EV LV L) →
ty ∅ EV LV L → eff ∅ EV LV L → ty0 → Type :=
| ok_ctx_top :
  ∀ T,
  ok_ty LEnv_empty T →
  ok_ctx ctx_top ∅→ LEnv_empty T [] T
| ok_ctx_md :
  ∀ EV LV V L (D : dtx EV LV V L) Γ Π T E β T' E' T'',
  ok_dtx D Γ Π β (ms_res T E) T'' →
  LEnv_lookup β Π = (T', E') →
  ok_Γ Π Γ →
  ok_ctx (ctx_md D) (env_ext Γ (ty_cont T (ef_lbl (lbl_id (lid_b β)) :: E) T' E')) Π
  T' E' T''
| ok_ctx_op :
  ∀ EV LV V L (C : ctx EV LV V L) Γ Π N ℓ E T'',
  ok_ctx C Γ Π (ty_ms (it_msig N) ℓ) E T'' →
  ok_Γ Π Γ →
  ok_ctx (ctx_op C) Γ Π (ty_it N ℓ) E T''
| ok_ctx_up :
  ∀ EV LV V L (C : ctx EV LV V L) Γ Π ℓ T E E' T'',
  ok_ctx C Γ Π T ((ef_lbl ℓ) :: (E ++ E')) T'' →
  ok_Γ Π Γ →
  ok_ctx (ctx_up C) Γ Π (ty_ms (ms_res T E) ℓ) E' T''
| ok_ctx_Down :
  ∀ EV LV V L (C : ctx EV LV V L) Γ Π T E T',
  ok_ctx C Γ Π T E T' →
  ok_ty Π T → ok_eff Π E →
  ok_Γ Π Γ →
  ok_ctx (ctx_Down C) (compose L_shift_ty Γ) (LEnv_push Π T E)
    (L_shift_ty T) ((ef_lbl (lbl_id (lid_b VZ))) :: (L_shift_eff E)) T'
| ok_ctx_let1 :
  ∀ EV LV V L (C : ctx EV LV V L) t Γ Π S E T T',
  ok_ctx C Γ Π T E T' →
  ok_tm Π (env_ext Γ S) t T E →
  ok_ty Π S →
  ok_Γ Π Γ →
  ok_ctx (ctx_let1 C t) Γ Π S E T'
| ok_ctx_let2 :
  ∀ EV LV V L (C : ctx EV LV V L) s Γ Π S E T T',
  ok_ctx C Γ Π T E T' →
  ok_tm Π Γ s S E →
  ok_Γ Π Γ →
  ok_ctx (ctx_let2 C s) (env_ext Γ S) Π T E T'
| ok_ctx_throw1 :
  ∀ EV LV V L (C : ctx EV LV V L) s Γ Π T E T' E' T'',
  ok_ctx C Γ Π T' E' T'' →
  ok_tm Π Γ s T E →
  ok_Γ Π Γ →
  ok_ctx (ctx_throw1 C s) Γ Π (ty_cont T E T' E') E' T''
| ok_ctx_throw2 :
  ∀ EV LV V L (C : ctx EV LV V L) t Γ Π T E T' E' T'',
  ok_ctx C Γ Π T' E' T'' →
  ok_tm Π Γ t (ty_cont T E T' E') E' →
  ok_Γ Π Γ →
  ok_ctx (ctx_throw2 C t) Γ Π T E T''
| ok_ctx_app_eff :
  ∀ EV LV V L (C : ctx EV LV V L) E₁ Γ Π σ ℓ E₂ T'',
  ok_ctx C Γ Π (ty_ms (EV_subst_ms E₁ σ) ℓ) E₂ T'' →
  ok_eff Π E₁ →
  ok_Γ Π Γ →
  ok_ctx (ctx_app_eff C E₁) Γ Π (ty_ms (ms_ev σ) ℓ) E₂ T''
| ok_ctx_app_lbl :
  ∀ EV LV V L (C : ctx EV LV V L) ℓ₁ Γ Π σ ℓ₂ E T'',
  ok_ctx C Γ Π (ty_ms (LV_subst_ms ℓ₁ σ) ℓ₂) E T'' →
  ok_lbl Π ℓ₁ →
  ok_Γ Π Γ →
  ok_ctx (ctx_app_lbl C ℓ₁) Γ Π (ty_ms (ms_lv σ) ℓ₂) E T''
| ok_ctx_app_tm1 :
  ∀ EV LV V L (C : ctx EV LV V L) s Γ Π E σ ℓ S T'',
  ok_ctx C Γ Π (ty_ms σ ℓ) E T'' →
  ok_tm Π Γ s S E →
  ok_Γ Π Γ →
  ok_ctx (ctx_app_tm1 C s) Γ Π (ty_ms (ms_tm S σ) ℓ) E T''
| ok_ctx_app_tm2 :
  ∀ EV LV V L (C : ctx EV LV V L) t Γ Π E σ ℓ S T'',
  ok_ctx C Γ Π (ty_ms σ ℓ) E T'' →
  ok_tm Π Γ t (ty_ms (ms_tm S σ) ℓ) E →
  ok_Γ Π Γ →
  ok_ctx (ctx_app_tm2 C t) Γ Π S E T''
| ok_ctx_sub :
  ∀ EV LV V L (C : ctx EV LV V L) Γ Π T1 E1 T2 E2 T'',
  ok_ctx C Γ Π T2 E2 T'' →
  subty T1 T2 → se E1 E2 →
  ok_Γ Π Γ →
  ok_ctx C Γ Π T1 E1 T''

with
ok_dtx :
∀ EV LV V L, dtx EV LV V L → (V → ty ∅ EV LV L) → (LEnv EV LV L) →
L → ms ∅ EV LV L → ty0 → Type :=
| ok_dtx_ctx :
  ∀ EV LV V L (C : ctx EV LV V L) β Γ Π σ T',
  ok_ctx C Γ Π (ty_ms σ (lbl_id (lid_b β))) [] T' →
  ok_Γ Π Γ →
  ok_dtx (dtx_ctx C β) Γ Π β σ T'
| ok_dtx_eff :
  ∀ EV LV V L (D : dtx EV LV V L) Γ Π β σ T',
  ok_dtx D Γ Π β (ms_ev σ) T' →
  ok_Γ Π Γ →
  ok_dtx (dtx_eff D) (EV_shift_ty ∘ Γ) (EV_shift_LEnv Π) β σ T'
| ok_dtx_lbl :
  ∀ EV LV V L (D : dtx EV LV V L) Γ Π β σ T',
  ok_dtx D Γ Π β (ms_lv σ) T' →
  ok_Γ Π Γ →
  ok_dtx (dtx_lbl D) (LV_shift_ty ∘ Γ) (LV_shift_LEnv Π) β σ T'
| ok_dtx_tm :
  ∀ EV LV V L (D : dtx EV LV V L) Γ Π β S σ T',
  ok_dtx D Γ Π β (ms_tm S σ) T' →
  ok_Γ Π Γ →
  ok_dtx (dtx_tm D) (env_ext Γ S) Π β σ T'
.

Definition ctx_ref EV LV V L
(Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
(T : ty ∅ EV LV L) (E : eff ∅ EV LV L)
(t₁ t₂ : tm EV LV V L) : Prop :=
∀ C T', ok_ctx C Γ Π T E T' → Xs_ctx C = \{} →
∀ ξ₁ (v₁ : val0), step_refl_tran ⟨[], ctx_plug C t₁⟩ ⟨ξ₁, v₁⟩ →
∃ ξ₂ (v₂ : val0), step_refl_tran ⟨[], ctx_plug C t₂⟩ ⟨ξ₂, v₂⟩.

Notation "【 Π Γ ⊢ t₁ '≼ᶜᵗˣ' t₂ : T # E 】" := (ctx_ref Π Γ T E t₁ t₂)
  (Π at level 0, Γ at level 0, t₁ at level 0, t₂ at level 0, T at level 0).

Definition ctx_eq EV LV V L
(Π : LEnv EV LV L) (Γ : V → ty ∅ EV LV L)
(T : ty ∅ EV LV L) (E : eff ∅ EV LV L)
(t₁ t₂ : tm EV LV V L) : Prop :=
【Π Γ ⊢ t₁ ≼ᶜᵗˣ t₂ : T # E 】 ∧ 【Π Γ ⊢ t₂ ≼ᶜᵗˣ t₁ : T # E 】.

Notation "【 Π Γ ⊢ t₁ '≈ᶜᵗˣ' t₂ : T # E 】" := (ctx_eq Π Γ T E t₁ t₂)
  (Π at level 0, Γ at level 0, t₁ at level 0, t₂ at level 0, T at level 0).
