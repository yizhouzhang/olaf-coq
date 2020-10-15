Require Import Lang.Syntax Lang.Bindings.
Set Implicit Arguments.

Section section_ktx.

Context (EV LV V L : Set).

(** Use [t] to fill in the hole of [ktx] *)
Fixpoint ktx_plug
(K : ktx EV LV V L) (t : tm EV LV V L) {struct K} :
tm EV LV V L :=
match K with
| ktx_hole => t
| ktx_op K => tm_op (ktx_plug K t)
| ktx_up K => tm_up (ktx_plug K t)
| ktx_down K X => tm_down X (ktx_plug K t)
| ktx_let K s => tm_let (ktx_plug K t) s
| ktx_throw K s => tm_throw (ktx_plug K t) s
| ktx_app_eff K E => tm_app_eff (ktx_plug K t) E
| ktx_app_lbl K ℓ => tm_app_lbl (ktx_plug K t) ℓ
| ktx_app_tm1 K s => tm_app_tm (ktx_plug K t) s
| ktx_app_tm2 K v => tm_app_tm v (ktx_plug K t)
end.

(** Compose outer evaluation context [K] and inner evaluation context
[J] to form a new evaluation context. *)
Fixpoint ktx_comp
(K : ktx EV LV V L) (J : ktx EV LV V L) {struct K} :
ktx EV LV V L :=
match K with
| ktx_hole => J
| ktx_op K => ktx_op (ktx_comp K J)
| ktx_up K => ktx_up (ktx_comp K J)
| ktx_down K X => ktx_down (ktx_comp K J) X
| ktx_let K t => ktx_let (ktx_comp K J) t
| ktx_throw K t => ktx_throw (ktx_comp K J) t
| ktx_app_eff K E => ktx_app_eff (ktx_comp K J) E
| ktx_app_lbl K ℓ => ktx_app_lbl (ktx_comp K J) ℓ
| ktx_app_tm1 K t => ktx_app_tm1 (ktx_comp K J) t
| ktx_app_tm2 K v => ktx_app_tm2 (ktx_comp K J) v
end.

(** Return [True] iff [X] is not a delimiter in [K]. *)
Fixpoint tunnels (X : var) (K : ktx EV LV V L) : Prop :=
match K with
| ktx_hole => True
| ktx_op K => tunnels X K
| ktx_up K => tunnels X K
| ktx_down K Y => tunnels X K ∧ X ≠ Y
| ktx_let K _ => tunnels X K
| ktx_throw K _ => tunnels X K
| ktx_app_eff K _ => tunnels X K
| ktx_app_lbl K _ => tunnels X K
| ktx_app_tm1 K _ => tunnels X K
| ktx_app_tm2 K _ => tunnels X K
end.

End section_ktx.


Inductive config :=
| config_mk : list var → tm0 → config
.

Notation "⟨ ξ , t ⟩" := (config_mk ξ t) : core_scope.

Inductive step : config → config → Prop :=
(** reduction rules *)
| step_let :
  ∀ ξ (v : val0) t,
  step ⟨ξ, tm_let v t⟩ ⟨ξ, V_subst_tm v t⟩
| step_throw :
  ∀ ξ K t,
  step
  ⟨ξ, tm_throw (val_cont K) t⟩
  ⟨ξ, ktx_plug K t⟩
| step_op :
  ∀ ξ m ι,
  step
  ⟨ξ, tm_op (val_fix m ι)⟩
  ⟨ξ, val_md (V_subst_md (val_fix m ι) m) ι⟩
| step_app_eff :
  ∀ ξ m ι E,
  step
  ⟨ξ, tm_app_eff (val_md (md_ev m) ι) E⟩
  ⟨ξ, val_md (EV_subst_md E m) ι⟩
| step_app_lbl :
  ∀ ξ m ι ℓ,
  step
  ⟨ξ, tm_app_lbl (val_md (md_lv m) ι) ℓ⟩
  ⟨ξ, val_md (LV_subst_md ℓ m) ι⟩
| step_app_tm :
  ∀ ξ m ι (v : val0),
  step
  ⟨ξ, tm_app_tm (val_md (md_tm m) ι) v⟩
  ⟨ξ, val_md (V_subst_md v m) ι⟩
| step_Down :
  ∀ ξ t X,
  X ∉ from_list ξ → (* This arbitrariness of [X] induces non-determinism *)
  step
  ⟨ξ, ⬇ t⟩
  ⟨X :: ξ, ⇩ X (L_subst_tm (lid_f X) t)⟩
| step_down_val :
  ∀ ξ X (v : val0),
  step ⟨ξ, ⇩ X v⟩ ⟨ξ, v⟩
| step_down_up :
  ∀ ξ X K t,
  tunnels X K →
  step
  ⟨ξ, ⇩ X (ktx_plug K (⇧ (val_md (md_res t) (lid_f X))))⟩
  ⟨ξ, V_subst_tm (val_cont (ktx_down K X)) t⟩

(** structural rules *)
| step_ktx_let :
  ∀ ξ₁ ξ₂ t₁ t₂ s,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_let t₁ s⟩ ⟨ξ₂, tm_let t₂ s⟩
| step_ktx_throw :
  ∀ ξ₁ ξ₂ t₁ t₂ s,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_throw t₁ s⟩ ⟨ξ₂, tm_throw t₂ s⟩
| step_ktx_app_tm1 :
  ∀ ξ₁ ξ₂ t₁ t₂ s,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_app_tm t₁ s⟩ ⟨ξ₂, tm_app_tm t₂ s⟩
| step_ktx_app_tm2 :
  ∀ ξ₁ ξ₂ (v : val0) t₁ t₂ ,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_app_tm v t₁⟩ ⟨ξ₂, tm_app_tm v t₂⟩
| step_ktx_app_eff :
  ∀ ξ₁ ξ₂ t₁ t₂ E,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_app_eff t₁ E⟩ ⟨ξ₂, tm_app_eff t₂ E⟩
| step_ktx_app_lbl :
  ∀ ξ₁ ξ₂ t₁ t₂ ℓ,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_app_lbl t₁ ℓ⟩ ⟨ξ₂, tm_app_lbl t₂ ℓ⟩
| step_ktx_op :
  ∀ ξ₁ ξ₂ t₁ t₂ ,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_op t₁⟩ ⟨ξ₂, tm_op t₂⟩
| step_ktx_up :
  ∀ ξ₁ ξ₂ t₁ t₂ ,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_up t₁⟩ ⟨ξ₂, tm_up t₂⟩
| step_ktx_down :
  ∀ ξ₁ ξ₂ t₁ t₂ X,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, ⇩ X t₁⟩ ⟨ξ₂, ⇩ X t₂⟩
.

(** The transitive closure of the reduction relation. *)
Definition step_tran := @Relation_Operators.clos_trans_1n _ step.

(** The reflexive and transitive closure of the reduction relation. *)
Definition step_refl_tran := @Relation_Operators.clos_refl_trans_1n _ step.

(** Reduction in a given number of steps. *)
Inductive step_n : nat → config → config → Prop :=
| step_n_O : ∀ c, step_n O c c
| step_n_S : ∀ n c₁ c₂ c₃,
    step c₁ c₂ →
    step_n n c₂ c₃ →
    step_n (S n) c₁ c₃
.
