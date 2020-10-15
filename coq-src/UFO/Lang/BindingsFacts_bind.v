Require Import UFO.Lang.Syntax.
Require Import UFO.Lang.Bindings_map.
Require Import UFO.Lang.Bindings_bind.
Require Import UFO.Lang.BindingsFacts_map.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Section section_bind_app.
Hint Rewrite app_assoc.

Lemma EP_bind_eff_app EP' EP EV LV L
  (f : EP → eff EP' EV LV L) (E₁ E₂ : eff EP EV LV L) :
  EP_bind_eff f E₁ ++ EP_bind_eff f E₂ = EP_bind_eff f (E₁ ++ E₂).
Proof.
  induction E₁ ; crush.
Qed.

Lemma EV_bind_eff_app EP EV EV' LV L
  (f : EV → eff EP EV' LV L) (E₁ E₂ : eff EP EV LV L) :
  EV_bind_eff f E₁ ++ EV_bind_eff f E₂ = EV_bind_eff f (E₁ ++ E₂).
Proof.
  induction E₁ ; crush.
Qed.

Lemma LV_bind_eff_app EP EV LV LV' L
  (f : LV → lbl LV' L) (E₁ E₂ : eff EP EV LV L) :
  LV_bind_eff f E₁ ++ LV_bind_eff f E₂ = LV_bind_eff f (E₁ ++ E₂).
Proof.
  induction E₁ ; crush.
Qed.

Lemma L_bind_eff_app EP EV LV L L'
  (f : L → lid L') (E₁ E₂ : eff EP EV LV L) :
  L_bind_eff f E₁ ++ L_bind_eff f E₂ = L_bind_eff f (E₁ ++ E₂).
Proof.
  induction E₁ ; crush.
Qed.

End section_bind_app.

Lemma EV_bind_XEnv_empty
EV EV' LV (f : EV → eff ∅ EV' LV ∅) :
EV_bind_XEnv f empty = empty.
Proof.
apply map_empty.
Qed.

Lemma EV_bind_XEnv_single
EV EV' LV (f : EV → eff ∅ EV' LV ∅) X (T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅) :
EV_bind_XEnv f (X ~ (T, E)) = X ~ (EV_bind_ty f T, EV_bind_eff f E).
Proof.
apply map_single.
Qed.

Lemma EV_bind_XEnv_concat
EV EV' LV (f : EV → eff ∅ EV' LV ∅) (Ξ Ξ' : XEnv EV LV) :
EV_bind_XEnv f (Ξ & Ξ') =
(EV_bind_XEnv f Ξ) & (EV_bind_XEnv f Ξ').
Proof.
apply map_concat.
Qed.

Lemma EV_bind_XEnv_dom
EV EV' LV (f : EV → eff ∅ EV' LV ∅) (Ξ : XEnv EV LV) :
dom (EV_bind_XEnv f Ξ) = dom Ξ.
Proof.
induction Ξ as [ | ? ? [? ?] IHΞ ] using env_ind.
+ rewrite EV_bind_XEnv_empty.
  repeat rewrite dom_empty.
  reflexivity.
+ rewrite EV_bind_XEnv_concat, EV_bind_XEnv_single.
  repeat rewrite dom_concat, dom_single.
  rewrite IHΞ.
  reflexivity.
Qed.

Lemma LV_bind_XEnv_empty
EV LV LV' (f : LV → lbl LV' ∅) :
LV_bind_XEnv f (empty : XEnv EV LV) = empty.
Proof.
apply map_empty.
Qed.

Lemma LV_bind_XEnv_single
EV LV LV' (f : LV → lbl LV' ∅) X (T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅) :
LV_bind_XEnv f (X ~ (T, E)) = X ~ (LV_bind_ty f T, LV_bind_eff f E).
Proof.
apply map_single.
Qed.

Lemma LV_bind_XEnv_concat
EV LV LV' (f : LV → lbl LV' ∅) (Ξ Ξ' : XEnv EV LV) :
LV_bind_XEnv f (Ξ & Ξ') =
(LV_bind_XEnv f Ξ) & (LV_bind_XEnv f Ξ').
Proof.
apply map_concat.
Qed.

Lemma LV_bind_XEnv_dom
EV LV LV' (f : LV → lbl LV' ∅) (Ξ : XEnv EV LV) :
dom (LV_bind_XEnv f Ξ) = dom Ξ.
Proof.
induction Ξ as [ | ? ? [? ?] IHΞ ] using env_ind.
+ rewrite LV_bind_XEnv_empty.
  repeat rewrite dom_empty.
  reflexivity.
+ rewrite LV_bind_XEnv_concat, LV_bind_XEnv_single.
  repeat rewrite dom_concat, dom_single.
  rewrite IHΞ.
  reflexivity.
Qed.


Section section_binds_EV_bind.
Context (EV EV' LV : Set).
Context (f : EV → eff ∅ EV' LV ∅).
Context (X : var).

Lemma binds_EV_bind T E (Ξ : XEnv EV LV) :
binds X (T, E) Ξ →
binds X (EV_bind_ty f T, EV_bind_eff f E) (EV_bind_XEnv f Ξ).
Proof.
intro Hbinds.
induction Ξ as [ | Ξ' X' [ T' E' ] IHΞ' ] using env_ind.
+ apply binds_empty_inv in Hbinds ; crush.
+ apply binds_concat_inv in Hbinds.
  rewrite EV_bind_XEnv_concat, EV_bind_XEnv_single.
  destruct Hbinds as [ Hbinds | Hbinds ].
  - apply binds_single_inv in Hbinds ; crush.
  - destruct Hbinds as [ FrX Hbinds ] ; auto.
Qed.

Lemma binds_EV_bind_inv
(T' : ty ∅ EV' LV ∅) (E' : eff ∅ EV' LV ∅) (Ξ : XEnv EV LV) :
binds X (T', E') (EV_bind_XEnv f Ξ) →
∃ T E,
T' = EV_bind_ty f T ∧ E' = EV_bind_eff f E ∧ binds X (T, E) Ξ.
Proof.
intro Hbinds'.
induction Ξ as [ | Ξ Y [ T E ] IHΞ ] using env_ind.
+ rewrite EV_bind_XEnv_empty in Hbinds'.
  apply binds_empty_inv in Hbinds' ; crush.
+ rewrite EV_bind_XEnv_concat, EV_bind_XEnv_single in Hbinds'.
  apply binds_concat_inv in Hbinds'.
  destruct Hbinds' as [ Hbinds' | Hbinds' ].
  - apply binds_single_inv in Hbinds'.
    destruct Hbinds' as [ [] Heq ].
    inversion Heq ; subst.
    eauto.
  - destruct Hbinds' as [ FrX Hbinds' ].
    specialize (IHΞ Hbinds').
    destruct IHΞ as [T'' [E'' [? [? ?]]]].
    repeat eexists ; eauto.
Qed.

End section_binds_EV_bind.


Section section_binds_LV_bind.
Context (EV LV LV' : Set).
Context (f : LV → lbl LV' ∅).
Context (X : var).

Lemma binds_LV_bind T E (Ξ : XEnv EV LV) :
binds X (T, E) Ξ →
binds X (LV_bind_ty f T, LV_bind_eff f E) (LV_bind_XEnv f Ξ).
Proof.
intro Hbinds.
induction Ξ as [ | Ξ' X' [ T' E' ] IHΞ' ] using env_ind.
+ apply binds_empty_inv in Hbinds ; crush.
+ apply binds_concat_inv in Hbinds.
  rewrite LV_bind_XEnv_concat, LV_bind_XEnv_single.
  destruct Hbinds as [ Hbinds | Hbinds ].
  - apply binds_single_inv in Hbinds ; crush.
  - destruct Hbinds as [ FrX Hbinds ] ; auto.
Qed.

Lemma binds_LV_bind_inv
(T' : ty ∅ EV LV' ∅) (E' : eff ∅ EV LV' ∅) (Ξ : XEnv EV LV) :
binds X (T', E') (LV_bind_XEnv f Ξ) →
∃ T E,
T' = LV_bind_ty f T ∧ E' = LV_bind_eff f E ∧ binds X (T, E) Ξ.
Proof.
intro Hbinds'.
induction Ξ as [ | Ξ Y [ T E ] IHΞ ] using env_ind.
+ rewrite LV_bind_XEnv_empty in Hbinds'.
  apply binds_empty_inv in Hbinds' ; crush.
+ rewrite LV_bind_XEnv_concat, LV_bind_XEnv_single in Hbinds'.
  apply binds_concat_inv in Hbinds'.
  destruct Hbinds' as [ Hbinds' | Hbinds' ].
  - apply binds_single_inv in Hbinds'.
    destruct Hbinds' as [ [] Heq ].
    inversion Heq ; subst.
    eauto.
  - destruct Hbinds' as [ FrX Hbinds' ].
    specialize (IHΞ Hbinds').
    destruct IHΞ as [T'' [E'' [? [? ?]]]].
    repeat eexists ; eauto.
Qed.

End section_binds_LV_bind.


(** * Identity *)

Section section_EP_bind_id.

Definition
  EP_bind_ef_id
  EP EV LV L (f : EP → eff EP EV LV L) (Hf : ∀ α, f α = [ef_par α])
  (e : ef EP EV LV L) :
  EP_bind_ef f e = [e]
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EP_bind_ef_id.

Fixpoint
  EP_bind_eff_id
  EP EV LV L (f : EP → eff EP EV LV L) (Hf : ∀ α, f α = [ef_par α])
  (E : eff EP EV LV L) {struct E} :
  EP_bind_eff f E = E
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite EP_bind_eff_id.

Fixpoint
  EP_bind_it_id
  EP EV LV L (f : EP → eff EP EV LV L) (Hf : ∀ α, f α = [ef_par α])
  κ (N : it EP EV LV L κ) {struct N} :
  EP_bind_it f N = N
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite EP_bind_it_id.

Fixpoint
  EP_bind_ty_id
  EP EV LV L (f : EP → eff EP EV LV L) (Hf : ∀ α, f α = [ef_par α])
  (T : ty EP EV LV L) {struct T} :
  EP_bind_ty f T = T
with
  EP_bind_ms_id
  EP EV LV L (f : EP → eff EP EV LV L) (Hf : ∀ α, f α = [ef_par α])
  (σ : ms EP EV LV L) {struct σ} :
  EP_bind_ms f σ = σ
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite EP_bind_ty_id.
Hint Rewrite EP_bind_ms_id.

Fixpoint
  EP_bind_is_id
  EP EV LV L (f : EP → eff EP EV LV L) (Hf : ∀ α, f α = [ef_par α])
  (Σ : is EP EV LV L) {struct Σ} :
  EP_bind_is f Σ = Σ
.
Proof.
destruct Σ ; crush.
Qed.

End section_EP_bind_id.

Section section_EV_bind_id.

Definition
  EV_bind_ef_id
  EP EV LV L (f : EV → eff EP EV LV L) (Hf : ∀ α, f α = [ef_var α])
  (e : ef EP EV LV L) :
  EV_bind_ef f e = [e]
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EV_bind_ef_id.

Fixpoint
  EV_bind_eff_id
  EP EV LV L (f : EV → eff EP EV LV L) (Hf : ∀ α, f α = [ef_var α])
  (E : eff EP EV LV L) {struct E} :
  EV_bind_eff f E = E
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite EV_bind_eff_id.

Fixpoint
  EV_bind_it_id
  EP EV LV L (f : EV → eff EP EV LV L) (Hf : ∀ α, f α = [ef_var α])
  κ (N : it EP EV LV L κ) {struct N} :
  EV_bind_it f N = N
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite EV_bind_it_id.

Fixpoint
  EV_bind_ty_id
  EP EV LV L (f : EV → eff EP EV LV L) (Hf : ∀ α, f α = [ef_var α])
  (T : ty EP EV LV L) {struct T} :
  EV_bind_ty f T = T
with
  EV_bind_ms_id
  EP EV LV L (f : EV → eff EP EV LV L) (Hf : ∀ α, f α = [ef_var α])
  (σ : ms EP EV LV L) {struct σ} :
  EV_bind_ms f σ = σ
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite EV_bind_ty_id.
Hint Rewrite EV_bind_ms_id.

Fixpoint
  EV_bind_is_id
  EP EV LV L (f : EV → eff EP EV LV L) (Hf : ∀ α, f α = [ef_var α])
  (Σ : is EP EV LV L) {struct Σ} :
  EV_bind_is f Σ = Σ
.
Proof.
destruct Σ ; crush.
Qed.

Fixpoint
  EV_bind_md_id
  EV LV V L (f : EV → eff ∅ EV LV L) (Hf : ∀ α, f α = [ef_var α])
  (m : md EV LV V L) {struct m} :
  EV_bind_md f m = m
with
  EV_bind_ktx_id
  EV LV V L (f : EV → eff ∅ EV LV L) (Hf : ∀ α, f α = [ef_var α])
  (K : ktx EV LV V L) {struct K} :
  EV_bind_ktx f K = K
with
  EV_bind_val_id
  EV LV V L (f : EV → eff ∅ EV LV L) (Hf : ∀ α, f α = [ef_var α])
  (v : val EV LV V L) {struct v} :
  EV_bind_val f v = v
with
  EV_bind_tm_id
  EV LV V L (f : EV → eff ∅ EV LV L) (Hf : ∀ α, f α = [ef_var α])
  (t : tm EV LV V L) {struct t} :
  EV_bind_tm f t = t.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Hint Rewrite EV_bind_val_id EV_bind_tm_id.

Lemma EV_bind_XEnv_id
EV LV (f : EV → eff ∅ EV LV ∅) (Hf : ∀ α, f α = [ef_var α])
(Ξ : XEnv EV LV) :
EV_bind_XEnv f Ξ = Ξ.
Proof.
induction Ξ as [ | Ξ X [T E] IHΞ ] using env_ind.
+ rewrite EV_bind_XEnv_empty.
  reflexivity.
+ rewrite EV_bind_XEnv_concat, EV_bind_XEnv_single.
  erewrite IHΞ, EV_bind_ty_id, EV_bind_eff_id ; crush.
Qed.

End section_EV_bind_id.

Section section_LV_bind_id.

Definition
  LV_bind_lbl_id
  LV L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (ℓ : lbl LV L) :
  LV_bind_lbl f ℓ = ℓ
.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite LV_bind_lbl_id.

Fixpoint
  LV_bind_ef_id
  EP EV LV L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (e : ef EP EV LV L) :
  LV_bind_ef f e = e
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite LV_bind_ef_id.

Fixpoint
  LV_bind_eff_id
  EP EV LV L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (E : eff EP EV LV L) {struct E} :
  LV_bind_eff f E = E
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite LV_bind_eff_id.

Fixpoint
  LV_bind_it_id
  EP EV LV L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  κ (N : it EP EV LV L κ) {struct N} :
  LV_bind_it f N = N
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite LV_bind_it_id.

Fixpoint
  LV_bind_ty_id
  EP EV LV L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (T : ty EP EV LV L) {struct T} :
  LV_bind_ty f T = T
with
  LV_bind_ms_id
  EP EV LV L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (σ : ms EP EV LV L) {struct σ} :
  LV_bind_ms f σ = σ
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite LV_bind_ty_id.
Hint Rewrite LV_bind_ms_id.

Fixpoint
  LV_bind_is_id
  EP EV LV L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (Σ : is EP EV LV L) {struct Σ} :
  LV_bind_is f Σ = Σ
.
Proof.
destruct Σ ; crush.
Qed.

Fixpoint
  LV_bind_md_id
  EV LV V L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (m : md EV LV V L) {struct m} :
  LV_bind_md f m = m
with
  LV_bind_ktx_id
  EV LV V L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (K : ktx EV LV V L) {struct K} :
  LV_bind_ktx f K = K
with
  LV_bind_val_id
  EV LV V L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (v : val EV LV V L) {struct v} :
  LV_bind_val f v = v
with
  LV_bind_tm_id
  EV LV V L (f : LV → lbl LV L) (Hf : ∀ α, f α = lbl_var α)
  (t : tm EV LV V L) {struct t} :
  LV_bind_tm f t = t.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Hint Rewrite LV_bind_val_id LV_bind_tm_id.

Lemma LV_bind_XEnv_id
EV LV (f : LV → lbl LV ∅) (Hf : ∀ α, f α = lbl_var α)
(Ξ : XEnv EV LV) :
LV_bind_XEnv f Ξ = Ξ.
Proof.
induction Ξ as [ | Ξ X [T E] IHΞ ] using env_ind.
+ rewrite LV_bind_XEnv_empty.
  reflexivity.
+ rewrite LV_bind_XEnv_concat, LV_bind_XEnv_single.
  erewrite IHΞ, LV_bind_ty_id, LV_bind_eff_id ; crush.
Qed.

End section_LV_bind_id.

Section section_L_bind_id.

Definition
  L_bind_lid_id
  L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (ID : lid L) :
  L_bind_lid f ID = ID
.
Proof.
destruct ID ; crush.
Qed.

Hint Rewrite L_bind_lid_id.

Definition
  L_bind_lbl_id
  LV L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (ℓ : lbl LV L) :
  L_bind_lbl f ℓ = ℓ
.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite L_bind_lbl_id.

Fixpoint
  L_bind_ef_id
  EP EV LV L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (e : ef EP EV LV L) :
  L_bind_ef f e = e
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite L_bind_ef_id.

Fixpoint
  L_bind_eff_id
  EP EV LV L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (E : eff EP EV LV L) {struct E} :
  L_bind_eff f E = E
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite L_bind_eff_id.

Fixpoint
  L_bind_it_id
  EP EV LV L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  κ (N : it EP EV LV L κ) {struct N} :
  L_bind_it f N = N
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite L_bind_it_id.

Fixpoint
  L_bind_ty_id
  EP EV LV L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (T : ty EP EV LV L) {struct T} :
  L_bind_ty f T = T
with
  L_bind_ms_id
  EP EV LV L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (σ : ms EP EV LV L) {struct σ} :
  L_bind_ms f σ = σ
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite L_bind_ty_id.
Hint Rewrite L_bind_ms_id.

Fixpoint
  L_bind_is_id
  EP EV LV L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (Σ : is EP EV LV L) {struct Σ} :
  L_bind_is f Σ = Σ
.
Proof.
destruct Σ ; crush.
Qed.

Fixpoint
  L_bind_md_id
  EV LV V L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (m : md EV LV V L) {struct m} :
  L_bind_md f m = m
with
  L_bind_ktx_id
  EV LV V L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (K : ktx EV LV V L) {struct K} :
  L_bind_ktx f K = K
with
  L_bind_val_id
  EV LV V L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (v : val EV LV V L) {struct v} :
  L_bind_val f v = v
with
  L_bind_tm_id
  EV LV V L (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (t : tm EV LV V L) {struct t} :
  L_bind_tm f t = t.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

End section_L_bind_id.

Fixpoint
  V_bind_md_id
  EV LV V L (f : V → val EV LV V L) (Hf : ∀ x, f x = val_var x)
  (m : md EV LV V L) {struct m} :
  V_bind_md f m = m
with
  V_bind_ktx_id
  EV LV V L (f : V → val EV LV V L) (Hf : ∀ x, f x = val_var x)
  (K : ktx EV LV V L) {struct K} :
  V_bind_ktx f K = K
with
  V_bind_val_id
  EV LV V L (f : V → val EV LV V L) (Hf : ∀ x, f x = val_var x)
  (v : val EV LV V L) {struct v} :
  V_bind_val f v = v
with
  V_bind_tm_id
  EV LV V L (f : V → val EV LV V L) (Hf : ∀ x, f x = val_var x)
  (t : tm EV LV V L) {struct t} :
  V_bind_tm f t = t.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.


(** * Composition *)

Section section_EP_bind_map.

Hint Rewrite <- EP_map_eff_app.

Hint Extern 1 => match goal with
| [ |- context[ EP_map_eff _ (EP_map_eff _ _) ] ] => erewrite EP_map_map_eff ; crush
| [ |- context[ EP_map_eff _ (LV_map_eff _ _) ] ] => erewrite EP_LV_map_eff ; crush
| [ |- context[ EP_map_eff _ (L_map_eff _ _) ] ] => erewrite EP_L_map_eff ; crush
end.

Definition
  EP_bind_map_ef
  (EP₁ EP₂₁ EP₂₂ EP₃ EV LV L : Set)
  (f₁ : EP₁ → EP₂₁) (f₂ : EP₂₁ → eff EP₃ EV LV L)
  (g₁ : EP₁ → eff EP₂₂ EV LV L) (g₂ : EP₂₂ → EP₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EP_map_eff g₂ (g₁ x))
  (e : ef EP₁ EV LV L) :
  EP_bind_ef f₂ (EP_map_ef f₁ e) = EP_map_eff g₂ (EP_bind_ef g₁ e)
.
Proof.
destruct e ; simpl ;
crush.
Qed.

Fixpoint
  EP_bind_map_eff
  (EP₁ EP₂₁ EP₂₂ EP₃ EV LV L : Set)
  (f₁ : EP₁ → EP₂₁) (f₂ : EP₂₁ → eff EP₃ EV LV L)
  (g₁ : EP₁ → eff EP₂₂ EV LV L) (g₂ : EP₂₂ → EP₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EP_map_eff g₂ (g₁ x))
  (E : eff EP₁ EV LV L) {struct E} :
  EP_bind_eff f₂ (EP_map_eff f₁ E) = EP_map_eff g₂ (EP_bind_eff g₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite EP_bind_map_ef ;
repeat erewrite EP_bind_map_eff ;
crush.
Qed.

Fixpoint
  EP_bind_map_it
  (EP₁ EP₂₁ EP₂₂ EP₃ EV LV L : Set)
  (f₁ : EP₁ → EP₂₁) (f₂ : EP₂₁ → eff EP₃ EV LV L)
  (g₁ : EP₁ → eff EP₂₂ EV LV L) (g₂ : EP₂₂ → EP₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EP_map_eff g₂ (g₁ x))
  κ (N : it EP₁ EV LV L κ) {struct N} :
  EP_bind_it f₂ (EP_map_it f₁ N) = EP_map_it g₂ (EP_bind_it g₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EP_bind_map_it ;
repeat erewrite EP_bind_map_eff ;
crush.
Qed.

Hint Rewrite EP_EV_map_eff.

Fixpoint
  EP_bind_map_ty
  (EP₁ EP₂₁ EP₂₂ EP₃ EV LV L : Set)
  (f₁ : EP₁ → EP₂₁) (f₂ : EP₂₁ → eff EP₃ EV LV L)
  (g₁ : EP₁ → eff EP₂₂ EV LV L) (g₂ : EP₂₂ → EP₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EP_map_eff g₂ (g₁ x))
  (T : ty EP₁ EV LV L) {struct T} :
  EP_bind_ty f₂ (EP_map_ty f₁ T) = EP_map_ty g₂ (EP_bind_ty g₁ T)
with
  EP_bind_map_ms
  (EP₁ EP₂₁ EP₂₂ EP₃ EV LV L : Set)
  (f₁ : EP₁ → EP₂₁) (f₂ : EP₂₁ → eff EP₃ EV LV L)
  (g₁ : EP₁ → eff EP₂₂ EV LV L) (g₂ : EP₂₂ → EP₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EP_map_eff g₂ (g₁ x))
  (σ : ms EP₁ EV LV L) {struct σ} :
  EP_bind_ms f₂ (EP_map_ms f₁ σ) = EP_map_ms g₂ (EP_bind_ms g₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EP_bind_map_ty ;
  repeat erewrite EP_bind_map_ms ;
  repeat erewrite EP_bind_map_it ;
  repeat erewrite EP_bind_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EP_bind_map_ty ;
  repeat erewrite EP_bind_map_ms ;
  repeat erewrite EP_bind_map_eff ;
  crush.
Qed.

Fixpoint
  EP_bind_map_is
  (EP₁ EP₂₁ EP₂₂ EP₃ EV LV L : Set)
  (f₁ : EP₁ → EP₂₁) (f₂ : EP₂₁ → eff EP₃ EV LV L)
  (g₁ : EP₁ → eff EP₂₂ EV LV L) (g₂ : EP₂₂ → EP₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EP_map_eff g₂ (g₁ x))
  (Σ : is EP₁ EV LV L) {struct Σ} :
  EP_bind_is f₂ (EP_map_is f₁ Σ) = EP_map_is g₂ (EP_bind_is g₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EP_bind_map_ms ;
repeat erewrite EP_bind_map_is ;
crush.
Qed.

End section_EP_bind_map.

Section section_EV_bind_map.

Hint Rewrite <- EV_map_eff_app.

Hint Extern 1 => match goal with
| [ |- context[ EV_map_eff _ (EV_map_eff _ _) ] ] => erewrite EV_map_map_eff ; crush
| [ |- context[ EV_map_eff _ (LV_map_eff _ _) ] ] => erewrite EV_LV_map_eff ; crush
| [ |- context[ EV_map_eff _ (L_map_eff _ _) ] ] => erewrite EV_L_map_eff ; crush
end.

Definition
  EV_bind_map_ef
  (EP EV₁ EV₂₁ EV₂₂ EV₃ LV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EP EV₃ LV L)
  (g₁ : EV₁ → eff EP EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (e : ef EP EV₁ LV L) :
  EV_bind_ef f₂ (EV_map_ef f₁ e) = EV_map_eff g₂ (EV_bind_ef g₁ e)
.
Proof.
destruct e ; simpl ;
crush.
Qed.

Fixpoint EV_bind_map_eff (EP EV₁ EV₂₁ EV₂₂ EV₃ LV L : Set) (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EP EV₃ LV L)
  (g₁ : EV₁ → eff EP EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (E : eff EP EV₁ LV L) {struct E} :
  EV_bind_eff f₂ (EV_map_eff f₁ E) = EV_map_eff g₂ (EV_bind_eff g₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite EV_bind_map_ef ;
repeat erewrite EV_bind_map_eff ;
crush.
Qed.

Fixpoint
  EV_bind_map_it
  (EP EV₁ EV₂₁ EV₂₂ EV₃ LV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EP EV₃ LV L)
  (g₁ : EV₁ → eff EP EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  κ (N : it EP EV₁ LV L κ) {struct N} :
  EV_bind_it f₂ (EV_map_it f₁ N) = EV_map_it g₂ (EV_bind_it g₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EV_bind_map_it ;
repeat erewrite EV_bind_map_eff ;
crush.
Qed.

Fixpoint
  EV_bind_map_ty
  (EP EV₁ EV₂₁ EV₂₂ EV₃ LV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EP EV₃ LV L)
  (g₁ : EV₁ → eff EP EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (T : ty EP EV₁ LV L) {struct T} :
  EV_bind_ty f₂ (EV_map_ty f₁ T) = EV_map_ty g₂ (EV_bind_ty g₁ T)
with
  EV_bind_map_ms
  (EP EV₁ EV₂₁ EV₂₂ EV₃ LV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EP EV₃ LV L)
  (g₁ : EV₁ → eff EP EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (σ : ms EP EV₁ LV L) {struct σ} :
  EV_bind_ms f₂ (EV_map_ms f₁ σ) = EV_map_ms g₂ (EV_bind_ms g₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_bind_map_ty ;
  repeat erewrite EV_bind_map_ms ;
  repeat erewrite EV_bind_map_it ;
  repeat erewrite EV_bind_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EV_bind_map_ty ;
  repeat erewrite EV_bind_map_ms ;
  repeat erewrite EV_bind_map_eff ;
  crush.
Qed.

Hint Rewrite EP_EV_map_eff.

Fixpoint
  EV_bind_map_is
  (EP EV₁ EV₂₁ EV₂₂ EV₃ LV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EP EV₃ LV L)
  (g₁ : EV₁ → eff EP EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (Σ : is EP EV₁ LV L) {struct Σ} :
  EV_bind_is f₂ (EV_map_is f₁ Σ) = EV_map_is g₂ (EV_bind_is g₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EV_bind_map_ms ;
repeat erewrite EV_bind_map_is ;
crush.
Qed.

Fixpoint
  EV_bind_map_md
  (EV₁ EV₂₁ EV₂₂ EV₃ LV V L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff ∅ EV₃ LV L)
  (g₁ : EV₁ → eff ∅ EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (m : md EV₁ LV V L) {struct m} :
  EV_bind_md f₂ (EV_map_md f₁ m) = EV_map_md g₂ (EV_bind_md g₁ m)
with
  EV_bind_map_ktx
  (EV₁ EV₂₁ EV₂₂ EV₃ LV V L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff ∅ EV₃ LV L)
  (g₁ : EV₁ → eff ∅ EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (K : ktx EV₁ LV V L) {struct K} :
  EV_bind_ktx f₂ (EV_map_ktx f₁ K) = EV_map_ktx g₂ (EV_bind_ktx g₁ K)
with
  EV_bind_map_val
  (EV₁ EV₂₁ EV₂₂ EV₃ LV V L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff ∅ EV₃ LV L)
  (g₁ : EV₁ → eff ∅ EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (v : val EV₁ LV V L) {struct v} :
  EV_bind_val f₂ (EV_map_val f₁ v) = EV_map_val g₂ (EV_bind_val g₁ v)
with
  EV_bind_map_tm
  (EV₁ EV₂₁ EV₂₂ EV₃ LV V L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff ∅ EV₃ LV L)
  (g₁ : EV₁ → eff ∅ EV₂₂ LV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (t : tm EV₁ LV V L) {struct t} :
  EV_bind_tm f₂ (EV_map_tm f₁ t) = EV_map_tm g₂ (EV_bind_tm g₁ t).
Proof.
+ destruct m ; simpl ;
  repeat erewrite EV_bind_map_tm ;
  repeat erewrite EV_bind_map_md ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite EV_bind_map_ktx ;
  repeat erewrite EV_bind_map_tm ;
  repeat erewrite EV_bind_map_val ;
  repeat erewrite EV_bind_map_ty ;
  repeat erewrite EV_bind_map_eff ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_bind_map_md ;
  repeat erewrite EV_bind_map_ktx ;
  repeat erewrite EV_bind_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_bind_map_ty ;
  repeat erewrite EV_bind_map_eff ;
  repeat erewrite EV_bind_map_val ;
  repeat erewrite EV_bind_map_md ;
  repeat erewrite EV_bind_map_tm ;
  crush.
Qed.

Lemma  EV_bind_map_XEnv
  (EV₁ EV₂₁ EV₂₂ EV₃ LV : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff ∅ EV₃ LV ∅)
  (g₁ : EV₁ → eff ∅ EV₂₂ LV ∅) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (Ξ : XEnv EV₁ LV) :
  EV_bind_XEnv f₂ (EV_map_XEnv f₁ Ξ) = EV_map_XEnv g₂ (EV_bind_XEnv g₁ Ξ).
Proof.
induction Ξ as [ | Ξ X [T E] IHΞ ] using env_ind.
+ repeat (rewrite EV_map_XEnv_empty || rewrite EV_bind_XEnv_empty).
  reflexivity.
+ rewrite EV_map_XEnv_concat, EV_bind_XEnv_concat.
  rewrite EV_map_XEnv_single, EV_bind_XEnv_single.
  rewrite EV_bind_XEnv_concat, EV_map_XEnv_concat.
  rewrite EV_bind_XEnv_single, EV_map_XEnv_single.
  erewrite IHΞ, EV_bind_map_ty, EV_bind_map_eff ; crush.
Qed.

End section_EV_bind_map.

Section section_LV_bind_map.

Hint Rewrite <- LV_map_eff_app.

Hint Extern 1 => match goal with
| [ |- context[ LV_map_lbl _ (LV_map_lbl _ _) ] ] => erewrite LV_map_map_lbl ; crush
| [ |- context[ LV_map_lbl _ (L_map_lbl _ _) ] ] => erewrite LV_L_map_lbl ; crush
end.

Definition
  LV_bind_map_lbl
  (LV₁ LV₂₁ LV₂₂ LV₃ L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (ℓ : lbl LV₁ L) :
  LV_bind_lbl f₂ (LV_map_lbl f₁ ℓ) = LV_map_lbl g₂ (LV_bind_lbl g₁ ℓ)
.
Proof.
destruct ℓ ; simpl ; crush.
Qed.

Definition
  LV_bind_map_ef
  (EP EV LV₁ LV₂₁ LV₂₂ LV₃ L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (e : ef EP EV LV₁ L) :
  LV_bind_ef f₂ (LV_map_ef f₁ e) = LV_map_ef g₂ (LV_bind_ef g₁ e)
.
Proof.
+ destruct e ; simpl ;
  repeat erewrite LV_bind_map_lbl ;
  crush.
Qed.

Fixpoint
  LV_bind_map_eff
  (EP EV LV₁ LV₂₁ LV₂₂ LV₃ L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (E : eff EP EV LV₁ L) {struct E} :
  LV_bind_eff f₂ (LV_map_eff f₁ E) = LV_map_eff g₂ (LV_bind_eff g₁ E)
.
Proof.
+ destruct E ; simpl ;
  repeat erewrite LV_bind_map_ef ;
  repeat erewrite LV_bind_map_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_map_it
  (EP EV LV₁ LV₂₁ LV₂₂ LV₃ L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  κ (N : it EP EV LV₁ L κ) {struct N} :
  LV_bind_it f₂ (LV_map_it f₁ N) = LV_map_it g₂ (LV_bind_it g₁ N)
.
Proof.
+ destruct N ; simpl ;
  repeat erewrite LV_bind_map_it ;
  repeat erewrite LV_bind_map_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_map_ty
  (EP EV LV₁ LV₂₁ LV₂₂ LV₃ L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (T : ty EP EV LV₁ L) {struct T} :
  LV_bind_ty f₂ (LV_map_ty f₁ T) = LV_map_ty g₂ (LV_bind_ty g₁ T)
with
  LV_bind_map_ms
  (EP EV LV₁ LV₂₁ LV₂₂ LV₃ L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (σ : ms EP EV LV₁ L) {struct σ} :
  LV_bind_ms f₂ (LV_map_ms f₁ σ) = LV_map_ms g₂ (LV_bind_ms g₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite LV_bind_map_ty ;
  repeat erewrite LV_bind_map_ms ;
  repeat erewrite LV_bind_map_it ;
  repeat erewrite LV_bind_map_eff ;
  repeat erewrite LV_bind_map_lbl ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite LV_bind_map_ty ;
  repeat erewrite LV_bind_map_ms ;
  repeat erewrite LV_bind_map_eff ;
  repeat erewrite LV_bind_map_lbl ;
  crush.
Qed.

Fixpoint
  LV_bind_map_is
  (EP EV LV₁ LV₂₁ LV₂₂ LV₃ L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (Σ : is EP EV LV₁ L) {struct Σ} :
  LV_bind_is f₂ (LV_map_is f₁ Σ) = LV_map_is g₂ (LV_bind_is g₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite LV_bind_map_ms ;
repeat erewrite LV_bind_map_is ;
crush.
Qed.

Fixpoint
  LV_bind_map_md
  (EV LV₁ LV₂₁ LV₂₂ LV₃ V L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (m : md EV LV₁ V L) {struct m} :
  LV_bind_md f₂ (LV_map_md f₁ m) = LV_map_md g₂ (LV_bind_md g₁ m)
with
  LV_bind_map_ktx
  (EV LV₁ LV₂₁ LV₂₂ LV₃ V L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (K : ktx EV LV₁ V L) {struct K} :
  LV_bind_ktx f₂ (LV_map_ktx f₁ K) = LV_map_ktx g₂ (LV_bind_ktx g₁ K)
with
  LV_bind_map_val
  (EV LV₁ LV₂₁ LV₂₂ LV₃ V L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (v : val EV LV₁ V L) {struct v} :
  LV_bind_val f₂ (LV_map_val f₁ v) = LV_map_val g₂ (LV_bind_val g₁ v)
with
  LV_bind_map_tm
  (EV LV₁ LV₂₁ LV₂₂ LV₃ V L : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ L)
  (g₁ : LV₁ → lbl LV₂₂ L) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (t : tm EV LV₁ V L) {struct t} :
  LV_bind_tm f₂ (LV_map_tm f₁ t) = LV_map_tm g₂ (LV_bind_tm g₁ t).
Proof.
+ destruct m ; simpl ;
  repeat erewrite LV_bind_map_tm ;
  repeat erewrite LV_bind_map_md ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite LV_bind_map_ktx ;
  repeat erewrite LV_bind_map_val ;
  repeat erewrite LV_bind_map_lbl ;
  repeat erewrite LV_bind_map_ty ;
  repeat erewrite LV_bind_map_eff ;
  repeat erewrite LV_bind_map_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite LV_bind_map_md ;
  repeat erewrite LV_bind_map_tm ;
  repeat erewrite LV_bind_map_ktx ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite LV_bind_map_ty ;
  repeat erewrite LV_bind_map_lbl ;
  repeat erewrite LV_bind_map_eff ;
  repeat erewrite LV_bind_map_val ;
  repeat erewrite LV_bind_map_md ;
  repeat erewrite LV_bind_map_tm ;
  crush.
Qed.

Lemma LV_bind_map_XEnv
  (EV LV₁ LV₂₁ LV₂₂ LV₃ : Set)
  (f₁ : LV₁ → LV₂₁) (f₂ : LV₂₁ → lbl LV₃ _)
  (g₁ : LV₁ → lbl LV₂₂ _) (g₂ : LV₂₂ → LV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = LV_map_lbl g₂ (g₁ x))
  (Ξ : XEnv EV LV₁) :
  LV_bind_XEnv f₂ (LV_map_XEnv f₁ Ξ) = LV_map_XEnv g₂ (LV_bind_XEnv g₁ Ξ).
Proof.
induction Ξ as [ | Ξ X [T E] IHΞ ] using env_ind.
+ repeat (rewrite LV_map_XEnv_empty || rewrite LV_bind_XEnv_empty).
  reflexivity.
+ rewrite LV_map_XEnv_concat, LV_bind_XEnv_concat.
  rewrite LV_map_XEnv_single, LV_bind_XEnv_single.
  rewrite LV_bind_XEnv_concat, LV_map_XEnv_concat.
  rewrite LV_bind_XEnv_single, LV_map_XEnv_single.
  erewrite IHΞ, LV_bind_map_ty, LV_bind_map_eff ; crush.
Qed.

End section_LV_bind_map.

Section section_L_bind_map.

Hint Rewrite <- L_map_eff_app.

Hint Extern 1 => match goal with
| [ |- context[ L_map_lid _ (L_map_lid _ _) ] ] => erewrite L_map_map_lid ; crush
end.

Definition
  L_bind_map_lid
  (L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (ID : lid L₁) :
  L_bind_lid f₂ (L_map_lid f₁ ID) = L_map_lid g₂ (L_bind_lid g₁ ID)
.
Proof.
destruct ID ; simpl ;
crush.
Qed.

Definition
  L_bind_map_lbl
  (LV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (ℓ : lbl LV L₁) :
  L_bind_lbl f₂ (L_map_lbl f₁ ℓ) = L_map_lbl g₂ (L_bind_lbl g₁ ℓ)
.
Proof.
destruct ℓ ; simpl ;
repeat erewrite L_bind_map_lid ;
crush.
Qed.

Definition
  L_bind_map_ef
  (EP EV LV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (e : ef EP EV LV L₁) :
  L_bind_ef f₂ (L_map_ef f₁ e) = L_map_ef g₂ (L_bind_ef g₁ e)
.
Proof.
+ destruct e ; simpl ;
  repeat erewrite L_bind_map_lbl ;
  crush.
Qed.

Fixpoint
  L_bind_map_eff
  (EP EV LV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (E : eff EP EV LV L₁) {struct E} :
  L_bind_eff f₂ (L_map_eff f₁ E) = L_map_eff g₂ (L_bind_eff g₁ E)
.
Proof.
+ destruct E ; simpl ;
  repeat erewrite L_bind_map_ef ;
  repeat erewrite L_bind_map_eff ;
  crush.
Qed.

Fixpoint
  L_bind_map_it
  (EP EV LV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  κ (N : it EP EV LV L₁ κ) {struct N} :
  L_bind_it f₂ (L_map_it f₁ N) = L_map_it g₂ (L_bind_it g₁ N)
.
Proof.
+ destruct N ; simpl ;
  repeat erewrite L_bind_map_it ;
  repeat erewrite L_bind_map_eff ;
  crush.
Qed.

Fixpoint
  L_bind_map_ty
  (EP EV LV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (T : ty EP EV LV L₁) {struct T} :
  L_bind_ty f₂ (L_map_ty f₁ T) = L_map_ty g₂ (L_bind_ty g₁ T)
with
  L_bind_map_ms
  (EP EV LV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (σ : ms EP EV LV L₁) {struct σ} :
  L_bind_ms f₂ (L_map_ms f₁ σ) = L_map_ms g₂ (L_bind_ms g₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_bind_map_ty ;
  repeat erewrite L_bind_map_ms ;
  repeat erewrite L_bind_map_it ;
  repeat erewrite L_bind_map_eff ;
  repeat erewrite L_bind_map_lbl ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite L_bind_map_ms ;
  repeat erewrite L_bind_map_ty ;
  repeat erewrite L_bind_map_eff ;
  crush.
Qed.

Fixpoint
  L_bind_map_is
  (EP EV LV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (Σ : is EP EV LV L₁) {struct Σ} :
  L_bind_is f₂ (L_map_is f₁ Σ) = L_map_is g₂ (L_bind_is g₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite L_bind_map_ms ;
repeat erewrite L_bind_map_is ;
crush.
Qed.

Fixpoint
  L_bind_map_md
  (EV LV V L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (m : md EV LV V L₁) {struct m} :
  L_bind_md f₂ (L_map_md f₁ m) = L_map_md g₂ (L_bind_md g₁ m)
with
  L_bind_map_ktx
  (EV LV V L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (K : ktx EV LV V L₁) {struct K} :
  L_bind_ktx f₂ (L_map_ktx f₁ K) = L_map_ktx g₂ (L_bind_ktx g₁ K)
with
  L_bind_map_val
  (EV LV V L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (v : val EV LV V L₁) {struct v} :
  L_bind_val f₂ (L_map_val f₁ v) = L_map_val g₂ (L_bind_val g₁ v)
with
  L_bind_map_tm
  (EV LV V L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (t : tm EV LV V L₁) {struct t} :
  L_bind_tm f₂ (L_map_tm f₁ t) = L_map_tm g₂ (L_bind_tm g₁ t).
Proof.
+ destruct m ; simpl ;
  repeat erewrite L_bind_map_tm ;
  repeat erewrite L_bind_map_md ;
  repeat erewrite L_bind_map_lid ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite L_bind_map_ktx ;
  repeat erewrite L_bind_map_tm ;
  repeat erewrite L_bind_map_val ;
  repeat erewrite L_bind_map_ty ;
  repeat erewrite L_bind_map_eff ;
  repeat erewrite L_bind_map_lbl ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_bind_map_ktx ;
  repeat erewrite L_bind_map_md ;
  repeat erewrite L_bind_map_tm ;
  repeat erewrite L_bind_map_lid ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_bind_map_ty ;
  repeat erewrite L_bind_map_eff ;
  repeat erewrite L_bind_map_lbl ;
  repeat erewrite L_bind_map_val ;
  repeat erewrite L_bind_map_tm ;
  repeat erewrite L_bind_map_md ;
  repeat erewrite L_bind_map_lid ;
  crush.
Qed.

End section_L_bind_map.

Section section_V_bind_map.

Hint Extern 1 => match goal with
| [ |- context[ V_map_val _ (V_map_val _ _) ] ] => erewrite V_map_map_val ; crush
| [ |- context[ LV_map_val _ (V_map_val _ _) ] ] => erewrite LV_V_map_val ; crush
| [ |- context[ EV_map_val _ (V_map_val _ _) ] ] => erewrite EV_V_map_val ; crush
| [ |- context[ V_map_val _ (L_map_val _ _) ] ] => erewrite V_L_map_val ; crush
end.

Fixpoint
  V_bind_map_md
  (EV LV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV LV V₃ L)
  (g₁ : V₁ → val EV LV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
  (m : md EV LV V₁ L) {struct m} :
  V_bind_md f₂ (V_map_md f₁ m) = V_map_md g₂ (V_bind_md g₁ m)
with
  V_bind_map_ktx
  (EV LV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV LV V₃ L)
  (g₁ : V₁ → val EV LV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
  (K : ktx EV LV V₁ L) {struct K} :
  V_bind_ktx f₂ (V_map_ktx f₁ K) = V_map_ktx g₂ (V_bind_ktx g₁ K)
with
  V_bind_map_val
  (EV LV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV LV V₃ L)
  (g₁ : V₁ → val EV LV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
  (v : val EV LV V₁ L) {struct v} :
  V_bind_val f₂ (V_map_val f₁ v) = V_map_val g₂ (V_bind_val g₁ v)
with
  V_bind_map_tm
  (EV LV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV LV V₃ L)
  (g₁ : V₁ → val EV LV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
  (t : tm EV LV V₁ L) {struct t} :
  V_bind_tm f₂ (V_map_tm f₁ t) = V_map_tm g₂ (V_bind_tm g₁ t).
Proof.
+ destruct m ; simpl ;
  repeat erewrite V_bind_map_md ;
  repeat erewrite V_bind_map_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite V_bind_map_ktx ;
  repeat erewrite V_bind_map_val ;
  repeat erewrite V_bind_map_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_map_ktx ;
  repeat erewrite V_bind_map_md ;
  repeat erewrite V_bind_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_map_val ;
  repeat erewrite V_bind_map_tm ;
  repeat erewrite V_bind_map_md ;
  crush.
Qed.

End section_V_bind_map.

Section section_EP_bind_EV_map.

Definition
  EP_bind_EV_map_ef EP EP' EV EV' LV L
  (g : EV → EV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EV_map_eff g (f₁ x))
  (e : ef EP EV LV L) :
  EP_bind_ef f₂ (EV_map_ef g e) = EV_map_eff g (EP_bind_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EV_map_eff_app.

Fixpoint
  EP_bind_EV_map_eff EP EP' EV EV' LV L
  (g : EV → EV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EV_map_eff g (f₁ x))
  (E : eff EP EV LV L) {struct E} :
  EP_bind_eff f₂ (EV_map_eff g E) = EV_map_eff g (EP_bind_eff f₁ E)
.
Proof.
  destruct E ; simpl ;
  repeat erewrite EP_bind_EV_map_ef ;
  repeat erewrite EP_bind_EV_map_eff ;
  crush.
Qed.

Fixpoint
  EP_bind_EV_map_it EP EP' EV EV' LV L
  (g : EV → EV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EV_map_eff g (f₁ x))
  κ (N : it EP EV LV L κ) {struct N} :
  EP_bind_it f₂ (EV_map_it g N) = EV_map_it g (EP_bind_it f₁ N)
.
Proof.
  destruct N ; simpl ;
  repeat erewrite EP_bind_EV_map_it ;
  repeat erewrite EP_bind_EV_map_eff ;
  crush.
Qed.

Fixpoint
  EP_bind_EV_map_ty EP EP' EV EV' LV L
  (g : EV → EV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EV_map_eff g (f₁ x))
  (T : ty EP EV LV L) {struct T} :
  EP_bind_ty f₂ (EV_map_ty g T) = EV_map_ty g (EP_bind_ty f₁ T)
with
  EP_bind_EV_map_ms EP EP' EV EV' LV L
  (g : EV → EV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EV_map_eff g (f₁ x))
  (σ : ms EP EV LV L) {struct σ} :
  EP_bind_ms f₂ (EV_map_ms g σ) = EV_map_ms g (EP_bind_ms f₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EP_bind_EV_map_ty ;
  repeat erewrite EP_bind_EV_map_ms ;
  repeat erewrite EP_bind_EV_map_it ;
  repeat erewrite EP_bind_EV_map_eff ;
  crush.
+ destruct σ ; simpl.
  - erewrite EP_bind_EV_map_ms ; [ reflexivity | ].
    intro ; unfold compose ; rewrite H ; simpl.
    repeat erewrite EV_map_map_eff ; reflexivity.
  - erewrite EP_bind_EV_map_ms ; [ reflexivity | ].
    intro ; unfold compose ; rewrite H ; simpl.
    erewrite EV_LV_map_eff ; reflexivity.
  - erewrite EP_bind_EV_map_ty, EP_bind_EV_map_ms ; crush.
  - erewrite EP_bind_EV_map_ty, EP_bind_EV_map_eff ; crush.
Qed.

Hint Rewrite EP_EV_map_eff.

Fixpoint
  EP_bind_EV_map_is EP EP' EV EV' LV L
  (g : EV → EV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EV_map_eff g (f₁ x))
  (Σ : is EP EV LV L) {struct Σ} :
  EP_bind_is f₂ (EV_map_is g Σ) = EV_map_is g (EP_bind_is f₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EP_bind_EV_map_is ;
repeat erewrite EP_bind_EV_map_ms ;
crush.
Qed.

End section_EP_bind_EV_map.

Section section_EP_bind_LV_map.

Definition
  EP_bind_LV_map_ef EP EP' EV LV LV' L
  (g : LV → LV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV' L)
  (H : ∀ x, f₂ x = LV_map_eff g (f₁ x))
  (e : ef EP EV LV L) :
  EP_bind_ef f₂ (LV_map_ef g e) = LV_map_eff g (EP_bind_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite LV_map_eff_app.

Fixpoint
  EP_bind_LV_map_eff EP EP' EV LV LV' L
  (g : LV → LV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV' L)
  (H : ∀ x, f₂ x = LV_map_eff g (f₁ x))
  (E : eff EP EV LV L) {struct E} :
  EP_bind_eff f₂ (LV_map_eff g E) = LV_map_eff g (EP_bind_eff f₁ E)
.
Proof.
  destruct E ; simpl ;
  repeat erewrite EP_bind_LV_map_ef ;
  repeat erewrite EP_bind_LV_map_eff ;
  crush.
Qed.

Fixpoint
  EP_bind_LV_map_it EP EP' EV LV LV' L
  (g : LV → LV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV' L)
  (H : ∀ x, f₂ x = LV_map_eff g (f₁ x))
  κ (N : it EP EV LV L κ) {struct N} :
  EP_bind_it f₂ (LV_map_it g N) = LV_map_it g (EP_bind_it f₁ N)
.
Proof.
  destruct N ; simpl ;
  repeat erewrite EP_bind_LV_map_it ;
  repeat erewrite EP_bind_LV_map_eff ;
  crush.
Qed.

Fixpoint
  EP_bind_LV_map_ty EP EP' EV LV LV' L
  (g : LV → LV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV' L)
  (H : ∀ x, f₂ x = LV_map_eff g (f₁ x))
  (T : ty EP EV LV L) {struct T} :
  EP_bind_ty f₂ (LV_map_ty g T) = LV_map_ty g (EP_bind_ty f₁ T)
with
  EP_bind_LV_map_ms EP EP' EV LV LV' L
  (g : LV → LV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV' L)
  (H : ∀ x, f₂ x = LV_map_eff g (f₁ x))
  (σ : ms EP EV LV L) {struct σ} :
  EP_bind_ms f₂ (LV_map_ms g σ) = LV_map_ms g (EP_bind_ms f₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EP_bind_LV_map_ty ;
  repeat erewrite EP_bind_LV_map_ms ;
  repeat erewrite EP_bind_LV_map_it ;
  repeat erewrite EP_bind_LV_map_eff ;
  crush.
+ destruct σ ; simpl.
  - erewrite EP_bind_LV_map_ms ; [ reflexivity | ].
    intro ; unfold compose ; rewrite H ; simpl.
    erewrite EV_LV_map_eff ; reflexivity.
  - erewrite EP_bind_LV_map_ms ; [ reflexivity | ].
    intro ; unfold compose ; rewrite H ; simpl.
    repeat erewrite LV_map_map_eff ; reflexivity.
  - erewrite EP_bind_LV_map_ty, EP_bind_LV_map_ms ; crush.
  - erewrite EP_bind_LV_map_ty, EP_bind_LV_map_eff ; crush.
Qed.

Hint Rewrite EP_LV_map_eff.

Fixpoint
  EP_bind_LV_map_is EP EP' EV LV LV' L
  (g : LV → LV') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV' L)
  (H : ∀ x, f₂ x = LV_map_eff g (f₁ x))
  (Σ : is EP EV LV L) {struct Σ} :
  EP_bind_is f₂ (LV_map_is g Σ) = LV_map_is g (EP_bind_is f₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EP_bind_LV_map_is ;
repeat erewrite EP_bind_LV_map_ms ;
crush.
Qed.

End section_EP_bind_LV_map.

Section section_EP_bind_L_map.

Definition
  EP_bind_L_map_ef EP EP' EV LV L L'
  (g : L → L') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (e : ef EP EV LV L) :
  EP_bind_ef f₂ (L_map_ef g e) = L_map_eff g (EP_bind_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite L_map_eff_app.

Fixpoint
  EP_bind_L_map_eff EP EP' EV LV L L'
  (g : L → L') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (E : eff EP EV LV L) {struct E} :
  EP_bind_eff f₂ (L_map_eff g E) = L_map_eff g (EP_bind_eff f₁ E)
.
Proof.
  destruct E ; simpl ;
  repeat erewrite EP_bind_L_map_ef ;
  repeat erewrite EP_bind_L_map_eff ;
  crush.
Qed.

Fixpoint
  EP_bind_L_map_it EP EP' EV LV L L'
  (g : L → L') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  κ (N : it EP EV LV L κ) {struct N} :
  EP_bind_it f₂ (L_map_it g N) = L_map_it g (EP_bind_it f₁ N)
.
Proof.
  destruct N ; simpl ;
  repeat erewrite EP_bind_L_map_it ;
  repeat erewrite EP_bind_L_map_eff ;
  crush.
Qed.

Fixpoint
  EP_bind_L_map_ty EP EP' EV LV L L'
  (g : L → L') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (T : ty EP EV LV L) {struct T} :
  EP_bind_ty f₂ (L_map_ty g T) = L_map_ty g (EP_bind_ty f₁ T)
with
  EP_bind_L_map_ms EP EP' EV LV L L'
  (g : L → L') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (σ : ms EP EV LV L) {struct σ} :
  EP_bind_ms f₂ (L_map_ms g σ) = L_map_ms g (EP_bind_ms f₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EP_bind_L_map_ty ;
  repeat erewrite EP_bind_L_map_ms ;
  repeat erewrite EP_bind_L_map_it ;
  repeat erewrite EP_bind_L_map_eff ;
  crush.
+ destruct σ ; simpl.
  - erewrite EP_bind_L_map_ms ; [ reflexivity | ].
    intro ; unfold compose ; rewrite H ; simpl.
    erewrite EV_L_map_eff ; reflexivity.
  - erewrite EP_bind_L_map_ms ; [ reflexivity | ].
    intro ; unfold compose ; rewrite H ; simpl.
    erewrite LV_L_map_eff ; reflexivity.
  - erewrite EP_bind_L_map_ty, EP_bind_L_map_ms ; crush.
  - erewrite EP_bind_L_map_ty, EP_bind_L_map_eff ; crush.
Qed.

Hint Rewrite EP_L_map_eff.

Fixpoint
  EP_bind_L_map_is EP EP' EV LV L L'
  (g : L → L') (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (Σ : is EP EV LV L) {struct Σ} :
  EP_bind_is f₂ (L_map_is g Σ) = L_map_is g (EP_bind_is f₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EP_bind_L_map_ms ;
repeat erewrite EP_bind_L_map_is ;
crush.
Qed.

End section_EP_bind_L_map.

Fixpoint
  EV_bind_V_map_md EV EV' LV V V' L
  (g : V → V') (f : EV → eff ∅ EV' LV L)
  (m : md EV LV V L) {struct m} :
  EV_bind_md f (V_map_md g m) = V_map_md g (EV_bind_md f m)
with
  EV_bind_V_map_ktx EV EV' LV V V' L
  (g : V → V') (f : EV → eff ∅ EV' LV L)
  (K : ktx EV LV V L) {struct K} :
  EV_bind_ktx f (V_map_ktx g K) = V_map_ktx g (EV_bind_ktx f K)
with
  EV_bind_V_map_tm EV EV' LV V V' L
  (g : V → V') (f : EV → eff ∅ EV' LV L)
  (t : tm EV LV V L) {struct t} :
  EV_bind_tm f (V_map_tm g t) = V_map_tm g (EV_bind_tm f t)
with
  EV_bind_V_map_val EV EV' LV V V' L
  (g : V → V') (f : EV → eff ∅ EV' LV L)
  (v : val EV LV V L) {struct v} :
  EV_bind_val f (V_map_val g v) = V_map_val g (EV_bind_val f v)
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Fixpoint
  LV_bind_V_map_md EV LV LV' V V' L
  (g : V → V') (f : LV → lbl LV' L)
  (m : md EV LV V L) {struct m} :
  LV_bind_md f (V_map_md g m) = V_map_md g (LV_bind_md f m)
with
  LV_bind_V_map_tm EV LV LV' V V' L
  (g : V → V') (f : LV → lbl LV' L)
  (t : tm EV LV V L) {struct t} :
  LV_bind_tm f (V_map_tm g t) = V_map_tm g (LV_bind_tm f t)
with
  LV_bind_V_map_ktx EV LV LV' V V' L
  (g : V → V') (f : LV → lbl LV' L)
  (K : ktx EV LV V L) {struct K} :
  LV_bind_ktx f (V_map_ktx g K) = V_map_ktx g (LV_bind_ktx f K)
with
  LV_bind_V_map_val EV LV LV' V V' L
  (g : V → V') (f : LV → lbl LV' L)
  (v : val EV LV V L) {struct v} :
  LV_bind_val f (V_map_val g v) = V_map_val g (LV_bind_val f v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite LV_bind_V_map_md ;
  repeat erewrite LV_bind_V_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite LV_bind_V_map_tm ;
  repeat erewrite LV_bind_V_map_val ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite LV_bind_V_map_ktx ;
  repeat erewrite LV_bind_V_map_val ;
  repeat erewrite LV_bind_V_map_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite LV_bind_V_map_ktx ;
  repeat erewrite LV_bind_V_map_tm ;
  repeat erewrite LV_bind_V_map_md ;
  crush.
Qed.

Fixpoint
  L_bind_V_map_md EV LV V V' L L'
  (g : V → V') (f : L → lid L')
  (m : md EV LV V L) {struct m} :
  L_bind_md f (V_map_md g m) = V_map_md g (L_bind_md f m)
with
  L_bind_V_map_tm EV LV V V' L L'
  (g : V → V') (f : L → lid L')
  (t : tm EV LV V L) {struct t} :
  L_bind_tm f (V_map_tm g t) = V_map_tm g (L_bind_tm f t)
with
  L_bind_V_map_ktx EV LV V V' L L'
  (g : V → V') (f : L → lid L')
  (K : ktx EV LV V L) {struct K} :
  L_bind_ktx f (V_map_ktx g K) = V_map_ktx g (L_bind_ktx f K)
with
  L_bind_V_map_val EV LV V V' L L'
  (g : V → V') (f : L → lid L')
  (v : val EV LV V L) {struct v} :
  L_bind_val f (V_map_val g v) = V_map_val g (L_bind_val f v)
.
Proof.
+ destruct m ; crush.
+ destruct t ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
Qed.

Section section_EV_bind_LV_map.

Hint Extern 1 => match goal with
| [ |- context[ LV_map_eff _ (LV_map_eff _ _) ] ] => erewrite LV_map_map_eff ; crush
| [ |- context[ LV_map_eff _ (L_map_eff _ _) ] ] => erewrite LV_L_map_eff ; crush
| [ |- context[ EV_map_eff _ (LV_map_eff _ _) ] ] => erewrite EV_LV_map_eff ; crush
end.

Hint Rewrite LV_map_eff_app.

Definition
  EV_bind_LV_map_ef EP EV EV' LV LV' L
  (g : LV → LV') (f₁ : EV → eff EP EV' LV' L) (f₂ : EV → eff EP EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  (e : ef EP EV LV L) :
  EV_bind_ef f₁ (LV_map_ef g e) = LV_map_eff g (EV_bind_ef f₂ e)
.
Proof.
destruct e ; simpl ; crush.
Qed.

Fixpoint
  EV_bind_LV_map_eff EP EV EV' LV LV' L
  (g : LV → LV') (f₁ : EV → eff EP EV' LV' L) (f₂ : EV → eff EP EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  (E : eff EP EV LV L) {struct E} :
  EV_bind_eff f₁ (LV_map_eff g E) = LV_map_eff g (EV_bind_eff f₂ E)
.
Proof.
destruct E ; simpl ; [ crush | ].
erewrite EV_bind_LV_map_ef, EV_bind_LV_map_eff ; crush.
Qed.

Fixpoint
  EV_bind_LV_map_it EP EV EV' LV LV' L
  (g : LV → LV') (f₁ : EV → eff EP EV' LV' L) (f₂ : EV → eff EP EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  κ (N : it EP EV LV L κ) {struct N} :
  EV_bind_it f₁ (LV_map_it g N) = LV_map_it g (EV_bind_it f₂ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EV_bind_LV_map_it ;
repeat erewrite EV_bind_LV_map_eff ;
crush.
Qed.

Fixpoint
  EV_bind_LV_map_ty EP EV EV' LV LV' L
  (g : LV → LV') (f₁ : EV → eff EP EV' LV' L) (f₂ : EV → eff EP EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  (T : ty EP EV LV L) {struct T} :
  EV_bind_ty f₁ (LV_map_ty g T) = LV_map_ty g (EV_bind_ty f₂ T)
with
  EV_bind_LV_map_ms EP EV EV' LV LV' L
  (g : LV → LV') (f₁ : EV → eff EP EV' LV' L) (f₂ : EV → eff EP EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  (σ : ms EP EV LV L) {struct σ} :
  EV_bind_ms f₁ (LV_map_ms g σ) = LV_map_ms g (EV_bind_ms f₂ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_bind_LV_map_ty ;
  repeat erewrite EV_bind_LV_map_ms ;
  repeat erewrite EV_bind_LV_map_it ;
  repeat erewrite EV_bind_LV_map_eff ;
  repeat erewrite EV_bind_LV_map_lbl ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EV_bind_LV_map_ty ;
  repeat erewrite EV_bind_LV_map_ms ;
  repeat erewrite EV_bind_LV_map_eff ;
  repeat erewrite EV_bind_LV_map_lbl ;
  crush.
Qed.

Hint Rewrite EP_LV_map_eff.

Fixpoint
  EV_bind_LV_map_is EP EV EV' LV LV' L
  (g : LV → LV') (f₁ : EV → eff EP EV' LV' L) (f₂ : EV → eff EP EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  (Σ : is EP EV LV L) {struct Σ} :
  EV_bind_is f₁ (LV_map_is g Σ) = LV_map_is g (EV_bind_is f₂ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EV_bind_LV_map_is ;
repeat erewrite EV_bind_LV_map_ms ;
crush.
Qed.

Fixpoint
  EV_bind_LV_map_md EV EV' LV LV' V L
  (g : LV → LV') (f₁ : EV → eff ∅ EV' LV' L) (f₂ : EV → eff ∅ EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  (m : md EV LV V L) {struct m} :
  EV_bind_md f₁ (LV_map_md g m) = LV_map_md g (EV_bind_md f₂ m)
with
  EV_bind_LV_map_tm EV EV' LV LV' V L
  (g : LV → LV') (f₁ : EV → eff ∅ EV' LV' L) (f₂ : EV → eff ∅ EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  (t : tm EV LV V L) {struct t} :
  EV_bind_tm f₁ (LV_map_tm g t) = LV_map_tm g (EV_bind_tm f₂ t)
with
  EV_bind_LV_map_val EV EV' LV LV' V L
  (g : LV → LV') (f₁ : EV → eff ∅ EV' LV' L) (f₂ : EV → eff ∅ EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  (v : val EV LV V L) {struct v} :
  EV_bind_val f₁ (LV_map_val g v) = LV_map_val g (EV_bind_val f₂ v)
with
  EV_bind_LV_map_ktx EV EV' LV LV' V L
  (g : LV → LV') (f₁ : EV → eff ∅ EV' LV' L) (f₂ : EV → eff ∅ EV' LV L)
  (Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x))
  (K : ktx EV LV V L) {struct K} :
  EV_bind_ktx f₁ (LV_map_ktx g K) = LV_map_ktx g (EV_bind_ktx f₂ K)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite EV_bind_LV_map_md ;
  repeat erewrite EV_bind_LV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_bind_LV_map_tm ;
  repeat erewrite EV_bind_LV_map_md ;
  repeat erewrite EV_bind_LV_map_val ;
  repeat erewrite EV_bind_LV_map_ty ;
  repeat erewrite EV_bind_LV_map_eff ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_bind_LV_map_ktx ;
  repeat erewrite EV_bind_LV_map_tm ;
  repeat erewrite EV_bind_LV_map_md ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite EV_bind_LV_map_ktx ;
  repeat erewrite EV_bind_LV_map_tm ;
  repeat erewrite EV_bind_LV_map_val ;
  repeat erewrite EV_bind_LV_map_ty ;
  repeat erewrite EV_bind_LV_map_eff ;
  crush.
Qed.

Lemma EV_bind_LV_map_XEnv
EV EV' LV LV'
(g : LV → LV') (f₁ : EV → eff ∅ EV' LV' ∅) (f₂ : EV → eff ∅ EV' LV ∅)
(Hf : ∀ x, f₁ x = LV_map_eff g (f₂ x)) (Ξ : XEnv EV LV) :
EV_bind_XEnv f₁ (LV_map_XEnv g Ξ) = LV_map_XEnv g (EV_bind_XEnv f₂ Ξ).
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat (rewrite LV_map_XEnv_empty || rewrite EV_bind_XEnv_empty).
  reflexivity.
+ repeat rewrite EV_bind_XEnv_concat, LV_map_XEnv_concat,
    EV_bind_XEnv_single, LV_map_XEnv_single.
  erewrite EV_bind_LV_map_ty, EV_bind_LV_map_eff, IHΞ ; crush.
Qed.

End section_EV_bind_LV_map.

Definition
  LV_bind_EV_map_ef EP EV EV' LV LV' L
  (g : EV → EV') (f : LV → lbl LV' L)
  (e : ef EP EV LV L) :
  LV_bind_ef f (EV_map_ef g e) = EV_map_ef g (LV_bind_ef f e)
.
Proof.
destruct e ; crush.
Qed.

Fixpoint
  LV_bind_EV_map_eff EP EV EV' LV LV' L
  (g : EV → EV') (f : LV → lbl LV' L)
  (E : eff EP EV LV L) {struct E} :
  LV_bind_eff f (EV_map_eff g E) = EV_map_eff g (LV_bind_eff f E)
.
Proof.
  destruct E ; simpl ;
  repeat erewrite LV_bind_EV_map_ef ;
  repeat erewrite LV_bind_EV_map_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_EV_map_it EP EV EV' LV LV' L
  (g : EV → EV') (f : LV → lbl LV' L)
  κ (N : it EP EV LV L κ) {struct N} :
  LV_bind_it f (EV_map_it g N) = EV_map_it g (LV_bind_it f N)
.
Proof.
  destruct N ; simpl ;
  repeat erewrite LV_bind_EV_map_ef ;
  repeat erewrite LV_bind_EV_map_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_EV_map_ty EP EV EV' LV LV' L
  (g : EV → EV') (f : LV → lbl LV' L)
  (T : ty EP EV LV L) {struct T} :
  LV_bind_ty f (EV_map_ty g T) = EV_map_ty g (LV_bind_ty f T)
with
  LV_bind_EV_map_ms EP EV EV' LV LV' L
  (g : EV → EV') (f : LV → lbl LV' L)
  (σ : ms EP EV LV L) {struct σ} :
  LV_bind_ms f (EV_map_ms g σ) = EV_map_ms g (LV_bind_ms f σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite LV_bind_EV_map_ty ;
  repeat erewrite LV_bind_EV_map_ms ;
  repeat erewrite LV_bind_EV_map_it ;
  repeat erewrite LV_bind_EV_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite LV_bind_EV_map_ty ;
  repeat erewrite LV_bind_EV_map_ms ;
  repeat erewrite LV_bind_EV_map_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_EV_map_md EV EV' LV LV' V L
  (g : EV → EV') (f : LV → lbl LV' L)
  (m : md EV LV V L) {struct m} :
  LV_bind_md f (EV_map_md g m) = EV_map_md g (LV_bind_md f m)
with
  LV_bind_EV_map_tm EV EV' LV LV' V L
  (g : EV → EV') (f : LV → lbl LV' L)
  (t : tm EV LV V L) {struct t} :
  LV_bind_tm f (EV_map_tm g t) = EV_map_tm g (LV_bind_tm f t)
with
  LV_bind_EV_map_ktx EV EV' LV LV' V L
  (g : EV → EV') (f : LV → lbl LV' L)
  (K : ktx EV LV V L) {struct K} :
  LV_bind_ktx f (EV_map_ktx g K) = EV_map_ktx g (LV_bind_ktx f K)
with
  LV_bind_EV_map_val EV EV' LV LV' V L
  (g : EV → EV') (f : LV → lbl LV' L)
  (v : val EV LV V L) {struct v} :
  LV_bind_val f (EV_map_val g v) = EV_map_val g (LV_bind_val f v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite LV_bind_EV_map_md ;
  repeat erewrite LV_bind_EV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite LV_bind_EV_map_tm ;
  repeat erewrite LV_bind_EV_map_md ;
  repeat erewrite LV_bind_EV_map_val ;
  repeat erewrite LV_bind_EV_map_ty ;
  repeat erewrite LV_bind_EV_map_eff ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite LV_bind_EV_map_ktx ;
  repeat erewrite LV_bind_EV_map_tm ;
  repeat erewrite LV_bind_EV_map_val ;
  repeat erewrite LV_bind_EV_map_ty ;
  repeat erewrite LV_bind_EV_map_eff ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite LV_bind_EV_map_tm ;
  repeat erewrite LV_bind_EV_map_md ;
  repeat erewrite LV_bind_EV_map_ktx ;
  crush.
Qed.

Lemma LV_bind_EV_map_XEnv
EV EV' LV LV'
(g : EV → EV') (f : LV → lbl LV' _)
(Ξ : XEnv EV LV) :
EV_map_XEnv g (LV_bind_XEnv f Ξ) = LV_bind_XEnv f (EV_map_XEnv g Ξ).
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat rewrite EV_map_XEnv_empty, LV_bind_XEnv_empty.
  reflexivity.
+ repeat rewrite
    EV_map_XEnv_concat, LV_bind_XEnv_concat,
    EV_map_XEnv_single, LV_bind_XEnv_single.
  erewrite LV_bind_EV_map_ty, LV_bind_EV_map_eff, IHΞ ;
  crush.
Qed.

Section section_EV_bind_L_map.

Hint Extern 1 => match goal with
| [ |- context[ L_map_eff _ (L_map_eff _ _) ] ] => erewrite L_map_map_eff ; crush
| [ |- context[ L_map_eff _ (LV_map_eff _ _) ] ] => erewrite <- LV_L_map_eff ; crush
| [ |- context[ L_map_eff _ (EV_map_eff _ _) ] ] => erewrite <- EV_L_map_eff ; crush
end.

Definition
  EV_bind_L_map_ef EP EV EV' LV L L'
  (g : L → L') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (e : ef EP EV LV L) :
  EV_bind_ef f₂ (L_map_ef g e) = L_map_eff g (EV_bind_ef f₁ e)
.
Proof.
destruct e ; simpl ; crush.
Qed.

Hint Resolve L_map_eff_app.

Fixpoint
  EV_bind_L_map_eff EP EV EV' LV L L'
  (g : L → L') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (E : eff EP EV LV L) {struct E} :
  EV_bind_eff f₂ (L_map_eff g E) = L_map_eff g (EV_bind_eff f₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite EV_bind_L_map_ef ;
repeat erewrite EV_bind_L_map_eff ;
crush.
Qed.

Fixpoint
  EV_bind_L_map_it EP EV EV' LV L L'
  (g : L → L') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  κ (N : it EP EV LV L κ) {struct N} :
  EV_bind_it f₂ (L_map_it g N) = L_map_it g (EV_bind_it f₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EV_bind_L_map_it ;
repeat erewrite EV_bind_L_map_eff ;
crush.
Qed.

Fixpoint
  EV_bind_L_map_ty EP EV EV' LV L L'
  (g : L → L') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (T : ty EP EV LV L) {struct T} :
  EV_bind_ty f₂ (L_map_ty g T) = L_map_ty g (EV_bind_ty f₁ T)
with
  EV_bind_L_map_ms EP EV EV' LV L L'
  (g : L → L') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (σ : ms EP EV LV L) {struct σ} :
  EV_bind_ms f₂ (L_map_ms g σ) = L_map_ms g (EV_bind_ms f₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_bind_L_map_ty ;
  repeat erewrite EV_bind_L_map_ms ;
  repeat erewrite EV_bind_L_map_it ;
  repeat erewrite EV_bind_L_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EV_bind_L_map_ty ;
  repeat erewrite EV_bind_L_map_ms ;
  repeat erewrite EV_bind_L_map_eff ;
  crush.
Qed.

Hint Rewrite EP_L_map_eff.

Fixpoint
  EV_bind_L_map_is EP EV EV' LV L L'
  (g : L → L') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (Σ : is EP EV LV L) {struct Σ} :
  EV_bind_is f₂ (L_map_is g Σ) = L_map_is g (EV_bind_is f₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EV_bind_L_map_ms ;
repeat erewrite EV_bind_L_map_is ;
crush.
Qed.

Fixpoint
  EV_bind_L_map_md EV EV' LV V L L'
  (g : L → L') (f₁ : EV → eff ∅ EV' LV L) (f₂ : EV → eff ∅ EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (m : md EV LV V L) {struct m} :
  EV_bind_md f₂ (L_map_md g m) = L_map_md g (EV_bind_md f₁ m)
with
  EV_bind_L_map_tm EV EV' LV V L L'
  (g : L → L') (f₁ : EV → eff ∅ EV' LV L) (f₂ : EV → eff ∅ EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (t : tm EV LV V L) {struct t} :
  EV_bind_tm f₂ (L_map_tm g t) = L_map_tm g (EV_bind_tm f₁ t)
with
  EV_bind_L_map_ktx EV EV' LV V L L'
  (g : L → L') (f₁ : EV → eff ∅ EV' LV L) (f₂ : EV → eff ∅ EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (K : ktx EV LV V L) {struct K} :
  EV_bind_ktx f₂ (L_map_ktx g K) = L_map_ktx g (EV_bind_ktx f₁ K)
with
  EV_bind_L_map_val EV EV' LV V L L'
  (g : L → L') (f₁ : EV → eff ∅ EV' LV L) (f₂ : EV → eff ∅ EV' LV L')
  (H : ∀ x, f₂ x = L_map_eff g (f₁ x))
  (v : val EV LV V L) {struct v} :
  EV_bind_val f₂ (L_map_val g v) = L_map_val g (EV_bind_val f₁ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite EV_bind_L_map_md ;
  repeat erewrite EV_bind_L_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_bind_L_map_ty ;
  repeat erewrite EV_bind_L_map_eff ;
  repeat erewrite EV_bind_L_map_tm ;
  repeat erewrite EV_bind_L_map_md ;
  repeat erewrite EV_bind_L_map_val ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite EV_bind_L_map_ktx ;
  repeat erewrite EV_bind_L_map_tm ;
  repeat erewrite EV_bind_L_map_val ;
  repeat erewrite EV_bind_L_map_ty ;
  repeat erewrite EV_bind_L_map_eff ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_bind_L_map_ktx ;
  repeat erewrite EV_bind_L_map_tm ;
  repeat erewrite EV_bind_L_map_md ;
  crush.
Qed.

End section_EV_bind_L_map.

Section section_EV_bind_EP_map.

Hint Extern 1 => match goal with
| [ |- context[ EP_map_eff _ (EP_map_eff _ _) ] ] => erewrite EP_map_map_eff ; crush
| [ |- context[ EP_map_eff _ (LV_map_eff _ _) ] ] => erewrite EP_LV_map_eff ; crush
| [ |- context[ EP_map_eff _ (EV_map_eff _ _) ] ] => erewrite EP_EV_map_eff ; crush
end.

Definition
  EV_bind_EP_map_ef EP EP' EV EV' LV L
  (g : EP → EP') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EP_map_eff g (f₁ x))
  (e : ef EP EV LV L) :
  EV_bind_ef f₂ (EP_map_ef g e) = EP_map_eff g (EV_bind_ef f₁ e)
.
Proof.
destruct e ; simpl ; crush.
Qed.

Hint Resolve EP_map_eff_app.

Fixpoint
  EV_bind_EP_map_eff EP EP' EV EV' LV L
  (g : EP → EP') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EP_map_eff g (f₁ x))
  (E : eff EP EV LV L) {struct E} :
  EV_bind_eff f₂ (EP_map_eff g E) = EP_map_eff g (EV_bind_eff f₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite EV_bind_EP_map_ef ;
repeat erewrite EV_bind_EP_map_eff ;
crush.
Qed.

Fixpoint
  EV_bind_EP_map_it EP EP' EV EV' LV L
  (g : EP → EP') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EP_map_eff g (f₁ x))
  κ (N : it EP EV LV L κ) {struct N} :
  EV_bind_it f₂ (EP_map_it g N) = EP_map_it g (EV_bind_it f₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EV_bind_EP_map_it ;
repeat erewrite EV_bind_EP_map_eff ;
crush.
Qed.

Fixpoint
  EV_bind_EP_map_ty EP EP' EV EV' LV L
  (g : EP → EP') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EP_map_eff g (f₁ x))
  (T : ty EP EV LV L) {struct T} :
  EV_bind_ty f₂ (EP_map_ty g T) = EP_map_ty g (EV_bind_ty f₁ T)
with
  EV_bind_EP_map_ms EP EP' EV EV' LV L
  (g : EP → EP') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EP_map_eff g (f₁ x))
  (σ : ms EP EV LV L) {struct σ} :
  EV_bind_ms f₂ (EP_map_ms g σ) = EP_map_ms g (EV_bind_ms f₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_bind_EP_map_ty ;
  repeat erewrite EV_bind_EP_map_ms ;
  repeat erewrite EV_bind_EP_map_it ;
  repeat erewrite EV_bind_EP_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EV_bind_EP_map_ty ;
  repeat erewrite EV_bind_EP_map_ms ;
  repeat erewrite EV_bind_EP_map_eff ;
  crush.
Qed.

Fixpoint
  EV_bind_EP_map_is EP EP' EV EV' LV L
  (g : EP → EP') (f₁ : EV → eff EP EV' LV L) (f₂ : EV → eff EP' EV' LV L)
  (H : ∀ x, f₂ x = EP_map_eff g (f₁ x))
  (Σ : is EP EV LV L) {struct Σ} :
  EV_bind_is f₂ (EP_map_is g Σ) = EP_map_is g (EV_bind_is f₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EV_bind_EP_map_is ;
repeat erewrite EV_bind_EP_map_ms ;
crush.
Qed.

End section_EV_bind_EP_map.

Section section_LV_bind_L_map.

Definition
  LV_bind_L_map_lbl LV LV' L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, L_map_lbl g (f₁ x) = f₂ x)
  (ℓ : lbl LV L) :
  LV_bind_lbl f₂ (L_map_lbl g ℓ) = L_map_lbl g (LV_bind_lbl f₁ ℓ)
.
Proof.
destruct ℓ ; crush.
Qed.

Definition
  LV_bind_L_map_ef EV LV LV' L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, L_map_lbl g (f₁ x) = f₂ x)
  (e : ef ∅ EV LV L) :
  LV_bind_ef f₂ (L_map_ef g e) = L_map_ef g (LV_bind_ef f₁ e)
.
Proof.
destruct e ; simpl ; [ crush | crush | ].
erewrite LV_bind_L_map_lbl ; crush.
Qed.

Fixpoint
  LV_bind_L_map_eff EV LV LV' L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, L_map_lbl g (f₁ x) = f₂ x)
  (E : eff ∅ EV LV L) {struct E} :
  LV_bind_eff f₂ (L_map_eff g E) = L_map_eff g (LV_bind_eff f₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite LV_bind_L_map_ef ;
repeat erewrite LV_bind_L_map_eff ;
crush.
Qed.

Fixpoint
  LV_bind_L_map_it EV LV LV' L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, L_map_lbl g (f₁ x) = f₂ x)
  κ (N : it ∅ EV LV L κ) {struct N} :
  LV_bind_it f₂ (L_map_it g N) = L_map_it g (LV_bind_it f₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite LV_bind_L_map_it ;
repeat erewrite LV_bind_L_map_eff ;
crush.
Qed.

Hint Extern 1 => match goal with
| [ |- context[ L_map_lbl _ (L_map_lbl _ _) ] ] => erewrite L_map_map_lbl ; crush
| [ |- context[ L_map_lbl _ (LV_map_lbl _ _) ] ] => erewrite <- LV_L_map_lbl ; crush
end.

Fixpoint
  LV_bind_L_map_ty EV LV LV' L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, f₂ x = L_map_lbl g (f₁ x))
  (T : ty ∅ EV LV L) {struct T} :
  LV_bind_ty f₂ (L_map_ty g T) = L_map_ty g (LV_bind_ty f₁ T)
with
  LV_bind_L_map_ms EV LV LV' L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, f₂ x = L_map_lbl g (f₁ x))
  (σ : ms ∅ EV LV L) {struct σ} :
  LV_bind_ms f₂ (L_map_ms g σ) = L_map_ms g (LV_bind_ms f₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite LV_bind_L_map_ty ;
  repeat erewrite LV_bind_L_map_ms ;
  repeat erewrite LV_bind_L_map_it ;
  repeat erewrite LV_bind_L_map_eff ;
  repeat erewrite LV_bind_L_map_lbl ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite LV_bind_L_map_ty ;
  repeat erewrite LV_bind_L_map_ms ;
  repeat erewrite LV_bind_L_map_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_L_map_md EV LV LV' V L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, f₂ x = L_map_lbl g (f₁ x))
  (m : md EV LV V L) {struct m} :
  LV_bind_md f₂ (L_map_md g m) = L_map_md g (LV_bind_md f₁ m)
with
  LV_bind_L_map_tm EV LV LV' V L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, f₂ x = L_map_lbl g (f₁ x))
  (t : tm EV LV V L) {struct t} :
  LV_bind_tm f₂ (L_map_tm g t) = L_map_tm g (LV_bind_tm f₁ t)
with
  LV_bind_L_map_ktx EV LV LV' V L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, f₂ x = L_map_lbl g (f₁ x))
  (K : ktx EV LV V L) {struct K} :
  LV_bind_ktx f₂ (L_map_ktx g K) = L_map_ktx g (LV_bind_ktx f₁ K)
with
  LV_bind_L_map_val EV LV LV' V L L'
  (g : L → L') (f₁ : LV → lbl LV' L) (f₂ : LV → lbl LV' L')
  (H : ∀ x, f₂ x = L_map_lbl g (f₁ x))
  (v : val EV LV V L) {struct v} :
  LV_bind_val f₂ (L_map_val g v) = L_map_val g (LV_bind_val f₁ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite LV_bind_L_map_md ;
  repeat erewrite LV_bind_L_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite LV_bind_L_map_tm ;
  repeat erewrite LV_bind_L_map_md ;
  repeat erewrite LV_bind_L_map_val ;
  repeat erewrite LV_bind_L_map_ty ;
  repeat erewrite LV_bind_L_map_eff ;
  repeat erewrite LV_bind_L_map_lbl ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite LV_bind_L_map_ktx ;
  repeat erewrite LV_bind_L_map_tm ;
  repeat erewrite LV_bind_L_map_val ;
  repeat erewrite LV_bind_L_map_eff ;
  repeat erewrite LV_bind_L_map_lbl ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite LV_bind_L_map_tm ;
  repeat erewrite LV_bind_L_map_md ;
  repeat erewrite LV_bind_L_map_ktx ;
  crush.
Qed.

End section_LV_bind_L_map.

Section section_LV_bind_EP_map.

Hint Extern 1 => match goal with
| [ |- context[ EP_map_eff _ (EP_map_eff _ _) ] ] => erewrite EP_map_map_eff ; crush
| [ |- context[ EP_map_eff _ (LV_map_eff _ _) ] ] => erewrite EP_LV_map_eff ; crush
| [ |- context[ EP_map_eff _ (LV_map_eff _ _) ] ] => erewrite EP_LV_map_eff ; crush
end.

Definition
  LV_bind_EP_map_ef EP EP' EV LV LV' L
  (g : EP → EP') (f : LV → lbl LV' L)
  (e : ef EP EV LV L) :
  LV_bind_ef f (EP_map_ef g e) = EP_map_ef g (LV_bind_ef f e)
.
Proof.
destruct e ; simpl ; crush.
Qed.

Hint Resolve EP_map_eff_app.

Fixpoint
  LV_bind_EP_map_eff EP EP' EV LV LV' L
  (g : EP → EP') (f : LV → lbl LV' L)
  (E : eff EP EV LV L) {struct E} :
  LV_bind_eff f (EP_map_eff g E) = EP_map_eff g (LV_bind_eff f E)
.
Proof.
destruct E ; simpl ;
repeat erewrite LV_bind_EP_map_ef ;
repeat erewrite LV_bind_EP_map_eff ;
crush.
Qed.

Fixpoint
  LV_bind_EP_map_it EP EP' EV LV LV' L
  (g : EP → EP') (f : LV → lbl LV' L)
  κ (N : it EP EV LV L κ) {struct N} :
  LV_bind_it f (EP_map_it g N) = EP_map_it g (LV_bind_it f N)
.
Proof.
destruct N ; simpl ;
repeat erewrite LV_bind_EP_map_it ;
repeat erewrite LV_bind_EP_map_eff ;
crush.
Qed.

Fixpoint
  LV_bind_EP_map_ty EP EP' EV LV LV' L
  (g : EP → EP') (f : LV → lbl LV' L)
  (T : ty EP EV LV L) {struct T} :
  LV_bind_ty f (EP_map_ty g T) = EP_map_ty g (LV_bind_ty f T)
with
  LV_bind_EP_map_ms EP EP' EV LV LV' L
  (g : EP → EP') (f : LV → lbl LV' L)
  (σ : ms EP EV LV L) {struct σ} :
  LV_bind_ms f (EP_map_ms g σ) = EP_map_ms g (LV_bind_ms f σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite LV_bind_EP_map_ty ;
  repeat erewrite LV_bind_EP_map_ms ;
  repeat erewrite LV_bind_EP_map_it ;
  repeat erewrite LV_bind_EP_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite LV_bind_EP_map_ty ;
  repeat erewrite LV_bind_EP_map_ms ;
  repeat erewrite LV_bind_EP_map_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_EP_map_is EP EP' EV LV LV' L
  (g : EP → EP') (f : LV → lbl LV' L)
  (Σ : is EP EV LV L) {struct Σ} :
  LV_bind_is f (EP_map_is g Σ) = EP_map_is g (LV_bind_is f Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite LV_bind_EP_map_is ;
repeat erewrite LV_bind_EP_map_ms ;
crush.
Qed.

End section_LV_bind_EP_map.

Section section_V_bind_EV_map.

Hint Extern 1 => match goal with
| [ |- context[ EV_map_val _ (EV_map_val _ _) ] ] => erewrite EV_map_map_val ; crush
| [ |- context[ EV_map_val _ (LV_map_val _ _) ] ] => erewrite EV_LV_map_val ; crush
| [ |- context[ EV_map_val _ (L_map_val _ _) ] ] => erewrite EV_L_map_val ; crush
| [ |- context[ EV_map_val _ (V_map_val _ _) ] ] => erewrite EV_V_map_val ; crush
end.

Fixpoint
  V_bind_EV_map_md EV EV' LV V V' L
  (g : EV → EV') (f₁ : V → val EV' LV V' L) (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x))
  (m : md EV LV V L) {struct m} :
  V_bind_md f₁ (EV_map_md g m) = EV_map_md g (V_bind_md f₂ m)
with
  V_bind_EV_map_tm EV EV' LV V V' L
  (g : EV → EV') (f₁ : V → val EV' LV V' L) (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x))
  (t : tm EV LV V L) {struct t} :
  V_bind_tm f₁ (EV_map_tm g t) = EV_map_tm g (V_bind_tm f₂ t)
with
  V_bind_EV_map_ktx EV EV' LV V V' L
  (g : EV → EV') (f₁ : V → val EV' LV V' L) (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x))
  (K : ktx EV LV V L) {struct K} :
  V_bind_ktx f₁ (EV_map_ktx g K) = EV_map_ktx g (V_bind_ktx f₂ K)
with
  V_bind_EV_map_val EV EV' LV V V' L
  (g : EV → EV') (f₁ : V → val EV' LV V' L) (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x))
  (v : val EV LV V L) {struct v} :
  V_bind_val f₁ (EV_map_val g v) = EV_map_val g (V_bind_val f₂ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite V_bind_EV_map_md ;
  repeat erewrite V_bind_EV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_EV_map_tm ;
  repeat erewrite V_bind_EV_map_md ;
  repeat erewrite V_bind_EV_map_val ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite V_bind_EV_map_ktx ;
  repeat erewrite V_bind_EV_map_tm ;
  repeat erewrite V_bind_EV_map_val ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_EV_map_tm ;
  repeat erewrite V_bind_EV_map_ktx ;
  repeat erewrite V_bind_EV_map_md ;
  crush.
Qed.

End section_V_bind_EV_map.

Section section_V_bind_LV_map.

Hint Extern 1 => match goal with
| [ |- context[ LV_map_val _ (LV_map_val _ _) ] ] => erewrite LV_map_map_val ; crush
| [ |- context[ LV_map_val _ (EV_map_val _ _) ] ] => erewrite <- EV_LV_map_val ; crush
| [ |- context[ LV_map_val _ (L_map_val _ _) ] ] => erewrite LV_L_map_val ; crush
| [ |- context[ LV_map_val _ (V_map_val _ _) ] ] => erewrite LV_V_map_val ; crush
end.

Fixpoint
  V_bind_LV_map_md EV LV LV' V V' L
  (g : LV → LV') (f₁ : V → val EV LV' V' L) (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = LV_map_val g (f₂ x))
  (m : md EV LV V L) {struct m} :
  V_bind_md f₁ (LV_map_md g m) = LV_map_md g (V_bind_md f₂ m)
with
  V_bind_LV_map_tm EV LV LV' V V' L
  (g : LV → LV') (f₁ : V → val EV LV' V' L) (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = LV_map_val g (f₂ x))
  (t : tm EV LV V L) {struct t} :
  V_bind_tm f₁ (LV_map_tm g t) = LV_map_tm g (V_bind_tm f₂ t)
with
  V_bind_LV_map_ktx EV LV LV' V V' L
  (g : LV → LV') (f₁ : V → val EV LV' V' L) (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = LV_map_val g (f₂ x))
  (K : ktx EV LV V L) {struct K} :
  V_bind_ktx f₁ (LV_map_ktx g K) = LV_map_ktx g (V_bind_ktx f₂ K)
with
  V_bind_LV_map_val EV LV LV' V V' L
  (g : LV → LV') (f₁ : V → val EV LV' V' L) (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = LV_map_val g (f₂ x))
  (v : val EV LV V L) {struct v} :
  V_bind_val f₁ (LV_map_val g v) = LV_map_val g (V_bind_val f₂ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite V_bind_LV_map_md ;
  repeat erewrite V_bind_LV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_LV_map_val ;
  repeat erewrite V_bind_LV_map_md ;
  repeat erewrite V_bind_LV_map_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite V_bind_LV_map_ktx ;
  repeat erewrite V_bind_LV_map_val ;
  repeat erewrite V_bind_LV_map_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_LV_map_tm ;
  repeat erewrite V_bind_LV_map_ktx ;
  repeat erewrite V_bind_LV_map_md ;
  crush.
Qed.

End section_V_bind_LV_map.

Section section_V_bind_L_map.

Hint Extern 1 => match goal with
| [ |- context[ L_map_val _ (V_map_val _ _) ] ] => erewrite <- V_L_map_val ; crush
| [ |- context[ L_map_val _ (L_map_val _ _) ] ] => erewrite L_map_map_val ; crush
| [ |- context[ L_map_val _ (EV_map_val _ _) ] ] => erewrite <- EV_L_map_val ; crush
| [ |- context[ L_map_val _ (LV_map_val _ _) ] ] => erewrite <- LV_L_map_val ; crush
end.

Fixpoint
  V_bind_L_map_md EV LV V V' L L'
  (g : L → L') (f₁ : V → val EV LV V' L') (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x))
  (m : md EV LV V L) {struct m} :
  V_bind_md f₁ (L_map_md g m) = L_map_md g (V_bind_md f₂ m)
with
  V_bind_L_map_tm EV LV V V' L L'
  (g : L → L') (f₁ : V → val EV LV V' L') (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x))
  (t : tm EV LV V L) {struct t} :
  V_bind_tm f₁ (L_map_tm g t) = L_map_tm g (V_bind_tm f₂ t)
with
  V_bind_L_map_ktx EV LV V V' L L'
  (g : L → L') (f₁ : V → val EV LV V' L') (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x))
  (K : ktx EV LV V L) {struct K} :
  V_bind_ktx f₁ (L_map_ktx g K) = L_map_ktx g (V_bind_ktx f₂ K)
with
  V_bind_L_map_val EV LV V V' L L'
  (g : L → L') (f₁ : V → val EV LV V' L') (f₂ : V → val EV LV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x))
  (v : val EV LV V L) {struct v} :
  V_bind_val f₁ (L_map_val g v) = L_map_val g (V_bind_val f₂ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite V_bind_L_map_md ;
  repeat erewrite V_bind_L_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_L_map_val ;
  repeat erewrite V_bind_L_map_md ;
  repeat erewrite V_bind_L_map_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite V_bind_L_map_ktx ;
  repeat erewrite V_bind_L_map_tm ;
  repeat erewrite V_bind_L_map_val ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_L_map_ktx ;
  repeat erewrite V_bind_L_map_tm ;
  repeat erewrite V_bind_L_map_md ;
  crush.
Qed.

End section_V_bind_L_map.

Section section_L_bind_EP_map.

Hint Extern 1 => match goal with
| [ |- context[ EP_map_eff _ (EP_map_eff _ _) ] ] => erewrite EP_map_map_eff ; crush
| [ |- context[ EP_map_eff _ (L_map_eff _ _) ] ] => erewrite EP_L_map_eff ; crush
| [ |- context[ EP_map_eff _ (L_map_eff _ _) ] ] => erewrite EP_L_map_eff ; crush
end.

Definition
  L_bind_EP_map_ef EP EP' EV LV L L'
  (g : EP → EP') (f : L → lid L')
  (e : ef EP EV LV L) :
  L_bind_ef f (EP_map_ef g e) = EP_map_ef g (L_bind_ef f e)
.
Proof.
destruct e ; simpl ; crush.
Qed.

Hint Resolve EP_map_eff_app.

Fixpoint
  L_bind_EP_map_eff EP EP' EV LV L L'
  (g : EP → EP') (f : L → lid L')
  (E : eff EP EV LV L) {struct E} :
  L_bind_eff f (EP_map_eff g E) = EP_map_eff g (L_bind_eff f E)
.
Proof.
destruct E ; simpl ;
repeat erewrite L_bind_EP_map_ef ;
repeat erewrite L_bind_EP_map_eff ;
crush.
Qed.

Fixpoint
  L_bind_EP_map_it EP EP' EV LV L L'
  (g : EP → EP') (f : L → lid L')
  κ (N : it EP EV LV L κ) {struct N} :
  L_bind_it f (EP_map_it g N) = EP_map_it g (L_bind_it f N)
.
Proof.
destruct N ; simpl ;
repeat erewrite L_bind_EP_map_it ;
repeat erewrite L_bind_EP_map_eff ;
crush.
Qed.

Fixpoint
  L_bind_EP_map_ty EP EP' EV LV L L'
  (g : EP → EP') (f : L → lid L')
  (T : ty EP EV LV L) {struct T} :
  L_bind_ty f (EP_map_ty g T) = EP_map_ty g (L_bind_ty f T)
with
  L_bind_EP_map_ms EP EP' EV LV L L'
  (g : EP → EP') (f : L → lid L')
  (σ : ms EP EV LV L) {struct σ} :
  L_bind_ms f (EP_map_ms g σ) = EP_map_ms g (L_bind_ms f σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_bind_EP_map_ty ;
  repeat erewrite L_bind_EP_map_ms ;
  repeat erewrite L_bind_EP_map_it ;
  repeat erewrite L_bind_EP_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite L_bind_EP_map_ty ;
  repeat erewrite L_bind_EP_map_ms ;
  repeat erewrite L_bind_EP_map_eff ;
  crush.
Qed.

Fixpoint
  L_bind_EP_map_is EP EP' EV LV L L'
  (g : EP → EP') (f : L → lid L')
  (Σ : is EP EV LV L) {struct Σ} :
  L_bind_is f (EP_map_is g Σ) = EP_map_is g (L_bind_is f Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite L_bind_EP_map_is ;
repeat erewrite L_bind_EP_map_ms ;
crush.
Qed.

End section_L_bind_EP_map.

Section section_L_bind_EV_map.

Definition
  L_bind_EV_map_ef EP EV EV' LV L L'
  (g : EV → EV') (f : L → lid L')
  (e : ef EP EV LV L) :
  L_bind_ef f (EV_map_ef g e) = EV_map_ef g (L_bind_ef f e)
.
Proof.
destruct e ; simpl ; crush.
Qed.

Hint Rewrite L_bind_EV_map_ef.

Fixpoint
  L_bind_EV_map_eff EP EV EV' LV L L'
  (g : EV → EV') (f : L → lid L')
  (E : eff EP EV LV L) {struct E} :
  L_bind_eff f (EV_map_eff g E) = EV_map_eff g (L_bind_eff f E)
.
Proof.
destruct E ; simpl ; crush.
Qed.

Hint Rewrite L_bind_EV_map_eff.

Fixpoint
  L_bind_EV_map_it EP EV EV' LV L L'
  (g : EV → EV') (f : L → lid L')
  κ (N : it EP EV LV L κ) {struct N} :
  L_bind_it f (EV_map_it g N) = EV_map_it g (L_bind_it f N)
.
Proof.
destruct N ; simpl ; crush.
Qed.

Hint Rewrite L_bind_EV_map_it.

Fixpoint
  L_bind_EV_map_ty EP EV EV' LV L L'
  (g : EV → EV') (f : L → lid L')
  (T : ty EP EV LV L) {struct T} :
  L_bind_ty f (EV_map_ty g T) = EV_map_ty g (L_bind_ty f T)
with
  L_bind_EV_map_ms EP EV EV' LV L L'
  (g : EV → EV') (f : L → lid L')
  (σ : ms EP EV LV L) {struct σ} :
  L_bind_ms f (EV_map_ms g σ) = EV_map_ms g (L_bind_ms f σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_bind_EV_map_ty ;
  repeat erewrite L_bind_EV_map_ms ;
  repeat erewrite L_bind_EV_map_it ;
  repeat erewrite L_bind_EV_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite L_bind_EV_map_ms ;
  repeat erewrite L_bind_EV_map_ty ;
  repeat erewrite L_bind_EV_map_eff ;
  crush.
Qed.

Hint Rewrite L_bind_EV_map_ty.
Hint Rewrite L_bind_EV_map_ms.

Fixpoint
  L_bind_EV_map_is EP EV EV' LV L L'
  (g : EV → EV') (f : L → lid L')
  (Σ : is EP EV LV L) {struct Σ} :
  L_bind_is f (EV_map_is g Σ) = EV_map_is g (L_bind_is f Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite L_bind_EV_map_ms ;
repeat erewrite L_bind_EV_map_is ;
crush.
Qed.

Fixpoint
  L_bind_EV_map_md EV EV' LV V L L'
  (g : EV → EV') (f : L → lid L')
  (m : md EV LV V L) {struct m} :
  L_bind_md f (EV_map_md g m) = EV_map_md g (L_bind_md f m)
with
  L_bind_EV_map_tm EV EV' LV V L L'
  (g : EV → EV') (f : L → lid L')
  (t : tm EV LV V L) {struct t} :
  L_bind_tm f (EV_map_tm g t) = EV_map_tm g (L_bind_tm f t)
with
  L_bind_EV_map_ktx EV EV' LV V L L'
  (g : EV → EV') (f : L → lid L')
  (K : ktx EV LV V L) {struct K} :
  L_bind_ktx f (EV_map_ktx g K) = EV_map_ktx g (L_bind_ktx f K)
with
  L_bind_EV_map_val EV EV' LV V L L'
  (g : EV → EV') (f : L → lid L')
  (v : val EV LV V L) {struct v} :
  L_bind_val f (EV_map_val g v) = EV_map_val g (L_bind_val f v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite L_bind_EV_map_md ;
  repeat erewrite L_bind_EV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_bind_EV_map_val ;
  repeat erewrite L_bind_EV_map_md ;
  repeat erewrite L_bind_EV_map_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite L_bind_EV_map_ktx ;
  repeat erewrite L_bind_EV_map_tm ;
  repeat erewrite L_bind_EV_map_val ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_bind_EV_map_tm ;
  repeat erewrite L_bind_EV_map_ktx ;
  repeat erewrite L_bind_EV_map_md ;
  crush.
Qed.

End section_L_bind_EV_map.

Section section_L_bind_LV_map.

Definition
  L_bind_LV_map_lbl EV LV LV' L L'
  (g : LV → LV') (f : L → lid L')
  (ℓ : lbl LV L) :
  L_bind_lbl f (LV_map_lbl g ℓ) = LV_map_lbl g (L_bind_lbl f ℓ)
.
Proof.
destruct ℓ ; simpl ; crush.
Qed.

Hint Rewrite L_bind_LV_map_lbl.

Definition
  L_bind_LV_map_ef EP EV LV LV' L L'
  (g : LV → LV') (f : L → lid L')
  (e : ef EP EV LV L) :
  L_bind_ef f (LV_map_ef g e) = LV_map_ef g (L_bind_ef f e)
.
Proof.
destruct e ; simpl ; crush.
Qed.

Hint Rewrite L_bind_LV_map_ef.

Fixpoint
  L_bind_LV_map_eff EP EV LV LV' L L'
  (g : LV → LV') (f : L → lid L')
  (E : eff EP EV LV L) {struct E} :
  L_bind_eff f (LV_map_eff g E) = LV_map_eff g (L_bind_eff f E)
.
Proof.
destruct E ; simpl ; crush.
Qed.

Hint Rewrite L_bind_LV_map_eff.

Fixpoint
  L_bind_LV_map_it EP EV LV LV' L L'
  (g : LV → LV') (f : L → lid L')
  κ (N : it EP EV LV L κ) {struct N} :
  L_bind_it f (LV_map_it g N) = LV_map_it g (L_bind_it f N)
.
Proof.
destruct N ; simpl ; crush.
Qed.

Hint Rewrite L_bind_LV_map_it.

Fixpoint
  L_bind_LV_map_ty EP EV LV LV' L L'
  (g : LV → LV') (f : L → lid L')
  (T : ty EP EV LV L) {struct T} :
  L_bind_ty f (LV_map_ty g T) = LV_map_ty g (L_bind_ty f T)
with
  L_bind_LV_map_ms EP EV LV LV' L L'
  (g : LV → LV') (f : L → lid L')
  (σ : ms EP EV LV L) {struct σ} :
  L_bind_ms f (LV_map_ms g σ) = LV_map_ms g (L_bind_ms f σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_bind_LV_map_ty ;
  repeat erewrite L_bind_LV_map_ms ;
  repeat erewrite L_bind_LV_map_it ;
  repeat erewrite L_bind_LV_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite L_bind_LV_map_ty ;
  repeat erewrite L_bind_LV_map_ms ;
  repeat erewrite L_bind_LV_map_eff ;
  crush.
Qed.

Hint Rewrite L_bind_LV_map_ty L_bind_LV_map_ms.

Fixpoint
  L_bind_LV_map_is EP EV LV LV' L L'
  (g : LV → LV') (f : L → lid L')
  (Σ : is EP EV LV L) {struct Σ} :
  L_bind_is f (LV_map_is g Σ) = LV_map_is g (L_bind_is f Σ)
.
Proof.
destruct Σ  ; simpl ;
repeat erewrite L_bind_LV_map_ms ;
repeat erewrite L_bind_LV_map_is ;
crush.
Qed.

Fixpoint
  L_bind_LV_map_md EV LV LV' V L L'
  (g : LV → LV') (f : L → lid L')
  (m : md EV LV V L) {struct m} :
  L_bind_md f (LV_map_md g m) = LV_map_md g (L_bind_md f m)
with
  L_bind_LV_map_tm EV LV LV' V L L'
  (g : LV → LV') (f : L → lid L')
  (t : tm EV LV V L) {struct t} :
  L_bind_tm f (LV_map_tm g t) = LV_map_tm g (L_bind_tm f t)
with
  L_bind_LV_map_ktx EV LV LV' V L L'
  (g : LV → LV') (f : L → lid L')
  (K : ktx EV LV V L) {struct K} :
  L_bind_ktx f (LV_map_ktx g K) = LV_map_ktx g (L_bind_ktx f K)
with
  L_bind_LV_map_val EV LV LV' V L L'
  (g : LV → LV') (f : L → lid L')
  (v : val EV LV V L) {struct v} :
  L_bind_val f (LV_map_val g v) = LV_map_val g (L_bind_val f v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite L_bind_LV_map_md ;
  repeat erewrite L_bind_LV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_bind_LV_map_val ;
  repeat erewrite L_bind_LV_map_md ;
  repeat erewrite L_bind_LV_map_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite L_bind_LV_map_ktx ;
  repeat erewrite L_bind_LV_map_tm ;
  repeat erewrite L_bind_LV_map_val ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_bind_LV_map_ktx ;
  repeat erewrite L_bind_LV_map_tm ;
  repeat erewrite L_bind_LV_map_md ;
  crush.
Qed.

End section_L_bind_LV_map.

Section section_EP_EV_bind.

Hint Extern 1 => match goal with
| [ |- context[ EP_bind_eff _ (EV_map_eff _ _) ] ] => erewrite EP_bind_EV_map_eff ; crush
| [ |- context[ EP_bind_eff _ (EP_map_eff _ _) ] ] => erewrite EP_bind_map_eff ; crush
| [ |- context[ EP_bind_eff _ (L_map_eff _ _) ] ] => erewrite EP_bind_L_map_eff ; crush
end.

Definition
  EP_EV_bind_ef
  EP EP' EV EV' LV L
  (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (g₁ : EV → eff EP EV' LV L) (g₂ : EV → eff EP' EV' LV L)
  (P : ∀ x, EP_bind_eff f₂ (g₁ x) = g₂ x)
  (Q : ∀ x, EV_bind_eff g₂ (f₁ x) = f₂ x)
  (e : ef EP EV LV L) :
  EP_bind_eff f₂ (EV_bind_ef g₁ e) = EV_bind_eff g₂ (EP_bind_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Fixpoint
  EP_EV_bind_eff
  EP EP' EV EV' LV L
  (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (g₁ : EV → eff EP EV' LV L) (g₂ : EV → eff EP' EV' LV L)
  (P : ∀ x, EP_bind_eff f₂ (g₁ x) = g₂ x)
  (Q : ∀ x, EV_bind_eff g₂ (f₁ x) = f₂ x)
  (E : eff EP EV LV L) {struct E} :
  EP_bind_eff f₂ (EV_bind_eff g₁ E) = EV_bind_eff g₂ (EP_bind_eff f₁ E)
.
Proof.
destruct E ; simpl.
+ reflexivity.
+ rewrite <- EP_bind_eff_app, <- EV_bind_eff_app.
  repeat erewrite EP_EV_bind_ef ;
  repeat erewrite EP_EV_bind_eff ;
  crush.
Qed.

Fixpoint
  EP_EV_bind_it
  EP EP' EV EV' LV L
  (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (g₁ : EV → eff EP EV' LV L) (g₂ : EV → eff EP' EV' LV L)
  (P : ∀ x, EP_bind_eff f₂ (g₁ x) = g₂ x)
  (Q : ∀ x, EV_bind_eff g₂ (f₁ x) = f₂ x)
  κ (N : it EP EV LV L κ) {struct N} :
  EP_bind_it f₂ (EV_bind_it g₁ N) = EV_bind_it g₂ (EP_bind_it f₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EP_EV_bind_it ;
repeat erewrite EP_EV_bind_eff ;
crush.
Qed.

Fixpoint
  EP_EV_bind_ty
  EP EP' EV EV' LV L
  (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (g₁ : EV → eff EP EV' LV L) (g₂ : EV → eff EP' EV' LV L)
  (P : ∀ x, EP_bind_eff f₂ (g₁ x) = g₂ x)
  (Q : ∀ x, EV_bind_eff g₂ (f₁ x) = f₂ x)
  (T : ty EP EV LV L) {struct T} :
  EP_bind_ty f₂ (EV_bind_ty g₁ T) = EV_bind_ty g₂ (EP_bind_ty f₁ T)
with
  EP_EV_bind_ms
  EP EP' EV EV' LV L
  (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (g₁ : EV → eff EP EV' LV L) (g₂ : EV → eff EP' EV' LV L)
  (P : ∀ x, EP_bind_eff f₂ (g₁ x) = g₂ x)
  (Q : ∀ x, EV_bind_eff g₂ (f₁ x) = f₂ x)
  (σ : ms EP EV LV L) {struct σ} :
  EP_bind_ms f₂ (EV_bind_ms g₁ σ) = EV_bind_ms g₂ (EP_bind_ms f₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EP_EV_bind_ty ;
  repeat erewrite EP_EV_bind_it ;
  repeat erewrite EP_EV_bind_eff ;
  repeat erewrite EP_EV_bind_ms ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EP_EV_bind_ty ;
  repeat erewrite EP_EV_bind_eff ;
  repeat erewrite EP_EV_bind_ms ;
  try reflexivity ; try assumption.
  - destruct x ; simpl ; [ reflexivity | ].
    unfold compose ; erewrite EP_bind_EV_map_eff ; crush.
  - unfold compose ; intro ; erewrite EV_bind_map_eff ; crush.
  - unfold compose ; intro ; erewrite EP_bind_LV_map_eff ; crush.
  - unfold compose ; intro ; erewrite EV_bind_LV_map_eff ; crush. 
Qed.

Fixpoint
  EP_EV_bind_is
  EP EP' EV EV' LV L
  (f₁ : EP → eff EP' EV LV L) (f₂ : EP → eff EP' EV' LV L)
  (g₁ : EV → eff EP EV' LV L) (g₂ : EV → eff EP' EV' LV L)
  (P : ∀ x, EP_bind_eff f₂ (g₁ x) = g₂ x)
  (Q : ∀ x, EV_bind_eff g₂ (f₁ x) = f₂ x)
  (Σ : is EP EV LV L) {struct Σ} :
  EP_bind_is f₂ (EV_bind_is g₁ Σ) = EV_bind_is g₂ (EP_bind_is f₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EP_EV_bind_is ;
repeat erewrite EP_EV_bind_ms ;
try reflexivity ; try assumption.
- unfold compose ; intro ; erewrite EP_bind_map_eff ; crush.
- destruct x ; simpl ; [ reflexivity | ]. 
  unfold compose ; erewrite EV_bind_EP_map_eff ; crush.
Qed.

End section_EP_EV_bind.

Section section_EP_LV_bind.

Hint Extern 1 => match goal with
| [ |- context[ LV_bind_eff _ (EP_map_eff _ _) ] ] => erewrite LV_bind_EP_map_eff ; crush
| [ |- context[ LV_bind_eff _ (LV_map_eff _ _) ] ] => erewrite LV_bind_map_eff ; crush
| [ |- context[ LV_bind_eff _ (L_map_eff _ _) ] ] => erewrite LV_bind_L_map_eff ; crush
end.

Hint Rewrite <- LV_bind_eff_app.

Definition
  EP_LV_bind_ef
  EP EP' EV LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (e : ef EP EV LV L) :
  EP_bind_ef g₂ (LV_bind_ef f e) = LV_bind_eff f (EP_bind_ef g₁ e)
.
Proof.
destruct e ; crush.
Qed.

Fixpoint
  EP_LV_bind_eff
  EP EP' EV LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (E : eff EP EV LV L) {struct E} :
  EP_bind_eff g₂ (LV_bind_eff f E) = LV_bind_eff f (EP_bind_eff g₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite EP_LV_bind_ef ;
repeat erewrite EP_LV_bind_eff ;
crush.
Qed.

Fixpoint
  EP_LV_bind_it
  EP EP' EV LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  κ (N : it EP EV LV L κ) {struct N} :
  EP_bind_it g₂ (LV_bind_it f N) = LV_bind_it f (EP_bind_it g₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EP_LV_bind_it ;
repeat erewrite EP_LV_bind_eff ;
crush.
Qed.

Fixpoint
  EP_LV_bind_ty
  EP EP' EV LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (T : ty EP EV LV L) {struct T} :
  EP_bind_ty g₂ (LV_bind_ty f T) = LV_bind_ty f (EP_bind_ty g₁ T)
with
  EP_LV_bind_ms
  EP EP' EV LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (σ : ms EP EV LV L) {struct σ} :
  EP_bind_ms g₂ (LV_bind_ms f σ) = LV_bind_ms f (EP_bind_ms g₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EP_LV_bind_ty ;
  repeat erewrite EP_LV_bind_it ;
  repeat erewrite EP_LV_bind_eff ;
  repeat erewrite EP_LV_bind_ms ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EP_LV_bind_ty ;
  repeat erewrite EP_LV_bind_eff ;
  repeat erewrite EP_LV_bind_ms ;
  try reflexivity ; try assumption.
  - intro ; unfold compose ; erewrite LV_bind_EV_map_eff ; crush.
  - intro ; unfold compose ; erewrite LV_bind_map_eff ; crush.
Qed.

Fixpoint
  EP_LV_bind_is
  EP EP' EV LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (Σ : is EP EV LV L) {struct Σ} :
  EP_bind_is g₂ (LV_bind_is f Σ) = LV_bind_is f (EP_bind_is g₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EP_LV_bind_ms ;
repeat erewrite EP_LV_bind_is ;
crush.
Qed.

End section_EP_LV_bind.

Section section_EP_L_bind.

Hint Extern 1 => match goal with
| [ |- context[ L_bind_eff _ (EP_map_eff _ _) ] ] => erewrite L_bind_EP_map_eff ; crush
| [ |- context[ L_bind_eff _ (L_map_eff _ _) ] ] => erewrite L_bind_map_eff ; crush
| [ |- context[ L_bind_eff _ (EP_map_eff _ _) ] ] => erewrite L_bind_EP_map_eff ; crush
end.

Hint Rewrite <- L_bind_eff_app.

Definition
  EP_L_bind_ef
  EP EP' EV LV L L'
  (f : L → lid L')
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (e : ef EP EV LV L) :
  EP_bind_ef g₂ (L_bind_ef f e) = L_bind_eff f (EP_bind_ef g₁ e)
.
Proof.
destruct e ; crush.
Qed.

Fixpoint
  EP_L_bind_eff
  EP EP' EV LV L L'
  (f : L → lid L')
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (E : eff EP EV LV L) {struct E} :
  EP_bind_eff g₂ (L_bind_eff f E) = L_bind_eff f (EP_bind_eff g₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite EP_L_bind_ef ;
repeat erewrite EP_L_bind_eff ;
crush.
Qed.

Fixpoint
  EP_L_bind_it
  EP EP' EV LV L L'
  (f : L → lid L')
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  κ (N : it EP EV LV L κ) {struct N} :
  EP_bind_it g₂ (L_bind_it f N) = L_bind_it f (EP_bind_it g₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EP_L_bind_it ;
repeat erewrite EP_L_bind_eff ;
crush.
Qed.

Fixpoint
  EP_L_bind_ty
  EP EP' EV LV L L'
  (f : L → lid L')
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (T : ty EP EV LV L) {struct T} :
  EP_bind_ty g₂ (L_bind_ty f T) = L_bind_ty f (EP_bind_ty g₁ T)
with
  EP_L_bind_ms
  EP EP' EV LV L L'
  (f : L → lid L')
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (σ : ms EP EV LV L) {struct σ} :
  EP_bind_ms g₂ (L_bind_ms f σ) = L_bind_ms f (EP_bind_ms g₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EP_L_bind_ty ;
  repeat erewrite EP_L_bind_it ;
  repeat erewrite EP_L_bind_eff ;
  repeat erewrite EP_L_bind_ms ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EP_L_bind_ty ;
  repeat erewrite EP_L_bind_eff ;
  repeat erewrite EP_L_bind_ms ;
  try reflexivity ; try assumption.
  - intro ; unfold compose ; erewrite L_bind_EV_map_eff ; crush.
  - intro ; unfold compose ; erewrite L_bind_LV_map_eff ; crush.
Qed.

Fixpoint
  EP_L_bind_is
  EP EP' EV LV L L'
  (f : L → lid L')
  (g₁ : EP → eff EP' EV LV L) (g₂ : EP → eff EP' EV LV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (Σ : is EP EV LV L) {struct Σ} :
  EP_bind_is g₂ (L_bind_is f Σ) = L_bind_is f (EP_bind_is g₁ Σ)
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EP_L_bind_ms ;
repeat erewrite EP_L_bind_is ;
crush.
Qed.

End section_EP_L_bind.

Section section_EV_LV_bind.

Hint Extern 1 => match goal with
| [ |- context[ LV_bind_eff _ (EV_map_eff _ _) ] ] => erewrite LV_bind_EV_map_eff ; crush
| [ |- context[ LV_bind_eff _ (LV_map_eff _ _) ] ] => erewrite LV_bind_map_eff ; crush
| [ |- context[ LV_bind_eff _ (L_map_eff _ _) ] ] => erewrite LV_bind_L_map_eff ; crush
end.

Hint Rewrite <- LV_bind_eff_app.

Definition
  EV_LV_bind_ef
  EV EV' LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (e : ef ∅ EV LV L) :
  EV_bind_ef g₂ (LV_bind_ef f e) = LV_bind_eff f (EV_bind_ef g₁ e)
.
Proof.
destruct e ; crush.
Qed.

Fixpoint
  EV_LV_bind_eff
  EV EV' LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (E : eff ∅ EV LV L) {struct E} :
  EV_bind_eff g₂ (LV_bind_eff f E) = LV_bind_eff f (EV_bind_eff g₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite EV_LV_bind_ef ;
repeat erewrite EV_LV_bind_eff ;
crush.
Qed.

Fixpoint
  EV_LV_bind_it
  EV EV' LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  κ (N : it ∅ EV LV L κ) {struct N} :
  EV_bind_it g₂ (LV_bind_it f N) = LV_bind_it f (EV_bind_it g₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EV_LV_bind_it ;
repeat erewrite EV_LV_bind_eff ;
crush.
Qed.

Fixpoint
  EV_LV_bind_ty
  EV EV' LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (T : ty ∅ EV LV L) {struct T} :
  EV_bind_ty g₂ (LV_bind_ty f T) = LV_bind_ty f (EV_bind_ty g₁ T)
with
  EV_LV_bind_ms
  EV EV' LV LV' L
  (f : LV → lbl LV' L)
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (σ : ms ∅ EV LV L) {struct σ} :
  EV_bind_ms g₂ (LV_bind_ms f σ) = LV_bind_ms f (EV_bind_ms g₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_LV_bind_ty ;
  repeat erewrite EV_LV_bind_it ;
  repeat erewrite EV_LV_bind_eff ;
  repeat erewrite EV_LV_bind_ms ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EV_LV_bind_ty ;
  repeat erewrite EV_LV_bind_eff ;
  repeat erewrite EV_LV_bind_ms ;
  crush.
Qed.

Fixpoint
  EV_LV_bind_md
  EV EV' LV LV' V L
  (f : LV → lbl LV' L)
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (m : md EV LV V L) {struct m} :
  EV_bind_md g₂ (LV_bind_md f m) = LV_bind_md f (EV_bind_md g₁ m)
with
  EV_LV_bind_tm
  EV EV' LV LV' V L
  (f : LV → lbl LV' L)
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (t : tm EV LV V L) {struct t} :
  EV_bind_tm g₂ (LV_bind_tm f t) = LV_bind_tm f (EV_bind_tm g₁ t)
with
  EV_LV_bind_ktx
  EV EV' LV LV' V L
  (f : LV → lbl LV' L)
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (K : ktx EV LV V L) {struct K} :
  EV_bind_ktx g₂ (LV_bind_ktx f K) = LV_bind_ktx f (EV_bind_ktx g₁ K)
with
  EV_LV_bind_val
  EV EV' LV LV' V L
  (f : LV → lbl LV' L)
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV' L)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (v : val EV LV V L) {struct v} :
  EV_bind_val g₂ (LV_bind_val f v) = LV_bind_val f (EV_bind_val g₁ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite EV_LV_bind_md ;
  repeat erewrite EV_LV_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_LV_bind_ty ;
  repeat erewrite EV_LV_bind_eff ;
  repeat erewrite EV_LV_bind_val ;
  repeat erewrite EV_LV_bind_tm ;
  repeat erewrite EV_LV_bind_md ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite EV_LV_bind_ktx ;
  repeat erewrite EV_LV_bind_eff ;
  repeat erewrite EV_LV_bind_tm ;
  repeat erewrite EV_LV_bind_val ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_LV_bind_tm ;
  repeat erewrite EV_LV_bind_md ;
  repeat erewrite EV_LV_bind_ktx ;
  crush.
Qed.

Lemma
  EV_LV_bind_XEnv
  EV EV' LV LV'
  (f : LV → lbl LV' ∅)
  (g₁ : EV → eff ∅ EV' LV ∅) (g₂ : EV → eff ∅ EV' LV' ∅)
  (Q : ∀ x, LV_bind_eff f (g₁ x) = g₂ x)
  (Ξ : XEnv EV LV) :
  EV_bind_XEnv g₂ (LV_bind_XEnv f Ξ) = LV_bind_XEnv f (EV_bind_XEnv g₁ Ξ)
.
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat (rewrite LV_bind_XEnv_empty || rewrite EV_bind_XEnv_empty).
  reflexivity.
+ repeat rewrite
    EV_bind_XEnv_concat, LV_bind_XEnv_concat,
    EV_bind_XEnv_single, LV_bind_XEnv_single.
  erewrite EV_LV_bind_ty, EV_LV_bind_eff, IHΞ ; crush.
Qed.

End section_EV_LV_bind.

Section section_EV_V_bind.

Hint Extern 1 => match goal with
| [ |- context[ EV_bind_val _ (V_map_val _ _) ] ] => erewrite EV_bind_V_map_val ; crush
| [ |- context[ EV_bind_val _ (L_map_val _ _) ] ] => erewrite EV_bind_L_map_val ; crush
| [ |- context[ EV_bind_val _ (EV_map_val _ _) ] ] => erewrite EV_bind_map_val ; crush
| [ |- context[ EV_bind_val _ (LV_map_val _ _) ] ] => erewrite EV_bind_LV_map_val ; crush
end.

Fixpoint
  EV_V_bind_md EV EV' LV V V' L
  (f₁ : V → val EV' LV V' L) (f₂ : V → val EV LV V' L)
  (g : EV → eff ∅ EV' LV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x)
  (m : md EV LV V L) {struct m} :
  V_bind_md f₁ (EV_bind_md g m) = EV_bind_md g (V_bind_md f₂ m)
with
  EV_V_bind_tm EV EV' LV V V' L
  (f₁ : V → val EV' LV V' L) (f₂ : V → val EV LV V' L)
  (g : EV → eff ∅ EV' LV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x)
  (t : tm EV LV V L) {struct t} :
  V_bind_tm f₁ (EV_bind_tm g t) = EV_bind_tm g (V_bind_tm f₂ t)
with
  EV_V_bind_ktx EV EV' LV V V' L
  (f₁ : V → val EV' LV V' L) (f₂ : V → val EV LV V' L)
  (g : EV → eff ∅ EV' LV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x)
  (K : ktx EV LV V L) {struct K} :
  V_bind_ktx f₁ (EV_bind_ktx g K) = EV_bind_ktx g (V_bind_ktx f₂ K)
with
  EV_V_bind_val EV EV' LV V V' L
  (f₁ : V → val EV' LV V' L) (f₂ : V → val EV LV V' L)
  (g : EV → eff ∅ EV' LV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x)
  (v : val EV LV V L) {struct v} :
  V_bind_val f₁ (EV_bind_val g v) = EV_bind_val g (V_bind_val f₂ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite EV_V_bind_md ;
  repeat erewrite EV_V_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_V_bind_val ;
  repeat erewrite EV_V_bind_md ;
  repeat erewrite EV_V_bind_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite EV_V_bind_ktx ;
  repeat erewrite EV_V_bind_val ;
  repeat erewrite EV_V_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_V_bind_md ;
  repeat erewrite EV_V_bind_ktx ;
  repeat erewrite EV_V_bind_tm ;
  crush.
Qed.

End section_EV_V_bind.

Section section_LV_V_bind.

Hint Extern 1 => match goal with
| [ |- context[ LV_bind_val _ (L_map_val _ _) ] ] => erewrite LV_bind_L_map_val ; crush
| [ |- context[ LV_bind_val _ (LV_map_val _ _) ] ] => erewrite LV_bind_map_val ; crush
| [ |- context[ LV_bind_val _ (EV_map_val _ _) ] ] => erewrite LV_bind_EV_map_val ; crush
| [ |- context[ LV_bind_val _ (V_map_val _ _) ] ] => erewrite LV_bind_V_map_val ; crush
end.

Fixpoint
  LV_V_bind_md EV LV LV' V V' L
  (f₁ : V → val EV LV V' L) (f₂ : V → val EV LV' V' L)
  (g : LV → lbl LV' L)
  (H : ∀ x, LV_bind_val g (f₁ x) = f₂ x)
  (m : md EV LV V L) {struct m} :
  V_bind_md f₂ (LV_bind_md g m) = LV_bind_md g (V_bind_md f₁ m)
with
  LV_V_bind_tm EV LV LV' V V' L
  (f₁ : V → val EV LV V' L) (f₂ : V → val EV LV' V' L)
  (g : LV → lbl LV' L)
  (H : ∀ x, LV_bind_val g (f₁ x) = f₂ x)
  (t : tm EV LV V L) {struct t} :
  V_bind_tm f₂ (LV_bind_tm g t) = LV_bind_tm g (V_bind_tm f₁ t)
with
  LV_V_bind_ktx EV LV LV' V V' L
  (f₁ : V → val EV LV V' L) (f₂ : V → val EV LV' V' L)
  (g : LV → lbl LV' L)
  (H : ∀ x, LV_bind_val g (f₁ x) = f₂ x)
  (K : ktx EV LV V L) {struct K} :
  V_bind_ktx f₂ (LV_bind_ktx g K) = LV_bind_ktx g (V_bind_ktx f₁ K)
with
  LV_V_bind_val EV LV LV' V V' L
  (f₁ : V → val EV LV V' L) (f₂ : V → val EV LV' V' L)
  (g : LV → lbl LV' L)
  (H : ∀ x, LV_bind_val g (f₁ x) = f₂ x)
  (v : val EV LV V L) {struct v} :
  V_bind_val f₂ (LV_bind_val g v) = LV_bind_val g (V_bind_val f₁ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite LV_V_bind_md ;
  repeat erewrite LV_V_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite LV_V_bind_val ;
  repeat erewrite LV_V_bind_tm ;
  repeat erewrite LV_V_bind_md ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite LV_V_bind_ktx ;
  repeat erewrite LV_V_bind_val ;
  repeat erewrite LV_V_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite LV_V_bind_ktx ;
  repeat erewrite LV_V_bind_md ;
  repeat erewrite LV_V_bind_tm ;
  crush.
Qed.

End section_LV_V_bind.

Section section_EV_L_bind.

Hint Extern 1 => match goal with
| [ |- context[ L_bind_eff _ (EV_map_eff _ _) ] ] => erewrite L_bind_EV_map_eff ; crush
| [ |- context[ L_bind_eff _ (LV_map_eff _ _) ] ] => erewrite L_bind_LV_map_eff ; crush
| [ |- context[ L_bind_eff _ (L_map_eff _ _) ] ] => erewrite L_bind_map_eff ; crush
end.

Hint Rewrite <- L_bind_eff_app.

Definition
  EV_L_bind_ef
  EV EV' LV L L'
  (f : L → lid L')
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV L')
  (Q : ∀ x, g₂ x = L_bind_eff f (g₁ x))
  (e : ef ∅ EV LV L) :
  EV_bind_ef g₂ (L_bind_ef f e) = L_bind_eff f (EV_bind_ef g₁ e)
.
Proof.
destruct e ; simpl ; crush.
Qed.

Fixpoint
  EV_L_bind_eff
  EV EV' LV L L'
  (f : L → lid L')
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV L')
  (Q : ∀ x, g₂ x = L_bind_eff f (g₁ x))
  (E : eff ∅ EV LV L) {struct E} :
  EV_bind_eff g₂ (L_bind_eff f E) = L_bind_eff f (EV_bind_eff g₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite EV_L_bind_ef ;
repeat erewrite EV_L_bind_eff ;
crush.
Qed.

Fixpoint
  EV_L_bind_it
  EV EV' LV L L'
  (f : L → lid L')
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV L')
  (Q : ∀ x, g₂ x = L_bind_eff f (g₁ x))
  κ (N : it ∅ EV LV L κ) {struct N} :
  EV_bind_it g₂ (L_bind_it f N) = L_bind_it f (EV_bind_it g₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite EV_L_bind_it ;
repeat erewrite EV_L_bind_eff ;
crush.
Qed.

Fixpoint
  EV_L_bind_ty
  EV EV' LV L L'
  (f : L → lid L')
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV L')
  (Q : ∀ x, g₂ x = L_bind_eff f (g₁ x))
  (T : ty ∅ EV LV L) {struct T} :
  EV_bind_ty g₂ (L_bind_ty f T) = L_bind_ty f (EV_bind_ty g₁ T)
with
  EV_L_bind_ms
  EV EV' LV L L'
  (f : L → lid L')
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV L')
  (Q : ∀ x, g₂ x = L_bind_eff f (g₁ x))
  (σ : ms ∅ EV LV L) {struct σ} :
  EV_bind_ms g₂ (L_bind_ms f σ) = L_bind_ms f (EV_bind_ms g₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_L_bind_ty ;
  repeat erewrite EV_L_bind_it ;
  repeat erewrite EV_L_bind_ms ;
  repeat erewrite EV_L_bind_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EV_L_bind_ty ;
  repeat erewrite EV_L_bind_eff ;
  repeat erewrite EV_L_bind_ms ;
  crush.
Qed.

Fixpoint
  EV_L_bind_md
  EV EV' LV V L L'
  (f : L → lid L')
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV L')
  (Q : ∀ x, g₂ x = L_bind_eff f (g₁ x))
  (m : md EV LV V L) {struct m} :
  EV_bind_md g₂ (L_bind_md f m) = L_bind_md f (EV_bind_md g₁ m)
with
  EV_L_bind_tm
  EV EV' LV V L L'
  (f : L → lid L')
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV L')
  (Q : ∀ x, g₂ x = L_bind_eff f (g₁ x))
  (t : tm EV LV V L) {struct t} :
  EV_bind_tm g₂ (L_bind_tm f t) = L_bind_tm f (EV_bind_tm g₁ t)
with
  EV_L_bind_ktx
  EV EV' LV V L L'
  (f : L → lid L')
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (K : ktx EV LV V L) {struct K} :
  EV_bind_ktx g₂ (L_bind_ktx f K) = L_bind_ktx f (EV_bind_ktx g₁ K)
with
  EV_L_bind_val
  EV EV' LV V L L'
  (f : L → lid L')
  (g₁ : EV → eff ∅ EV' LV L) (g₂ : EV → eff ∅ EV' LV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (v : val EV LV V L) {struct v} :
  EV_bind_val g₂ (L_bind_val f v) = L_bind_val f (EV_bind_val g₁ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite EV_L_bind_md ;
  repeat erewrite EV_L_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_L_bind_tm ;
  repeat erewrite EV_L_bind_md ;
  repeat erewrite EV_L_bind_val ;
  repeat erewrite EV_L_bind_eff ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite EV_L_bind_ktx ;
  repeat erewrite EV_L_bind_tm ;
  repeat erewrite EV_L_bind_eff ;
  repeat erewrite EV_L_bind_val ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_L_bind_md ;
  repeat erewrite EV_L_bind_ktx ;
  crush.
Qed.

End section_EV_L_bind.

Section section_LV_L_bind.

Hint Extern 1 => match goal with
| [ |- context[ L_bind_lbl _ (LV_map_lbl _ _) ] ] => erewrite L_bind_LV_map_lbl ; crush
| [ |- context[ L_bind_lbl _ (L_map_lbl _ _) ] ] => erewrite L_bind_map_lbl ; crush
end.

Hint Rewrite <- L_bind_eff_app.

Definition
  LV_L_bind_lbl
  LV LV' L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  (ℓ : lbl LV L) :
  LV_bind_lbl g₂ (L_bind_lbl f ℓ) = L_bind_lbl f (LV_bind_lbl g₁ ℓ)
.
Proof.
destruct ℓ ; simpl ; [ | crush ].
rewrite <- Q ; crush.
Qed.

Definition
  LV_L_bind_ef
  EV LV LV' L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  (e : ef ∅ EV LV L) :
  LV_bind_ef g₂ (L_bind_ef f e) = L_bind_ef f (LV_bind_ef g₁ e)
.
Proof.
destruct e ; simpl ;
repeat erewrite LV_L_bind_lbl ;
crush.
Qed.

Fixpoint
  LV_L_bind_eff
  EV LV LV' L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  (E : eff ∅ EV LV L) {struct E} :
  LV_bind_eff g₂ (L_bind_eff f E) = L_bind_eff f (LV_bind_eff g₁ E)
.
Proof.
destruct E ; simpl ;
repeat erewrite LV_L_bind_ef ;
repeat erewrite LV_L_bind_eff ;
crush.
Qed.

Fixpoint
  LV_L_bind_it
  EV LV LV' L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  κ (N : it ∅ EV LV L κ) {struct N} :
  LV_bind_it g₂ (L_bind_it f N) = L_bind_it f (LV_bind_it g₁ N)
.
Proof.
destruct N ; simpl ;
repeat erewrite LV_L_bind_it ;
repeat erewrite LV_L_bind_eff ;
crush.
Qed.

Fixpoint
  LV_L_bind_ty
  EV LV LV' L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  (T : ty ∅ EV LV L) {struct T} :
  LV_bind_ty g₂ (L_bind_ty f T) = L_bind_ty f (LV_bind_ty g₁ T)
with
  LV_L_bind_ms
  EV LV LV' L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  (σ : ms ∅ EV LV L) {struct σ} :
  LV_bind_ms g₂ (L_bind_ms f σ) = L_bind_ms f (LV_bind_ms g₁ σ)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite LV_L_bind_ty ;
  repeat erewrite LV_L_bind_ms ;
  repeat erewrite LV_L_bind_it ;
  repeat erewrite LV_L_bind_eff ;
  repeat erewrite LV_L_bind_lbl ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite LV_L_bind_ms ;
  repeat erewrite LV_L_bind_ty ;
  repeat erewrite LV_L_bind_eff ;
  repeat erewrite LV_L_bind_lbl ;
  crush.
Qed.

Fixpoint
  LV_L_bind_md
  EV LV LV' V L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  (m : md EV LV V L) {struct m} :
  LV_bind_md g₂ (L_bind_md f m) = L_bind_md f (LV_bind_md g₁ m)
with
  LV_L_bind_tm
  EV LV LV' V L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  (t : tm EV LV V L) {struct t} :
  LV_bind_tm g₂ (L_bind_tm f t) = L_bind_tm f (LV_bind_tm g₁ t)
with
  LV_L_bind_ktx
  EV LV LV' V L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  (K : ktx EV LV V L) {struct K} :
  LV_bind_ktx g₂ (L_bind_ktx f K) = L_bind_ktx f (LV_bind_ktx g₁ K)
with
  LV_L_bind_val
  EV LV LV' V L L'
  (f : L → lid L')
  (g₁ : LV → lbl LV' L) (g₂ : LV → lbl LV' L')
  (Q : ∀ x, g₂ x = L_bind_lbl f (g₁ x))
  (v : val EV LV V L) {struct v} :
  LV_bind_val g₂ (L_bind_val f v) = L_bind_val f (LV_bind_val g₁ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite LV_L_bind_md ;
  repeat erewrite LV_L_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite LV_L_bind_lbl ;
  repeat erewrite LV_L_bind_eff ;
  repeat erewrite LV_L_bind_val ;
  repeat erewrite LV_L_bind_md ;
  repeat erewrite LV_L_bind_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite LV_L_bind_ktx ;
  repeat erewrite LV_L_bind_val ;
  repeat erewrite LV_L_bind_tm ;
  repeat erewrite LV_L_bind_lbl ;
  repeat erewrite LV_L_bind_eff ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite LV_L_bind_ktx ;
  repeat erewrite LV_L_bind_md ;
  repeat erewrite LV_L_bind_tm ;
  crush.
Qed.

End section_LV_L_bind.

Section section_V_L_bind.

Hint Extern 1 => match goal with
| [ |- context[ L_bind_val _ (LV_map_val _ _) ] ] => erewrite L_bind_LV_map_val ; crush
| [ |- context[ L_bind_val _ (EV_map_val _ _) ] ] => erewrite L_bind_EV_map_val ; crush
| [ |- context[ L_bind_val _ (V_map_val _ _) ] ] => erewrite L_bind_V_map_val ; crush
| [ |- context[ L_bind_val _ (L_map_val _ _) ] ] => erewrite L_bind_map_val ; crush
end.

Fixpoint
  V_L_bind_md
  EV LV V V' L L'
  (f : L → lid L')
  (g₁ : V → val EV LV V' L) (g₂ : V → val EV LV V' L')
  (Q : ∀ x, g₂ x = L_bind_val f (g₁ x))
  (m : md EV LV V L) {struct m} :
  V_bind_md g₂ (L_bind_md f m) = L_bind_md f (V_bind_md g₁ m)
with
  V_L_bind_tm
  EV LV V V' L L'
  (f : L → lid L')
  (g₁ : V → val EV LV V' L) (g₂ : V → val EV LV V' L')
  (Q : ∀ x, g₂ x = L_bind_val f (g₁ x))
  (t : tm EV LV V L) {struct t} :
  V_bind_tm g₂ (L_bind_tm f t) = L_bind_tm f (V_bind_tm g₁ t)
with
  V_L_bind_ktx
  EV LV V V' L L'
  (f : L → lid L')
  (g₁ : V → val EV LV V' L) (g₂ : V → val EV LV V' L')
  (Q : ∀ x, g₂ x = L_bind_val f (g₁ x))
  (K : ktx EV LV V L) {struct K} :
  V_bind_ktx g₂ (L_bind_ktx f K) = L_bind_ktx f (V_bind_ktx g₁ K)
with
  V_L_bind_val
  EV LV V V' L L'
  (f : L → lid L')
  (g₁ : V → val EV LV V' L) (g₂ : V → val EV LV V' L')
  (Q : ∀ x, g₂ x = L_bind_val f (g₁ x))
  (v : val EV LV V L) {struct v} :
  V_bind_val g₂ (L_bind_val f v) = L_bind_val f (V_bind_val g₁ v)
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite V_L_bind_md ;
  repeat erewrite V_L_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_L_bind_eff ;
  repeat erewrite V_L_bind_md ;
  repeat erewrite V_L_bind_val ;
  repeat erewrite V_L_bind_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite V_L_bind_ktx ;
  repeat erewrite V_L_bind_val ;
  repeat erewrite V_L_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_L_bind_ktx ;
  repeat erewrite V_L_bind_md ;
  repeat erewrite V_L_bind_tm ;
  crush.
Qed.

End section_V_L_bind.

Section section_EV_bind_bind.

Hint Extern 1 => match goal with
| [ |- context[ EV_bind_eff _ (L_map_eff _ _) ] ] => erewrite EV_bind_L_map_eff ; crush
| [ |- context[ EV_bind_eff _ (EV_map_eff _ _) ] ] => erewrite EV_bind_map_eff ; crush
| [ |- context[ EV_bind_eff _ (LV_map_eff _ _) ] ] => erewrite
EV_bind_LV_map_eff ; crush
end.

Fixpoint
  EV_bind_bind_ef (EV₁ EV₂ EV₃ LV L : Set)
  (f₁ : EV₁ → eff ∅ EV₂ LV L) (f₂ : EV₂ → eff ∅ EV₃ LV L)
  (g : EV₁ → eff ∅ EV₃ LV L)
  (Hfg : ∀ α, g α = EV_bind_eff f₂ (f₁ α))
  (e : ef ∅ EV₁ LV L) :
  EV_bind_eff f₂ (EV_bind_ef f₁ e) = EV_bind_ef g e
.
Proof.
+ destruct e ; simpl ;
  repeat erewrite EV_bind_bind_lbl ;
  crush.
Qed.

Fixpoint
  EV_bind_bind_eff (EV₁ EV₂ EV₃ LV L : Set)
  (f₁ : EV₁ → eff  ∅ EV₂ LV L) (f₂ : EV₂ → eff  ∅ EV₃ LV L)
  (g : EV₁ → eff  ∅ EV₃ LV L)
  (Hfg : ∀ α, g α = EV_bind_eff f₂ (f₁ α))
  (E : eff ∅ EV₁ LV L) {struct E} :
  EV_bind_eff f₂ (EV_bind_eff f₁ E) = EV_bind_eff g E
.
Proof.
+ destruct E ; simpl ; [ crush | ].
  rewrite <- EV_bind_eff_app.
  erewrite EV_bind_bind_ef, EV_bind_bind_eff ; crush.
Qed.

Fixpoint
  EV_bind_bind_it (EV₁ EV₂ EV₃ LV L : Set)
  (f₁ : EV₁ → eff  ∅ EV₂ LV L) (f₂ : EV₂ → eff  ∅ EV₃ LV L)
  (g : EV₁ → eff  ∅ EV₃ LV L)
  (Hfg : ∀ α, g α = EV_bind_eff f₂ (f₁ α))
  κ (N : it ∅ EV₁ LV L κ) {struct N} :
  EV_bind_it f₂ (EV_bind_it f₁ N) = EV_bind_it g N
.
Proof.
+ destruct N ; simpl ;
  repeat erewrite EV_bind_bind_it ;
  repeat erewrite EV_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  EV_bind_bind_ty (EV₁ EV₂ EV₃ LV L : Set)
  (f₁ : EV₁ → eff  ∅ EV₂ LV L) (f₂ : EV₂ → eff  ∅ EV₃ LV L)
  (g : EV₁ → eff  ∅ EV₃ LV L)
  (Hfg : ∀ α, g α = EV_bind_eff f₂ (f₁ α))
  (T : ty ∅ EV₁ LV L) {struct T} :
  EV_bind_ty f₂ (EV_bind_ty f₁ T) = EV_bind_ty g T
with
  EV_bind_bind_ms (EV₁ EV₂ EV₃ LV L : Set)
  (f₁ : EV₁ → eff  ∅ EV₂ LV L) (f₂ : EV₂ → eff  ∅ EV₃ LV L)
  (g : EV₁ → eff  ∅ EV₃ LV L)
  (Hfg : ∀ α, g α = EV_bind_eff f₂ (f₁ α))
  (σ : ms ∅ EV₁ LV L) {struct σ} :
  EV_bind_ms f₂ (EV_bind_ms f₁ σ) = EV_bind_ms g σ
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_bind_bind_ty ;
  repeat erewrite EV_bind_bind_ms ;
  repeat erewrite EV_bind_bind_it ;
  repeat erewrite EV_bind_bind_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EV_bind_bind_ms ;
  repeat erewrite EV_bind_bind_ty ;
  repeat erewrite EV_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  EV_bind_bind_md (EV₁ EV₂ EV₃ LV V L : Set)
  (f₁ : EV₁ → eff  ∅ EV₂ LV L) (f₂ : EV₂ → eff  ∅ EV₃ LV L)
  (g : EV₁ → eff  ∅ EV₃ LV L)
  (Hfg : ∀ α, g α = EV_bind_eff f₂ (f₁ α))
  (m : md EV₁ LV V L) {struct m} :
  EV_bind_md f₂ (EV_bind_md f₁ m) = EV_bind_md g m
with
  EV_bind_bind_tm (EV₁ EV₂ EV₃ LV V L : Set)
  (f₁ : EV₁ → eff  ∅ EV₂ LV L) (f₂ : EV₂ → eff  ∅ EV₃ LV L)
  (g : EV₁ → eff  ∅ EV₃ LV L)
  (Hfg : ∀ α, g α = EV_bind_eff f₂ (f₁ α))
  (t : tm EV₁ LV V L) {struct t} :
  EV_bind_tm f₂ (EV_bind_tm f₁ t) = EV_bind_tm g t
with
  EV_bind_bind_ktx (EV₁ EV₂ EV₃ LV V L : Set)
  (f₁ : EV₁ → eff  ∅ EV₂ LV L) (f₂ : EV₂ → eff  ∅ EV₃ LV L)
  (g : EV₁ → eff  ∅ EV₃ LV L)
  (Hfg : ∀ α, g α = EV_bind_eff f₂ (f₁ α))
  (K : ktx EV₁ LV V L) {struct K} :
  EV_bind_ktx f₂ (EV_bind_ktx f₁ K) = EV_bind_ktx g K
with
  EV_bind_bind_val (EV₁ EV₂ EV₃ LV V L : Set)
  (f₁ : EV₁ → eff  ∅ EV₂ LV L) (f₂ : EV₂ → eff  ∅ EV₃ LV L)
  (g : EV₁ → eff  ∅ EV₃ LV L)
  (Hfg : ∀ α, g α = EV_bind_eff f₂ (f₁ α))
  (v : val EV₁ LV V L) {struct v} :
  EV_bind_val f₂ (EV_bind_val f₁ v) = EV_bind_val g v
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite EV_bind_bind_tm ;
  repeat erewrite EV_bind_bind_md ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_bind_bind_eff ;
  repeat erewrite EV_bind_bind_val ;
  repeat erewrite EV_bind_bind_tm ;
  repeat erewrite EV_bind_bind_md ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite EV_bind_bind_ktx ;
  repeat erewrite EV_bind_bind_val ;
  repeat erewrite EV_bind_bind_eff ;
  repeat erewrite EV_bind_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_bind_bind_ktx ;
  repeat erewrite EV_bind_bind_tm ;
  repeat erewrite EV_bind_bind_md ;
  crush.
Qed.

End section_EV_bind_bind.

Section section_LV_bind_bind.

Hint Extern 1 => match goal with
| [ |- context[ LV_bind_lbl _ (L_map_lbl _ _) ] ] => erewrite LV_bind_L_map_lbl ; crush
| [ |- context[ LV_bind_lbl _ (LV_map_lbl _ _) ] ] => erewrite LV_bind_map_lbl ; crush
end.

Definition
  LV_bind_bind_lbl
  (LV₁ LV₂ LV₃ L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  (ℓ : lbl LV₁ L) :
  LV_bind_lbl f₂ (LV_bind_lbl f₁ ℓ) = LV_bind_lbl g ℓ
.
Proof.
  destruct ℓ ; crush.
Qed.

Definition
  LV_bind_bind_ef
  (EV LV₁ LV₂ LV₃ L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  (e : ef ∅ EV LV₁ L) :
  LV_bind_ef f₂ (LV_bind_ef f₁ e) = LV_bind_ef g e
.
Proof.
  destruct e ; simpl ;
  repeat erewrite LV_bind_bind_lbl ;
  crush.
Qed.

Fixpoint
  LV_bind_bind_eff
  (EV LV₁ LV₂ LV₃ L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  (E : eff ∅ EV LV₁ L) {struct E} :
  LV_bind_eff f₂ (LV_bind_eff f₁ E) = LV_bind_eff g E
.
Proof.
  destruct E ; simpl ;
  repeat erewrite LV_bind_bind_ef ;
  repeat erewrite LV_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_bind_it
  (EV LV₁ LV₂ LV₃ L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  κ (N : it ∅ EV LV₁ L κ) {struct N} :
  LV_bind_it f₂ (LV_bind_it f₁ N) = LV_bind_it g N
.
Proof.
  destruct N ; simpl ;
  repeat erewrite LV_bind_bind_it ;
  repeat erewrite LV_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_bind_ty
  (EV LV₁ LV₂ LV₃ L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  (T : ty ∅ EV LV₁ L) {struct T} :
  LV_bind_ty f₂ (LV_bind_ty f₁ T) = LV_bind_ty g T
with
  LV_bind_bind_ms
  (EV LV₁ LV₂ LV₃ L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  (σ : ms ∅ EV LV₁ L) {struct σ} :
  LV_bind_ms f₂ (LV_bind_ms f₁ σ) = LV_bind_ms g σ
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite LV_bind_bind_ty ;
  repeat erewrite LV_bind_bind_ms ;
  repeat erewrite LV_bind_bind_it ;
  repeat erewrite LV_bind_bind_lbl ;
  repeat erewrite LV_bind_bind_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite LV_bind_bind_ty ;
  repeat erewrite LV_bind_bind_ms ;
  repeat erewrite LV_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  LV_bind_bind_md
  (EV LV₁ LV₂ LV₃ V L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  (m : md EV LV₁ V L) {struct m} :
  LV_bind_md f₂ (LV_bind_md f₁ m) = LV_bind_md g m
with
  LV_bind_bind_tm
  (EV LV₁ LV₂ LV₃ V L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  (t : tm EV LV₁ V L) {struct t} :
  LV_bind_tm f₂ (LV_bind_tm f₁ t) = LV_bind_tm g t
with
  LV_bind_bind_ktx
  (EV LV₁ LV₂ LV₃ V L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  (K : ktx EV LV₁ V L) {struct K} :
  LV_bind_ktx f₂ (LV_bind_ktx f₁ K) = LV_bind_ktx g K
with
  LV_bind_bind_val
  (EV LV₁ LV₂ LV₃ V L : Set)
  (f₁ : LV₁ → lbl LV₂ L) (f₂ : LV₂ → lbl LV₃ L)
  (g : LV₁ → lbl LV₃ L)
  (Hfg : ∀ p, LV_bind_lbl f₂ (f₁ p) = g p)
  (v : val EV LV₁ V L) {struct v} :
  LV_bind_val f₂ (LV_bind_val f₁ v) = LV_bind_val g v
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite LV_bind_bind_md ;
  repeat erewrite LV_bind_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite LV_bind_bind_eff ;
  repeat erewrite LV_bind_bind_tm ;
  repeat erewrite LV_bind_bind_lbl ;
  repeat erewrite LV_bind_bind_val ;
  repeat erewrite LV_bind_bind_md ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite LV_bind_bind_ktx ;
  repeat erewrite LV_bind_bind_eff ;
  repeat erewrite LV_bind_bind_val ;
  repeat erewrite LV_bind_bind_tm ;
  repeat erewrite LV_bind_bind_lbl ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite LV_bind_bind_ktx ;
  repeat erewrite LV_bind_bind_tm ;
  repeat erewrite LV_bind_bind_md ;
  crush.
Qed.

End section_LV_bind_bind.

Section section_V_bind_bind.

Hint Extern 1 => match goal with
| [ |- context[ V_bind_val _ (L_map_val _ _) ] ] => erewrite V_bind_L_map_val ; crush
| [ |- context[ V_bind_val _ (LV_map_val _ _) ] ] => erewrite V_bind_LV_map_val ; crush
| [ |- context[ V_bind_val _ (EV_map_val _ _) ] ] => erewrite V_bind_EV_map_val ; crush
| [ |- context[ V_bind_val _ (V_map_val _ _) ] ] => erewrite V_bind_map_val ; crush
end.

Fixpoint
  V_bind_bind_md (EV LV V₁ V₂ V₃ L : Set)
  (f₁ : V₁ → val EV LV V₂ L) (f₂ : V₂ → val EV LV V₃ L)
  (g : V₁ → val EV LV V₃ L)
  (Hf : ∀ x, g x = V_bind_val f₂ (f₁ x))
  (m : md EV LV V₁ L) {struct m} :
  V_bind_md f₂ (V_bind_md f₁ m) = V_bind_md g m
with
  V_bind_bind_tm (EV LV V₁ V₂ V₃ L : Set)
  (f₁ : V₁ → val EV LV V₂ L) (f₂ : V₂ → val EV LV V₃ L)
  (g : V₁ → val EV LV V₃ L)
  (Hf : ∀ x, g x = V_bind_val f₂ (f₁ x))
  (t : tm EV LV V₁ L) {struct t} :
  V_bind_tm f₂ (V_bind_tm f₁ t) = V_bind_tm g t
with
  V_bind_bind_ktx (EV LV V₁ V₂ V₃ L : Set)
  (f₁ : V₁ → val EV LV V₂ L) (f₂ : V₂ → val EV LV V₃ L)
  (g : V₁ → val EV LV V₃ L)
  (Hf : ∀ x, g x = V_bind_val f₂ (f₁ x))
  (K : ktx EV LV V₁ L) {struct K} :
  V_bind_ktx f₂ (V_bind_ktx f₁ K) = V_bind_ktx g K
with
  V_bind_bind_val (EV LV V₁ V₂ V₃ L : Set)
  (f₁ : V₁ → val EV LV V₂ L) (f₂ : V₂ → val EV LV V₃ L)
  (g : V₁ → val EV LV V₃ L)
  (Hf : ∀ x, g x = V_bind_val f₂ (f₁ x))
  (v : val EV LV V₁ L) {struct v} :
  V_bind_val f₂ (V_bind_val f₁ v) = V_bind_val g v
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite V_bind_bind_md ;
  repeat erewrite V_bind_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_bind_eff ;
  repeat erewrite V_bind_bind_val ;
  repeat erewrite V_bind_bind_md ;
  repeat erewrite V_bind_bind_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite V_bind_bind_ktx ;
  repeat erewrite V_bind_bind_val ;
  repeat erewrite V_bind_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_bind_ktx ;
  repeat erewrite V_bind_bind_md ;
  repeat erewrite V_bind_bind_tm ;
  crush.
Qed.

End section_V_bind_bind.

Section section_L_bind_bind.

Hint Extern 1 => match goal with
| [ |- context[ L_bind_lid _ (L_map_lid _ _) ] ] => erewrite L_bind_map_lid ; crush
end.

Definition
  L_bind_bind_lid
  (L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (i : lid L₁) :
  L_bind_lid f₂ (L_bind_lid f₁ i) = L_bind_lid g i
.
Proof.
  destruct i ; simpl ; crush.
Qed.

Definition
  L_bind_bind_lbl
  (LV L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (ℓ : lbl LV L₁) :
  L_bind_lbl f₂ (L_bind_lbl f₁ ℓ) = L_bind_lbl g ℓ
.
Proof.
  destruct ℓ ; simpl ; [ crush | ].
  erewrite L_bind_bind_lid ; crush.
Qed.

Definition
  L_bind_bind_ef
  (EV LV L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (e : ef ∅ EV LV L₁) :
  L_bind_ef f₂ (L_bind_ef f₁ e) = L_bind_ef g e
.
Proof.
  destruct e ; simpl ;
  repeat erewrite L_bind_bind_lbl ;
  crush.
Qed.

Fixpoint
  L_bind_bind_eff
  (EV LV L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (E : eff ∅ EV LV L₁) {struct E} :
  L_bind_eff f₂ (L_bind_eff f₁ E) = L_bind_eff g E
.
Proof.
  destruct E ; simpl ;
  repeat erewrite L_bind_bind_ef ;
  repeat erewrite L_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  L_bind_bind_it
  (EV LV L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  κ (N : it ∅ EV LV L₁ κ) {struct N} :
  L_bind_it f₂ (L_bind_it f₁ N) = L_bind_it g N
.
Proof.
  destruct N ; simpl ;
  repeat erewrite L_bind_bind_it ;
  repeat erewrite L_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  L_bind_bind_ty
  (EV LV L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (T : ty ∅ EV LV L₁) {struct T} :
  L_bind_ty f₂ (L_bind_ty f₁ T) = L_bind_ty g T
with
  L_bind_bind_ms
  (EV LV L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (σ : ms ∅ EV LV L₁) {struct σ} :
  L_bind_ms f₂ (L_bind_ms f₁ σ) = L_bind_ms g σ.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_bind_bind_ty ;
  repeat erewrite L_bind_bind_ms ;
  repeat erewrite L_bind_bind_it ;
  repeat erewrite L_bind_bind_eff ;
  repeat erewrite L_bind_bind_lbl ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite L_bind_bind_ty ;
  repeat erewrite L_bind_bind_ms ;
  repeat erewrite L_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  L_bind_bind_md
  (EV LV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (m : md EV LV V L₁) {struct m} :
  L_bind_md f₂ (L_bind_md f₁ m) = L_bind_md g m
with
  L_bind_bind_tm
  (EV LV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (t : tm EV LV V L₁) {struct t} :
  L_bind_tm f₂ (L_bind_tm f₁ t) = L_bind_tm g t
with
  L_bind_bind_ktx
  (EV LV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (K : ktx EV LV V L₁) {struct K} :
  L_bind_ktx f₂ (L_bind_ktx f₁ K) = L_bind_ktx g K
with
  L_bind_bind_val
  (EV LV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (v : val EV LV V L₁) {struct v} :
  L_bind_val f₂ (L_bind_val f₁ v) = L_bind_val g v
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite L_bind_bind_tm ;
  repeat erewrite L_bind_bind_md ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_bind_bind_eff ;
  repeat erewrite L_bind_bind_lbl ;
  repeat erewrite L_bind_bind_val ;
  repeat erewrite L_bind_bind_tm ;
  repeat erewrite L_bind_bind_md ;
  repeat erewrite L_bind_bind_lid ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite L_bind_bind_ktx ;
  repeat erewrite L_bind_bind_tm ;
  repeat erewrite L_bind_bind_val ;
  repeat erewrite L_bind_bind_eff ;
  repeat erewrite L_bind_bind_lbl ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_bind_bind_tm ;
  repeat erewrite L_bind_bind_md ;
  repeat erewrite L_bind_bind_ktx ;
  repeat erewrite L_bind_bind_lid ;
  crush.
Qed.

End section_L_bind_bind.
