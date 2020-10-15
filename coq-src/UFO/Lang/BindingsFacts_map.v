Require Import UFO.Lang.Syntax.
Require Import UFO.Lang.Bindings_map.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Lemma EP_map_eff_app EP EP' EV LV L
  (f : EP → EP') (E₁ E₂ : eff EP EV LV L) :
  EP_map_eff f E₁ ++ EP_map_eff f E₂ = EP_map_eff f (E₁ ++ E₂).
Proof.
  induction E₁ ; crush.
Qed.

Lemma EV_map_eff_app EP EV EV' LV L
  (f : EV → EV') (E₁ E₂ : eff EP EV LV L) :
  EV_map_eff f E₁ ++ EV_map_eff f E₂ = EV_map_eff f (E₁ ++ E₂).
Proof.
  induction E₁ ; crush.
Qed.

Lemma LV_map_eff_app EP EV LV LV' L
  (f : LV → LV') (E₁ E₂ : eff EP EV LV L) :
  LV_map_eff f E₁ ++ LV_map_eff f E₂ = LV_map_eff f (E₁ ++ E₂).
Proof.
  induction E₁ ; crush.
Qed.

Lemma L_map_eff_app EP EV LV L L'
  (f : L → L') (E₁ E₂ : eff EP EV LV L) :
  L_map_eff f E₁ ++ L_map_eff f E₂ = L_map_eff f (E₁ ++ E₂).
Proof.
  induction E₁ ; crush.
Qed.

Lemma EV_map_XEnv_empty
EV EV' LV (f : EV → EV') :
EV_map_XEnv f empty = (empty : XEnv EV' LV).
Proof.
apply map_empty.
Qed.

Lemma LV_map_XEnv_empty
EV LV LV' (f : LV → LV') :
LV_map_XEnv f empty = (empty : XEnv EV LV').
Proof.
apply map_empty.
Qed.

Lemma EV_map_XEnv_single
EV EV' LV (f : EV → EV') X (T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅) :
EV_map_XEnv f (X ~ (T, E)) = X ~ (EV_map_ty f T, EV_map_eff f E).
Proof.
apply map_single.
Qed.

Lemma LV_map_XEnv_single
EV LV LV' (f : LV → LV') X (T : ty ∅ EV LV ∅) (E : eff ∅ EV LV ∅) :
LV_map_XEnv f (X ~ (T, E)) = X ~ (LV_map_ty f T, LV_map_eff f E).
Proof.
apply map_single.
Qed.

Lemma EV_map_XEnv_concat
EV EV' LV (f : EV → EV') (Ξ Ξ' : XEnv EV LV) :
EV_map_XEnv f (Ξ & Ξ') =
(EV_map_XEnv f Ξ) & (EV_map_XEnv f Ξ').
Proof.
apply map_concat.
Qed.

Lemma LV_map_XEnv_concat
EV LV LV' (f : LV → LV') (Ξ Ξ' : XEnv EV LV) :
LV_map_XEnv f (Ξ & Ξ') =
(LV_map_XEnv f Ξ) & (LV_map_XEnv f Ξ').
Proof.
apply map_concat.
Qed.

Lemma EV_map_XEnv_dom
EV EV' LV (f : EV → EV') (Ξ : XEnv EV LV) :
dom (EV_map_XEnv f Ξ) = dom Ξ.
Proof.
induction Ξ as [ | ? ? [? ?] IHΞ ] using env_ind.
+ rewrite EV_map_XEnv_empty.
  repeat rewrite dom_empty.
  reflexivity.
+ rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  repeat rewrite dom_concat, dom_single.
  rewrite IHΞ.
  reflexivity.
Qed.

Lemma LV_map_XEnv_dom
EV LV LV' (f : LV → LV') (Ξ : XEnv EV LV) :
dom (LV_map_XEnv f Ξ) = dom Ξ.
Proof.
induction Ξ as [ | ? ? [? ?] IHΞ ] using env_ind.
+ rewrite LV_map_XEnv_empty.
  repeat rewrite dom_empty.
  reflexivity.
+ rewrite LV_map_XEnv_concat, LV_map_XEnv_single.
  repeat rewrite dom_concat, dom_single.
  rewrite IHΞ.
  reflexivity.
Qed.


Section section_binds_EV_map.
Context (EV EV' LV : Set).
Context (f : EV → EV').
Context (X : var).

Lemma binds_EV_map T E (Ξ : XEnv EV LV) :
binds X (T, E) Ξ →
binds X (EV_map_ty f T, EV_map_eff f E) (EV_map_XEnv f Ξ).
Proof.
intro Hbinds.
induction Ξ as [ | Ξ' X' [ T' E' ] IHΞ' ] using env_ind.
+ apply binds_empty_inv in Hbinds ; crush.
+ apply binds_concat_inv in Hbinds.
  rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  destruct Hbinds as [ Hbinds | Hbinds ].
  - apply binds_single_inv in Hbinds ; crush.
  - destruct Hbinds as [ FrX Hbinds ] ; auto.
Qed.

Lemma binds_EV_map_inv
(T' : ty ∅ EV' LV ∅) (E' : eff ∅ EV' LV ∅) (Ξ : XEnv EV LV) :
binds X (T', E') (EV_map_XEnv f Ξ) →
∃ T E,
T' = EV_map_ty f T ∧ E' = EV_map_eff f E ∧ binds X (T, E) Ξ.
Proof.
intro Hbinds'.
induction Ξ as [ | Ξ Y [ T E ] IHΞ ] using env_ind.
+ rewrite EV_map_XEnv_empty in Hbinds'.
  apply binds_empty_inv in Hbinds' ; crush.
+ rewrite EV_map_XEnv_concat, EV_map_XEnv_single in Hbinds'.
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

End section_binds_EV_map.


Section section_binds_LV_map.
Context (EV LV LV' : Set).
Context (f : LV → LV').
Context (X : var).

Lemma binds_LV_map T E (Ξ : XEnv EV LV) :
binds X (T, E) Ξ →
binds X (LV_map_ty f T, LV_map_eff f E) (LV_map_XEnv f Ξ).
Proof.
intro Hbinds.
induction Ξ as [ | Ξ' X' [ T' E' ] IHΞ' ] using env_ind.
+ apply binds_empty_inv in Hbinds ; crush.
+ apply binds_concat_inv in Hbinds.
  rewrite LV_map_XEnv_concat, LV_map_XEnv_single.
  destruct Hbinds as [ Hbinds | Hbinds ].
  - apply binds_single_inv in Hbinds ; crush.
  - destruct Hbinds as [ FrX Hbinds ] ; auto.
Qed.

Lemma binds_LV_map_inv
(T' : ty ∅ EV LV' ∅) (E' : eff ∅ EV LV' ∅) (Ξ : XEnv EV LV) :
binds X (T', E') (LV_map_XEnv f Ξ) →
∃ T E,
T' = LV_map_ty f T ∧ E' = LV_map_eff f E ∧ binds X (T, E) Ξ.
Proof.
intro Hbinds'.
induction Ξ as [ | Ξ Y [ T E ] IHΞ ] using env_ind.
+ rewrite LV_map_XEnv_empty in Hbinds'.
  apply binds_empty_inv in Hbinds' ; crush.
+ rewrite LV_map_XEnv_concat, LV_map_XEnv_single in Hbinds'.
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

End section_binds_LV_map.


(** * Identity *)

Section section_EP_map_id.

Definition
  EP_map_ef_id EP EV LV L (f : EP → EP) (Hf : ∀ x, f x = x) (e : ef EP EV LV L) :
  EP_map_ef f e = e.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EP_map_ef_id.

Fixpoint
  EP_map_eff_id EP EV LV L (f : EP → EP) (Hf : ∀ x, f x = x) (E : eff EP EV LV L) :
  EP_map_eff f E = E.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite EP_map_eff_id.

Fixpoint
  EP_map_it_id EP EV LV L (f : EP → EP) (Hf : ∀ x, f x = x) κ (N : it EP EV LV L κ) :
  EP_map_it f N = N.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite EP_map_it_id.

Fixpoint
  EP_map_ty_id EP EV LV L (f : EP → EP) (Hf : ∀ x, f x = x)
  (T : ty EP EV LV L) {struct T} :
  EP_map_ty f T = T
with
  EP_map_ms_id EP EV LV L (f : EP → EP) (Hf : ∀ x, f x = x)
  (σ : ms EP EV LV L) {struct σ} :
  EP_map_ms f σ = σ
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite EP_map_ty_id.
Hint Rewrite EP_map_ms_id.

Fixpoint
  EP_map_is_id EP EV LV L (f : EP → EP) (Hf : ∀ x, f x = x)
  (Σ : is EP EV LV L) {struct Σ} :
  EP_map_is f Σ = Σ
.
Proof.
destruct Σ ; crush.
Qed.

End section_EP_map_id.

Section section_EV_map_id.

Definition
  EV_map_ef_id EP EV LV L (f : EV → EV) (Hf : ∀ x, f x = x) (e : ef EP EV LV L) :
  EV_map_ef f e = e.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EV_map_ef_id.

Fixpoint
  EV_map_eff_id EP EV LV L (f : EV → EV) (Hf : ∀ x, f x = x) (E : eff EP EV LV L) :
  EV_map_eff f E = E.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite EV_map_eff_id.

Fixpoint
  EV_map_it_id EP EV LV L (f : EV → EV) (Hf : ∀ x, f x = x) κ (N : it EP EV LV L κ) :
  EV_map_it f N = N.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite EV_map_it_id.

Fixpoint
  EV_map_ty_id EP EV LV L (f : EV → EV) (Hf : ∀ x, f x = x)
  (T : ty EP EV LV L) {struct T} :
  EV_map_ty f T = T
with
  EV_map_ms_id EP EV LV L (f : EV → EV) (Hf : ∀ x, f x = x)
  (σ : ms EP EV LV L) {struct σ} :
  EV_map_ms f σ = σ
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite EV_map_ty_id EV_map_ms_id.

Fixpoint
  EV_map_is_id EP EV LV L (f : EV → EV) (Hf : ∀ x, f x = x)
  (Σ : is EP EV LV L) {struct Σ} :
  EV_map_is f Σ = Σ
.
Proof.
destruct Σ ; crush.
Qed.

Fixpoint
  EV_map_md_id EV LV V L (f : EV → EV) (Hf : ∀ x, f x = x)
  (m : md EV LV V L) {struct m} :
  EV_map_md f m = m
with
  EV_map_ktx_id EV LV V L (f : EV → EV) (Hf : ∀ x, f x = x)
  (K : ktx EV LV V L) {struct K} :
  EV_map_ktx f K = K
with
  EV_map_val_id EV LV V L (f : EV → EV) (Hf : ∀ x, f x = x)
  (v : val EV LV V L) {struct v} :
  EV_map_val f v = v
with
  EV_map_tm_id EV LV V L (f : EV → EV) (Hf : ∀ x, f x = x)
  (t : tm EV LV V L) {struct t} :
  EV_map_tm f t = t
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Lemma EV_map_XEnv_id
EV LV (f : EV → EV) (Hf : ∀ x, f x = x)
(Ξ : XEnv EV LV) :
EV_map_XEnv f Ξ = Ξ.
Proof.
induction Ξ as [ | Ξ X [T E] IHΞ ] using env_ind.
+ rewrite EV_map_XEnv_empty.
  reflexivity.
+ rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  erewrite IHΞ, EV_map_ty_id, EV_map_eff_id ; crush.
Qed.

End section_EV_map_id.


Section section_LV_map_id.

Definition
  LV_map_lbl_id LV L (f : LV → LV) (Hf : ∀ x, f x = x)
  (ℓ : lbl LV L) :
  LV_map_lbl f ℓ = ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite LV_map_lbl_id.

Definition
  LV_map_ef_id EP EV LV L (f : LV → LV) (Hf : ∀ x, f x = x) (e : ef EP EV LV L) : LV_map_ef f e = e.
Proof.
destruct e ; crush.
Qed.
Hint Rewrite LV_map_ef_id.

Fixpoint
  LV_map_eff_id EP EV LV L (f : LV → LV) (Hf : ∀ x, f x = x)
  (E : eff EP EV LV L) :
  LV_map_eff f E = E.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite LV_map_eff_id.

Fixpoint
  LV_map_it_id EP EV LV L (f : LV → LV) (Hf : ∀ x, f x = x)
  κ (N : it EP EV LV L κ) :
  LV_map_it f N = N.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite LV_map_it_id.

Fixpoint
  LV_map_ty_id EP EV LV L (f : LV → LV) (Hf : ∀ x, f x = x)
  (T : ty EP EV LV L) {struct T} :
  LV_map_ty f T = T
with
  LV_map_ms_id EP EV LV L (f : LV → LV) (Hf : ∀ x, f x = x)
  (σ : ms EP EV LV L) {struct σ} :
  LV_map_ms f σ = σ
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite LV_map_ty_id LV_map_ms_id.

Fixpoint
  LV_map_is_id EP EV LV L (f : LV → LV) (Hf : ∀ x, f x = x)
  (Σ : is EP EV LV L) {struct Σ} :
  LV_map_is f Σ = Σ
.
Proof.
destruct Σ ; crush.
Qed.

Fixpoint
  LV_map_md_id EV LV V L (f : LV → LV) (Hf : ∀ x, f x = x)
  (h : md EV LV V L) {struct h} :
  LV_map_md f h = h
with
  LV_map_ktx_id EV LV V L (f : LV → LV) (Hf : ∀ x, f x = x)
  (K : ktx EV LV V L) {struct K} :
  LV_map_ktx f K = K
with
  LV_map_val_id EV LV V L (f : LV → LV) (Hf : ∀ x, f x = x)
  (v : val EV LV V L) {struct v} :
  LV_map_val f v = v
with
  LV_map_tm_id EV LV V L (f : LV → LV) (Hf : ∀ x, f x = x)
  (t : tm EV LV V L) {struct t} :
  LV_map_tm f t = t
.
Proof.
+ destruct h ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Lemma LV_map_XEnv_id
(EV LV : Set) (f : LV → LV) (Hf : ∀ x, f x = x)
(Ξ : XEnv EV LV) :
LV_map_XEnv f Ξ = Ξ.
Proof.
induction Ξ as [ | Ξ X [T E] IHΞ ] using env_ind.
+ rewrite LV_map_XEnv_empty.
  reflexivity.
+ rewrite LV_map_XEnv_concat, LV_map_XEnv_single.
  erewrite IHΞ, LV_map_ty_id, LV_map_eff_id ; crush.
Qed.

End section_LV_map_id.


Section section_L_map_id.

Definition
  L_map_lid_id (L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (ID : lid L) :
  L_map_lid f ID = ID.
Proof.
destruct ID ; crush.
Qed.

Hint Rewrite L_map_lid_id.

Definition
  L_map_lbl_id (LV L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (ℓ : lbl LV L) :
  L_map_lbl f ℓ = ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite L_map_lbl_id.

Definition
  L_map_ef_id EP EV LV L (f : L → L) (Hf : ∀ x, f x = x)
  (e : ef EP EV LV L) :
  L_map_ef f e = e.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite L_map_ef_id.

Fixpoint
  L_map_eff_id EP EV LV L (f : L → L) (Hf : ∀ x, f x = x)
  (E : eff EP EV LV L) :
  L_map_eff f E = E.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite L_map_eff_id.

Fixpoint
  L_map_it_id EP EV LV L (f : L → L) (Hf : ∀ x, f x = x)
  κ (N : it EP EV LV L κ) :
  L_map_it f N = N.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite L_map_it_id.

Fixpoint
  L_map_ty_id EP EV LV L (f : L → L) (Hf : ∀ x, f x = x)
  (T : ty EP EV LV L) {struct T} :
  L_map_ty f T = T
with
  L_map_ms_id EP EV LV L (f : L → L) (Hf : ∀ x, f x = x)
  (σ : ms EP EV LV L) {struct σ} :
  L_map_ms f σ = σ
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite L_map_ty_id.
Hint Rewrite L_map_ms_id.

Fixpoint
  L_map_is_id EP EV LV L (f : L → L) (Hf : ∀ x, f x = x)
  (Σ : is EP EV LV L) {struct Σ} :
  L_map_is f Σ = Σ
.
Proof.
destruct Σ ; crush.
Qed.

Fixpoint
  L_map_md_id EV LV V L (f : L → L) (Hf : ∀ x, f x = x)
  (m : md EV LV V L) {struct m} :
  L_map_md f m = m
with
  L_map_ktx_id EV LV V L (f : L → L) (Hf : ∀ x, f x = x)
  (K : ktx EV LV V L) {struct K} :
  L_map_ktx f K = K
with
  L_map_val_id EV LV V L (f : L → L) (Hf : ∀ x, f x = x)
  (v : val EV LV V L) {struct v} :
  L_map_val f v = v
with
  L_map_tm_id EV LV V L (f : L → L) (Hf : ∀ x, f x = x)
  (t : tm EV LV V L) {struct t} :
  L_map_tm f t = t
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

End section_L_map_id.


Fixpoint
  V_map_md_id EV LV V L (f : V → V) (Hf : ∀ x, f x = x)
  (m : md EV LV V L) {struct m} :
  V_map_md f m = m
with
  V_map_ktx_id EV LV V L (f : V → V) (Hf : ∀ x, f x = x)
  (K : ktx EV LV V L) {struct K} :
  V_map_ktx f K = K
with
  V_map_val_id EV LV V L (f : V → V) (Hf : ∀ x, f x = x)
  (v : val EV LV V L) {struct v} :
  V_map_val f v = v
with
  V_map_tm_id EV LV V L (f : V → V) (Hf : ∀ x, f x = x)
  (t : tm EV LV V L) {struct t} :
  V_map_tm f t = t
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.


(** Composition *)

Section section_EP_map_map.

Definition
  EP_map_map_ef EP1 EP2 EP3 EV LV L
  (f₁ : EP1 → EP2) (f₂ : EP2 → EP3) (g : EP1 → EP3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (e : ef EP1 EV LV L) :
  EP_map_ef f₂ (EP_map_ef f₁ e) = EP_map_ef g e
.
Proof.
destruct e ; simpl ;
crush.
Qed.

Fixpoint
  EP_map_map_eff EP1 EP2 EP3 EV LV L
  (f₁ : EP1 → EP2) (f₂ : EP2 → EP3) (g : EP1 → EP3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (E : eff EP1 EV LV L) :
  EP_map_eff f₂ (EP_map_eff f₁ E) = EP_map_eff g E
.
Proof.
destruct E ; simpl ;
repeat erewrite EP_map_map_ef ;
repeat erewrite EP_map_map_eff ;
crush.
Qed.

Fixpoint
  EP_map_map_it EP1 EP2 EP3 EV LV L
  (f₁ : EP1 → EP2) (f₂ : EP2 → EP3) (g : EP1 → EP3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  κ (N : it EP1 EV LV L κ) :
  EP_map_it f₂ (EP_map_it f₁ N) = EP_map_it g N
.
Proof.
destruct N ; simpl ;
repeat erewrite EP_map_map_it ;
repeat erewrite EP_map_map_eff ;
crush.
Qed.

Fixpoint
  EP_map_map_ty EP1 EP2 EP3 EV LV L
  (f₁ : EP1 → EP2) (f₂ : EP2 → EP3) (g : EP1 → EP3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (T : ty EP1 EV LV L) {struct T} :
  EP_map_ty f₂ (EP_map_ty f₁ T) = EP_map_ty g T
with
  EP_map_map_ms EP1 EP2 EP3 EV LV L
  (f₁ : EP1 → EP2) (f₂ : EP2 → EP3) (g : EP1 → EP3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (σ : ms EP1 EV LV L) {struct σ} :
  EP_map_ms f₂ (EP_map_ms f₁ σ) = EP_map_ms g σ.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EP_map_map_ty ;
  repeat erewrite EP_map_map_ms ;
  repeat erewrite EP_map_map_it ;
  repeat erewrite EP_map_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EP_map_map_ty ;
  repeat erewrite EP_map_map_ms ;
  repeat erewrite EP_map_map_eff ;
  crush.
Qed.

Fixpoint
  EP_map_map_is EP1 EP2 EP3 EV LV L
  (f₁ : EP1 → EP2) (f₂ : EP2 → EP3) (g : EP1 → EP3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (Σ : is EP1 EV LV L) {struct Σ} :
  EP_map_is f₂ (EP_map_is f₁ Σ) = EP_map_is g Σ
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EP_map_map_ms ;
repeat erewrite EP_map_map_is ;
crush.
Qed.

End section_EP_map_map.

Definition
  EV_map_map_ef EP EV1 EV2 EV3 LV L
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (e : ef EP EV1 LV L) :
  EV_map_ef f₂ (EV_map_ef f₁ e) = EV_map_ef g e
.
Proof.
destruct e ; simpl ;
crush.
Qed.

Fixpoint
  EV_map_map_eff EP (EV1 EV2 EV3 LV L : Set)
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (E : eff EP EV1 LV L) :
  EV_map_eff f₂ (EV_map_eff f₁ E) = EV_map_eff g E
.
Proof.
destruct E ; simpl ;
repeat erewrite EV_map_map_ef ;
repeat erewrite EV_map_map_eff ;
crush.
Qed.

Fixpoint
  EV_map_map_it EP (EV1 EV2 EV3 LV L : Set)
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  κ (N : it EP EV1 LV L κ) :
  EV_map_it f₂ (EV_map_it f₁ N) = EV_map_it g N
.
Proof.
destruct N ; simpl ;
repeat erewrite EV_map_map_it ;
repeat erewrite EV_map_map_eff ;
crush.
Qed.

Fixpoint
  EV_map_map_ty EP EV1 EV2 EV3 LV L
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (T : ty EP EV1 LV L) {struct T} :
  EV_map_ty f₂ (EV_map_ty f₁ T) = EV_map_ty g T
with
  EV_map_map_ms EP EV1 EV2 EV3 LV L
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (σ : ms EP EV1 LV L) {struct σ} :
  EV_map_ms f₂ (EV_map_ms f₁ σ) = EV_map_ms g σ.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_map_map_ty ;
  repeat erewrite EV_map_map_ms ;
  repeat erewrite EV_map_map_it ;
  repeat erewrite EV_map_map_eff ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite EV_map_map_ty ;
  repeat erewrite EV_map_map_ms ;
  repeat erewrite EV_map_map_eff ;
  crush.
Qed.

Fixpoint
  EV_map_map_is EP EV1 EV2 EV3 LV L
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (Σ : is EP EV1 LV L) {struct Σ} :
  EV_map_is f₂ (EV_map_is f₁ Σ) = EV_map_is g Σ
.
Proof.
destruct Σ ; simpl ;
repeat erewrite EV_map_map_ms ;
repeat erewrite EV_map_map_is ;
crush.
Qed.

Fixpoint
  EV_map_map_md EV1 EV2 EV3 LV V L
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (m : md EV1 LV V L) {struct m} :
  EV_map_md f₂ (EV_map_md f₁ m) = EV_map_md g m
with
  EV_map_map_ktx EV1 EV2 EV3 LV V L
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (K : ktx EV1 LV V L) {struct K} :
  EV_map_ktx f₂ (EV_map_ktx f₁ K) = EV_map_ktx g K
with
  EV_map_map_val EV1 EV2 EV3 LV V L
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (v : val EV1 LV V L) {struct v} :
  EV_map_val f₂ (EV_map_val f₁ v) = EV_map_val g v
with
  EV_map_map_tm EV1 EV2 EV3 LV V L
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (t : tm EV1 LV V L) {struct t} :
  EV_map_tm f₂ (EV_map_tm f₁ t) = EV_map_tm g t.
Proof.
+ destruct m ; simpl ;
  repeat erewrite EV_map_map_md ;
  repeat erewrite EV_map_map_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite EV_map_map_ktx ;
  repeat erewrite EV_map_map_tm ;
  repeat erewrite EV_map_map_val ;
  repeat erewrite EV_map_map_eff ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_map_map_md ;
  repeat erewrite EV_map_map_ktx ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_map_map_ty ;
  repeat erewrite EV_map_map_eff ;
  repeat erewrite EV_map_map_val ;
  repeat erewrite EV_map_map_tm ;
  repeat erewrite EV_map_map_md ;
  crush.
Qed.

Lemma EV_map_map_XEnv
EV1 EV2 EV3 LV
(f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
(Hf : ∀ x, f₂ (f₁ x) = g x)
(Ξ : XEnv EV1 LV) :
EV_map_XEnv f₂ (EV_map_XEnv f₁ Ξ) = EV_map_XEnv g Ξ.
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat rewrite EV_map_XEnv_empty ; reflexivity.
+ repeat rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  erewrite EV_map_map_ty, EV_map_map_eff, IHΞ ; crush.
Qed.


Definition
  LV_map_map_lbl LV1 LV2 LV3 L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (ℓ : lbl LV1 L) :
  LV_map_lbl f₂ (LV_map_lbl f₁ ℓ) = LV_map_lbl g ℓ
.
Proof.
destruct ℓ ; simpl ;
crush.
Qed.

Definition
  LV_map_map_ef EP EV LV1 LV2 LV3 L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (e : ef EP EV LV1 L) :
  LV_map_ef f₂ (LV_map_ef f₁ e) = LV_map_ef g e
.
Proof.
destruct e ; simpl ;
repeat erewrite LV_map_map_lbl ;
crush.
Qed.

Fixpoint
  LV_map_map_eff EP EV LV1 LV2 LV3 L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (E : eff EP EV LV1 L) :
  LV_map_eff f₂ (LV_map_eff f₁ E) = LV_map_eff g E
.
Proof.
destruct E ; simpl ;
repeat erewrite LV_map_map_ef ;
repeat erewrite LV_map_map_eff ;
crush.
Qed.

Fixpoint
  LV_map_map_it EP EV LV1 LV2 LV3 L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  κ (N : it EP EV LV1 L κ) :
  LV_map_it f₂ (LV_map_it f₁ N) = LV_map_it g N
.
Proof.
destruct N ; simpl ;
repeat erewrite LV_map_map_it ;
repeat erewrite LV_map_map_eff ;
crush.
Qed.

Fixpoint
  LV_map_map_ty EP EV LV1 LV2 LV3 L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (T : ty EP EV LV1 L) {struct T} :
  LV_map_ty f₂ (LV_map_ty f₁ T) = LV_map_ty g T
with
  LV_map_map_ms EP EV LV1 LV2 LV3 L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (σ : ms EP EV LV1 L) {struct σ} :
  LV_map_ms f₂ (LV_map_ms f₁ σ) = LV_map_ms g σ.
Proof.
+ destruct T ; simpl ;
  repeat erewrite LV_map_map_ty ;
  repeat erewrite LV_map_map_ms ;
  repeat erewrite LV_map_map_it ;
  repeat erewrite LV_map_map_eff ;
  repeat erewrite LV_map_map_lbl ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite LV_map_map_ty ;
  repeat erewrite LV_map_map_ms ;
  repeat erewrite LV_map_map_eff ;
  repeat erewrite LV_map_map_lbl ;
  crush.
Qed.

Fixpoint
  LV_map_map_is EP EV LV1 LV2 LV3 L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (Σ : is EP EV LV1 L) {struct Σ} :
  LV_map_is f₂ (LV_map_is f₁ Σ) = LV_map_is g Σ
.
Proof.
destruct Σ ; simpl ;
repeat erewrite LV_map_map_ms ;
repeat erewrite LV_map_map_is ;
crush.
Qed.

Fixpoint
  LV_map_map_md EV LV1 LV2 LV3 V L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (m : md EV LV1 V L) {struct m} :
  LV_map_md f₂ (LV_map_md f₁ m) = LV_map_md g m
with
  LV_map_map_ktx EV LV1 LV2 LV3 V L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (K : ktx EV LV1 V L) {struct K} :
  LV_map_ktx f₂ (LV_map_ktx f₁ K) = LV_map_ktx g K
with
  LV_map_map_val EV LV1 LV2 LV3 V L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (v : val EV LV1 V L) {struct v} :
  LV_map_val f₂ (LV_map_val f₁ v) = LV_map_val g v
with
  LV_map_map_tm EV LV1 LV2 LV3 V L
  (f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (t : tm EV LV1 V L) {struct t} :
  LV_map_tm f₂ (LV_map_tm f₁ t) = LV_map_tm g t
.
Proof.
+ destruct m ; simpl ;
  repeat erewrite LV_map_map_md ;
  repeat erewrite LV_map_map_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite LV_map_map_ktx ;
  repeat erewrite LV_map_map_tm ;
  repeat erewrite LV_map_map_val ;
  repeat erewrite LV_map_map_eff ;
  repeat erewrite LV_map_map_lbl ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite LV_map_map_md ;
  repeat erewrite LV_map_map_ktx ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite LV_map_map_tm ;
  repeat erewrite LV_map_map_md ;
  repeat erewrite LV_map_map_lbl ;
  repeat erewrite LV_map_map_ty ;
  repeat erewrite LV_map_map_eff ;
  repeat erewrite LV_map_map_val ;
  crush.
Qed.

Lemma LV_map_map_XEnv
EV LV1 LV2 LV3
(f₁ : LV1 → LV2) (f₂ : LV2 → LV3) (g : LV1 → LV3)
(Hf : ∀ x, f₂ (f₁ x) = g x)
(Ξ : XEnv EV LV1) :
LV_map_XEnv f₂ (LV_map_XEnv f₁ Ξ) = LV_map_XEnv g Ξ.
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat rewrite LV_map_XEnv_empty ; reflexivity.
+ repeat rewrite LV_map_XEnv_concat, LV_map_XEnv_single.
  erewrite LV_map_map_ty, LV_map_map_eff, IHΞ ; crush.
Qed.

Definition
  L_map_map_lid L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (id : lid L1) :
  L_map_lid f₂ (L_map_lid f₁ id) = L_map_lid g id
.
Proof.
destruct id ; simpl ; crush.
Qed.

Definition
  L_map_map_lbl LV L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (ℓ : lbl LV L1) :
  L_map_lbl f₂ (L_map_lbl f₁ ℓ) = L_map_lbl g ℓ
.
Proof.
destruct ℓ ; simpl ;
repeat erewrite L_map_map_lid ;
crush.
Qed.

Definition
  L_map_map_ef EP EV LV L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (e : ef EP EV LV L1) :
  L_map_ef f₂ (L_map_ef f₁ e) = L_map_ef g e
.
Proof.
destruct e ; simpl ;
repeat erewrite L_map_map_lbl ;
crush.
Qed.

Fixpoint
  L_map_map_eff EP EV LV L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (E : eff EP EV LV L1) :
  L_map_eff f₂ (L_map_eff f₁ E) = L_map_eff g E
.
Proof.
destruct E ; simpl ;
repeat erewrite L_map_map_ef ;
repeat erewrite L_map_map_eff ;
crush.
Qed.

Fixpoint
  L_map_map_it EP EV LV L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  κ (N : it EP EV LV L1 κ) :
  L_map_it f₂ (L_map_it f₁ N) = L_map_it g N
.
Proof.
destruct N ; simpl ;
repeat erewrite L_map_map_it ;
repeat erewrite L_map_map_eff ;
crush.
Qed.

Fixpoint
  L_map_map_ty EP EV LV L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (T : ty EP EV LV L1) {struct T} :
  L_map_ty f₂ (L_map_ty f₁ T) = L_map_ty g T
with
  L_map_map_ms EP EV LV L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (σ : ms EP EV LV L1) {struct σ} :
  L_map_ms f₂ (L_map_ms f₁ σ) = L_map_ms g σ
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_map_map_ty ;
  repeat erewrite L_map_map_ms ;
  repeat erewrite L_map_map_it ;
  repeat erewrite L_map_map_eff ;
  repeat erewrite L_map_map_lbl ;
  crush.
+ destruct σ ; simpl ;
  repeat erewrite L_map_map_ty ;
  repeat erewrite L_map_map_ms ;
  repeat erewrite L_map_map_eff ;
  repeat erewrite L_map_map_lbl ;
  crush.
Qed.

Fixpoint
  L_map_map_is EP EV LV L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (Σ : is EP EV LV L1) {struct Σ} :
  L_map_is f₂ (L_map_is f₁ Σ) = L_map_is g Σ
.
Proof.
destruct Σ ; simpl ;
repeat erewrite L_map_map_ms ;
repeat erewrite L_map_map_is ;
crush.
Qed.

Fixpoint
  L_map_map_md EV LV V L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (m : md EV LV V L1) {struct m} :
  L_map_md f₂ (L_map_md f₁ m) = L_map_md g m
with
  L_map_map_ktx EV LV V L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (K : ktx EV LV V L1) {struct K} :
  L_map_ktx f₂ (L_map_ktx f₁ K) = L_map_ktx g K
with
  L_map_map_val EV LV V L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (v : val EV LV V L1) {struct v} :
  L_map_val f₂ (L_map_val f₁ v) = L_map_val g v
with
  L_map_map_tm EV LV V L1 L2 L3
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (t : tm EV LV V L1) {struct t} :
  L_map_tm f₂ (L_map_tm f₁ t) = L_map_tm g t.
Proof.
+ destruct m ; simpl ;
  repeat erewrite L_map_map_md ;
  repeat erewrite L_map_map_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite L_map_map_ktx ;
  repeat erewrite L_map_map_val ;
  repeat erewrite L_map_map_lbl ;
  repeat erewrite L_map_map_ty ;
  repeat erewrite L_map_map_eff ;
  repeat erewrite L_map_map_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_map_map_lid ;
  repeat erewrite L_map_map_md ;
  repeat erewrite L_map_map_ktx ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_map_map_ty ;
  repeat erewrite L_map_map_md ;
  repeat erewrite L_map_map_lid ;
  repeat erewrite L_map_map_eff ;
  repeat erewrite L_map_map_val ;
  repeat erewrite L_map_map_tm ;
  repeat erewrite L_map_map_lbl ;
  crush.
Qed.

Fixpoint
  V_map_map_md EV LV V1 V2 V3 L
  (f₁ : V1 → V2) (f₂ : V2 → V3) (g : V1 → V3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (m : md EV LV V1 L) {struct m} :
  V_map_md f₂ (V_map_md f₁ m) = V_map_md g m
with
  V_map_map_ktx EV LV V1 V2 V3 L
  (f₁ : V1 → V2) (f₂ : V2 → V3) (g : V1 → V3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (K : ktx EV LV V1 L) {struct K} :
  V_map_ktx f₂ (V_map_ktx f₁ K) = V_map_ktx g K
with
  V_map_map_val EV LV V1 V2 V3 L
  (f₁ : V1 → V2) (f₂ : V2 → V3) (g : V1 → V3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (v : val EV LV V1 L) {struct v} :
  V_map_val f₂ (V_map_val f₁ v) = V_map_val g v
with
  V_map_map_tm EV LV V1 V2 V3 L
  (f₁ : V1 → V2) (f₂ : V2 → V3) (g : V1 → V3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (t : tm EV LV V1 L) {struct t} :
  V_map_tm f₂ (V_map_tm f₁ t) = V_map_tm g t.
Proof.
+ destruct m ; simpl ;
  repeat erewrite V_map_map_md ;
  repeat erewrite V_map_map_tm ;
  crush.
+ destruct K ; simpl ;
  repeat erewrite V_map_map_ktx ;
  repeat erewrite V_map_map_tm ;
  repeat erewrite V_map_map_val ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_map_map_ktx ;
  repeat erewrite V_map_map_md ;
  repeat erewrite V_map_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_map_map_ty ;
  repeat erewrite V_map_map_md ;
  repeat erewrite V_map_map_eff ;
  repeat erewrite V_map_map_val ;
  repeat erewrite V_map_map_tm ;
  crush.
Qed.

Section section_EV_L_map.

Definition
  EV_L_map_ef EP EV EV' LV L L' (f₁ : EV → EV') (f₂ : L → L')
  (e : ef EP EV LV L) :
  EV_map_ef f₁ (L_map_ef f₂ e) = L_map_ef f₂ (EV_map_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EV_L_map_ef.

Fixpoint
  EV_L_map_eff EP EV EV' LV L L' (f₁ : EV → EV') (f₂ : L → L')
  (E : eff EP EV LV L) {struct E} :
  EV_map_eff f₁ (L_map_eff f₂ E) = L_map_eff f₂ (EV_map_eff f₁ E)
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite EV_L_map_eff.

Fixpoint
  EV_L_map_it EP EV EV' LV L L' (f₁ : EV → EV') (f₂ : L → L')
  κ (N : it EP EV LV L κ) {struct N} :
  EV_map_it f₁ (L_map_it f₂ N) = L_map_it f₂ (EV_map_it f₁ N)
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite EV_L_map_it.

Fixpoint
  EV_L_map_ty EP EV EV' LV L L' (f₁ : EV → EV') (f₂ : L → L')
  (T : ty EP EV LV L) {struct T} :
  EV_map_ty f₁ (L_map_ty f₂ T) = L_map_ty f₂ (EV_map_ty f₁ T)
with
  EV_L_map_ms EP EV EV' LV L L' (f₁ : EV → EV') (f₂ : L → L')
  (σ : ms EP EV LV L) {struct σ} :
  EV_map_ms f₁ (L_map_ms f₂ σ) = L_map_ms f₂ (EV_map_ms f₁ σ)
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite EV_L_map_ty.
Hint Rewrite EV_L_map_ms.

Fixpoint
  EV_L_map_is EP EV EV' LV L L' (f₁ : EV → EV') (f₂ : L → L')
  (Σ : is EP EV LV L) {struct Σ} :
  EV_map_is f₁ (L_map_is f₂ Σ) = L_map_is f₂ (EV_map_is f₁ Σ)
.
Proof.
destruct Σ ; crush.
Qed.

Fixpoint
  EV_L_map_md EV EV' LV V L L' (f₁ : EV → EV') (f₂ : L → L')
  (m : md EV LV V L) {struct m} :
  EV_map_md f₁ (L_map_md f₂ m) = L_map_md f₂ (EV_map_md f₁ m)
with
  EV_L_map_ktx EV EV' LV V L L' (f₁ : EV → EV') (f₂ : L → L')
  (K : ktx EV LV V L) {struct K} :
  EV_map_ktx f₁ (L_map_ktx f₂ K) = L_map_ktx f₂ (EV_map_ktx f₁ K)
with
  EV_L_map_val EV EV' LV V L L' (f₁ : EV → EV') (f₂ : L → L')
  (v : val EV LV V L) {struct v} :
  EV_map_val f₁ (L_map_val f₂ v) = L_map_val f₂ (EV_map_val f₁ v)
with
  EV_L_map_tm EV EV' LV V L L' (f₁ : EV → EV') (f₂ : L → L')
  (t : tm EV LV V L) {struct t} :
  EV_map_tm f₁ (L_map_tm f₂ t) = L_map_tm f₂ (EV_map_tm f₁ t)
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

End section_EV_L_map.


Section section_LV_L_map.

Definition
  LV_L_map_lbl LV LV' L L' (f₁ : LV → LV') (f₂ : L → L')
  (ℓ : lbl LV L) :
  LV_map_lbl f₁ (L_map_lbl f₂ ℓ) = L_map_lbl f₂ (LV_map_lbl f₁ ℓ)
.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite LV_L_map_lbl.

Definition
  LV_L_map_ef EP EV LV LV' L L' (f₁ : LV → LV') (f₂ : L → L')
  (e : ef EP EV LV L) :
  LV_map_ef f₁ (L_map_ef f₂ e) = L_map_ef f₂ (LV_map_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite LV_L_map_ef.

Fixpoint
  LV_L_map_eff EP EV LV LV' L L' (f₁ : LV → LV') (f₂ : L → L')
  (E : eff EP EV LV L) {struct E} :
  LV_map_eff f₁ (L_map_eff f₂ E) = L_map_eff f₂ (LV_map_eff f₁ E)
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite LV_L_map_eff.

Fixpoint
  LV_L_map_it EP EV LV LV' L L' (f₁ : LV → LV') (f₂ : L → L')
  κ (N : it EP EV LV L κ) {struct N} :
  LV_map_it f₁ (L_map_it f₂ N) = L_map_it f₂ (LV_map_it f₁ N)
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite LV_L_map_it.

Fixpoint
  LV_L_map_ty EP EV LV LV' L L' (f₁ : LV → LV') (f₂ : L → L')
  (T : ty EP EV LV L) {struct T} :
  LV_map_ty f₁ (L_map_ty f₂ T) = L_map_ty f₂ (LV_map_ty f₁ T)
with
  LV_L_map_ms EP EV LV LV' L L' (f₁ : LV → LV') (f₂ : L → L')
  (σ : ms EP EV LV L) {struct σ} :
  LV_map_ms f₁ (L_map_ms f₂ σ) = L_map_ms f₂ (LV_map_ms f₁ σ)
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite LV_L_map_ty.
Hint Rewrite LV_L_map_ms.

Fixpoint
  LV_L_map_is EP EV LV LV' L L' (f₁ : LV → LV') (f₂ : L → L')
  (Σ : is EP EV LV L) {struct Σ} :
  LV_map_is f₁ (L_map_is f₂ Σ) = L_map_is f₂ (LV_map_is f₁ Σ)
.
Proof.
destruct Σ ; crush.
Qed.

Fixpoint
  LV_L_map_md EV LV LV' V L L' (f₁ : LV → LV') (f₂ : L → L')
  (m : md EV LV V L) {struct m} :
  LV_map_md f₁ (L_map_md f₂ m) = L_map_md f₂ (LV_map_md f₁ m)
with
  LV_L_map_ktx EV LV LV' V L L' (f₁ : LV → LV') (f₂ : L → L')
  (K : ktx EV LV V L) {struct K} :
  LV_map_ktx f₁ (L_map_ktx f₂ K) = L_map_ktx f₂ (LV_map_ktx f₁ K)
with
  LV_L_map_val EV LV LV' V L L' (f₁ : LV → LV') (f₂ : L → L')
  (v : val EV LV V L) {struct v} :
  LV_map_val f₁ (L_map_val f₂ v) = L_map_val f₂ (LV_map_val f₁ v)
with
  LV_L_map_tm EV LV LV' V L L' (f₁ : LV → LV') (f₂ : L → L')
  (t : tm EV LV V L) {struct t} :
  LV_map_tm f₁ (L_map_tm f₂ t) = L_map_tm f₂ (LV_map_tm f₁ t)
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

End section_LV_L_map.


Section section_EV_LV_map.

Definition
  EV_LV_map_ef EP EV EV' LV LV' L (f₁ : EV → EV') (f₂ : LV → LV')
  (e : ef EP EV LV L) :
  EV_map_ef f₁ (LV_map_ef f₂ e) = LV_map_ef f₂ (EV_map_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EV_LV_map_ef.

Fixpoint
  EV_LV_map_eff EP EV EV' LV LV' L (f₁ : EV → EV') (f₂ : LV → LV')
  (E : eff EP EV LV L) {struct E} :
  EV_map_eff f₁ (LV_map_eff f₂ E) = LV_map_eff f₂ (EV_map_eff f₁ E)
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite EV_LV_map_eff.

Fixpoint
  EV_LV_map_it EP EV EV' LV LV' L (f₁ : EV → EV') (f₂ : LV → LV')
  κ (N : it EP EV LV L κ) {struct N} :
  EV_map_it f₁ (LV_map_it f₂ N) = LV_map_it f₂ (EV_map_it f₁ N)
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite EV_LV_map_it.

Fixpoint
  EV_LV_map_ty EP EV EV' LV LV' L (f₁ : EV → EV') (f₂ : LV → LV')
  (T : ty EP EV LV L) {struct T} :
  EV_map_ty f₁ (LV_map_ty f₂ T) = LV_map_ty f₂ (EV_map_ty f₁ T)
with
  EV_LV_map_ms EP EV EV' LV LV' L (f₁ : EV → EV') (f₂ : LV → LV')
  (σ : ms EP EV LV L) {struct σ} :
  EV_map_ms f₁ (LV_map_ms f₂ σ) = LV_map_ms f₂ (EV_map_ms f₁ σ)
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite EV_LV_map_ty.
Hint Rewrite EV_LV_map_ms.

Fixpoint
  EV_LV_map_is EP EV EV' LV LV' L (f₁ : EV → EV') (f₂ : LV → LV')
  (Σ : is EP EV LV L) {struct Σ} :
  EV_map_is f₁ (LV_map_is f₂ Σ) = LV_map_is f₂ (EV_map_is f₁ Σ)
.
Proof.
destruct Σ ; crush.
Qed.

Fixpoint
  EV_LV_map_md EV EV' LV LV' V L (f₁ : EV → EV') (f₂ : LV → LV')
  (m : md EV LV V L) {struct m} :
  EV_map_md f₁ (LV_map_md f₂ m) = LV_map_md f₂ (EV_map_md f₁ m)
with
  EV_LV_map_ktx EV EV' LV LV' V L (f₁ : EV → EV') (f₂ : LV → LV')
  (K : ktx EV LV V L) {struct K} :
  EV_map_ktx f₁ (LV_map_ktx f₂ K) = LV_map_ktx f₂ (EV_map_ktx f₁ K)
with
  EV_LV_map_val EV EV' LV LV' V L (f₁ : EV → EV') (f₂ : LV → LV')
  (v : val EV LV V L) {struct v} :
  EV_map_val f₁ (LV_map_val f₂ v) = LV_map_val f₂ (EV_map_val f₁ v)
with
  EV_LV_map_tm EV EV' LV LV' V L (f₁ : EV → EV') (f₂ : LV → LV')
  (t : tm EV LV V L) {struct t} :
  EV_map_tm f₁ (LV_map_tm f₂ t) = LV_map_tm f₂ (EV_map_tm f₁ t)
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Lemma EV_LV_map_XEnv
EV EV' LV LV' (f₁ : EV → EV') (f₂ : LV → LV')
(Ξ : XEnv EV LV) :
EV_map_XEnv f₁ (LV_map_XEnv f₂ Ξ) = LV_map_XEnv f₂ (EV_map_XEnv f₁ Ξ).
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat rewrite EV_map_XEnv_empty, LV_map_XEnv_empty ; reflexivity.
+ repeat rewrite EV_map_XEnv_concat, LV_map_XEnv_concat,
    EV_map_XEnv_single, LV_map_XEnv_single.
  rewrite EV_LV_map_ty, EV_LV_map_eff, IHΞ.
  reflexivity.
Qed.

End section_EV_LV_map.


Fixpoint
  EV_V_map_md EV EV' LV V V' L (f₁ : EV → EV') (f₂ : V → V')
  (m : md EV LV V L) {struct m} :
  EV_map_md f₁ (V_map_md f₂ m) = V_map_md f₂ (EV_map_md f₁ m)
with
  EV_V_map_ktx EV EV' LV V V' L (f₁ : EV → EV') (f₂ : V → V')
  (K : ktx EV LV V L) {struct K} :
  EV_map_ktx f₁ (V_map_ktx f₂ K) = V_map_ktx f₂ (EV_map_ktx f₁ K)
with
  EV_V_map_val EV EV' LV V V' L (f₁ : EV → EV') (f₂ : V → V')
  (v : val EV LV V L) {struct v} :
  EV_map_val f₁ (V_map_val f₂ v) = V_map_val f₂ (EV_map_val f₁ v)
with
  EV_V_map_tm EV EV' LV V V' L (f₁ : EV → EV') (f₂ : V → V')
  (t : tm EV LV V L) {struct t} :
  EV_map_tm f₁ (V_map_tm f₂ t) = V_map_tm f₂ (EV_map_tm f₁ t)
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.


Fixpoint
  LV_V_map_md EV LV LV' V V' L (f₁ : LV → LV') (f₂ : V → V')
  (m : md EV LV V L) {struct m} :
  LV_map_md f₁ (V_map_md f₂ m) = V_map_md f₂ (LV_map_md f₁ m)
with
  LV_V_map_ktx EV LV LV' V V' L (f₁ : LV → LV') (f₂ : V → V')
  (K : ktx EV LV V L) {struct K} :
  LV_map_ktx f₁ (V_map_ktx f₂ K) = V_map_ktx f₂ (LV_map_ktx f₁ K)
with
  LV_V_map_val EV LV LV' V V' L (f₁ : LV → LV') (f₂ : V → V')
  (v : val EV LV V L) {struct v} :
  LV_map_val f₁ (V_map_val f₂ v) = V_map_val f₂ (LV_map_val f₁ v)
with
  LV_V_map_tm EV LV LV' V V' L (f₁ : LV → LV') (f₂ : V → V')
  (t : tm EV LV V L) {struct t} :
  LV_map_tm f₁ (V_map_tm f₂ t) = V_map_tm f₂ (LV_map_tm f₁ t)
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Fixpoint
  V_L_map_md EV LV V V' L L' (f₁ : V → V') (f₂ : L → L')
  (m : md EV LV V L) {struct m} :
  V_map_md f₁ (L_map_md f₂ m) = L_map_md f₂ (V_map_md f₁ m)
with
  V_L_map_ktx EV LV V V' L L' (f₁ : V → V') (f₂ : L → L')
  (K : ktx EV LV V L) {struct K} :
  V_map_ktx f₁ (L_map_ktx f₂ K) = L_map_ktx f₂ (V_map_ktx f₁ K)
with
  V_L_map_val EV LV V V' L L' (f₁ : V → V') (f₂ : L → L')
  (v : val EV LV V L) {struct v} :
  V_map_val f₁ (L_map_val f₂ v) = L_map_val f₂ (V_map_val f₁ v)
with
  V_L_map_tm EV LV V V' L L' (f₁ : V → V') (f₂ : L → L')
  (t : tm EV LV V L) {struct t} :
  V_map_tm f₁ (L_map_tm f₂ t) = L_map_tm f₂ (V_map_tm f₁ t)
.
Proof.
+ destruct m ; crush.
+ destruct K ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Section section_EP_L_map.

Definition
  EP_L_map_ef EP EP' EV LV L L' (f₁ : EP → EP') (f₂ : L → L')
  (e : ef EP EV LV L) :
  EP_map_ef f₁ (L_map_ef f₂ e) = L_map_ef f₂ (EP_map_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EP_L_map_ef.

Fixpoint
  EP_L_map_eff EP EP' EV LV L L' (f₁ : EP → EP') (f₂ : L → L')
  (E : eff EP EV LV L) {struct E} :
  EP_map_eff f₁ (L_map_eff f₂ E) = L_map_eff f₂ (EP_map_eff f₁ E)
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite EP_L_map_eff.

Fixpoint
  EP_L_map_it EP EP' EV LV L L' (f₁ : EP → EP') (f₂ : L → L')
  κ (N : it EP EV LV L κ) {struct N} :
  EP_map_it f₁ (L_map_it f₂ N) = L_map_it f₂ (EP_map_it f₁ N)
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite EP_L_map_it.

Fixpoint
  EP_L_map_ty EP EP' EV LV L L' (f₁ : EP → EP') (f₂ : L → L')
  (T : ty EP EV LV L) {struct T} :
  EP_map_ty f₁ (L_map_ty f₂ T) = L_map_ty f₂ (EP_map_ty f₁ T)
with
  EP_L_map_ms EP EP' EV LV L L' (f₁ : EP → EP') (f₂ : L → L')
  (σ : ms EP EV LV L) {struct σ} :
  EP_map_ms f₁ (L_map_ms f₂ σ) = L_map_ms f₂ (EP_map_ms f₁ σ)
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite EP_L_map_ty.
Hint Rewrite EP_L_map_ms.

Fixpoint
  EP_L_map_is EP EP' EV LV L L' (f₁ : EP → EP') (f₂ : L → L')
  (Σ : is EP EV LV L) {struct Σ} :
  EP_map_is f₁ (L_map_is f₂ Σ) = L_map_is f₂ (EP_map_is f₁ Σ)
.
Proof.
destruct Σ ; crush.
Qed.

End section_EP_L_map.

Section section_EP_LV_map.

Definition
  EP_LV_map_ef EP EP' EV LV LV' L (f₁ : EP → EP') (f₂ : LV → LV')
  (e : ef EP EV LV L) :
  EP_map_ef f₁ (LV_map_ef f₂ e) = LV_map_ef f₂ (EP_map_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EP_LV_map_ef.

Fixpoint
  EP_LV_map_eff EP EP' EV LV LV' L (f₁ : EP → EP') (f₂ : LV → LV')
  (E : eff EP EV LV L) {struct E} :
  EP_map_eff f₁ (LV_map_eff f₂ E) = LV_map_eff f₂ (EP_map_eff f₁ E)
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite EP_LV_map_eff.

Fixpoint
  EP_LV_map_it EP EP' EV LV LV' L (f₁ : EP → EP') (f₂ : LV → LV')
  κ (N : it EP EV LV L κ) {struct N} :
  EP_map_it f₁ (LV_map_it f₂ N) = LV_map_it f₂ (EP_map_it f₁ N)
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite EP_LV_map_it.

Fixpoint
  EP_LV_map_ty EP EP' EV LV LV' L (f₁ : EP → EP') (f₂ : LV → LV')
  (T : ty EP EV LV L) {struct T} :
  EP_map_ty f₁ (LV_map_ty f₂ T) = LV_map_ty f₂ (EP_map_ty f₁ T)
with
  EP_LV_map_ms EP EP' EV LV LV' L (f₁ : EP → EP') (f₂ : LV → LV')
  (σ : ms EP EV LV L) {struct σ} :
  EP_map_ms f₁ (LV_map_ms f₂ σ) = LV_map_ms f₂ (EP_map_ms f₁ σ)
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite EP_LV_map_ty.
Hint Rewrite EP_LV_map_ms.

Fixpoint
  EP_LV_map_is EP EP' EV LV LV' L (f₁ : EP → EP') (f₂ : LV → LV')
  (Σ : is EP EV LV L) {struct Σ} :
  EP_map_is f₁ (LV_map_is f₂ Σ) = LV_map_is f₂ (EP_map_is f₁ Σ)
.
Proof.
destruct Σ ; crush.
Qed.

End section_EP_LV_map.

Section section_EP_EV_map.

Definition
  EP_EV_map_ef EP EP' EV EV' LV L (f₁ : EP → EP') (f₂ : EV → EV')
  (e : ef EP EV LV L) :
  EP_map_ef f₁ (EV_map_ef f₂ e) = EV_map_ef f₂ (EP_map_ef f₁ e)
.
Proof.
destruct e ; crush.
Qed.

Hint Rewrite EP_EV_map_ef.

Fixpoint
  EP_EV_map_eff EP EP' EV EV' LV L (f₁ : EP → EP') (f₂ : EV → EV')
  (E : eff EP EV LV L) {struct E} :
  EP_map_eff f₁ (EV_map_eff f₂ E) = EV_map_eff f₂ (EP_map_eff f₁ E)
.
Proof.
destruct E ; crush.
Qed.

Hint Rewrite EP_EV_map_eff.

Fixpoint
  EP_EV_map_it EP EP' EV EV' LV L (f₁ : EP → EP') (f₂ : EV → EV')
  κ (N : it EP EV LV L κ) {struct N} :
  EP_map_it f₁ (EV_map_it f₂ N) = EV_map_it f₂ (EP_map_it f₁ N)
.
Proof.
destruct N ; crush.
Qed.

Hint Rewrite EP_EV_map_it.

Fixpoint
  EP_EV_map_ty EP EP' EV EV' LV L (f₁ : EP → EP') (f₂ : EV → EV')
  (T : ty EP EV LV L) {struct T} :
  EP_map_ty f₁ (EV_map_ty f₂ T) = EV_map_ty f₂ (EP_map_ty f₁ T)
with
  EP_EV_map_ms EP EP' EV EV' LV L (f₁ : EP → EP') (f₂ : EV → EV')
  (σ : ms EP EV LV L) {struct σ} :
  EP_map_ms f₁ (EV_map_ms f₂ σ) = EV_map_ms f₂ (EP_map_ms f₁ σ)
.
Proof.
+ destruct T ; crush.
+ destruct σ ; crush.
Qed.

Hint Rewrite EP_EV_map_ty.
Hint Rewrite EP_EV_map_ms.

Fixpoint
  EP_EV_map_is EP EP' EV EV' LV L (f₁ : EP → EP') (f₂ : EV → EV')
  (Σ : is EP EV LV L) {struct Σ} :
  EP_map_is f₁ (EV_map_is f₂ Σ) = EV_map_is f₂ (EP_map_is f₁ Σ)
.
Proof.
destruct Σ ; crush.
Qed.

End section_EP_EV_map.