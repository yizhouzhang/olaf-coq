Require Import UFO.Lang.Syntax.
Require Import UFO.Lang.Bindings_map.
Require Import TLC.LibReflect.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

Local Obligation Tactic := idtac.

Program Definition fsub_lid L (id' : lid L) (X : var) (id : lid L) : lid L :=
  match id' with
  | lid_f Y => _
  | lid_b _ => id'
  end.
Next Obligation.
Proof.
intros L id' X id Y G.
destruct (var_compare X Y) eqn:Heq ;
  rewrite var_compare_eq in Heq ;
  rew_bool_eq in Heq ; [ apply id | apply id' ].
Defined.

Definition fsub_lbl LV L (ℓ : lbl LV L) (X : var) (id : lid L) : lbl LV L :=
  match ℓ with
  | lbl_var _ => ℓ
  | lbl_id id' => lbl_id (fsub_lid id' X id)
  end.

Definition
  fsub_ef EP EV LV L (e : ef EP EV LV L) (X : var) (id : lid L) : ef EP EV LV L :=
  match e with
  | ef_par _ => e
  | ef_var _ => e
  | ef_lbl ℓ => ef_lbl (fsub_lbl ℓ X id)
  end
.

Fixpoint
  fsub_eff EP EV LV L (E : eff EP EV LV L) (X : var) (id : lid L) : eff EP EV LV L :=
  match E with
  | [] => []
  | e :: E' => (fsub_ef e X id) :: (fsub_eff E' X id)
  end
.

Fixpoint
  fsub_it EP EV LV L κ (N : it EP EV LV L κ) (X : var) (id : lid L) : it EP EV LV L κ :=
  match N with
  | it_name 𝔽 => it_name 𝔽
  | it_inst N E => it_inst (fsub_it N X id) (fsub_eff E X id)
  end
.

Fixpoint
  fsub_ms EP EV LV L (σ : ms EP EV LV L) (X : var) (id : lid L) : ms EP EV LV L :=
  match σ with
  | ms_ev σ => ms_ev (fsub_ms σ X id)
  | ms_lv σ => ms_lv (fsub_ms σ X id)
  | ms_tm T σ => ms_tm (fsub_ty T X id) (fsub_ms σ X id)
  | ms_res T E => ms_res (fsub_ty T X id) (fsub_eff E X id)
  end
with
  fsub_ty EP EV LV L (T : ty EP EV LV L) (X : var) (id : lid L) : ty EP EV LV L :=
  match T with
  | 𝟙 => 𝟙
  | ty_it N ℓ => ty_it (fsub_it N X id) (fsub_lbl ℓ X id)
  | ty_ms σ ℓ => ty_ms (fsub_ms σ X id) (fsub_lbl ℓ X id)
  | ty_cont Ta Ea Tb Eb =>
    ty_cont (fsub_ty Ta X id) (fsub_eff Ea X id) (fsub_ty Tb X id) (fsub_eff Eb X id)
  end
.

Fixpoint
  fsub_md EV LV V L (m : md EV LV V L) (X : var) (id : lid L) : md EV LV V L :=
  match m with
  | md_ev m => md_ev (fsub_md m X id)
  | md_lv m => md_lv (fsub_md m X id)
  | md_tm m => md_tm (fsub_md m X id)
  | md_res t => md_res (fsub_tm t X id)
  end
with
  fsub_ktx EV LV V L (K : ktx EV LV V L) (X : var) (id : lid L) : ktx EV LV V L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K Y =>
      ktx_down (fsub_ktx K X id) Y
  | ktx_up K =>
      ktx_up (fsub_ktx K X id)
  | ktx_op K =>
      ktx_op (fsub_ktx K X id)
  | ktx_let K t =>
      ktx_let (fsub_ktx K X id) (fsub_tm t X id)
  | ktx_throw K t =>
      ktx_throw (fsub_ktx K X id) (fsub_tm t X id)
  | ktx_app_eff K E =>
      ktx_app_eff (fsub_ktx K X id) (fsub_eff E X id)
  | ktx_app_lbl K ℓ =>
      ktx_app_lbl (fsub_ktx K X id) (fsub_lbl ℓ X id)
  | ktx_app_tm1 K t =>
      ktx_app_tm1 (fsub_ktx K X id) (fsub_tm t X id)
  | ktx_app_tm2 K v =>
      ktx_app_tm2 (fsub_ktx K X id) (fsub_val v X id)
  end
with
  fsub_val EV LV V L (v : val EV LV V L) (X : var) (id : lid L) : val EV LV V L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_cont K => fsub_ktx K X id
  | val_md m id' => val_md (fsub_md m X id) (fsub_lid id' X id)
  | val_fix m id' => val_fix (fsub_md m X id) (fsub_lid id' X id)
  end
with
  fsub_tm EV LV V L (t : tm EV LV V L) (X : var) (id : lid L) : tm EV LV V L :=
  match t with
  | tm_val v => fsub_val v X id
  | tm_op t => tm_op (fsub_tm t X id)
  | ⇧ t => ⇧ (fsub_tm t X id)
  | ⬇ t => ⬇ (fsub_tm t X (L_shift_lid id))
  | ⇩ X t => ⇩ X (fsub_tm t X id)
  | tm_let s t => tm_let (fsub_tm s X id) (fsub_tm t X id)
  | tm_throw t s => tm_throw (fsub_tm t X id) (fsub_tm s X id)
  | tm_app_eff t E => tm_app_eff (fsub_tm t X id) (fsub_eff E X id)
  | tm_app_lbl t ℓ => tm_app_lbl (fsub_tm t X id) (fsub_lbl ℓ X id)
  | tm_app_tm t s => tm_app_tm (fsub_tm t X id) (fsub_tm s X id)
  end
.
