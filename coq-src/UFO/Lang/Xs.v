Require Import Syntax.
Set Implicit Arguments.

Implicit Types EP EV LV V L : Set.

(** Extract free label identifiers *)

Definition Xs_lid L (ι : lid L) :=
match ι with
| lid_f X => \{ X }
| _ => \{}
end.

Definition Xs_lbl LV L (ℓ : lbl LV L) :=
match ℓ with
| lbl_id ι => Xs_lid ι
| _ => \{}
end.

Definition Xs_ef EP EV LV L (e : ef EP EV LV L ) :=
match e with
| ef_lbl ℓ => Xs_lbl ℓ
| _ => \{}
end.

Fixpoint Xs_eff EP EV LV L (E : eff EP EV LV L) :=
match E with
| e :: E => Xs_ef e \u Xs_eff E
| _ => \{}
end.

Fixpoint Xs_it EP EV LV L κ (N : it EP EV LV L κ) :=
match N with
| it_name _ => \{}
| it_inst N E => Xs_it N \u Xs_eff E
end.

Fixpoint
Xs_ty EP EV LV L (T : ty EP EV LV L) :=
  match T with
  | 𝟙 => \{}
  | ty_it N ℓ => Xs_it N \u Xs_lbl ℓ
  | ty_cont T₁ E₁ T₂ E₂ =>
      Xs_ty T₁ \u Xs_eff E₁ \u Xs_ty T₂ \u Xs_eff E₂
  | ty_ms σ ℓ =>
      Xs_ms σ \u Xs_lbl ℓ
  end
with
Xs_ms EP EV LV L (σ : ms EP EV LV L) :=
  match σ with
  | ms_ev σ => Xs_ms σ
  | ms_lv σ => Xs_ms σ
  | ms_tm T σ => Xs_ty T \u Xs_ms σ
  | ms_res T E => Xs_ty T \u Xs_eff E
  end
.

Fixpoint
  Xs_md EV LV V L (m : md EV LV V L) :=
  match m with
  | md_ev m => Xs_md m
  | md_lv m => Xs_md m
  | md_tm m => Xs_md m
  | md_res t => Xs_tm t
  end
with
  Xs_ktx EV LV V L (K : ktx EV LV V L) :=
  match K with
  | ktx_hole => \{}
  | ktx_down K Y =>
      Xs_ktx K \u \{Y}
  | ktx_up K =>
      Xs_ktx K
  | ktx_op K =>
      Xs_ktx K
  | ktx_let K t =>
      Xs_ktx K \u Xs_tm t
  | ktx_throw K t =>
      Xs_ktx K \u Xs_tm t
  | ktx_app_eff K E =>
      Xs_ktx K \u Xs_eff E
  | ktx_app_lbl K ℓ =>
      Xs_ktx K \u Xs_lbl ℓ
  | ktx_app_tm1 K t =>
      Xs_ktx K \u Xs_tm t
  | ktx_app_tm2 K v =>
      Xs_ktx K \u Xs_val v
  end
with
  Xs_val EV LV V L (v : val EV LV V L) :=
  match v with
  | val_unit => \{}
  | val_var x => \{}
  | val_cont K => Xs_ktx K
  | val_md m id => Xs_md m \u Xs_lid id
  | val_fix m id => Xs_md m \u Xs_lid id
  end
with
  Xs_tm EV LV V L (t : tm EV LV V L) :=
  match t with
  | tm_val v => Xs_val v
  | tm_op t => Xs_tm t
  | ⇧ t => Xs_tm t
  | ⬇ t => Xs_tm t
  | ⇩ X t => Xs_tm t \u \{X}
  | tm_let s t => Xs_tm s \u Xs_tm t
  | tm_throw t s => Xs_tm t \u Xs_tm s
  | tm_app_eff t E => Xs_tm t \u Xs_eff E
  | tm_app_lbl t ℓ => Xs_tm t \u Xs_lbl ℓ
  | tm_app_tm t s => Xs_tm t \u Xs_tm s
  end
.
