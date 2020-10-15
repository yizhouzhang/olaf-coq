Require Import UFO.Rel.Definitions.
Require Import UFO.Rel.Adequacy.
Require Import UFO.Rel.Parametricity.
Require Import UFO.Lang.Xs.
Require Import UFO.Lang.OperationalFacts.
Require Import UFO.Lang.Static.

Section section_type_safety.

Hint Rewrite from_list_nil.
Hint Resolve LibList.noduplicates_nil.

Theorem type_safety t T ξ' t' :
  wf_tm empty ∅→ t T [] →
  Xs_tm t = \{} →
  step_refl_tran ⟨[], t⟩ ⟨ξ', t'⟩ →
  (∃ v : val0, t' = v) ∨ (∃ ξ'' t'', step ⟨ξ', t'⟩ ⟨ξ'', t''⟩).
Proof.
intros WF_t Closed_t StepRT.
apply step_refl_tran_to_step_n in StepRT ; destruct StepRT as [n Step_n].
eapply 𝓞_left_is_sound with (cfg := ⟨[], t⟩) (cfg' := ⟨ξ', t'⟩) (ζ := []) ;
try reflexivity ; try eassumption ; crush.
eapply n_adequacy.
+ split ; rewrite dom_empty ; apply subset_empty_l.
+ eapply LN_parametricity_tm ; [ constructor | intro ; auto | eauto ].
Qed.

End section_type_safety.
