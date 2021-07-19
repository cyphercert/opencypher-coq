From Qcert.NRAEnv.Lang Require Import NRAEnv.
From Qcert.Data Require Import ForeignRuntime.
From Qcert.Data.Operators Require UnaryOperatorsSem.
Require Import String.

Inductive foreign_graph_data_model : Set := Vertex (n : nat)
                                          | Edge (n : nat).
Scheme Equality for foreign_graph_data_model.

Inductive fgdm_normalized (fgdm : foreign_graph_data_model) : Prop :=
  fgdm_always_normalized.

Definition fgdm_tostring (fgdm : foreign_graph_data_model) :=
  match fgdm with
  | Vertex n => ("vertex_" ++ Digits.nat_to_string10 n)%string
  | Edge n   => ("edge_"   ++ Digits.nat_to_string10 n)%string
  end.

Program Instance foreign_graph_data : foreign_data :=
  mk_foreign_data foreign_graph_data_model _ fgdm_normalized _ _ _ _.
Next Obligation.
  red; unfold Equivalence.equiv, RelationClasses.complement.
  exact foreign_graph_data_model_eq_dec.
Defined.
Next Obligation.
  apply fgdm_always_normalized.
Defined.
Next Obligation.
  constructor; exact fgdm_tostring.
Defined.

(* Need to rewrite this *)
Program Instance foreign_graph_operators : foreign_operators :=
  mk_foreign_operators foreign_graph_data
                       Empty_set _ _ _ _
                       Empty_set _ _ _ _
                       UnaryOperatorsSem.defaultDataToString
                       UnaryOperatorsSem.defaultDataToString.
Next Obligation.
  constructor.
  red.
  destruct x, y.
Defined.
Next Obligation.
  constructor; intros [].
Defined.
Next Obligation.
  destruct op.
Defined.
Next Obligation.
  destruct op.
Defined.
Next Obligation.
  intros [].
Defined.
Next Obligation.
  constructor; intros [].
Defined.
Next Obligation.
  destruct op.
Defined.
Next Obligation.
  destruct op.
Defined.

Program Instance foreign_graph_runtime : foreign_runtime :=
  {| foreign_runtime_data := foreign_graph_data;
     foreign_runtime_operators := foreign_graph_operators
  |}.
