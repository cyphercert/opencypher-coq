Require Import String.
Require Import List.
Require Import BinNums.
Require Import BinInt.
Import ListNotations.

Require Import Cypher.
Require Import PropertyGraph.
Require Import PGTableExtraction.
Require Import KleeneTranslation.
Require Import PGMatrixExtraction.


Import PropertyGraph.
Import Property.

From RelationAlgebra Require Import syntax matrix bmx ordinal.

Set Implicit Arguments.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.
(*Local Open Scope nraenv_scope.*)

Module DataExamples.
  Definition property_graph1 : PropertyGraph.t :=
    {| vertices := [1; 2; 3; 4; 5; 6]
    ;  edges    := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]
    ;  st       := fun e => match e with
                            | 1  => (2, 1)
                            | 2  => (1, 3)
                            | 3  => (3, 2)
                            | 4  => (2, 4)
                            | 5  => (5, 2)
                            | 6  => (2, 5)
                            | 7  => (3, 4)
                            | 8  => (4, 3)
                            | 9  => (4, 5)
                            | 10 => (5, 4)
                            | 11 => (6, 3)
                            | 12 => (5, 6)
                            | _  => (0, 0)
                            end
    ; vlab      := fun v => match v with
                            | 1 => ["USER"]
                            | 2 => ["USER"]
                            | 3 => ["USER"; "HOST"]
                            | 4 => ["USER"; "HOST"]
                            | 5 => ["USER"; "GUEST"]
                            | 6 => ["USER"; "GUEST"]
                            | _ => []
                            end
    ; elab      := fun e => match e with
                            | 1  => "FRIEND_OF"
                            | 2  => "KNOWS"
                            | 3  => "KNOWS"
                            | 4  => "KNOWS"
                            | 5  => "FRIEND_OF"
                            | 6  => "FRIEND_OF"
                            | 7  => "FRIEND_OF"
                            | 8  => "FRIEND_OF"
                            | 9  => "KNOWS"
                            | 10 => "KNOWS"
                            | 11 => "KNOWS"
                            | 12 => "FRIEND_OF"
                            | _  => ""
                            end
    ; vprops    := nil
    ; eprops    := nil
    |}.

  Definition vertex_pattern1 : Pattern.pvertex :=
    {| vlabels := ["USER"];
       vprops  := nil |}.

  Definition edge_pattern1 : Pattern.pedge := 
    {| elabels := nil;
       eprops  := nil;
       edir    := BOTH;
       enum    := 0;
       evertex := vertex_pattern1 |}.

 (* Definition vertex_pattern2 : Pattern.t :=
    (|"v"#"USER","HOST"|).

  Definition edge_pattern1 : Pattern.t :=
    (|"v"#"HOST"|)-["e"#"KNOWS"]->(|"w"#"GUEST"|).

  Definition edge_pattern2 := 
    (|"v"|)-["e"#"KNOWS"]-(|"w"#"GUEST"|).

  Definition complex_pattern := 
    (|"v1"|)-["e1"#"KNOWS"]->(|"v2"#"HOST"|)<-["e2"#"KNOWS"|"FRIEND_OF"]-(|"v3"#"GUEST","USER"|)*).
End DataExamples.
Import DataExamples.

(*Definition mk_const_env (pg : PropertyGraph.t) : bindings :=
  [ ("vertices", pg_extract_vtable pg)
  ; ("edges", pg_extract_etable pg)
  ]. *)

(*Definition eval_pattern (p : Pattern.t) (pg : PropertyGraph.t) : option data :=
  nraenv_eval_top nil (pattern_to_nraenv p) (mk_const_env pg).

Definition evals_to_sem (p : Pattern.t) (pg : PropertyGraph.t) : data -> Prop :=
  nraenv_sem nil (mk_const_env pg) (pattern_to_nraenv p) (drec nil) dunit.

Definition eval_in_kleene (n : positive) := eval (*A:*) Label 
                                                 (*s, t:*) (fun _ : Label => n) (fun _ : Label => n) 
                                                 (*X, f': ?*)
                                                 (*f:*) (e_var2matrix property_graph1) 
                                                 (*x:*) (pattern_to_matrix vertex_pattern1).
 *)
(* Compute (eval_pattern vertex_pattern1 property_graph1).
Compute (eval_pattern vertex_pattern2 property_graph1).
Compute (eval_pattern edge_pattern1 property_graph1).
Compute (eval_pattern edge_pattern2 property_graph1).
Compute (eval_pattern complex_pattern property_graph1). *)
