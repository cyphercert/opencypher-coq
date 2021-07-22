From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import BinNums.
From Coq Require Import BinInt.
Import ListNotations.

From OpencypherCoq Require Import ForeignGraphRuntime.
From OpencypherCoq Require Import Cypher.
From OpencypherCoq Require Import PropertyGraph.
From OpencypherCoq Require Import PGTableExtraction.
From OpencypherCoq Require Import NRATranslation.

From Qcert Require Import Data.Model.Data.
From Qcert Require Import Lang.NRAEnv.
From Qcert Require Import BinaryOperators.

Import PropertyGraph.
Import Property.
Import PatternNotations.
Import NRAEnvNotations.
Local Open Scope pat_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope nraenv_scope.

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
    ; vprops    := [ ("name", fun v => p_string match v with
                                                        | 1 => "Dave"
                                                        | 2 => "Ron"
                                                        | 3 => "Renna"
                                                        | 4 => "Shradha"
                                                        | 5 => "David"
                                                        | 6 => "Rohan"
                                                        | _ => ""
                                                        end)
                  ; ("age", fun v => p_int match v with
                                                    | 1 => 42
                                                    | 2 => 32
                                                    | 3 => 39
                                                    | 4 => 29
                                                    | 5 => 23
                                                    | 6 => 52
                                                    | _ => 0
                                                    end)
                  ]
    ; eprops    := [ ("since", fun e => if 5 =? e then p_empty
                                        else p_string match e with
                                                              | 1  => "2012"
                                                              | 2  => "2018"
                                                              | 3  => "2000"
                                                              | 4  => "2011"
                                                              | 6  => "2001"
                                                              | 7  => "2015"

                                                              | 8  => "2015"
                                                              | 9  => "2009"
                                                              | 10 => "2006"
                                                              | 11 => "2007"
                                                              | 12 => "2012"
                                                              | _  => ""
                                                              end)
                  ]
    |}.

  Definition pattern1 : Pattern.t :=
  (|"v"#"USER"|).

  Definition pattern2 : Pattern.t :=
  (|"v"#"USER","HOST"|).

  Definition pattern3 : Pattern.t :=
  (|"v"#"HOST"|)-["e"#"KNOWS"]->(|"w"#"GUEST"|).


End DataExamples.
Import DataExamples.

Definition mk_const_env (pg : PropertyGraph.t) : bindings :=
  [ ("vertices", pg_extract_vtable pg)
  ; ("edges", pg_extract_etable pg)
  ].

Definition eval_pattern (p : Pattern.t) (pg : PropertyGraph.t) : option data :=
  nraenv_eval_top nil (pattern_to_nraenv p) (mk_const_env pg).

Definition evals_to_sem (p : Pattern.t) (pg : PropertyGraph.t) : data -> Prop :=
  nraenv_sem nil (mk_const_env pg) (pattern_to_nraenv p) (drec nil) dunit.

Compute (pattern_to_nraenv pattern3).

Compute (nraenv_eval_top nil (
(* ------------------------ *)

NRAEnvConst (dstring "kek") elem% const_coll [dstring "kek"]

(* NRAEnvBinop OpBagUnion *)
(*                                  (NRAEnvUnop UnaryOperators.OpBag *)
(*                                     (NRAEnvConst (dstring "KNOWS"))) *)
(*                                  (NRAEnvConst (dcoll [])) *)
(*                            NRAEnvMap *)
(*                            (NRAEnvUnop (UnaryOperators.OpDot "type") *)
(*                            (NRAEnvUnop (UnaryOperators.OpDot "edge") NRAEnvID)) *)
(*                            (NRAEnvGetConstant "edges") *)

(* (NRAEnvSelect *)
(*                         (NRAEnvUnop (UnaryOperators.OpDot "type") *)
(*                            (NRAEnvUnop (UnaryOperators.OpDot "edge") NRAEnvID) *)
(*                          elem% NRAEnvBinop OpBagUnion *)
(*                                  (NRAEnvUnop UnaryOperators.OpBag *)
(*                                     (NRAEnvConst (dstring "KNOWS"))) *)
(*                                  (NRAEnvConst (dcoll []))) (NRAEnvGetConstant "edges")) *)



(* ------------------------ *)
             ) (mk_const_env property_graph1)).

Compute (eval_pattern pattern3 property_graph1).


(* Lemma sem : evals_to_sem Pattern.pattern1 PropertyGraph.property_graph1 dunit. *)

(* Lemma evals : (eval_pattern Pattern.pattern1 PropertyGraph.property_graph1) = Some dunit. *)

(* From Mtac2 Require Import Mtac2. *)
(* Notation "[rl: ]" := rlnil. *)
(* Notation "[rl: x ; .. ; y ]" := (rlcons x (.. (rlcons y rlnil) ..)). *)
(* Notation RedAll := ([rl:RedBeta;RedDeltaC;RedDeltaX;RedDelta;RedZeta;RedMatch;RedFix]). *)
(* Import M. *)
(* Import M.notations. *)
(* From Mtac2 Require Tactics. *)
(* Import T. *)

(* Mtac Do ( *)
(*   let t := eval_pattern Pattern.pattern1 PropertyGraph.property_graph1 in *)
(*   let t := reduce (RedOneStep RedAll) t in *)
(*   print_term t *)
(* ). *)

(* Goal (eval_pattern Pattern.pattern1 PropertyGraph.property_graph1) = Some dunit. *)
(*   vm_compute. *)

(* Proof. *)
(*   red. *)
(*   vm_compute. *)

(* Proof. *)
(*   unfold eval_pattern. *)
(*   vm_compute (pg_extract_vtable _). *)
(*   vm_compute (pattern_to_nraenv _). *)
(*   assert (pattern_to_nraenv Pattern.pattern1 = NRAEnvID). *)
(*   cbv. *)
(*   (* Definition kek := pattern_to_nraenv Pattern.pattern1. *) *)
(*   remember (pattern_to_nraenv Pattern.pattern1) as expr. *)
(*   . *)
(*   vm_compute in Heqexpr. *)
(*   . *)
