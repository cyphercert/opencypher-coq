From Coq Require Import String.
From Coq Require Import List.
Import ListNotations.

From OpencypherCoq Require Import Cypher.
From OpencypherCoq Require Import ForeignGraphRuntime.

From Qcert Require Import NRAEnv.Lang.NRAEnv.
From Qcert Require Import Data.Model.Data.
From Qcert Require Import Operators.UnaryOperators.
From Qcert Require Import Operators.BinaryOperators.

Open Scope string_scope.
Open Scope list_scope.
Open Scope nraenv_scope.

Definition dot (s : string) : nraenv -> nraenv := NRAEnvUnop (OpDot s).

Definition const_coll : list data -> nraenv :=
  fold_right (fun x => NRAEnvBinop OpBagUnion (NRAEnvUnop OpBag (NRAEnvConst x))) (NRAEnvConst (dcoll nil)).

Definition const_tcoll (cname : string) (ds : list data) : nraenv := Eval hnf in
  const_coll (map (fun d => drec [(cname, d)]) ds).

(* Definition const_nat (n : nat) : nraenv := *)
(*   NRAEnvConst (dnat (BinInt.Z.of_nat n)). *)

Definition map_rename_rec (s1 s2:string) (e:nraenv) : nraenv :=
  NRAEnvMap ((NRAEnvBinop OpRecConcat)
                ((NRAEnvUnop (OpRec s2)) ((NRAEnvUnop (OpDot s1)) NRAEnvID))
                ((NRAEnvUnop (OpRecRemove s1)) NRAEnvID)) e.

 Definition get_last_vname (p : Pattern.t) : string :=
   match p with
   | Pattern.pvertex name _ => name
   | Pattern.pedge _ _ _ _ name _ => name
   | Pattern.pmultiedge _ _ _ _ _ _ name _ => name
   end.

Module NRAEnvNotations.

  Notation "x =% y" := (NRAEnvBinop OpEqual x y) (at level 70, no associativity) : nraenv_scope.
  Notation "x .% y" := (dot y x) (at level 30) : nraenv_scope.

End NRAEnvNotations.
Import NRAEnvNotations.

Definition vertex_to_nraenv (vp : Pattern.vpat) : nraenv :=
  match vp with
  | Pattern.vertex vname vlabels =>
      map_rename_rec "vertex" vname
        (NRAEnvSelect
          (NRAEnvBinop OpEqual
            (const_coll nil)
            ((NRAEnvBinop OpBagDiff
              (const_tcoll "label" (map dstring vlabels))
              (NRAEnvID.%"vertex".%"labels"))))
          (NRAEnvGetConstant "vertices"))
  end.

Definition edge_to_nraenv := term.

Definition expand (vname : string) (src : nraenv) (ename : string) (etype : list string)
  (wname : string) (trg : nraenv) : nraenv :=
  NRAEnvSelect (NRAEnvID.%ename.%"src" =% NRAEnvID.%vname.%"id")
    (NRAEnvNaturalJoin 
      src
      (NRAEnvSelect (dot "trg" (dot ename NRAEnvID) =% dot "id" (dot wname NRAEnvID))
        (NRAEnvNaturalJoin
          (map_rename_rec "edge" ename
            (NRAEnvSelect
              (NRAEnvBinop 
                OpContains (const_coll (map dstring etype)) (dot "type" (dot "edge" NRAEnvID)))
              (NRAEnvGetConstant "edges")))
          trg))).

(* Maybe this will work for no repeated edge semantics. *)
Definition unique_expand (vname : string) (src : nraenv) (ename : string) (etype : list label) 
  (wname : string) (trg : nraenv) (enames : list string) : nraenv :=
  let rel := expand vname src ename etype wname trg in 
  NRAEnvSelect
    ((NRAEnvProject enames rel) == (NRAEnvUnop OpDistinct (NRAEnvProject enames rel)))
    (rel).

Fixpoint get_enames (p : Pattern.t) : list string :=
  match p with 
  | Pattern.vertex _ _=> nil
  | Pattern.edge pattern ename _ _ _ _ => (ename :: get_enames (pattern))
  | Pattern.multiedge pattern enames _ _ _ _ _ _ => 
    (app enames (get_enames (pattern)))
  end.

Fixpoint pattern_to_nraenv (p : Pattern.t) : nraenv :=
  match p with
  | Pattern.vertex vname vlabels =>
      vertex_to_nraenv vname vlabels
  (* No repeated edge semantics. *)
  | Pattern.edge pattern ename etype edirection wname wlabels =>
      let vname := get_vname pattern in
      match edirection with 
      | Pattern.OUT => expand vname (pattern_to_nraenv pattern) ename etype wname (vertex_to_nraenv wname wlabels)
        (*unique_expand vname (pattern_to_nraenv pattern) ename etype wname (vertex_to_nraenv wname wlabels) (ename :: (get_enames pattern))*)
      | Pattern.IN => expand wname (vertex_to_nraenv wname wlabels) ename etype vname (pattern_to_nraenv pattern)
        (*unique_expand wname (vertex_to_nraenv wname wlabels) ename etype vname (pattern_to_nraenv pattern) (ename :: (get_enames pattern))*)
      | Pattern.BOTH =>
        (NRAEnvBinop OpBagUnion
          (expand vname (pattern_to_nraenv pattern) ename etype wname (vertex_to_nraenv wname wlabels))
          (*(unique_expand vname (pattern_to_nraenv pattern) ename etype wname (vertex_to_nraenv wname wlabels) (ename :: (get_enames pattern)))*)
          (expand wname (vertex_to_nraenv wname wlabels) ename etype vname (pattern_to_nraenv pattern)))
          (*(unique_expand wname (vertex_to_nraenv wname wlabels) ename etype vname (pattern_to_nraenv pattern) (ename :: (get_enames pattern))))*)
      end
  | _ => NRAEnvConst dunit
  end.

Close Scope string_scope.
Close Scope nraenv_scope.

(* Fixpoint clause_to_nraenv (clause : Clause.t) : nraenv := *)
(*   match clause with *)
(*   | MATCH patterns => match patterns with *)
(*     | [] => NRAEnvConst dcoll (dunit) *)
(*     | head :: tail => NRAEnvNaturalJoin (pattern_to_nraenv head) (clause_to_nraenv (MATCH tail)) *)
(*     end *)
(*   | WITH pexpr => (*Where is relation?*) *)
(*   end. *)

(* Fixpoint query_to_nraenv (query : Query.t) : nraenv := *)
(*   match query.(clauses) with *)
(*   | [] => NRAEnvConst dcoll (dunit) *)
(*   | head :: tail => NRAEnvNaturalJoin (clause_to_nraenv head) (query_to_nraenv tail) *)
(*   end. *)
