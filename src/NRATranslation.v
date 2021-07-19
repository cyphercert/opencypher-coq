From Coq Require Import String.
From Coq Require Import List.

From OpencypherCoq Require Import Cypher.
From OpencypherCoq Require Import ForeignGraphRuntime.

From Qcert Require Import NRAEnv.Lang.NRAEnv.
From Qcert Require Import Data.Model.Data.
From Qcert Require Import Operators.UnaryOperators.
From Qcert Require Import Operators.BinaryOperators.

Definition dot (s : string) : nraenv -> nraenv := NRAEnvUnop (OpDot s).

(* Definition all (bs : nraenv) : nraenv := *)

Open Scope string_scope.

Definition const_coll : list data -> nraenv :=
  fold_right (fun x => NRAEnvBinop OpBagUnion (NRAEnvConst x)) (NRAEnvConst (dcoll nil)).

(* Definition const_nat (n : nat) : nraenv := *)
(*   NRAEnvConst (dnat (BinInt.Z.of_nat n)). *)

Definition map_rename_rec (s1 s2:string) (e:nraenv) : nraenv :=
  NRAEnvMap ((NRAEnvBinop OpRecConcat)
                ((NRAEnvUnop (OpRec s2)) ((NRAEnvUnop (OpDot s1)) NRAEnvID))
                ((NRAEnvUnop (OpRecRemove s1)) NRAEnvID)) e.

Fixpoint pattern_to_nraenv (p : Pattern.t) : nraenv :=
  match p with
  | Pattern.vertex vname vlabels =>
      map_rename_rec "vertex" vname
        (NRAEnvSelect
          (NRAEnvBinop OpEqual
            (const_coll nil)
            ((NRAEnvBinop OpBagDiff
              (const_coll (map (fun l => drec (("label", dstring l) :: nil)) vlabels))
              (dot "labels" (dot "vertex" NRAEnvID)))))
          (NRAEnvGetConstant "vertices"))
  | Pattern.edge pattern ename etype edirection wname wlabels =>
    match pattern with 
    | Pattern.vertex vname vlabels =>
        NRAEnvJoin 
          (match edirection with
          | Pattern.OUT => dot "src" (dot ename NRAenvID) =? dot "id" (dot vname NRAenvID)
          | Pattern.IN => dot "trg" (dot ename NRAenvID) =? dot "id" (dot vname NRAenvID)
          | Pattern.BOTH => 
            match (dot "src" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID)) with
            | dbool true =>  dot "trg" (dot ename NRAenvID) =? dot "id" (dot vname NRAenvID)
            | dbool false => dot "src" (dot ename NRAenvID) =? dot "id" (dot vname NRAenvID)) 
          (pattern_to_nraenv pattern)
          (NRAEnvJoin 
            (match edirection with
            | Pattern.OUT => dot "trg" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID)
            | Pattern.IN => dot "src" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID)
            | Pattern.BOTH => NRAEnvBinOp OpOr (dot "src" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID))
              dot "trg" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID))
            (map_rename_rec "edge" ename
              (NRAEnvSelect
                (NRAEnvBinop OpEqual
                  (const_coll nil)
                  ((NRAEnvBinop OpBagDiff
                    (dot "type" (dot "edge" NRAEnvID))
                    (const_coll (drec (("type", dstring etype) :: nil)) etype))))
                (NRAEnvGetConstant "edges")))
            (pattern_to_nraenv (Pattern.vertex wname wlabels))) 
    | Pattern.edge pattern' ename' etype' edirection' wname' wlabels => 
        NRAEnvJoin 
          (match edirection with
          | Pattern.OUT => dot "src" (dot ename NRAenvID) =? dot "id" (dot wname' NRAenvID)
          | Pattern.IN => dot "trg" (dot ename NRAenvID) =? dot "id" (dot wname' NRAenvID)
          | Pattern.BOTH => 
            match (dot "src" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID)) with
            | dbool true =>  dot "trg" (dot ename NRAenvID) =? dot "id" (dot wname' NRAenvID)
            | dbool false => dot "src" (dot ename NRAenvID) =? dot "id" (dot wname' NRAenvID)) 
          (pattern_to_nraenv pattern)
          (NRAEnvJoin 
            (match edirection with
            | Pattern.OUT => dot "trg" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID)
            | Pattern.IN => dot "src" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID)
            | Pattern.BOTH => NRAEnvBinOp OpOr (dot "src" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID))
              dot "trg" (dot ename NRAenvID) =? dot "id" (dot wname NRAenvID))
            (map_rename_rec "edge" ename
              (NRAEnvSelect
                (NRAEnvBinop OpEqual
                  (const_coll nil)
                  ((NRAEnvBinop OpBagDiff
                    (dot "type" (dot "edge" NRAEnvID))
                    (const_coll (drec (("type", dstring etype) :: nil)) etype))))
                (NRAEnvGetConstant "edges")))
            (pattern_to_nraenv (Pattern.vertex wname wlabels)))
      | (*In case when we have multiedge, we use behavior from edge case.*)
  | _ => NRAEnvConst dunit
  end.

(* Fixpoint compute_pattern (pattern : Pattern.t) (graph : PropertyGraph.t) := *)
(*   match pattern with *)
(*   | Pattern.vertex vname vlabels => GRA_operations.get_vertices vname vlabels graph *)
(*   | Pattern.edge pattern ename etype edirection wname wlabels => GRA_operations.get_edges  *)
(*                                                                   pattern ename etype edirection wname wlabels graph *)
(*   | Pattern.multiedge pattern enames etype low up vnames wname vlabels => GRA_operations.transitive_get_edges  *)
(*                                                                             pattern enames etype low up vnames wname vlabels graph *)
(*   end. *)

(* Fixpoint compute_clause (clause : Clause.t) (graph : PropertyGraph.t) := *)
(*   match clause with *)
(*   | MATCH patterns => match patterns with *)
(*     | [] => NRAEnvConst dunit *)
(*     | head :: tail => match tail with  *)
(*       | [] => compute_pattern head graph *)
(*       | head' :: tail' => NRAEnvJoin (compute_pattern head graph) (compute_clause (MATCH tail) graph) *)
(*       end *)
(*     end *)
(*   | WITH pexpr => RelationOperation.projection pexpr *)
(*   end. *)

(* Fixpoint compute_query (query : Query.t) (graph : PropertyGraph.t) := *)
(*   match query.(clauses) with *)
(*   | [] => NRAEnvConst dcol (drec ) *)
(*   | head :: tail => NRAEnvNaturalJoin (compute_clause head graph) (compute_query tail graph) *)
(*   end. *)
