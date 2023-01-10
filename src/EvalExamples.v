Require Import String.

Require Import List.
Require Import BinNums.
Require Import BinInt.
Import ListNotations.


Require Import Cypher.
Import PropertyGraph.
Require Import Utils.
Require Import Lia.

From RelationAlgebra Require Import syntax matrix bmx ordinal.
From RelationAlgebra Require Import monoid boolean prop sups bmx.


Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

(** Tests for database model **)

Module DataExamples.
Definition property_graph1 : PropertyGraph.t :=
    {| PropertyGraph.vertices := [1; 2; 3; 4; 5; 6]
    ;  PropertyGraph.edges    := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12]
    ;  PropertyGraph.ends     := fun e => match e with
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
    ; PropertyGraph.vlabels := fun v => match v with
                            | 1 => ["USER"]
                            | 2 => ["HOST"]
                            | 3 => ["USER"; "HOST"]
                            | 4 => ["USER"; "HOST"]
                            | 5 => ["USER"; "GUEST"]
                            | 6 => ["USER"; "GUEST"]
                            | _ => []
                            end
    ; PropertyGraph.elabel  := fun e => match e with
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
    ; PropertyGraph.vprops    := fun _ => nil
    ; PropertyGraph.eprops    := fun _ => nil
    |}.

  Definition vertex_pattern1 : Pattern.pvertex :=
    {| Pattern.vlabels := ["USER"];
       Pattern.vname   := None;
       Pattern.vprops  := nil |}.

  Definition edge_pattern1 : Pattern.pedge := 
    {| Pattern.ename   := None;
       Pattern.elabels := nil;
       Pattern.eprops  := nil;
       Pattern.edir    := Pattern.BOTH |}.

  Definition pattern1 : Pattern.t :=
    Pattern.hop (Pattern.start vertex_pattern1) edge_pattern1 vertex_pattern1.

  Definition length : positive := Pos.of_nat (Datatypes.length(PropertyGraph.vertices property_graph1)).
  Definition length_nat : nat := Datatypes.length(PropertyGraph.vertices property_graph1).

  Lemma lt1 : (1 < length_nat)%ltb.
  Proof.
    unfold length_nat. simpl. lia.
  Qed.

  Lemma lt2 : (2 < length_nat)%ltb.
  Proof.
    unfold length_nat. simpl. lia. Qed.

  Definition num {length_nat: nat} : ord DataExamples.length_nat := @Ord DataExamples.length_nat 1 lt1.
  Definition num2 {length_nat: nat} : ord DataExamples.length_nat := @Ord DataExamples.length_nat 2 lt2.

 (*Let pattern1_test1 {num : ord DataExamples.length_nat} : DataExamples.evaluated (@Ord DataExamples.length_nat 1 lt1) (@Ord DataExamples.length_nat 1 lt1)  = true.
  Proof. unfold evaluated. simpl. Qed.* * *)

  Definition vertex_pattern2 : Pattern.pvertex :=
    {| Pattern.vname   := None;
       Pattern.vlabels := ["HOST"];
       Pattern.vprops  := nil |}.

  Definition edge_pattern2 : Pattern.pedge :=
    {| Pattern.ename   := None;
       Pattern.elabels := ["FRIEND_OF"];
       Pattern.eprops  := nil;
       Pattern.edir    := Pattern.BOTH; |}.

  Definition pattern2 : Pattern.t :=
    Pattern.hop (Pattern.start vertex_pattern1) edge_pattern2 vertex_pattern2.

  Lemma lt4 : (4 < length_nat)%ltb.
  Proof.
    unfold length_nat. simpl. lia.
  Qed.

  Definition num4 {length_nat: nat} : ord DataExamples.length_nat := @Ord DataExamples.length_nat 4 lt4.

  Lemma lt5 : (5 < length_nat)%ltb.
  Proof.
    unfold length_nat. simpl. lia.
  Qed.

  Definition num5 {length_nat: nat} : ord DataExamples.length_nat := @Ord DataExamples.length_nat 5 lt5.

  Definition edge_pattern3 : Pattern.pedge :=
    {| Pattern.ename   := None;
       Pattern.elabels := ["KNOWS"];
       Pattern.eprops  := nil;
       Pattern.edir    := Pattern.BOTH |}.

  Definition pattern3 : Pattern.t :=
    Pattern.hop (Pattern.start vertex_pattern1) edge_pattern3 vertex_pattern2.

End DataExamples.
