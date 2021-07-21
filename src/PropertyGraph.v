From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import Nat.
Import ListNotations.

From hahn Require Import Hahn.

Module Property.
  Inductive t := 
  | p_int (i : nat)
  | p_string (s : string)
  | p_empty
  .
  
  Definition name := string.
  
  Definition eqb (p p' : t) : bool :=
    match p, p' with
    | p_int i, p_int i' => Nat.eqb i i'
    | p_string s, p_string s' => String.eqb s s'
    | p_empty, p_empty => true
    | _, _ => false
    end.

  Lemma eqP : Equality.axiom eqb.
  Proof.
    unfold eqb. red. ins. desf; try constructor; desf.
    all: apply Bool.iff_reflect.
    all: symmetry; etransitivity.
    all: try apply PeanoNat.Nat.eqb_eq; try apply String.eqb_eq.
    all: split; intros AA; subst; auto.
    all: inv AA.
  Qed.
End Property.

Module PropertyGraph.
  Definition vertex    := nat.
  Definition edge      := nat.
  Definition label     := string.

  Record t :=
    mk { vertices : list vertex;
         edges    : list edge;
         st       : edge -> vertex * vertex;
         vlab     : vertex -> list label;
         elab     : edge -> label;
         vprops   : list (Property.name * (vertex -> Property.t)); 
         eprops   : list (Property.name * (edge   -> Property.t)); 
      }.

Open Scope string_scope.

(*Default values*)
Definition property_graph1 : t :=
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
  ; vprops    := [ ("name", fun v => Property.p_string match v with
                                                       | 1 => "Dave"
                                                       | 2 => "Ron"
                                                       | 3 => "Renna"
                                                       | 4 => "Shradha"
                                                       | 5 => "David"
                                                       | 6 => "Rohan"
                                                       | _ => ""
                                                       end)
                 ; ("age", fun v => Property.p_int match v with
                                                   | 1 => 42
                                                   | 2 => 32
                                                   | 3 => 39
                                                   | 4 => 29
                                                   | 5 => 23
                                                   | 6 => 52
                                                   | _ => 0
                                                   end)
                 ]
  ; eprops    := [ ("since", fun e => if Nat.eqb 5 e then Property.p_empty
                                      else Property.p_string match e with
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
End PropertyGraph.

