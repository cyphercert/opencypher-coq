Require Import BinNums.
Require Import BinInt.
Require Import List.
Require Import String.
Require Import Bool.
Import ListNotations.

Require Import Notations.
Require Import Ltac.
Require Import Logic.
(* From RelationAlgebra Require Import kleene boolean sups matrix.*)
From RelationAlgebra Require Import syntax matrix bmx ordinal.

Require Import Cypher.
Require Import PropertyGraph.
Import PropertyGraph.
Import Pattern.

Definition label_neq (a b : label) : bool := negb (String.eqb a b).
  
Fixpoint get_types (n : positive) (etypes : list label) (tr : bool) :=
  match etypes with
  | [] => e_zer n n
  | h :: tl => e_pls (get_types n tl tr) (if tr then e_cnv (e_var h) else e_var h)
  end.

Fixpoint k_edges (n : positive) (etypes : list label) (tr : bool) (k : nat) :=
  match k with 
  | O => e_one n
  | S k' => e_dot (get_types n etypes tr) (k_edges n etypes tr k')
  end.

Definition pvertex_to_matrix (n : positive) (vvar : string) (vlabels : list string): 
expr (fun _ : string => n) (fun _ : string => n) n n :=
  List.fold_left 
    (fun (m : expr (fun _ => n) (fun _  => n) n n) vlabel => e_dot (e_var vlabel) m)
    vlabels 
    (e_one n).

Fixpoint pattern_to_matrix (n : positive) (p : Pattern.t) :
  expr (fun _ : string => n) (fun _ : string => n) n n :=
  match p with 
  | pvertex vvar vlabels => pvertex_to_matrix n vvar vlabels    
  | pedge p evar etypes edir wvar wlabels =>
    let e := match edir with 
      | IN => get_types n etypes true
      | OUT => get_types n etypes false
      | BOTH => e_pls (get_types n etypes true) (get_types n etypes false)
      end in e_dot (e_dot (pattern_to_matrix n p) e) (pvertex_to_matrix n wvar wlabels) 
 | pmultiedge p evar etypes edir low up wvar wlabels =>
   let e := match up with 
     | None =>  match edir with
      | IN => e_dot (k_edges n etypes true (low - 1)) (e_itr (get_types n etypes true))
      | OUT =>  e_dot (k_edges n etypes false (low - 1)) (e_itr (get_types n etypes false))
      | BOTH => e_pls 
        (e_dot (k_edges n etypes true (low - 1)) (e_itr (get_types n etypes true)))
        (e_dot (k_edges n etypes false (low - 1)) (e_itr (get_types n etypes false)))
      end
     | Some up' => match edir with
      | IN => List.fold_right 
        (fun x y => e_pls x y) 
        (e_one n) 
        (map (fun k => k_edges n etypes true k) (List.seq low (up' - low)))
      | OUT => List.fold_right 
        (fun x y => e_pls x y) 
        (e_one n) 
        (map (fun k => k_edges n etypes false k) (List.seq low (up' - low)))
      | BOTH => e_pls 
        (List.fold_right 
          (fun x y => e_pls x y) 
          (e_one n) 
          (map (fun k => k_edges n etypes true k) (List.seq low (up' - low))))
        (List.fold_right 
          (fun x y => e_pls x y) 
          (e_one n) 
          (map (fun k => k_edges n etypes false k) (List.seq low up')))
      end
   end
   in e_dot (e_dot (pattern_to_matrix n p) e) (pvertex_to_matrix n wvar wlabels)
  end.
