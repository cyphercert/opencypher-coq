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
Require Import PGMatrixExtraction.

Definition types_to_expr (n : positive) (etypes : list label) (tr : bool) :
expr (fun _ : Label => n) (fun _ : Label => n) n n :=
  List.fold_right 
    (fun x (y : expr (fun _ => n) (fun _  => n) n n) => 
      e_pls (if tr then e_cnv (e_var (elabel x)) else e_var (elabel x)) y)
    (e_zer n n)
    etypes.

Definition labels_to_expr (n : positive) (vlabels : list label) : 
expr (fun _ : Label => n) (fun _ : Label => n) n n :=
  List.fold_right 
    (fun x (y : expr (fun _ => n)  (fun _  => n) n n) => e_dot (e_var (vlabel x)) y)
    (e_one n)
    vlabels.

Fixpoint k_edges (n : positive) (etypes : list label) (tr : bool) (k : nat) :=
  match k with 
  | O => e_one n
  | S k' => e_dot (types_to_expr n etypes tr) (k_edges n etypes tr k')
  end.

Fixpoint pattern_to_matrix (n : positive) (p : Pattern.t) :
expr (fun _ : Label => n) (fun _ : Label => n) n n :=
  match p with 
  | pvertex vvar vlabels => labels_to_expr n vlabels    
  | pedge p evar etypes edir wvar wlabels =>
    let e := match edir with 
      | IN => types_to_expr n etypes true
      | OUT => types_to_expr n etypes false
      | BOTH => e_pls (types_to_expr n etypes true) (types_to_expr n etypes false)
      end in e_dot (e_dot (pattern_to_matrix n p) e) (labels_to_expr n wlabels) 
 | pmultiedge p evar etypes edir low up wvar wlabels =>
   let e := match up with 
     | None =>  match edir with
      | IN => e_dot (k_edges n etypes true (low - 1)) (e_itr (types_to_expr n etypes true))
      | OUT =>  e_dot (k_edges n etypes false (low - 1)) (e_itr (types_to_expr n etypes false))
      | BOTH => e_pls 
        (e_dot (k_edges n etypes true (low - 1)) (e_itr (types_to_expr n etypes true)))
        (e_dot (k_edges n etypes false (low - 1)) (e_itr (types_to_expr n etypes false)))
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
          (map (fun k => k_edges n etypes false k) (List.seq low (up' - low))))
      end
   end
   in e_dot (e_dot (pattern_to_matrix n p) e) (labels_to_expr n wlabels)
  end.

(* http://perso.ens-lyon.fr/damien.pous/ra/html/RelationAlgebra.syntax.html#s.e.f *)
(* Use as a variable f. *)
Definition e_var2matrix (g : PropertyGraph.t) (l : Label) :=
  match l with 
  | vlabel v => let ms := pg_extract_lmatrices (List.length g.(vertices)) g.(vlab) in
    List.fold_right
      (fun x y => match fst x with
                  | vlabel v => snd x
                  | _ => y
                  end)
      (fun _ _ => false)
      ms
  | elabel e => 
    let ms := pg_extract_tmatrices (List.length g.(vertices)) g.(edges) g.(elab) g.(st) in
    List.fold_right
      (fun x y => match fst x with
                  | elabel e => snd x
                  | _ => y
                  end)
      (fun _ _ => false)
      ms
  end.