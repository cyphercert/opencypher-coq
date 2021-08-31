Require Import PropertyGraph.
Import PropertyGraph.
Require Import List.
Import ListNotations.

Fixpoint list_unique (l : list label) : list label :=
  match l with
  | [] => []
  | h :: tl => h :: filter (fun x => negb (String.eqb x h)) (list_unique tl)
  end.

Definition list_inb (e : label) (l : list label) : bool := 
  List.fold_right (fun x y => orb (String.eqb x e) y) false l.

Fixpoint list_inb_b (e : bool) (l : list bool) : bool :=
  match l with 
  | [] => false 
  | h :: tl => if (Bool.eqb e h) then true else list_inb_b e tl
  end.