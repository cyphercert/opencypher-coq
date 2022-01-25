Require Import PropertyGraph.
Import PropertyGraph.
Require Import List.
Import ListNotations.

Inductive Label :=
| vlabel (l : label)
| elabel (l : label)
.

Fixpoint list_unique (l : list label) : list label :=
  match l with
  | [] => []
  | h :: tl => h :: filter (fun x => negb (String.eqb x h)) (list_unique tl)
  end.

Fixpoint list_inb_b (e : bool) (l : list bool) : bool :=
  match l with 
  | [] => false 
  | h :: tl => if (Bool.eqb e h) then true else list_inb_b e tl
  end.

Definition Label_eqb (a : Label) (b : Label) : bool := 
  match a with 
  | vlabel a' => match b with 
                 | vlabel b' => String.eqb a' b'
                 | elabel b' => false
                 end
  | elabel a' => match b with 
                 | vlabel b' => false
                 | elabel b' => String.eqb a' b'
                 end
  end.

Fixpoint list_inb (e : Label) (l : list Label) : bool :=
  match l with 
  | [] => false 
  | h :: tl => if (Label_eqb e h) then true else list_inb e tl
  end.