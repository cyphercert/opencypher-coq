(*Fixpoint contain (a : list label) (b : label) : bool :=
  match a with 
  | [] => False
  | h :: tl => match
Fixpoint in (a b : list label) : bool :=
  match a with
  | [] => True
  | h :: tl => match h*)

Module GRA_operations.
  Definition get_vertices (vname : var) (vlabels : list label) 
                          (graph : PropertyGraph.t) :=

  Fixpoint get_edges (pattern : Pattern.t) 
                     (ename : var) (etype : list label) (edirection : direction) 
                     (wname : var) (wlabels : list label)
    match pattern with 
    | Pattern.vertex vname vlabels => 
      
    | Pattern.edge pattern' ename' etype' edirection' wname' wlabels' =>
      
    | Pattern.multiedge pattern' enames etype' low up vnames wname' vlabels => 
      
    end.

  Fixpoint transitive_get_edges (pattern : Pattern.t) 
                                (enames : list var) (etype : label) (low : nat) (up : option nat) 
                                (vnames : list var) (wname : var) (vlabels : list label) :=
    match p with 
    | Pattern.vertex vname vlabels' => 
    
    | Pattern.edge pattern' ename etype' edirection wname' wlabels =>

    | Pattern.multiedge pattern' enames' etype' low' up' vnames' wname' vlabels' => 

    end.
End GRA_operations.