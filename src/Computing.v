Fixpoint compute_pattern (pattern : Pattern.t) (graph : PropertyGraph.t) : list data :=
  match pattern with
  | Pattern.vertex vname vlabels => GRA_operations.get_vertices vname vlabels graph
  | Pattern.edge pattern ename etype edirection wname wlabels => GRA_operations.get_edges pattern ename etype edirection wname wlabels graph
  | Pattern.multiedge pattern enames etype low up vnames wname vlabels => GRA_operations.transitive_get_edges 
                                                                            pattern enames etype low up vnames wname vlabels graph
  end.

Fixpoint compute_clause (clause : Clause.t) (graph : PropertyGraph.t) : list data :=
  match clause with
  | MATCH patterns => match patterns with
                      | [] => NRAEnvConst dunit
                      | head :: tail => macro_cNRAEnvNaturalJoin (compute_pattern head graph) (compute_clause (MATCH tail) graph)
                      .
  | WITH pexpr => RelationOperation.projection pexpr
  end.

Fixpoint compute_query (query : Query.t) (graph : PropertyGraph.t) : list data :=
    match query.clauses with
    | [] => NRAEnvConst dunit
    | head :: tail => macro_cNRAEnvNaturalJoin (compute_clause head graph) (compute_query tail graph)
    end.