Module Relation.
  Record t :=
    mk { (* sch *)
        scheme : Scheme.t;
        data   : list (list Property.t);
      }.
End Relation.

Definition graph_to_vertices_relation (graph : PropertyGraph.t) : RelationOperation.t := 
Definition graph_to_edges_relation (graph : PropertyGraph.t) : RelationOperation.t := 