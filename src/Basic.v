From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssreflect.seq.
Require Import String.
(* From hahn Require Import HahnBase. *)

Definition vertex    := nat.
Definition edge      := nat.
Definition label     := string.
Definition attribute := string.

Module Attribute.
  Definition t := string.
  
  Definition eqb (s s' : t) := String.eqb s s'.

  Lemma eqP : Equality.axiom eqb.
  Proof. unfold eqb. red. apply eqb_spec. Qed.
End Attribute.

Canonical Structure attribute_eqMixin := EqMixin Attribute.eqP.
Canonical Structure attribute_eqType := Eval hnf in EqType Attribute.t attribute_eqMixin.

Module Scheme.
  Definition t := seq Attribute.t.
  
  Definition eqb (s s' : t) : bool := eqseq s s'.
End Scheme.

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
    unfold eqb. red. intros. apply introP; desf; simpls.
    (* TODO: is there a better way to do it in SSReflect? *)
    { by move/EqNat.beq_nat_true->. }
    { by move/String.eqb_eq->. }
    all: move=>A B; inv B.
    { rewrite PeanoNat.Nat.eqb_refl in A. simpls. }
    rewrite String.eqb_refl in A. simpls.
  Qed.
End Property.

Canonical Structure property_eqMixin := EqMixin Property.eqP.
Canonical Structure property_eqType := Eval hnf in EqType Property.t property_eqMixin.

Module Relation.
  Record t :=
    mk { (* sch *)
        scheme : Scheme.t;
        data   : seq (seq Property.t);
      }.

  Record wf (r : Relation.t) :=
    { scheme_len : forall l (IN : l \in (data r)),
        List.length l = List.length (scheme r);
    }.

  Definition union r r' : option t :=
    if Scheme.eqb (scheme r) (scheme r')
    then mk (scheme r) 
    else None.
End Relation.

Module PropertyGraph.
  Record t :=
    mk { (* V *)
        vertices : list vertex;
        (* E *)
        edges    : list edge;
        (* st *)
        st       : edge -> vertex * vertex;

        (* \mathcal{L}*)
        vlab     : list (vertex * label);
        (* \mathcal{T}*)
        elab     : edge -> label;
        
        (* Pᵥ *)
        vprop    : list (Property.name * (vertex -> Property.t)); 
        (* Pₑ *)
        eprop    : list (Property.name * (edge   -> Property.t)); 
      }.
End PropertyGraph.
