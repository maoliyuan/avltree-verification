Inductive tree (Node: Type): Type :=
| E : tree Node
| T (l: tree Node) (x: Node) (r: tree Node).

Arguments E {_}.
Arguments T {_} _ _ _.

Inductive half_tree (Node: Type): Type :=
| LH (x: Node) (r: tree Node): half_tree Node
| RH (l: tree Node) (x: Node): half_tree Node.

Arguments LH {_} _ _.
Arguments RH {_} _ _.

Fixpoint tree_rel {Node1 Node2: Type} (node_rel: Node1 -> Node2 -> Prop)
                  (t1: tree Node1) (t2: tree Node2): Prop :=
  match t1, t2 with
  | E, E => True
  | T l1 x1 r1, T l2 x2 r2 =>
    tree_rel node_rel l1 l2 /\ node_rel x1 x2 /\ tree_rel node_rel r1 r2
  | _, _ => False
  end.

