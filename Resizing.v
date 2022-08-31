From HoTT Require Import Basics Types Truncations Groups.

(** Truncation level is independent of the universe. *)

Proposition istrunc_resize@{u v | u < v} {n : trunc_index}
  : forall X : Type@{u}, IsTrunc@{u} n X -> IsTrunc@{v} n X.
Proof.
  induction n; intro X.
  1: { intros [z C].
       exists z; exact C. }
  intros istrunc x0 x1.
  exact (IHn _ (istrunc x0 x1)).
Defined.


(** It follows that we can resize groups, for example. *)
Proposition group_resize@{u v | u < v} : Group@{u} -> Group@{v}.
Proof.
  intros [G ? ? ? [[[]]]].
  snrapply (Build_Group G).
  1-3: exact _.
  repeat split.
  1: exact (istrunc_resize _ _).
  all: assumption.
Defined.

Coercion group_resize : Group >-> Group.

(** Now we can avoid overly polymorphic functions in e.g. Groups.v, which makes keeping track of universes easier. *)
