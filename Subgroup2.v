From HoTT Require Import HoTT.

(* Things to add to Subgroup.v *)
(* Should also make G argument to subgroup_group implicit. *)

Definition subgroup_generated_gen_incl {G : Group} (X : G -> Type)
           (g : G) (H : X g)
  : subgroup_generated X
  := (g; tr (sgt_in H)).

Local Lemma path_subgroup_generated_helper {G : Group}
           (X Y : G -> Type)
           (K : forall g, merely (X g) -> merely (Y g))
  : forall g, Trunc (-1) (subgroup_generated_type X g) -> Trunc (-1) (subgroup_generated_type Y g).
Proof.
  intro g.
  intro ing.
  strip_truncations.
  induction ing as [g x| |g h Xg IHYg Xh IHYh].
  - pose (y := K g (tr x)).
    cbn in y.
    exact (Trunc_functor (-1) sgt_in y).
  - exact (tr sgt_unit).
  - strip_truncations.
    apply tr.
    apply sgt_op; assumption.
Defined.

Definition path_subgroup_generated `{Univalence} {G : Group}
           (X Y : G -> Type)
           (K : forall g, Trunc (-1) (X g) <-> Trunc (-1) (Y g))
  : subgroup_generated X = subgroup_generated Y.
Proof.
  rapply equiv_path_subgroup'. (* Uses Univalence. *)
  intro g.
  split.
  - apply path_subgroup_generated_helper, K.
  - apply path_subgroup_generated_helper.
    exact (fun x => snd (K x)).
Defined.

(* Equal subgroups have isomorphism underlying groups. *)
Definition equiv_subgroup_group {G : Group}
           (H1 H2 : Subgroup G)
  : H1 = H2 -> GroupIsomorphism H1 H2.
Proof.
  intro p.
  induction p.
  exact grp_iso_id.
Defined.
