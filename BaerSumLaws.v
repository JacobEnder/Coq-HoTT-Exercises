From HoTT Require Import Basics Types Pointed.
From HoTT Require Import Homotopy.ExactSequence WildCat.
From HoTT Require Import AbGroups.AbelianGroup AbSES.Core AbSES.Pullback AbSES.Pushout.
From HoTT Require Import BaerSum AbGroups.AbPushout.

Require Import AbProjective.

(* Jacob: The swap isomorphism of the direct product of two abelian groups. *)

Definition direct_sum_swap {A B : AbGroup} : (ab_biprod A B) $<~> (ab_biprod B A).
Proof.
  snrapply Build_GroupIsomorphism.
  + snrapply Build_GroupHomomorphism.
  - intro x. exact (snd x, fst x).
    - intro x. reflexivity.
  + snrapply Build_IsEquiv.
    1: intro x; exact (snd x, fst x).
    all: reflexivity.
Defined.

(* Jacob: A quick proof that the swap map is its own inverse. *)

Lemma swap_involution {A B : AbGroup} : @direct_sum_swap A B $o direct_sum_swap == idmap.
Proof.
   intro a. reflexivity.
Defined.

(* Composing group homomorphisms with the identity has no effect. *)

Lemma grp_compose_id_r `{Funext} {A B : Group} (f : A $-> B) : grp_homo_compose f grp_homo_id = f.
Proof.
    apply equiv_path_grouphomomorphism. reflexivity.
Defined.

Lemma grp_compose_id_l `{Funext} {A B : Group} (f : A $-> B) : grp_homo_compose grp_homo_id f = f.
Proof.
    apply equiv_path_grouphomomorphism. reflexivity.
Defined.

(** We can check equality of maps out of a pushout on the two inclusions. *)
Lemma abses_pushout_equal_components `{Univalence} {A B C Y : AbGroup}
  (f : A $-> B) (g : A $-> C) (phi psi : ab_pushout f g $-> Y)
  : ((phi o ab_pushout_inl == psi o ab_pushout_inl) *
       (phi o ab_pushout_inr == psi o ab_pushout_inr))
      <-> (phi == psi).
Admitted.

Lemma abses_pushout_homotopic' `{Univalence} {A A' B : AbGroup} (f f' : A $-> A') (h : f == f')
  : abses_pushout0 (B:=B) f $=> abses_pushout0 f'.
Proof.
  intro E.
  apply abses_path_data_to_iso.
  snrefine (_; (_,_)).
  - snrapply functor_ab_pushout.
    1-3: apply grp_homo_id.
    2: reflexivity.
    exact h.
  - intro x; simpl.
    apply qglue.
    apply tr.
    exists mon_unit.
    apply path_prod'; cbn.
    + refine (grp_homo_unit _ @ _).
      apply grp_moveL_gM.
      exact (left_identity _ @ ap _ (right_identity _)^).
    + rewrite 2 grp_unit_r.
      exact (grp_homo_inv _ _ @ ap _ (grp_homo_unit _)).
  - apply abses_pushout_equal_components; split.
    + intro x.
      refine (ab_pushout_rec_beta_left f (inclusion _) _ _ _ _ @ _).
      1: symmetry; rapply cx_isexact.
      simpl; symmetry.
      refine (grp_unit_l _ @ ap (projection E) (grp_unit_l _) @ _).
      apply grp_homo_unit.
    + intro x.
      refine (ab_pushout_rec_beta_right f (inclusion _) _ _ _ _ @ _).
      1: symmetry; rapply cx_isexact.
      simpl; symmetry.
      exact (grp_unit_l _ @ ap (projection E) (grp_unit_l _)).
Defined.

Definition abses_pushout_homotopic `{Univalence} {A A' B : AbGroup}
  (f f' : A $-> A') (h : f == f')
  : abses_pushout0 (B:=B) f == abses_pushout0 f'
  := equiv_path_data_homotopy _ _ (abses_pushout_homotopic' _ _ h).

(* Given a short exact sequence [A -> E -> B] and maps [f : A -> A'], [g : B' -> B], we can change the order of pushing out along f and pulling back along g. *)

(* Jacob: This is the first version of the proof - will look into reasoning backwards to avoid posing. *)

Lemma abses_reorder_pullback_pushout `{Univalence} {A A' B B' : AbGroup} (E : AbSES B A) (f : A $-> A') (g : B' $-> B) :
    abses_pushout0 f (abses_pullback0 g E) = abses_pullback0 g (abses_pushout0 f E).
Proof.
  (* There are morphisms [Eg -> E] and [E -> fE] by definition of the pullback and pushout *)
  pose (F := absesmorphism_compose (abses_pushout_morphism E f) (abses_pullback_morphism E g)).

  (* This composite has a factorization [f(Eg) -> fE], which can be identified with the middle
   filler map defining (fE)g in the below way. *)
  pose (K := abses_component1_trivial_pullback (abses_pushout_morphism_rec F) (reflexive_pointwise_paths _ _ _)).
  simpl in K.
  rewrite (grp_compose_id_r f) in K. 
  rewrite (grp_compose_id_l g) in K.
  exact K.                                                              
Defined.
 

