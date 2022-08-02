From HoTT Require Import Basics Types Pointed Homotopy.ExactSequence WildCat
  AbGroups.AbelianGroup AbSES.Core AbSES.Pullback AbSES.Pushout BaerSum AbGroups.AbPushout.

Require Import AbProjective.

(** The swap isomorphism of the direct product of two abelian groups. *)
Definition direct_sum_swap {A B : AbGroup} : (ab_biprod A B) $<~> (ab_biprod B A).
Proof.
  snrapply Build_GroupIsomorphism'.
  - apply equiv_prod_symm.
  - intro; reflexivity.
Defined.

(** Composing group homomorphisms with the identity has no effect. *)

(* Commented out for now, since unused:
Lemma grp_compose_id_r `{Funext} {A B : Group} (f : A $-> B) : grp_homo_compose f grp_homo_id = f.
Proof.
    apply equiv_path_grouphomomorphism. reflexivity.
Defined.

Lemma grp_compose_id_l `{Funext} {A B : Group} (f : A $-> B) : grp_homo_compose grp_homo_id f = f.
Proof.
    apply equiv_path_grouphomomorphism. reflexivity.
Defined.

Lemma abses_pushout_homotopic' `{Univalence} {A A' B : AbGroup} (f f' : A $-> A') (h : f == f')
  : abses_pushout0 (B:=B) f $=> abses_pushout0 f'.
Proof.
  induction (equiv_path_grouphomomorphism h).
  apply id_transformation.
Defined.

Definition abses_pushout_homotopic `{Univalence} {A A' B : AbGroup}
  (f f' : A $-> A') (h : f == f')
  : abses_pushout0 (B:=B) f == abses_pushout0 f'
  := equiv_path_data_homotopy _ _ (abses_pushout_homotopic' _ _ h).
*)

(** Given a morphism [f] of short exact sequences, the pushout of the domain along [f_1] equals the pullback of the codomain along [f_3]. *)
Lemma abses_pushout_is_pullback `{Univalence} {A A' B B' : AbGroup}
      {E : AbSES B A} {E' : AbSES B' A'} (f : AbSESMorphism E E')
  : abses_pushout0 (component1 f) E = abses_pullback0 (component3 f) E'.
Proof.
  (* The morphism [f : E -> E'] factors as [E -> f_1 E -> E'], where the first map is the map defining the pushout [f_1 E] and the second map is denoted [abses_pushout_morphism_rec f] below.  This second map is the identity on the first component, so it presents its domain as the pullback of [E'] along [f_3]. *)
  refine (abses_component1_trivial_pullback (abses_pushout_morphism_rec f) _); reflexivity.
Defined.

(** Given a short exact sequence [A -> E -> B] and maps [f : A -> A'], [g : B' -> B], we can change the order of pushing out along [f] and pulling back along [g]. *)
Lemma abses_reorder_pullback_pushout `{Univalence} {A A' B B' : AbGroup}
      (E : AbSES B A) (f : A $-> A') (g : B' $-> B)
  : abses_pushout0 f (abses_pullback0 g E) = abses_pullback0 g (abses_pushout0 f E).
Proof.
  (* There are morphisms [Eg -> E] and [E -> fE] by definition of the pullback and pushout. We define [F : Eg -> fE] to be the composite. Its first and third components are [f o id] and [id o g]. *)
  pose (F := absesmorphism_compose (abses_pushout_morphism E f) (abses_pullback_morphism E g)).
  (* We change [F] to a morphism that is the same except that the first and third components are [f] and [g]. Then [abses_pushout_is_pullback] shows that the pushout of [Eg] along [f] is equal to the pullback of [fE] along [g]. *)
  refine (abses_pushout_is_pullback (Build_AbSESMorphism f (component2 F) g _ _)); apply F.
Defined.

(** The following are a series of lemmas that we rely on for properties of the Baer sum. *)

(** For any short exact sequence [E], there is a morphism [E -> E + E], where each component is ab_diagonal. *)
Definition abses_diagonal `{Funext} {A B : AbGroup} (E : AbSES B A)
  : AbSESMorphism E (abses_direct_sum E E).
Proof.
  snrapply Build_AbSESMorphism.
  1,2,3: exact ab_diagonal.
  all: reflexivity.
Defined.

(** For any short exact sequence [E], there is dually a morphism [E + E -> E], with each component being the codiagonal. *)
Definition abses_codiagonal `{Funext} {A B : AbGroup} (E : AbSES B A)
  : AbSESMorphism (abses_direct_sum E E) E.
Proof.
  snrapply Build_AbSESMorphism.
  1,2,3: exact ab_codiagonal.
  all: intro x; cbn; apply grp_homo_op.
Defined.

(** There is always a morphism [E + F -> F + E] of short exact sequences, for any [E : AbSES B A] and [F : AbSES B' A']. *) 
Definition abses_swap_morphism `{Funext} {A A' B B' : AbGroup}
           (E : AbSES B A) (F : AbSES B' A')
  : AbSESMorphism (abses_direct_sum E F) (abses_direct_sum F E).
Proof.
  snrapply Build_AbSESMorphism.
  1,2,3: exact direct_sum_swap.
  all: reflexivity.
Defined.

(** Precomposing the codiagonal with the swap map has no effect. *)
Lemma ab_codiagonal_swap `{Funext} {A : AbGroup}
  : (@ab_codiagonal A) $o direct_sum_swap = ab_codiagonal.
Proof.
  apply equiv_path_grouphomomorphism.
  intro a; cbn.
  apply abgroup_commutative.
Defined.

(** The corresponding result for the diagonal is true definitionally, so it isn't strictly necessary to state it, but we record it anyways. *)
Definition ab_diagonal_swap {A : AbGroup}
  : direct_sum_swap $o (@ab_diagonal A) = ab_diagonal
  := idpath.
                                        
(** This is the isomorphism [A + (A + A) <~> (A + A) + A] that associativity relies on in Mac Lane. *)
Lemma ab_biprod_assoc {A : AbGroup}
  : ab_biprod A (ab_biprod A A) $<~> ab_biprod (ab_biprod A A) A.
Proof.
  snrapply Build_GroupIsomorphism'.
  - apply equiv_prod_assoc.
  - unfold IsSemiGroupPreserving; reflexivity.
Defined.

(** We now get that [(ab_diagonal + id) o ab_diagonal = (id + ab_diagonal) o ab_diagonal] after passing into the right direct sum via the above isomorphism. *)
Definition ab_commute_id_diagonal {A : AbGroup}
  : (functor_ab_biprod (@ab_diagonal A) grp_homo_id) $o ab_diagonal
    = ab_biprod_assoc $o (functor_ab_biprod grp_homo_id ab_diagonal) $o ab_diagonal
  := idpath.

(** A similar result for the codiagonal. *)
Lemma ab_commute_id_codiagonal `{Funext} {A : AbGroup}
  : (@ab_codiagonal A) $o (functor_ab_biprod ab_codiagonal grp_homo_id) $o ab_biprod_assoc
    = ab_codiagonal $o (functor_ab_biprod grp_homo_id ab_codiagonal).
Proof.
  apply equiv_path_grouphomomorphism.
  intro a; cbn.
  exact (grp_assoc _ _ _)^.
Defined.

(** A proof of commutativity of the Baer sum. *)
Lemma baer_sum_commutative `{Univalence} {A B : AbGroup} (E F : AbSES B A)
  : abses_baer_sum E F = abses_baer_sum F E.
Proof.
  unfold abses_baer_sum.
  refine (_ @ _).
  - refine (ap (abses_pullback0 ab_diagonal) _).
    refine (ap (fun f => abses_pushout0 f _) ab_codiagonal_swap^ @ _).
    refine (_^ @_).
    1: nrapply abses_pushout_compose.
    refine (ap _ (abses_pushout_is_pullback (abses_swap_morphism E F)) @ _).
    unfold abses_swap_morphism, component3.
    exact (abses_reorder_pullback_pushout _ ab_codiagonal direct_sum_swap).
  - exact (abses_pullback_compose ab_diagonal direct_sum_swap _).
  (* This uses that [direct_sum_swap $o ab_diagonal] is definitionally equal to [ab_diagonal]. *)
Defined.

(** For every [E : AbSES B A], there is a morphism of the split short exact sequence into [E]. *)
Lemma abses_split_morphism `{Funext} {A B : AbGroup} (E : AbSES B A)
  : AbSESMorphism (point (AbSES B A)) E.
Proof.
  snrapply Build_AbSESMorphism.
  - exact grp_homo_id.
  - exact (inclusion E $o ab_biprod_pr1).
  - exact grp_homo_const.
  - reflexivity.
  - intro x; cbn.
    apply iscomplex_abses.
Defined.

(** For every [E : AbSES B A], there is an identification of the split exact sequence with the pullback of E along the zero homomorphism [B $-> B]. *)
Definition abses_split_is_composite `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : point (AbSES B A) = abses_pullback0 (grp_homo_const) E
  := abses_component1_trivial_pullback (abses_split_morphism E) (fun _ => idpath).

(** The identity morphism from [E] to [E]. *)
Lemma abses_morphism_id {A B : AbGroup} (E : AbSES B A) : AbSESMorphism E E.
Proof.
  snrapply (Build_AbSESMorphism grp_homo_id grp_homo_id grp_homo_id).
  1,2: reflexivity.
Defined.

(** For every [E : AbSES B A], there is an identification of [E] with the pullback of [E] along [id_B]. *)
Definition abses_id_pullback `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : E = abses_pullback0 (@grp_homo_id B) E
  := abses_component1_trivial_pullback (abses_morphism_id E) (fun _ => idpath).

(** Given two abelian group homomorphisms [f] and [g], their pairing [(f, g) : B -> A + A] can be written as a composite. Note that [ab_biprod_corec] is an alias for [grp_prod_corec]. *)
Lemma ab_biprod_corec_diagonal `{Funext} {A B : AbGroup} (f g : B $-> A)
  : ab_biprod_corec f g = (functor_ab_biprod f g) $o ab_diagonal.
Proof.
  apply equiv_path_grouphomomorphism; reflexivity.
Defined.

(** For any short exact sequences [E], [E'], [F], [F'], and morphisms [f : E -> E'] and [g : F -> F'] there is a morphism [E + F -> E' + F']. *)
Lemma functor_abses_directsum `{Funext} {A A' B B' C C' D D' : AbGroup}
      {E : AbSES B A} {E' : AbSES B' A'} {F : AbSES D C} {F' : AbSES D' C'}
      (f : AbSESMorphism E E') (g : AbSESMorphism F F')
  : AbSESMorphism (abses_direct_sum E F) (abses_direct_sum E' F').
Proof.
  snrapply Build_AbSESMorphism.
  + exact (functor_ab_biprod (component1 f) (component1 g)).
  + exact (functor_ab_biprod (component2 f) (component2 g)).
  + exact (functor_ab_biprod (component3 f) (component3 g)).
  + intro x.
    apply path_prod; apply left_square.
  + intro x.
    apply path_prod; apply right_square.
Defined.

(** For any two [E, F : AbSES B A] and [f, g : B' $-> B], there is a morphism [Ef + Fg -> E + F] induced by the universal properties of the pullbacks of E and F, respectively. *)
Definition abses_directsum_pullback_morphism `{Funext} {A B B' C D D' : AbGroup}
      {E : AbSES B A} {F : AbSES D C} (f : B' $-> B) (g : D' $-> D)
  : AbSESMorphism (abses_direct_sum (abses_pullback0 f E) (abses_pullback0 g F))
                  (abses_direct_sum E F)
  := functor_abses_directsum (abses_pullback_morphism E f) (abses_pullback_morphism F g).

(** For any two [E, F : AbSES B A] and [f, g : B' $-> B], we have (E + F)(f + g) = Ef + Eg, where + denotes the direct sum. *)
Definition abses_directsum_distributive_pullbacks `{Univalence} {A B B' : AbGroup}
  {E F : AbSES B A} (f g : B' $-> B)
  : abses_pullback0 (functor_ab_biprod f g) (abses_direct_sum E F)
    = abses_direct_sum (abses_pullback0 f E) (abses_pullback0 g F)
  := (abses_component1_trivial_pullback (abses_directsum_pullback_morphism f g)
        (fun _ => idpath))^.

(** The analogous result follows for the Baer sum, rather than the direct sum. *)
Lemma baer_sum_distributive_pullbacks `{Univalence} {A B B' : AbGroup}
  {E : AbSES B A} (f g : B' $-> B)
  : abses_pullback0 (ab_homo_add f g) E = abses_baer_sum (abses_pullback0 f E) (abses_pullback0 g E).
Proof.
  unfold abses_baer_sum, ab_homo_add.
  refine ((abses_pullback_compose (B1:=ab_biprod B B) _ _ E)^ @ _).
  refine (ap (abses_pullback0 _) (abses_pushout_is_pullback (abses_codiagonal E))^ @ _).
  unfold abses_codiagonal, component1.
  refine ((abses_reorder_pullback_pushout _ _ _)^ @ _ @ abses_reorder_pullback_pushout _ _ _).
  refine (ap (abses_pushout0 _) _).
  refine (ap (fun h => abses_pullback0 h _) (ab_biprod_corec_diagonal _ _) @ _).
  refine ((abses_pullback_compose _ _ (abses_direct_sum E E))^ @ _).
  exact (ap (abses_pullback0 _) (abses_directsum_distributive_pullbacks f g)).
Defined.

(** Adding the zero homomorphism to any other [f : A $-> A] has no effect. *)
Lemma ab_homo_add_zero_r `{Funext} {A B : AbGroup} (f : A $-> B) : ab_homo_add f grp_homo_const = f.
Proof.
  apply equiv_path_grouphomomorphism; intro x.
  exact (grp_unit_r _).
Defined.

Lemma ab_homo_add_zero_l `{Funext} {A B : AbGroup} (f : A $-> B) : ab_homo_add grp_homo_const f = f.
Proof.
  apply equiv_path_grouphomomorphism; intro x.
  exact (grp_unit_l _).
Defined.

(** The right unit law for the Baer sum says that for all [E : AbSES B A], E + E_0 = E, where E_0 is the split short exact sequence. *)
Lemma baer_sum_unit_r `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum E (point (AbSES B A)) = E.
Proof.
  refine (ap (abses_baer_sum E) _ @ _).
  - exact (abses_split_is_composite E).
  - refine (ap (fun F => abses_baer_sum F (abses_pullback0 grp_homo_const E)) (abses_id_pullback E) @ _).
    refine ((baer_sum_distributive_pullbacks grp_homo_id grp_homo_const)^ @ _).
    refine (ap (fun f => abses_pullback0 f E) (ab_homo_add_zero_r _) @ _).
    symmetry; apply abses_id_pullback.
Defined.

(** The left unit law for the Baer sum is analogous. *)
Definition baer_sum_unit_l `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum (point (AbSES B A)) E = E
  := baer_sum_commutative _ _ @ baer_sum_unit_r _.

(** The negation of a homomorphism [f] of abelian groups. We locally denote this [-f]. *)
(* This can also be used in AbPushout.v in one spot. *)
Definition ab_homo_negate {A B : AbGroup} (f : A $-> B) : A $-> B
  := grp_homo_compose ab_homo_negation f.

(** This notation is just to make the proofs more concise. *)
Local Notation "- f" := (ab_homo_negate f).

(** For any [f : A $-> B], f + -f = 0. *)
Lemma ab_negate_homo_cancel `{Funext} {A B : AbGroup} (f : A $-> B)
  : ab_homo_add f (-f) = grp_homo_const.
Proof.
  apply equiv_path_grouphomomorphism; intro x.
  exact (grp_inv_r _).
Defined.

(** We can now prove the inverse laws for the Baer sum, which state that for any [E : AbSES B A], the pullback of [E] along [-id_B] acts as an additive inverse for [E] with respect to the Baer sum. *)
Lemma baer_sum_inverse_l `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum E (abses_pullback0 (-grp_homo_id) E) = point (AbSES B A).
Proof.
  refine (ap (fun F => abses_baer_sum F (abses_pullback0 _ E)) (abses_id_pullback E) @ _).
  refine ((baer_sum_distributive_pullbacks grp_homo_id (-grp_homo_id))^ @ _).
  refine (ap (fun f => abses_pullback0 f _) (ab_negate_homo_cancel _) @ _).
  symmetry; apply abses_split_is_composite.
Defined.

(** The right inverse law follows by commutativity. *)
Definition baer_sum_inverse_r `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum (abses_pullback0 (-grp_homo_id) E) E = point (AbSES B A)
  := baer_sum_commutative _ _ @ baer_sum_inverse_l _.

