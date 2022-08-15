From HoTT Require Import Basics Types Pointed Homotopy.ExactSequence WildCat
  AbGroups.AbelianGroup AbSES.Core AbSES.Pullback AbSES.Pushout AbSES.BaerSum AbSES.Ext AbGroups.AbPushout.

Require Import AbProjective.

(** This allows [Trunc_functor n f (tr x) to compute to [tr (f x)] using [cbn]. *)
Arguments O_rec /.

Local Open Scope mc_add_scope.

(** ** Lemmas about abelian groups *)
(** Place these results in Algebra/AbGroups/AbelianGroup. *)

(** For [A, B : AbGroup], homomorphisms A $-> B form an abelian group.  *)
Definition grp_hom `{Funext} (A B : AbGroup) : Group.
Proof.
  snrapply Build_Group.
    - exact (GroupHomomorphism A B).
    - intros f g.
      exact (ab_codiagonal $o ab_biprod_corec f g).
    - exact grp_homo_const. 
    - exact (fun f => grp_homo_compose ab_homo_negation f).
    - repeat split.
        1: exact _.
        all: hnf; intros; apply equiv_path_grouphomomorphism; intro; cbn.
        + apply associativity.
        + apply left_identity.
        + apply right_identity.
        + apply left_inverse.
        + apply right_inverse.
Defined.

Definition ab_hom (A B : AbGroup) `{Funext} : AbGroup.
Proof.
  snrapply (Build_AbGroup (grp_hom A B)).
    - intros f g. cbn.
      apply equiv_path_grouphomomorphism.
      intro x.
      cbn. apply commutativity.
Defined.

(** ** Lemmas about direct sums (or biproducts) *)
(** Create AbGroups/Biproduct and place these there, along with appropriate results from AbGroups/AbelianGroup. *)

(** Given two abelian group homomorphisms [f] and [g], their pairing [(f, g) : B -> A + A] can be written as a composite. Note that [ab_biprod_corec] is an alias for [grp_prod_corec]. *)
Lemma ab_biprod_corec_diagonal `{Funext} {A B : AbGroup} (f g : B $-> A)
  : ab_biprod_corec f g = (functor_ab_biprod f g) $o ab_diagonal.
Proof.
  apply equiv_path_grouphomomorphism; reflexivity.
Defined.

(** The swap isomorphism of the direct product of two abelian groups. *)
Definition direct_sum_swap {A B : AbGroup} : (ab_biprod A B) $<~> (ab_biprod B A).
Proof.
  snrapply Build_GroupIsomorphism'.
  - apply equiv_prod_symm.
  - intro; reflexivity.
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

(** The biproduct is associative. *)
Lemma ab_biprod_assoc {A B C : AbGroup}
  : ab_biprod A (ab_biprod B C) $<~> ab_biprod (ab_biprod A B) C.
Proof.
  snrapply Build_GroupIsomorphism'.
  - apply equiv_prod_assoc.
  - unfold IsSemiGroupPreserving; reflexivity.
Defined.

(** The iterated diagonals [(ab_diagonal + id) o ab_diagonal] and [(id + ab_diagonal) o ab_diagonal] agree, after reassociating the direct sum. *)
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

(** The next few results are used to prove associativity of the Baer sum. *)

(** A "twist" isomorphism [(A + B) + C <~> (C + B) + A]. *)
Lemma ab_biprod_twist {A B C : AbGroup}
  : ab_biprod (ab_biprod A B) C $<~> ab_biprod (ab_biprod C B) A.
Proof.
  snrapply Build_GroupIsomorphism.
  - snrapply Build_GroupHomomorphism.
    + intros [[a b] c].
      exact ((c,b),a).
    + unfold IsSemiGroupPreserving. reflexivity.
  - snrapply isequiv_adjointify.
    + intros [[c b] a].
      exact ((a,b),c).
    + reflexivity.
    + reflexivity.
Defined.

(** The triagonal and cotriagonal homomorphisms. *)
Definition ab_triagonal {A : AbGroup} : A $-> ab_biprod (ab_biprod A A) A
  := (functor_ab_biprod ab_diagonal grp_homo_id) $o ab_diagonal.

Definition ab_cotriagonal {A : AbGroup} : ab_biprod (ab_biprod A A) A $-> A
  := ab_codiagonal $o (functor_ab_biprod ab_codiagonal grp_homo_id).

(** For an abelian group [A], precomposing the triagonal on [A] with the twist map on [A] has no effect. *)
Definition ab_triagonal_twist {A : AbGroup}
  : ab_biprod_twist $o @ab_triagonal A = ab_triagonal
  := idpath.

(** A similar result for the cotriagonal. *)
Definition ab_cotriagonal_twist `{Funext} {A : AbGroup}
  : @ab_cotriagonal A $o ab_biprod_twist = ab_cotriagonal.
Proof.
  apply equiv_path_grouphomomorphism.
  intro x. cbn.
  refine ((grp_assoc _ _ _)^ @ _).
  refine (abgroup_commutative _ _ _ @ _).
  exact (ap (fun a =>  a * snd x) (abgroup_commutative _ _ _)).
Defined.


(** ** General lemmas about short exact sequences *)
(** Place in Algebra/AbGroups/AbSES/Core. *)

(** The identity morphism from [E] to [E]. *)
Lemma abses_morphism_id {A B : AbGroup} (E : AbSES B A) : AbSESMorphism E E.
Proof.
  snrapply (Build_AbSESMorphism grp_homo_id grp_homo_id grp_homo_id).
  1,2: reflexivity.
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

(** For any short exact sequence [E], there is a morphism [E -> abses_direct_sum E E], where each component is ab_diagonal. *)
Definition abses_diagonal `{Funext} {A B : AbGroup} (E : AbSES B A)
  : AbSESMorphism E (abses_direct_sum E E).
Proof.
  snrapply Build_AbSESMorphism.
  1,2,3: exact ab_diagonal.
  all: reflexivity.
Defined.

(** For any short exact sequence [E], there is dually a morphism [abses_direct_sum E E -> E], with each component being the codiagonal. *)
Definition abses_codiagonal `{Funext} {A B : AbGroup} (E : AbSES B A)
  : AbSESMorphism (abses_direct_sum E E) E.
Proof.
  snrapply Build_AbSESMorphism.
  1,2,3: exact ab_codiagonal.
  all: intro x; cbn; apply grp_homo_op.
Defined.

(** There is always a morphism [abses_direct_sum E F -> abses_direct_sum F E] of short exact sequences, for any [E : AbSES B A] and [F : AbSES B' A']. *)
Definition abses_swap_morphism `{Funext} {A A' B B' : AbGroup}
           (E : AbSES B A) (F : AbSES B' A')
  : AbSESMorphism (abses_direct_sum E F) (abses_direct_sum F E).
Proof.
  snrapply Build_AbSESMorphism.
  1,2,3: exact direct_sum_swap.
  all: reflexivity.
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

(** For [E, F, G : AbSES B A], there is a morphism [(E + F) + G -> (G + F) + E] induced by the above map, where [+] denotes [abses_direct_sum]. *)
Lemma abses_twist_directsum `{Univalence} {A B : AbGroup} (E F G : AbSES B A)
  : AbSESMorphism (abses_direct_sum (abses_direct_sum E F) G)
                  (abses_direct_sum (abses_direct_sum G F) E).
Proof.
  snrapply Build_AbSESMorphism.
  1,2,3: exact ab_biprod_twist.
  all: reflexivity.
Defined.


(** ** Results about pullbacks of short exact sequences *)
(** Place in Algebra/AbGroups/AbSES/Pullback. *)

(** For every [E : AbSES B A], the pullback of [E] along [id_B] is [E]. *)
Definition abses_pullback_id `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_pullback (@grp_homo_id B) E = E
  := (abses_pullback_component1_id (abses_morphism_id E) (fun _ => idpath))^.

(** For any two [E, F : AbSES B A] and [f, g : B' $-> B], there is a morphism [Ef + Fg -> E + F] induced by the universal properties of the pullbacks of E and F, respectively. *)
Definition abses_directsum_pullback_morphism `{Funext} {A B B' C D D' : AbGroup}
           {E : AbSES B A} {F : AbSES D C} (f : B' $-> B) (g : D' $-> D)
  : AbSESMorphism (abses_direct_sum (abses_pullback f E) (abses_pullback g F))
                  (abses_direct_sum E F)
  := functor_abses_directsum (abses_pullback_morphism E f) (abses_pullback_morphism F g).

(** For any two [E, F : AbSES B A] and [f, g : B' $-> B], we have (E + F)(f + g) = Ef + Eg, where + denotes the direct sum. *)
Definition abses_directsum_distributive_pullbacks `{Univalence} {A B B' C D D' : AbGroup}
           {E : AbSES B A} {F : AbSES D C} (f : B' $-> B) (g : D' $-> D)
  : abses_pullback (functor_ab_biprod f g) (abses_direct_sum E F)
    = abses_direct_sum (abses_pullback f E) (abses_pullback g F)
  := (abses_pullback_component1_id (abses_directsum_pullback_morphism f g)
        (fun _ => idpath))^.


(** ** Results about pushouts of short exact sequences *)
(** Place in Algebra/AbGroups/AbSES/Pushout. *)

(** Given [E : AbSES B A'] and [F : AbSES B A] and a morphism [f : E -> F], the pushout of [E] along [f_1] is [F] if [f_3] is homotopic to [id_B]. *)
Lemma abses_pushout_component3_id' `{Univalence}
      {A A' B : AbGroup} {E : AbSES B A'} {F : AbSES B A}
      (f : AbSESMorphism E F) (h : component3 f == grp_homo_id)
  : abses_pushout (component1 f) E $== F.
Proof.
  pose (g := abses_pushout_morphism_rec f).
  nrapply abses_path_data_to_iso.
  exists (component2 g); split.
  + intro x.
    exact (left_square g _)^.
  + intro x.
    exact ((right_square g _) @ h _)^.
Defined.

(** A version with equality instead of path data. *)
Definition abses_pushout_component3_id `{Univalence}
           {A A' B : AbGroup} {E : AbSES B A'} {F : AbSES B A}
           (f : AbSESMorphism E F) (h : component3 f == grp_homo_id)
  : abses_pushout (component1 f) E = F
  := equiv_path_abses_iso (abses_pushout_component3_id' f h).

(** For every [E : AbSES B A], the pushout of [E] along [id_A] is [E]. *)
Definition abses_pushout_id `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_pushout (@grp_homo_id A) E = E
  := abses_pushout_component3_id (abses_morphism_id E) (fun _ => idpath).

(** Pushing out along homotopic maps induces homotopic pushout functors. *)
Lemma abses_pushout_homotopic' `{Univalence} {A A' B : AbGroup} (f f' : A $-> A') (h : f == f')
  : abses_pushout (B:=B) f $=> abses_pushout f'.
Proof.
  induction (equiv_path_grouphomomorphism h).
  apply id_transformation.
Defined.

Definition abses_pushout_homotopic `{Univalence} {A A' B : AbGroup}
  (f f' : A $-> A') (h : f == f')
  : abses_pushout (B:=B) f == abses_pushout f'
  := equiv_path_data_homotopy _ _ (abses_pushout_homotopic' _ _ h).

(** Given short exact sequences [E] and [F] and homomorphisms [f : A' $-> A] and [g : D' $-> D], there is a morphism [E + F -> fE + gF] induced by the universal properties of the pushouts of [E] and [F]. *)
Definition abses_directsum_pushout_morphism `{Univalence}
           {A A' B C D D' : AbGroup} {E : AbSES B A'} {F : AbSES C D'}
           (f : A' $-> A) (g : D' $-> D)
  : AbSESMorphism (abses_direct_sum E F) (abses_direct_sum (abses_pushout f E) (abses_pushout g F))
  := functor_abses_directsum (abses_pushout_morphism E f) (abses_pushout_morphism F g).

(** For [E, F : AbSES B A'] and [f, g : A' $-> A], we have (f+g)(E+F) = fE + gF, where + denotes the direct sum. *)
Definition abses_directsum_distributive_pushouts `{Univalence}
           {A A' B C C' D : AbGroup} {E : AbSES B A'} {F : AbSES D C'} (f : A' $-> A) (g : C' $-> C)
  : abses_pushout (functor_ab_biprod f g) (abses_direct_sum E F)
    = abses_direct_sum (abses_pushout f E) (abses_pushout g F)
  := abses_pushout_component3_id (abses_directsum_pushout_morphism f g) (fun _ => idpath).


(** ** Results about the Baer sum *)
(** Place in Algebra/AbGroups/AbSES/BaerSum. *)

(** Given a morphism [f] of short exact sequences, the pushout of the domain along [f_1] equals the pullback of the codomain along [f_3]. *)
Lemma abses_pushout_is_pullback `{Univalence} {A A' B B' : AbGroup}
      {E : AbSES B A} {E' : AbSES B' A'} (f : AbSESMorphism E E')
  : abses_pushout (component1 f) E = abses_pullback (component3 f) E'.
Proof.
  (* The morphism [f : E -> E'] factors as [E -> f_1 E -> E'], where the first map is the map defining the pushout [f_1 E] and the second map is denoted [abses_pushout_morphism_rec f] below.  This second map is the identity on the first component, so it presents its domain as the pullback of [E'] along [f_3]. *)
  exact (abses_pullback_component1_id (abses_pushout_morphism_rec f) (fun _ => idpath)).
Defined.

(** Given a short exact sequence [A -> E -> B] and maps [f : A -> A'], [g : B' -> B], we can change the order of pushing out along [f] and pulling back along [g]. *)
Lemma abses_reorder_pullback_pushout `{Univalence} {A A' B B' : AbGroup}
      (E : AbSES B A) (f : A $-> A') (g : B' $-> B)
  : abses_pushout f (abses_pullback g E) = abses_pullback g (abses_pushout f E).
Proof.
  (* There are morphisms [Eg -> E] and [E -> fE] by definition of the pullback and pushout. We define [F : Eg -> fE] to be the composite. Its first and third components are [f o id] and [id o g]. *)
  pose (F := absesmorphism_compose (abses_pushout_morphism E f) (abses_pullback_morphism E g)).
  (* We change [F] to a morphism that is the same except that the first and third components are [f] and [g]. Then [abses_pushout_is_pullback] shows that the pushout of [Eg] along [f] is equal to the pullback of [fE] along [g]. *)
  refine (abses_pushout_is_pullback (Build_AbSESMorphism f (component2 F) g _ _)); apply F.
Defined.

(** The Baer sum distributes over pullbacks. *)
Lemma baer_sum_distributive_pullbacks `{Univalence} {A B B' : AbGroup}
  {E : AbSES B A} (f g : ab_hom B' B)
  : abses_pullback (f + g) E = abses_baer_sum (abses_pullback f E) (abses_pullback g E).
Proof.
  unfold abses_baer_sum.
  refine ((abses_pullback_compose (B1:=ab_biprod B B) _ _ E)^ @ _).
  refine (ap (abses_pullback _) (abses_pushout_is_pullback (abses_codiagonal E))^ @ _).
  unfold abses_codiagonal, component1.
  refine ((abses_reorder_pullback_pushout _ _ _)^ @ _ @ abses_reorder_pullback_pushout _ _ _).
  refine (ap (abses_pushout _) _).
  refine (ap (fun h => abses_pullback h _) (ab_biprod_corec_diagonal _ _) @ _).
  refine ((abses_pullback_compose _ _ (abses_direct_sum E E))^ @ _).
  exact (ap (abses_pullback _) (abses_directsum_distributive_pullbacks f g)).
Defined.

(** The Baer sum is commutative. *)
Lemma baer_sum_commutative `{Univalence} {A B : AbGroup} (E F : AbSES B A)
  : abses_baer_sum E F = abses_baer_sum F E.
Proof.
  unfold abses_baer_sum.
  (* The next line uses that [direct_sum_swap $o ab_diagonal] is definitionally equal to [ab_diagonal]: *)
  refine (_ @ abses_pullback_compose ab_diagonal direct_sum_swap _).
  refine (ap (abses_pullback ab_diagonal) _).
  refine (ap (fun f => abses_pushout f _) ab_codiagonal_swap^ @ _).
  refine ((abses_pushout_compose _ _ _)^ @ _).
  refine (ap _ (abses_pushout_is_pullback (abses_swap_morphism E F)) @ _).
  unfold abses_swap_morphism, component3.
  apply abses_reorder_pullback_pushout.
Defined.

(** The right unit law for the Baer sum says that for all [E : AbSES B A], E + E_0 = E, where E_0 is the split short exact sequence. *)
Lemma baer_sum_unit_r `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum E (point (AbSES B A)) = E.
Proof.
  refine (ap (abses_baer_sum E) _ @ _).
  - exact (abses_pullback_const E).
  - refine (ap (fun F => abses_baer_sum F (abses_pullback grp_homo_const E)) (abses_pullback_id E)^ @ _).
    refine ((baer_sum_distributive_pullbacks grp_homo_id grp_homo_const)^ @ _).
    refine (ap (fun f => abses_pullback f E) (grp_unit_r (G := ab_hom _ _) _) @ _).
    apply abses_pullback_id.
Defined.

(** The left unit law for the Baer sum is analogous. *)
Definition baer_sum_unit_l `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum (point (AbSES B A)) E = E
  := baer_sum_commutative _ _ @ baer_sum_unit_r _.

(** For any [E : AbSES B A], the pullback of [E] along [-id_B] acts as an additive inverse for [E] with respect to the Baer sum. *)
Lemma baer_sum_inverse_l `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum E (abses_pullback (group_inverse (g := ab_hom _ _) grp_homo_id) E) = point (AbSES B A).
Proof.
  refine (ap (fun F => abses_baer_sum F (abses_pullback _ E)) (abses_pullback_id E)^ @ _).
  refine ((baer_sum_distributive_pullbacks grp_homo_id (group_inverse (g := ab_hom _ _) grp_homo_id))^ @ _).
  refine (ap (fun f => abses_pullback f _) (grp_inv_r (G := ab_hom _ _) _) @ _).
  symmetry; apply abses_pullback_const.
Defined.

(** The right inverse law follows by commutativity. *)
Definition baer_sum_inverse_r `{Univalence} {A B : AbGroup} (E : AbSES B A)
  : abses_baer_sum (abses_pullback (-grp_homo_id) E) E = point (AbSES B A)
  := baer_sum_commutative _ _ @ baer_sum_inverse_l _.

(** The Baer sum distributes over pushouts. *)
Lemma baer_sum_distributive_pushouts `{Univalence}
      {A A' B : AbGroup} {E : AbSES B A'} (f g : ab_hom A' A)
  : abses_pushout (f + g) E = abses_baer_sum (abses_pushout f E) (abses_pushout g E).
Proof.
  unfold abses_baer_sum.
  refine ((abses_pushout_compose (A1 := ab_biprod A A) _ _ E)^ @ _).
  refine (_ @ abses_reorder_pullback_pushout _ ab_codiagonal ab_diagonal).
  refine (ap (abses_pushout ab_codiagonal) _).
  refine (ap (fun f => abses_pushout f E) (ab_biprod_corec_diagonal f g) @ _).
  refine ((abses_pushout_compose _ _ E)^ @ _).
  refine (ap (abses_pushout _) (abses_pushout_is_pullback (abses_diagonal E)) @ _).
  refine (abses_reorder_pullback_pushout _ _ _ @ _).
  exact (ap (abses_pullback _) (abses_directsum_distributive_pushouts f g)).
Defined.

(** Our next goal is to prove that the Baer sum is associative.  Rather than showing this directly, we first prove [baer_sum_twist], which says that [abses_baer_sum (abses_baer_sum E F) G = abses_baer_sum (abses_baer_sum G F) E].  The proof of this mimics the proof of commutativity above.  Then we prove associativity by combining this with commutativity. *)

(** The trinary Baer sum of three short exact sequences. *)
Definition abses_trinary_baer_sum `{Univalence} {A B : AbGroup} (E F G : AbSES B A)
  : AbSES B A
  := abses_pullback ab_triagonal
                   (abses_pushout ab_cotriagonal
                                  (abses_direct_sum (abses_direct_sum E F) G)).

(** For [E, F, G : AbSES B A], the Baer sum of [E], [F] and [G] (associated left) is equal to the trinary Baer sum of [E], [F] and [G]. *)
Lemma baer_sum_is_trinary `{Univalence} {A B : AbGroup} (E F G : AbSES B A)
  : abses_baer_sum (abses_baer_sum E F) G = abses_trinary_baer_sum E F G.
Proof.
  unfold abses_baer_sum, abses_trinary_baer_sum, ab_triagonal, ab_cotriagonal.
  refine (ap (abses_pullback _ o abses_pushout _) _^ @ _).
  - refine (_ @ ap (abses_direct_sum _) (abses_pullback_id G)).
    refine (_ @ abses_directsum_distributive_pullbacks _ _).
    refine (ap (abses_pullback _) _).
    refine (_ @ ap (abses_direct_sum _) (abses_pushout_id G)).
    apply abses_directsum_distributive_pushouts.
  - refine (ap (abses_pullback _) (abses_reorder_pullback_pushout _ _ _) @ _).
    refine (abses_pullback_compose _ _ _ @ _).
    refine (ap (abses_pullback _) _).
    apply abses_pushout_compose.
Defined.

(** For [E, F, G : AbSES B A], we can "twist" the order of the trinary Baer sum as follows. *)
Lemma twist_trinary_baer_sum `{Univalence} {A B : AbGroup} (E F G : AbSES B A)
  : abses_trinary_baer_sum E F G = abses_trinary_baer_sum G F E.
Proof.
  unfold abses_trinary_baer_sum.
  (* The next line uses the fact that [ab_triagonal] is definitionally equal to [ab_biprod_twist $o ab_triagonal]: *)
  refine (_ @ abses_pullback_compose ab_triagonal ab_biprod_twist _).
  refine (ap (abses_pullback _) _).
  refine (ap (fun f => abses_pushout f _) ab_cotriagonal_twist^ @ _).
  refine ((abses_pushout_compose _ _ _)^ @ _).
  refine (ap _ (abses_pushout_is_pullback (abses_twist_directsum E F G)) @ _).
  unfold abses_twist_directsum, component3.
  apply abses_reorder_pullback_pushout.
Defined.

(** It now follows that we can twist the order of the summands in the Baer sum. *)
Lemma baer_sum_twist `{Univalence} {A B : AbGroup} (E F G : AbSES B A)
  : abses_baer_sum (abses_baer_sum E F) G = abses_baer_sum (abses_baer_sum G F) E.
Proof.
  refine ((baer_sum_is_trinary E F G) @ _ @ (baer_sum_is_trinary G F E)^).
  apply twist_trinary_baer_sum.
Defined.

(** From these results, it finally follows that the Baer sum is associative. *)
Lemma baer_sum_associative `{Univalence} {A B : AbGroup} (E F G : AbSES B A)
  : abses_baer_sum (abses_baer_sum E F) G = abses_baer_sum E (abses_baer_sum F G).
Proof.
  refine ((baer_sum_twist _ _ _)^ @ _).
  refine (baer_sum_commutative _ _ @ _).
  apply ap.
  apply baer_sum_commutative.
Defined.

(** ** Results about [Ext1] *)
(** Place in AbGroups/AbSES/Ext. *)

(** [Ext B A] is an abelian group for any [A, B : AbGroup]. The proof of commutativity is a bit faster if we separate out the proof that [Ext B A] is a group. *)
Definition grp_ext `{Univalence} (A B : AbGroup) : Group.
Proof.
  snrapply (Build_Group (Ext B A)).
  - intros E F.
    strip_truncations.
    exact (tr (abses_baer_sum E F)).
  - exact (point (Ext B A)).
  - unfold Negate.
    exact (Trunc_functor _ (abses_pullback (group_inverse (g := ab_hom _ _) grp_homo_id))).
  - split; try split; try split.
    1: exact _.
    all: intro E.  1: intros F G.
    all: strip_truncations; unfold mon_unit, point, ispointed_ext; apply (ap tr).
    + symmetry; apply baer_sum_associative.
    + apply baer_sum_unit_l.
    + apply baer_sum_unit_r.
    + apply baer_sum_inverse_r.
    + apply baer_sum_inverse_l.
Defined.

Definition abgroup_ext `{Univalence} (A B : AbGroup) : AbGroup.
Proof.
  snrapply (Build_AbGroup (grp_ext B A)).
  intros E F.
  cbn.
  strip_truncations; cbn.
  apply ap.
  apply baer_sum_commutative.
Defined.


(** Pullbacks and pushouts in [Ext B A] follow from their counterparts in [AbSES B A]. *)
Definition ext_pullback {A B B' : AbGroup} (f : B' $-> B)
  : Ext B A -> Ext B' A
  := Trunc_functor _ (abses_pullback f).

Definition ext_pushout `{Univalence} {A A' B : AbGroup} (f : A $-> A')
  : Ext B A -> Ext B A'
  := Trunc_functor _ (abses_pushout f).

(** For [E : Ext B A], pulling back or pushing out along the identity has no effect. *)
Lemma ext_pullback_id `{Univalence} {A B : AbGroup} 
  : ext_pullback (grp_homo_id) == Id (Ext B A).
Proof.
  rapply Trunc_ind; intro E.
  cbn.
  apply ap.
  apply abses_pullback_id.
Defined.

Lemma ext_pushout_id `{Univalence} {A B : AbGroup} 
  : ext_pushout (grp_homo_id) == Id (Ext B A).
Proof.
  rapply Trunc_ind; intro E.
  cbn. apply ap.
  apply abses_pushout_id.
Defined.

(** Pulling back in [Ext B A] preserves composition *)
Lemma ext_pullback_compose `{Univalence} {A B0 B1 B2 : AbGroup}
      (f : B0 $-> B1) (g : B1 $-> B2)
  : ext_pullback (A := A) f o ext_pullback g == ext_pullback (g $o f).
Proof.
  rapply Trunc_ind; intro E.
  cbn.
  apply ap.
  apply abses_pullback_compose.
Defined.

(** Pushing out in [Ext B A] preserves composition *)
Lemma ext_pushout_compose `{Univalence} {A0 A1 A2 B : AbGroup}
      (f : A0 $-> A1) (g : A1 $-> A2)
  : ext_pushout (B := B) g o ext_pushout f == ext_pushout (g $o f).
Proof.
  rapply Trunc_ind; intro E.
  cbn.
  apply ap.
  apply abses_pushout_compose.
Defined.

(** Ext is a covariant 0-functor in its second variable. *)
Global Instance is0functor_ext_covariant `{Univalence} {B : AbGroup} 
  : Is0Functor (Ext B).
Proof.
  snrapply Build_Is0Functor.
  intros A A' f.
  exact (ext_pushout f).
Defined.

(** Ext is a contravariant 0-functor in its first variable. *)
Global Instance is0functor_ext_contravariant `{Univalence} {A : AbGroup} 
  : Is0Functor (A := AbGroup^op) (fun B => Ext B A).
Proof.
  snrapply Build_Is0Functor.
  intros B' B f.
  exact (ext_pullback f).
Defined.

(** Ext is a covariant 1-functor in its second variable. *)
Global Instance is1functor_ext_covariant `{Univalence} {B : AbGroup}
  : Is1Functor (Ext B).
Proof.
  snrapply Build_Is1Functor.
  - intros A A' f g h E.
    strip_truncations.
    cbn. apply ap.
    apply (abses_pushout_homotopic _ _ h).
  - intros A E.
    strip_truncations.
    cbn. apply ap.
    apply abses_pushout_id.
  - intros C C' D f g E. 
    strip_truncations.
    cbn. apply ap.
    symmetry; apply abses_pushout_compose.
Defined.

(** Ext is a contravariant 1-functor in its first variable. *)
Global Instance is1functor_ext_contravariant `{Univalence} {A : AbGroup}
  : Is1Functor (A := AbGroup^op) (fun B => Ext B A).
Proof.
  snrapply Build_Is1Functor.
  - intros C C' f g h E.
    strip_truncations.
    cbn. apply ap.
    apply (abses_pullback_phomotopic _ _ h).
  - intros C E.
    strip_truncations.
    cbn. apply ap.
    apply abses_pullback_id.
  - intros C C' D f g E.
    strip_truncations.
    cbn. apply ap.
    symmetry; apply abses_pullback_compose. 
Defined.

(** Pulling back in [Ext B A] induces a group homomorphism [Hom B' B $-> Ext B' A]. *)
Lemma ext_homo_pullback `{Univalence} {A B B' : AbGroup} (E : Ext B A)
  : GroupHomomorphism (ab_hom B' B) (abgroup_ext B' A).
Proof.
  snrapply Build_GroupHomomorphism.
  - intro f. exact (ext_pullback f E).
  - intros f g.
    strip_truncations.
    cbn. apply ap.
    apply baer_sum_distributive_pullbacks.
Defined.

(** Pushing out in [Ext B A] induces a group homomorphism [Hom A A' $-> Ext B A']. *)
Lemma ext_homo_pushout `{Univalence} {A A' B : AbGroup} (E : Ext B A)
  : GroupHomomorphism (ab_hom A A') (abgroup_ext B A').
Proof.
  snrapply Build_GroupHomomorphism.
  - intro f. exact (ext_pushout f E).
  - intros f g.
    strip_truncations.
    cbn. apply ap.
    apply baer_sum_distributive_pushouts.
Defined.

(*

Plan:

- Embed proofs of axioms for functors/groups when short/compile fast (Done)
- Change "is" lemmas to instances (Done)
- First argument in Ext/AbSES needs to be in opposite category (baersum branch too)
- AbSES functorial in each variable

Properties of Ext:
- Ext is a functor in both variables (pullback, pushforward);
  these are group homomorphisms. (Done)
- For a fixed s.e.s E, [fun f => abses_pullback f E] and [fun g => abses_pushout g E] are group homomorphisms. (Done)

Calculations of Ext:
- Ext(Z/n, A) = A/n (even just for A = Z)

Higher coherences (might be quite challenging):
- commutativity @ commutativity = idpath?
- triangle involving unit laws + assoc
- pentagon
- hexagon
See https://ncatlab.org/nlab/show/symmetric+monoidal+category

*)
