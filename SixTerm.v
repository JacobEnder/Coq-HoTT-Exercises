From HoTT Require Import Basics Types Pointed Truncations
          Algebra.Groups Algebra.AbGroups
          Homotopy.ExactSequence WildCat WildCat.Profunctor.

Require Import BaerSumLaws.

(** * The six-term exact sequence of Ext groups *)

(** We convert our purely exact sequence to a fiber sequence, to which the tools of Homotopy/ExactSequence.v more easily apply. *)

Definition fiberseq_abses_pullback `{Univalence} {A B C : AbGroup} {E : AbSES C B}
  : FiberSeq (AbSES C A) (AbSES E A) (AbSES B A)
  := fiberseq_isexact_purely
       (abses_pullback_pmap (A:=A) (projection E))
       (abses_pullback_pmap (inclusion E)).

(** Thus [Pi_les] gives the six-term exact sequence. We need to identify the maps. *)

(** todo: place in AbSES/Pullback.v *)
Definition abses_pullback_point `{Univalence} {A B B' : AbGroup} (f : B' $-> B)
  : abses_pullback f (point _) = point (AbSES B' A)
  := equiv_path_abses_iso (abses_pullback_point' f).

(** The functorial action of [abses_pullback_pmap] on loops. *)
Definition abses_loops_pullback_data `{Univalence} {B B' A : AbGroup} (g : B $-> B')
  : forall p, fmap loops (abses_pullback_pmap (A:=A) g) p
         = equiv_path_abses_iso
             ((abses_pullback_point' g)^$
                $@ (fmap (abses_pullback g) (equiv_path_abses_iso^-1 p)
                      $@ abses_pullback_point' g)).
Proof.
  intro p.
  refine (_ @ abses_path_data_compose_beta _ _).
  refine (_ @ ap011 _ (abses_path_data_V _) (abses_path_data_compose_beta _ _)).
  apply whiskerL.
  apply whiskerR.
  apply ap_abses_pullback.
Defined.

(** The inverse of [loops_abses]. *)
Definition loops_abses_inv `{Univalence} {A B : AbGroup}
  : loops (AbSES B A) <~> (B $-> A)
  := abses_endomorphism_trivial oE equiv_path_abses^-1.

(** Loop spaces of a 1-truncated type are automatically groups. *)
Definition loops_1trunc (X : pType) `{IsTrunc 1 X} : Group.
Proof.
  nrefine (Build_Group (loops X) concat idpath inverse _).
  nrapply Build_IsGroup; repeat split.
  - by apply istrunc_paths.
  - rapply concat_p_pp.
  - rapply concat_1p.
  - rapply concat_p1.
  - rapply concat_Vp.
  - rapply concat_pV.
Defined.

(* [loops_abses] is a group isomorphism *)
Definition iso_loops_abses `{Univalence} {A B : AbGroup}
  : GroupIsomorphism (ab_hom B A)
      (loops_1trunc (AbSES B A)).
Proof.
  srapply Build_GroupIsomorphism'.
  1: apply loops_abses.
  intros phi psi.
  snrapply (equiv_ap_inv' equiv_path_abses).
  apply path_sigma_hprop.
  apply equiv_path_grouphomomorphism; intros [a b].
  unfold loops_abses.
  rewrite (eissect equiv_path_abses (abses_endomorphism_trivial^-1 (sg_op phi psi))).
  unfold equiv_path_abses.
  nrefine (_ @ ap (fun x => (equiv_path_abses^-1 x).1 _) _).
  2: exact (abses_path_data_compose_beta _ _)^.
  rewrite (equiv_inverse_compose _ _ _).
  nrefine (_ @ ap (fun x => ((equiv_path_abses_data _ _)^-1 x).1 _) _^).
  2: apply eissect.
  cbn.
  apply path_prod'.
  - rewrite grp_unit_l.
    apply associativity.
  - exact (grp_unit_l _)^.
Defined.

(** [loops_abses_inv] is a group isomorphism *)
(* jarl: Of course this follows from the previous result, but we should decide on which one to keep. *)
Definition iso_loops_abses_inv `{Univalence} {A B : AbGroup}
  : GroupIsomorphism
      (loops_1trunc (AbSES B A))
      (ab_hom B A).
Proof.
  snrapply Build_GroupIsomorphism'.
  1: apply loops_abses_inv.
  unfold IsSemiGroupPreserving.
  (* We reformulate the equation in terms of path data. *)
  rapply (equiv_ind equiv_path_abses_iso); intros [p [p0 p1]].
  rapply (equiv_ind equiv_path_abses_iso); intros [q [q0 q1]].
  refine (ap loops_abses_inv _ @ _ @ ap011 sg_op _ _); only 3,4: symmetry.
  1: apply abses_path_data_compose_beta.
  all: refine (ap _ (equiv_inverse_compose _ _ _) @ _).
  all: nrefine (ap (abses_endomorphism_trivial o _^-1) (eissect _ _) @ _).
  2,3: reflexivity.
  apply equiv_path_grouphomomorphism; intro b; cbn.
  refine (ap fst _ @ _).
  { refine (ap q _ @ _).
    { refine (ab_biprod_decompose _ _ @ _).
      refine (ap (fun x => sg_op _ x) _).
      exact (ap (fun x => (_, x)) (p1 _)^). }
    refine (grp_homo_op _ _ _ @ ap (fun x => sg_op x _) _).
    apply q0. }
  reflexivity.
Defined.

(** Under the equivalence [loops_abses], [fmap loops (abses_pullback g)] corresponds to precomposition by [g]. *)
Definition abses_loops_pullback_inv `{Univalence} {B B' A : AbGroup} (g : B $-> B')
  : Square (IsGraph0:=isgraph_type) loops_abses_inv loops_abses_inv
      (fmap loops (abses_pullback_pmap (A:=A) g)) (fun f => f $o g).
Proof.
  intro phi; unfold loops_abses_inv.
  refine (ap abses_endomorphism_trivial _
            (x:=equiv_path_abses^-1%equiv (fmap loops _ phi))
            @ _).
  { refine (ap _ (abses_loops_pullback_data _ _) @ _).
    refine (equiv_inverse_compose _ _ _ @ _).
    exact (ap _ (eissect _ _)). }
  by apply equiv_path_grouphomomorphism.
Defined.

(* jarl: I was hoping to deduce the following from the previous using [vinverse], but couldn't get it to work. *)
Definition abses_loops_pullback `{Univalence} {B B' A : AbGroup} (g : B $-> B')
  : Square (IsGraph0:=isgraph_type) loops_abses loops_abses
      (fun f => f $o g) (fmap loops (abses_pullback_pmap (A:=A) g)).
Proof.
  intro phi.
  rapply moveR_equiv_M'.
  nrefine (_ @ (abses_loops_pullback_inv g (loops_abses phi))^).
  refine (ap (fun f => f $o g) (x:=phi) _^).
  unfold loops_abses_inv, loops_abses.
  refine (ap _ (eissect equiv_path_abses _) @ _).
  apply eisretr.
Defined.

(** ** The six-term exact sequence *)

(** Given a short exact sequence [B -> E -> C] and an abelian group [A], we show exactness at all points of the associated six-term exact sequence. *)

(* Place in Groups/Group.v? *)
Definition pequiv_groupisomorphism {A B : Group}
  : GroupIsomorphism A B -> (A <~>* B)
  := fun phi => Build_pEquiv _ _ phi _.

Coercion pequiv_groupisomorphism : GroupIsomorphism >-> pEquiv.

From HoTT Require Import Modalities.ReflectiveSubuniverse Modalities.Identity.

(* Place in Homotopy/ExactSequence.v *)
(** A purely exact sequence is [O]-exact for any modality [O]. *)
Definition isexact_purely_O {O : Modality} {F X Y : pType}
  (i : F ->* X) (f : X ->* Y) `{IsExact purely _ _ _ i f}
  : IsExact O i f.
Proof.
  srapply Build_IsExact.
  1: apply cx_isexact.
  exact _.
Defined.

(* jarl: The exact sequence [ab_hom C A $-> ab_hom E A $-> ab_hom B A] lives in the base universe, whereas the exact sequence coming from [loops [AbSES ? ?)] lives in a higher universe. Unforunately, [isexact_square_if] doesn't let the two fiber sequences live in separate universes (though maybe one could change it to allow for that). Instead, we've made [ab_hom] polymorphic so that it spits out an abelian group in whatever higher universe we need. *)

(** The sequence [ab_hom C A $-> ab_hom E A $-> ab_hom B A] is exact. *)
(* jarl: This needs to be sped up. *)
Definition abses_sixterm1 `{Univalence} {A B C : AbGroup@{u}}
  (E : AbSES@{u u _ v _ _ _ _} C B)
  : IsExact@{v v v _ _ _ _ _ _ _} (Tr (-1))
      (fmap10 ab_hom (projection E) A)
      (fmap10 ab_hom (inclusion E) A).
Proof.
  snrapply isexact_square_if.
  1-3: refine (loops_1trunc (AbSES _ A)); shelve.
  1-2: refine (fmap loops (abses_pullback_pmap _)).
  1: exact (projection E).
  1: exact (inclusion E). 
  1-3: symmetry; exact iso_loops_abses_inv.
  1,2: apply phomotopy_homotopy_hset; intro phi;
         exact (abses_loops_pullback _ phi).
  apply isexact_purely_O.
  apply isexact_loops.
  exact _.
Defined.

(** The untruncated connecting map. *)
Definition abses_sixterm_untrunc_connecting_map `{Univalence}
  {A B C: AbGroup} (E : AbSES C B)
  : ab_hom B A ->* AbSES C A
  := connecting_map (abses_pullback_pmap (A:=A) (projection E))
       (abses_pullback_pmap (inclusion E)) o* iso_loops_abses.

(** The connecting map into the truncation [Ext C A]. *)
Definition abses_sixterm_connecting_map `{Univalence}
  {A B C: AbGroup} (E : AbSES C B)
  : ab_hom B A ->* Ext C A
  := ptr o* (connecting_map (abses_pullback_pmap (A:=A) (projection E))
              (abses_pullback_pmap (inclusion E))
              o* iso_loops_abses).

(** Exactness at the domain of the untruncated connecting map. *)
Definition abses_sixterm2_untrunc `{Univalence}
  {A B C : AbGroup} (E : AbSES@{u u _ v _ _ _ _} C B)
  : IsExact@{v v v _ _ _ _ _ _ _} (Tr (-1))
      (fmap10 ab_hom (inclusion E) A)
      (abses_sixterm_untrunc_connecting_map E).
Proof.
  snrapply (isexact_equiv_i _ _ _ _ iso_loops_abses).
  2: rapply (fmap loops (abses_pullback_pmap (inclusion E))).
  1: exact iso_loops_abses.
  - apply phomotopy_homotopy_hset; intro phi.
    exact (abses_loops_pullback _ phi).
  - rapply isexact_purely_O.
Defined.

(* todo: Move to Pointed/pTrunc ? Is this already in the library? *)
Lemma fmap_pTr_square `{Univalence} {X Y : pType} (f : X ->* Y)
  : ptr o* f ==* fmap (pTr 0) f o* ptr.
Proof.
  srapply Build_pHomotopy.
  1: easy.
  by pointed_reduce.
Defined.

(** We replace the [ab_hom]s with their set-truncations, then the exact sequence is the set-truncation of the untruncated sequence just above, and exactness follows from [isexact_ptr]. *)
Definition abses_sixterm2 `{Univalence} {A B C: AbGroup}
  (E : AbSES@{u u _ v _ _ _ _} C B)
  : IsExact@{v v v _ _ _ _ _ _ _} (Tr (-1))
      (fmap10 ab_hom (inclusion E) A)
      (abses_sixterm_connecting_map E).
Proof.
  snrapply (isexact_square_if (Tr (-1))
              (F:=pTr 0 (ab_hom E A)) (X:=pTr 0 (ab_hom B A)) (Y:=Ext C A)).
  3,4: exact pequiv_ptr.
  - exact (fmap (pTr 0) (fmap10 ab_hom (inclusion E) A)).
  - exact (fmap (pTr 0) (abses_sixterm_untrunc_connecting_map E)).
  - reflexivity.
  - apply fmap_pTr_square.
  - refine (pmap_postcompose_idmap _ @* _).
    unfold abses_sixterm_connecting_map.
    apply fmap_pTr_square.
  - apply isexact_ptr.
    apply abses_sixterm2_untrunc.
Defined.

(* todo: place in Homotopy/ExactSequence.v *)
Lemma iscomplex_cancelL {F' F X Y : pType}
  (i : F ->* X) (f : X ->* Y) (e : F' <~>* F) `{C : IsComplex i f}
  : IsComplex (i o* e) f.
Proof.
  unfold IsComplex.
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  refine (pmap_prewhisker _ C @* _).
  apply postcompose_pconst.
Defined.

(** Precomposing with an equivalence doesn't change exactness. *)
(* todo: place in Homotopy/ExactSequence.v *)
Lemma isexact_cancelL (O : Modality) {F' F X Y : pType}
  (i : F ->* X) (f : X ->* Y) (e : F' <~>* F) `{IsExact O _ _ _ i f}
  : IsExact O (i o* e) f.
Proof.
  srapply Build_IsExact.
  { apply iscomplex_cancelL.
    apply cx_isexact. }
  rapply (@conn_map_homotopic O _ _ (cxfib _ o e)).
  intro x; cbn.
  srapply path_sigma'.
  1: reflexivity.
  cbn.
  exact (concat_1p _ @ concat_p1 _)^.
Defined.
  
Definition abses_sixterm3 `{Univalence} {A B C: AbGroup}
  (E : AbSES@{u u _ v _ _ _ _} C B)
  : IsExact@{v v v _ _ _ _ _ _ _} (Tr (-1))
      (abses_sixterm_connecting_map E)
      (fmap (pTr 0) (abses_pullback_pmap (A:=A) (projection E))).
(* jarl: Instead of [abses_pullback_pmap] we could use functoriality of Ext. *)
Proof.
  snrapply (isexact_square_if (Tr (-1))
              (F:=pTr 0 (ab_hom B A)) (X:=Ext C A) (Y:=Ext E A)).
  4,5: reflexivity.
  - exact (fmap (pTr 0) (abses_sixterm_untrunc_connecting_map E)).
  - exact (fmap (pTr 0) (abses_pullback_pmap (projection E))).
  - exact pequiv_ptr.
  - refine (pmap_postcompose_idmap _ @* _).
    apply fmap_pTr_square.
  - exact (pmap_postcompose_idmap _ @* (pmap_precompose_idmap _)^*).
  - apply isexact_ptr.
  rapply (isexact_cancelL (Tr (-1)) _ _ iso_loops_abses).
  rapply isexact_purely_O.
Defined.

Definition abses_sixterm4 `{Univalence} {A B C : AbGroup} (E : AbSES C B)
  : IsExact (Tr (-1))
      (fmap (pTr 0) (abses_pullback_pmap (A:=A) (projection E)))
      (fmap (pTr 0) (abses_pullback_pmap (A:=A) (inclusion E))).
Proof.
  rapply isexact_ptr.
  rapply isexact_purely_O.
Defined.
