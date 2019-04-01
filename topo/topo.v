Require Import Classical.
Require Import ClassicalChoice.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Section TopoSpace.

Parameter E : Type.

Lemma set_ext :
  forall (A B : E -> Prop), (forall x, A x <-> B x) -> A = B.
Proof.
  intros A B H.
  extensionality x.
  apply propositional_extensionality.
  auto.
Qed.

Definition compl (A : E -> Prop) := (fun x => ~ (A x)).
Lemma compl_invol :
  forall (A : E -> Prop), compl (compl A) = A.
Proof.
  intros A. apply set_ext.
  intros x; unfold compl; tauto.
Qed. 

Definition intersection (A B : E -> Prop) := (fun x => A x /\ B x).
Definition union (A B : E -> Prop) := (fun x => A x \/ B x).
Definition intersection_all (X : (E -> Prop) -> Prop) := (fun x => forall A, X A -> A x).
Definition union_all (X : (E -> Prop) -> Prop) := (fun x => exists A, X A /\ A x).
Definition intersection_indexed {I : Type} (f : I -> (E -> Prop)) := (fun x => forall i, f i x).
Definition union_indexed {I : Type} (f : I -> (E -> Prop)) := (fun x => exists i, f i x).
Definition empty := (fun (_ : E) => False).
Definition space := (fun (_ : E) => True).

Lemma compl_empty :
  compl empty = space.
Proof.
  apply set_ext.
  intros x; unfold compl, empty, space; tauto.
Qed.

Lemma compl_space :
  compl space = empty.
Proof.
  apply set_ext.
  intros x; unfold compl, empty, space; tauto.
Qed.

Lemma compl_intersection :
  forall A B, compl (intersection A B) = union (compl A) (compl B).
Proof.
  intros A B. apply set_ext.
  intros x; unfold compl, union, intersection; tauto.
Qed.

Lemma compl_union :
  forall A B, compl (union A B) = intersection (compl A) (compl B).
Proof.
  intros A B. apply set_ext.
  intros x; unfold compl, union, intersection; tauto.
Qed.

Lemma compl_intersection_all :
  forall X, compl (intersection_all X) = union_all (fun A => X (compl A)).
Proof.
  intros X. apply set_ext.
  intros x; unfold intersection_all, union_all.
  split; [|unfold compl; firstorder].
  intros H. apply not_all_ex_not in H.
  destruct H as [A H]; exists (compl A). rewrite compl_invol; tauto.
Qed.

Lemma compl_union_all :
  forall X, compl (union_all X) = intersection_all (fun A => X (compl A)).
Proof.
  intros X. apply set_ext.
  intros x; unfold intersection_all, union_all.
  split.
  - intros H A HA. generalize (not_ex_all_not _ _ H (compl A)).
    unfold compl in *; tauto.
  - intros H [A HA]. specialize (H (compl A)); rewrite compl_invol in H. unfold compl in *; tauto.
Qed.

Lemma compl_intersection_indexed :
  forall I (f : I -> _), compl (intersection_indexed f) = union_indexed (fun i => compl (f i)).
Proof.
  intros I f. apply set_ext.
  intros x; unfold compl, intersection_indexed, union_indexed.
  split; [|firstorder].
  intros H; apply not_all_ex_not in H; tauto.
Qed.

Lemma compl_union_indexed :
  forall I (f : I -> _), compl (union_indexed f) = intersection_indexed (fun i => compl (f i)).
Proof.
  intros I f. apply set_ext.
  intros x; unfold compl, intersection_indexed, union_indexed.
  firstorder.
Qed.

Lemma intersection_indexed_intersection_all :
  forall I (f : I -> _), intersection_indexed f = intersection_all (fun A => exists i, f i = A).
Proof.
  intros I f. apply set_ext.
  intros x; unfold intersection_indexed, intersection_all.
  split.
  - intros H A [i <-]; auto.
  - intros H i; apply H; exists i; auto.
Qed.

Lemma union_indexed_union_all :
  forall I (f : I -> _), union_indexed f = union_all (fun A => exists i, f i = A).
Proof.
  intros I f. apply set_ext.
  intros x; unfold union_indexed, union_all.
  split.
  - intros [i Hi]; exists (f i). split; [exists i|]; auto.
  - intros [A [[i <-] Hx]]; exists i; auto.
Qed.

Definition subset (A B : E -> Prop) := (forall x, A x -> B x).
Definition disjoint (A B : E -> Prop) := (forall x, ~(A x /\ B x)).

Lemma subset_transitive :
  forall A B C, subset A B -> subset B C -> subset A C.
Proof.
  intros A B C H1 H2 x Hx; apply H2; apply H1; auto.
Qed.

Lemma subset_compl :
  forall A B, subset (compl A) (compl B) -> subset B A.
Proof.
  intros A B H x; specialize (H x); unfold compl in H; tauto.
Qed.

Lemma subset_antisym :
  forall A B, subset A B -> subset B A -> A = B.
Proof.
  intros A B H1 H2; apply set_ext; firstorder.
Qed.

Parameter open : (E -> Prop) -> Prop.

Hypothesis space_open : open space.
Hypothesis union_all_open : forall (X : (E -> Prop) -> Prop), (forall A, X A -> open A) -> open (union_all X).
Hypothesis intersection_open : forall A B, open A -> open B -> open (intersection A B).

Lemma empty_open :
  open empty.
Proof.
  erewrite set_ext.
  - apply (union_all_open (fun _ => False)); tauto.
  - intros x; unfold union_all; firstorder.
Qed.

Lemma union_indexed_open :
  forall I (f : I -> _), (forall i, open (f i)) -> open (union_indexed f).
Proof.
  intros I f Hopen.
  rewrite union_indexed_union_all.
  apply union_all_open.
  intros A [i <-]; auto.
Qed.

Lemma union_open :
  forall A B, open A -> open B -> open (union A B).
Proof.
  intros A B HA HB.
  assert (H : _) by exact (union_indexed_open bool (fun b => if b then A else B) (ltac:(intros [|]; auto))).
  erewrite set_ext; [exact H|].
  intros x; unfold union, union_indexed.
  split.
  - intros [? | ?]; [exists true | exists false]; tauto.
  - intros [[|] ?]; tauto.
Qed.

Definition closed A := open (compl A).

Lemma empty_closed :
  closed empty.
Proof.
  unfold closed. rewrite compl_empty. apply space_open.
Qed.

Lemma space_closed :
  closed space.
Proof.
  unfold closed. rewrite compl_space. apply empty_open.
Qed.

Lemma intersection_all_closed :
  forall (X : (E -> Prop) -> Prop), (forall A, X A -> closed A) -> closed (intersection_all X).
Proof.
  intros X H.
  unfold closed in *.
  rewrite compl_intersection_all. apply union_all_open.
  intros A; specialize (H (compl A)); rewrite compl_invol in H; exact H.
Qed.

Lemma intersection_indexed_closed :
  forall I (f : I -> _), (forall i, closed (f i)) -> closed (intersection_indexed f).
Proof.
  intros I f H.
  unfold closed in *.
  rewrite compl_intersection_indexed.
  apply union_indexed_open. exact H.
Qed.

Lemma union_closed :
  forall A B, closed A -> closed B -> closed (union A B).
Proof.
  intros A B Ha Hb.
  unfold closed in *.
  rewrite compl_union.
  apply intersection_open; auto.
Qed.

Lemma intersection_closed :
  forall A B, closed A -> closed B -> closed (intersection A B).
Proof.
  intros A B Ha Hb.
  unfold closed in *.
  rewrite compl_intersection.
  apply union_open; auto.
Qed.

Fixpoint fintype (n : nat) :=
  match n with
  | O => Empty_set
  | S n => option (fintype n)
  end.

Lemma fintype_intersection_indexed :
  forall n (f : fintype (S n) -> _),
    intersection_indexed f = intersection (f None) (intersection_indexed (fun i => f (Some i))).
Proof.
  intros n f. apply set_ext. intros x; split.
  - unfold intersection_indexed; firstorder.
  - intros H [i|]; firstorder.
Qed.

Lemma fintype_union_indexed :
  forall n (f : fintype (S n) -> _),
    union_indexed f = union (f None) (union_indexed (fun i => f (Some i))).
Proof.
  intros n f. apply set_ext. intros x; split.
  - intros [[i|] Hi]; firstorder.
  - firstorder.
Qed.

Lemma intersection_finite_open :
  forall (n : nat) (f : fintype n -> _), (forall i, open (f i)) -> open (intersection_indexed f).
Proof.
  induction n.
  - intros f H.
    erewrite set_ext; [exact space_open|].
    intros x. unfold intersection_indexed, space. split; [tauto|intros _ []].
  - intros f H.
    rewrite fintype_intersection_indexed.
    apply intersection_open; auto.
Qed.

Lemma union_finite_closed :
  forall (n : nat) (f : fintype n -> _), (forall i, closed (f i)) -> closed (union_indexed f).
Proof.
  intros n f H.
  unfold closed in *.
  rewrite compl_union_indexed.
  apply intersection_finite_open.
  exact H.
Qed.

Definition compact (K : E -> Prop) :=
  forall I (f : I -> _), (forall i, open (f i)) -> subset K (union_indexed f) ->
                   exists (n : nat) (g : fintype n -> I), subset K (union_indexed (fun t => f (g t))).

Fixpoint remove_nones (I : Type) (n : nat) (f : fintype n -> option I) : { m : nat & fintype m -> I } :=
  match n, f with
  | O, _ => existT _ O (fun (z : fintype O) => match z with end)
  | S n, f =>
    let mg := remove_nones I n (fun (x : fintype n) => f (Some x)) in
    match f None with
    | None => mg
    | Some i => existT _ (S (projT1 mg)) (fun (z : fintype (S (projT1 mg))) => match z with None => i | Some z => projT2 mg z end)
    end
  end.

Lemma remove_none_correct_left :
  forall I n f i, (exists z, f z = Some i) -> (exists z, projT2 (remove_nones I n f) z = i).
Proof.
  intros I. induction n.
  - intros f i. simpl. intros [[]].
  - intros f i [[z|] Hz].
    + destruct (IHn (fun z => f (Some z)) i) as [z1 Hz1]; [eauto|].
      simpl; destruct (f None); [exists (Some z1)|exists z1]; simpl; apply Hz1.
    + simpl. unfold fintype in Hz. rewrite Hz. simpl.
      exists None; reflexivity.
Qed.

Lemma remove_none_correct_right :
  forall I n f i, (exists z, projT2 (remove_nones I n f) z = i) -> (exists z, f z = Some i).
Proof.
  intros I. induction n.
  - intros f i. simpl. intros [[]].
  - intros f i [z Hz].
    simpl in *.
    fold fintype in z, Hz. destruct (f None) as [j|] eqn:HfNone; simpl in *.
    + destruct z as [z|]; [|exists None; congruence].
      destruct (IHn (fun z => f (Some z)) i) as [z1 Hz1]; [eauto|].
      exists (Some z1); auto.
    + destruct (IHn (fun z => f (Some z)) i) as [z1 Hz1]; [eauto|].
      exists (Some z1); auto.
Qed.

Lemma remove_none_correct :
  forall I n f i, (exists z, f z = Some i) <-> (exists z, projT2 (remove_nones I n f) z = i).
Proof.
  intros I n f i; split; [apply remove_none_correct_left|apply remove_none_correct_right].
Qed.

Lemma fintype_choice :
  forall (n : nat) (A : fintype n -> Type) (R : forall i, A i -> Prop), (forall i, exists a, R i a) -> exists f, forall i, R i (f i).
Proof.
  induction n.
  - intros A R H. exists (fun (z : fintype O) => match z with end). intros [].
  - intros A R H.
    destruct (IHn (fun x => A (Some x)) (fun x => R (Some x))) as [f Hf]; [intros i; apply (H (Some i))|].
    destruct (H None) as [z Hz].
    exists (fun x => match x with None => z | Some x => f x end).
    intros [i|]; auto.
Qed.

Lemma compact_closed_intersection :
  forall K C, compact K -> closed C -> compact (intersection K C).
Proof.
  intros K C Hk Hc I f Hopen Hcover.
  specialize (Hk (option I) (fun i => match i with None => compl C | Some i => f i end)).
  destruct Hk as [n [g Hg]].
  - intros [i|]; [apply Hopen|exact Hc].
  - intros x Hx. destruct (classic (C x)).
    + unfold intersection in Hcover; destruct (Hcover x) as [i Hi]; [tauto|exists (Some i); auto].
    + exists None; tauto.
  - eexists; exists (projT2 (remove_nones _ _ g)).
    intros x [Hkx Hcx].
    specialize (Hg x Hkx).
    destruct Hg as [t Ht].
    destruct (g t) as [i|] eqn:Hgt; [|unfold compl in Ht; tauto].
    assert (Ht2 : exists t, projT2 (remove_nones _ _ g) t = i) by (apply remove_none_correct_left; firstorder).
    destruct Ht2 as [t2 Ht2]; exists t2; rewrite Ht2. auto.
Qed.

Lemma compact_closed_subset :
  forall K C, compact K -> closed C -> subset C K -> compact C.
Proof.
  intros K C HK HC Hsub.
  replace C with (intersection K C) by (apply set_ext; firstorder).
  apply compact_closed_intersection; auto.
Qed.

Definition closure (A : E -> Prop) := intersection_all (fun C => closed C /\ subset A C).
Lemma closure_contains :
  forall A, subset A (closure A).
Proof.
  intros A x Hx C [Hc1 Hc2]; auto.
Qed.

Lemma closure_closed :
  forall A, closed (closure A).
Proof.
  intros A.
  apply intersection_all_closed.
  firstorder.
Qed.

Lemma closure_smallest_closed :
  forall A C, subset A C -> closed C -> subset (closure A) C.
Proof.
  intros A C Hcontains Hclosed x Hclos.
  apply Hclos.
  split; auto.
Qed.

Lemma closure_closed_eq :
  forall A, closed A -> closure A = A.
Proof.
  intros A Hclosed. apply set_ext.
  firstorder using closure_contains, closure_smallest_closed.
Qed.

Lemma closure_intersection_subset :
  forall A B, subset (closure (intersection A B)) (intersection (closure A) (closure B)).
Proof.
  intros A B.
  apply closure_smallest_closed.
  - firstorder using closure_contains.
  - apply intersection_closed; apply closure_closed.
Qed.

Lemma closure_intersection_finite_subset :
  forall n (f : fintype n -> _), subset (closure (intersection_indexed f)) (intersection_indexed (fun i => closure (f i))).
Proof.
  induction n.
  - intros f x _ [].
  - intros f.
    rewrite fintype_intersection_indexed.
    eapply subset_transitive; [apply closure_intersection_subset|].
    rewrite fintype_intersection_indexed.
    firstorder.
Qed.

Definition interior (A : E -> Prop) := union_all (fun B => open B /\ subset B A).
Lemma interior_contained :
  forall (A : E -> Prop), subset (interior A) A.
Proof.
  intros A x [B [[Hopen Hcontains] HB]].
  apply Hcontains; auto.
Qed.

Lemma interior_open :
  forall A, open (interior A).
Proof.
  intros A.
  apply union_all_open.
  firstorder.
Qed.

Lemma interior_biggest_open :
  forall A B, subset B A -> open B -> subset B (interior A).
Proof.
  intros A B Hcontains Hopen x HB.
  exists B; tauto.
Qed.

Lemma interior_open_eq :
  forall A, open A -> interior A = A.
Proof.
  intros A Hopen. apply set_ext.
  firstorder using interior_contained, interior_biggest_open.
Qed.

Lemma closure_subset :
  forall A B, subset A B -> subset (closure A) (closure B).
Proof.
  intros A B Hsub.
  apply closure_smallest_closed; [|apply closure_closed].
  eapply subset_transitive; [apply Hsub|apply closure_contains].
Qed.

Lemma interior_subset :
  forall A B, subset A B -> subset (interior A) (interior B).
Proof.
  intros A B Hsub.
  apply interior_biggest_open; [|apply interior_open].
  eapply subset_transitive; [apply interior_contained|apply Hsub].
Qed.

Definition frontier A := intersection (closure A) (compl (interior A)).

Lemma frontier_closed :
  forall A, closed (frontier A).
Proof.
  intros A.
  apply intersection_closed.
  - apply closure_closed.
  - unfold closed. rewrite compl_invol. apply interior_open.
Qed.

Definition neighb (x : E) A := exists U, open U /\ U x /\ subset U A.

Lemma neighb_intersection :
  forall x A B, neighb x A -> neighb x B -> neighb x (intersection A B).
Proof.
  intros x A B [U HU] [V HV].
  exists (intersection U V).
  split; [|split].
  - apply intersection_open; tauto.
  - unfold intersection; tauto.
  - unfold subset in *; firstorder.
Qed.

Lemma neighb_intersection_finite :
  forall x n (f : fintype n -> _), (forall i, neighb x (f i)) -> neighb x (intersection_indexed f).
Proof.
  intros x. induction n.
  - intros f H. exists space. split; [apply space_open|].
    split; [firstorder|].
    intros _ _ [].
  - intros f H. rewrite fintype_intersection_indexed.
    apply neighb_intersection; auto.
Qed.

Lemma open_neighb :
  forall A x, open A -> A x -> neighb x A.
Proof.
  intros A x Hopen Hin. exists A.
  split; [auto|].
  split; [auto|].
  intros y; auto.
Qed.

Lemma neighb_interior :
  forall x A, neighb x A -> interior A x.
Proof.
  intros x A [U [HU [HUx Hsub]]].
  apply interior_subset in Hsub.
  rewrite (interior_open_eq U) in Hsub by auto.
  firstorder.
Qed.

Lemma neighb_subset :
  forall x A B, neighb x A -> subset A B -> neighb x B.
Proof.
  intros x A B [U HU] Hsub. exists U.
  firstorder.
Qed.

Lemma neighb_contains_open :
  forall (A : E -> Prop), (forall x, A x -> exists B, neighb x B /\ subset B A) -> open A.
Proof.
  intros A Hneighb.
  erewrite set_ext; [apply (interior_open A)|].
  intros x; split; [|apply interior_contained].
  intros Hx.
  destruct (Hneighb x Hx) as [B [[U [HUopen [HUx HUsub]]] Hsub]].
  exists U. split; [|auto]; split; [auto|].
  eapply subset_transitive; [apply HUsub|apply Hsub].
Qed.

Definition separated_T2 :=
  forall x y, x <> y -> exists U V, neighb x U /\ neighb y V /\ disjoint U V.

Lemma point_set_separate_func :
  forall x (A : E -> Prop) (P : E -> (E -> Prop) -> (E -> Prop) -> Prop),
    (forall y, A y -> exists U V, P y U V) -> ~(A x) -> exists (f : sig A -> ((E -> Prop) * (E -> Prop))),
      forall y, P (proj1_sig y) (fst (f y)) (snd (f y)).
Proof.
  intros x A P HP Hx.
  apply choice with (R := fun y fy => P (proj1_sig y) (fst fy) (snd fy)).
  intros [y Hy].
  destruct (HP _ Hy) as [U [V HUV]]. exists (U, V).
  simpl; exact HUV.
Qed.

Lemma compact_closed :
  separated_T2 -> forall K, compact K -> closed K.
Proof.
  intros Hsep K HK.
  apply neighb_contains_open.
  intros x Hx.
  destruct (choice (fun (y : sig K) UV => open (fst UV) /\ fst UV x /\ open (snd UV) /\ snd UV (proj1_sig y) /\ disjoint (fst UV) (snd UV))) as [f Hf].
  - intros [y Hy].
    destruct (Hsep x y (ltac:(congruence))) as [U [V [HU [HV HUV]]]].
    destruct HU as [U1 HU1]; destruct HV as [V1 HV1].
    exists (U1, V1); simpl.
    firstorder.
  - destruct (HK _ (fun y => (snd (f y)))) as [n [g Hg]].
    + firstorder.
    + intros y Hy. exists (exist _ y Hy). apply Hf.
    + exists (intersection_indexed (fun t => fst (f (g t)))). split.
      * apply open_neighb; [|firstorder].
        apply intersection_finite_open. firstorder.
      * apply subset_compl; rewrite compl_invol, compl_intersection_indexed.
        intros y Hy; destruct (Hg y Hy) as [t Ht]; exists t.
        firstorder.
Qed.

Definition locally_compact :=
  separated_T2 /\ (forall x, exists K, compact K /\ neighb x K).

Definition locally_compact_compact_neighb_base :
  locally_compact -> forall x U, neighb x U -> exists K, compact K /\ neighb x K /\ subset K U.
Proof.
  intros [Hsep Hcneigh] x U HU.
  destruct (Hcneigh x) as [K [HK HKn]].
  assert (HUKx : neighb x (intersection U K)) by (apply neighb_intersection; auto).
  assert (HF : subset (frontier (intersection U K)) K).
  {
    enough (subset (closure (intersection U K)) K) by firstorder.
    apply closure_smallest_closed; [|apply compact_closed; auto].
    firstorder.
  }
  assert (HFx : ~ (frontier (intersection U K)) x) by firstorder using neighb_interior.
  assert (HFK : compact (frontier (intersection U K))) by (eapply compact_closed_subset; eauto using frontier_closed).
  destruct (choice (fun (y : sig (frontier (intersection U K))) AB =>
                      subset (fst AB) (intersection U K) /\ neighb x (fst AB) /\
                      open (snd AB) /\ snd AB (proj1_sig y) /\ disjoint (fst AB) (snd AB))) as [f Hf].
  {
    intros [y Hy].
    destruct (Hsep x y (ltac:(congruence))) as [A [B [HA [HB Hdisj]]]].
    destruct HB as [B1 HB1].
    exists (intersection A (intersection U K), B1). simpl.
    split; [firstorder|].
    split; [apply neighb_intersection; auto|].
    firstorder.
  }
  destruct (HFK _ (fun x => snd (f x))) as [n [g Hg]].
  - intros i; specialize (Hf i); tauto.
  - intros y Hy; exists (exist _ y Hy); specialize (Hf (exist _ y Hy)); simpl in *; tauto.
  - set (W := closure (intersection (intersection U K) (intersection_indexed (fun t => fst (f (g t)))))).
    assert (HWsub : subset W (intersection U K)).
    + assert (HW : subset W (closure (intersection U K))).
      * apply closure_subset. firstorder.
      * assert (HWdisj : disjoint W (frontier (intersection U K))).
        -- intros y [HWy Hfy].
           destruct (Hg y Hfy) as [t Ht].
           specialize (Hf (g t)).
           apply closure_intersection_subset in HWy. destruct HWy as [_ HWy].
           apply closure_intersection_finite_subset in HWy.
           specialize (HWy t); simpl in HWy.
           generalize (closure_smallest_closed (fst (f (g t))) (compl (snd (f (g t))))); intros H.
           apply H in HWy; [unfold compl in HWy; tauto| |unfold closed; rewrite compl_invol; tauto].
           intros z Hz1 Hz2. firstorder.
        -- unfold frontier in HWdisj.
           assert (subset W (interior (intersection U K))) by (intros z Hz; unfold intersection, compl in *; specialize (HW z); specialize (HWdisj z); tauto).
           eapply subset_transitive; [apply H|apply interior_contained].
    + exists W. split.
      * eapply compact_closed_subset; [apply HK|apply closure_closed|].
        intros z Hz; specialize (HWsub z); unfold intersection in HWsub; tauto.
      * split; [|intros z Hz; specialize (HWsub z); unfold intersection in HWsub; tauto].
        eapply neighb_subset; [|apply closure_contains].
        apply neighb_intersection; [apply HUKx|].
        apply neighb_intersection_finite.
        intros t; specialize (Hf (g t)); tauto.
Qed.

Fixpoint fintype_max (n : nat) (f : fintype n -> nat) :=
  match n, f with
  | O, _ => O
  | S n, _ => max (f None) (fintype_max n (fun i => f (Some i)))
  end.

Lemma fintype_max_gt :
  forall (n : nat) (f : fintype n -> nat) (i : fintype n), f i <= fintype_max n f.
Proof.
  induction n.
  - intros _ [].
  - intros f [i|]; simpl; rewrite PeanoNat.Nat.max_le_iff.
    + right. apply (IHn (fun i => f (Some i)) i).
    + left. reflexivity.
Qed.

Lemma subset_decreasing_sequence :
  forall (f : nat -> _), (forall n, subset (f (S n)) (f n)) -> forall n m, n <= m -> subset (f m) (f n).
Proof.
  intros f H n m Hnm. induction Hnm.
  - firstorder.
  - eapply subset_transitive; [|apply IHHnm]. apply H.
Qed.

Lemma compact_decreasing_intersection :
  separated_T2 ->
  forall (K : nat -> _), (forall n, compact (K n)) -> (forall n, subset (K (S n)) (K n)) ->
                 intersection_indexed K = empty -> exists n, K n = empty.
Proof.
  intros Hsep K Hcompact Hn Hinter.
  destruct (Hcompact O _ (fun n => compl (K (S n)))) as [k [g Hg]].
  - intros i. apply compact_closed; auto.
  - intros x. assert (Hx : ~(intersection_indexed K x)) by (rewrite Hinter; unfold empty; tauto).
    apply not_all_ex_not in Hx. destruct Hx as [[|n] Hx]; firstorder.
  - exists (S (fintype_max k g)).
    apply set_ext; intros x.
    unfold empty; split; [|tauto].
    intros HKx.
    assert (HK0x : K 0 x) by (eapply subset_decreasing_sequence; [exact Hn| |exact HKx]; firstorder).
    specialize (Hg x HK0x).
    destruct Hg as [t Ht]; apply Ht.
    eapply subset_decreasing_sequence; [exact Hn| |exact HKx].
    apply le_n_S. apply fintype_max_gt.
Qed.

Definition dense A := closure A = space.
Definition nonempty (A : E -> Prop) := exists x, A x.

Lemma nonempty_empty_iff :
  forall A, nonempty A <-> A <> empty.
Proof.
  intros A. split.
  - intros [x Hx] H; rewrite H in Hx; unfold empty in *; congruence.
  - intros H.
    assert (H1 : ~(forall x, A x <-> empty x)) by auto using set_ext.
    apply not_all_ex_not in H1.
    destruct H1 as [x Hx]; exists x.
    unfold empty in Hx; tauto.
Qed.

Lemma compact_decreasing_intersection_nonempty :
  separated_T2 ->
  forall (K : nat -> _), (forall n, compact (K n)) -> (forall n, subset (K (S n)) (K n)) ->
                 (forall n, nonempty (K n)) -> nonempty (intersection_indexed K).
Proof.
  intros Hsep K Hcompact Hn Hnonempty.
  rewrite nonempty_empty_iff; intros H.
  apply compact_decreasing_intersection in H; auto.
  destruct H as [n HKn]. specialize (Hnonempty n).
  rewrite nonempty_empty_iff in Hnonempty; congruence.
Qed.

Lemma dense_open_iff :
  forall A, dense A <-> (forall B, nonempty B -> open B -> nonempty (intersection A B)).
Proof.
  intros A.
  split.
  - intros HA B HBne HBopen.
    rewrite nonempty_empty_iff. intros HAB.
    generalize (closure_smallest_closed A (compl B)).
    rewrite HA. intros H.
    enough (subset space (compl B)) by firstorder.
    apply H; [|unfold closed; rewrite compl_invol; auto].
    intros x; assert (intersection A B x <-> empty x) by (rewrite HAB; reflexivity).
    unfold intersection, empty, compl in *. tauto.
  - intros HB.
    apply set_ext. intros x.
    split; [unfold space; tauto|].
    intros _ C [HC HCsub].
    destruct (classic (C x)) as [HCx | HCx]; [auto|exfalso].
    specialize (HB (compl C) (ltac:(exists x; unfold compl; auto)) HC).
    firstorder.
Qed.

Lemma locally_compact_open_contains :
  locally_compact -> forall A, open A -> nonempty A -> exists K, compact K /\ nonempty (interior K) /\ subset K A.
Proof.
  intros Hlc A Hopen [x Hx].
  destruct (locally_compact_compact_neighb_base Hlc x A) as [K HK]; [apply open_neighb; auto|].
  exists K.
  split; [tauto|]. split; [|tauto].
  exists x. apply neighb_interior; tauto.
Qed.

Theorem Baire :
  locally_compact -> forall (A : nat -> _), (forall n, open (A n)) -> (forall n, dense (A n)) -> dense (intersection_indexed A).
Proof.
  intros Hlc A Hopen Hdense.
  destruct (choice (fun (U : sig (fun U => open U /\ nonempty U)) K => compact K /\ nonempty (interior K) /\ subset K (proj1_sig U))) as [f Hf].
  - intros [U [HUopen HUne]]. destruct (locally_compact_open_contains Hlc U HUopen HUne) as [K HK]; exists K.
    exact HK.
  - set (g := fun n U => intersection (A (pred n)) (interior (f U))).
    assert (Hg : forall n U, open (g n U) /\ nonempty (g n U)).
    + intros n U. unfold g.
      split; [eauto using intersection_open, interior_open|].
      apply dense_open_iff; [apply Hdense| |apply interior_open].
      specialize (Hf U); tauto.
    + rewrite dense_open_iff.
      intros V HVne HVopen. assert (HV : open V /\ nonempty V) by tauto.
      set (T := fix T (n : nat) {struct n} : _ := exist (fun U => open U /\ nonempty U) (g n (match n with 0 => exist _ V HV | S m => T m end)) (ltac:(apply Hg))).
      set (K := fun n => f (T n)).
      generalize (compact_decreasing_intersection_nonempty (ltac:(unfold locally_compact in Hlc; tauto)) K).
      intros H.
      assert (HK : nonempty (intersection_indexed K)).
      * apply H.
        -- intros n; specialize (Hf (T n)); tauto.
        -- intros n. unfold K.
           specialize (Hf (T (S n))); simpl in Hf; simpl.
           destruct Hf as [Hf1 [Hf2 Hf3]].
           eapply subset_transitive; [exact Hf3|].
           unfold g.
           eapply subset_transitive; [|apply interior_contained].
           firstorder.
        -- intros n; destruct (Hf (T n)) as [Hf1 [Hf2 Hf3]]. unfold K.
           destruct Hf2 as [x Hf2]. apply interior_contained in Hf2. exists x; auto.
      * destruct HK as [x Hx].
        exists x.
        assert (HT : forall n, proj1_sig (T n) x).
        -- intros n. specialize (Hx n). unfold K in Hx.
           destruct (Hf (T n)) as [Hf1 [Hf2 Hf3]]; apply Hf3; auto.
        -- split.
           ++ intros n. specialize (HT (S n)).
              simpl in HT. unfold g in HT. simpl in HT.
              firstorder.
           ++ specialize (HT 0). simpl in HT. unfold g in HT. simpl in HT.
              destruct HT as [_ HT]. apply interior_contained in HT.
              firstorder.
Qed.

End TopoSpace.