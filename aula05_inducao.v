(** * Indu\u00e7\u00e3o em Coq *)

Add LoadPath "/Users/marcosmonteiro/desktop/coq".
Require Export aula04_provas.

(* ############################################### *)
(** * Prova por indu\u00e7\u00e3o *)

(** Nem sempre \u00e9 poss\u00edvel provar somente por:
    - simplifica\u00e7\u00e3o
    - reescrita
    - an\u00e1lise de casos *)

(** Na aula passada, vimos o seguinte teorema *)

Print plus_O_n.

(** E se quisermos provar n + 0 = n? *)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0 .
Proof.
  intros n.
  simpl. (* n\u00e3o simplifica nada *)
  try reflexivity.
(** [reflexivity] n\u00e3o funciona, pois [n]
    em [n + 0] \u00e9 um n\u00famero arbitr\u00e1rio e
    n\u00e3o caso padr\u00e3o com o [+] *)
  Print NatPlayground2.plus.
Abort.

(** An\u00e1lise de casos tamb\u00e9m n\u00e3o ajuda. *)

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    simpl. reflexivity. (* quando [n] \u00e9 0, funciona *)
  - (* n = S n' *)
    simpl.       (* aqui [n] \u00e9 [S n'],
                  outro n\u00famero arbitr\u00e1rio *)
Abort.

(** Chamadas sucessivas a [destruct n']
    tamb\u00e9m n\u00e3o ajudaria. Precisamos de indu\u00e7\u00e3o. *)

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'.
                   reflexivity.
Qed.

(** Outro exemplo. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.
Qed.

(** Nota: [induction] move automaticamente
    vari\u00e1veis quantificadas para o contexto. *)

(** **** Exercise: (basic_induction)  *)
(** Prove os seguintes teoremas. Ser\u00e1 necess\u00e1rio
    buscar por resultados previamente provados. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.


(* ############################################### *)
(** * Provas aninhadas *)

(** \u00c9 possivel/aconselh\u00e1vel quebrar provas maiores
    em subprovas. Isto pode ser feito a partir de
    [Lemma], como tamb\u00e9m a partir de "sub-teoremas". *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  {
    simpl. reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

(** Outro exemplo: veja que a t\u00e1tica [rewrite]
    n\u00e3o \u00e9 muito "inteligente" sobre onde aplicar
    a reescrita no objetivo. *)

Theorem plus_rearrange_firsttry :
  forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q. Print plus_comm.
  (* S\u00f3 queremos trocar (n + m) por (m + n). *)
  rewrite -> plus_comm.
  (* Mas  reescrita n\u00e3o faz o que queremos. *)
Abort.

(** Veja a pr\u00f3xima prova. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

(** Mas tamb\u00e9m funcionaria s\u00f3 instanciando
    [n] e [m], deixando [p] e [q] ligados. *)
Theorem plus_rearrange' : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m.
  rewrite -> plus_comm. reflexivity.
Qed.

(** Contudo, a ordem das quantifica\u00e7\u00f5es
    pode vir a ser um problema. *)

Theorem plus_rearrange'' : forall n p q m : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.

(* ############################################### *)
(** * Mais exerc\u00edcios *)

(** **** Exercise: (mult_comm)  *)
(** Use [assert] para ajudar na prova. N\u00e3o \u00e9
    necess\u00e1rio usar indu\u00e7\u00e3o. *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite plus_assoc. rewrite plus_assoc.
  assert (H: n + m = m + n).
  { rewrite plus_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

(** Agora, prove comutatividade da multiplica\u00e7\u00e3o.
    Talvez seja necess\u00e1rio provar um teorema auxiliar.
    O teorema [plus_swap] ser\u00e1 \u00fatil. *)

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction m.
  - simpl. rewrite <- mult_n_O. reflexivity.
  - rewrite <- mult_n_Sm. simpl. rewrite plus_comm.
  assert (H: m * n = n * m).
  { rewrite IHm. reflexivity. }
  rewrite IHm. reflexivity.
Qed.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Induction
  https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html
*)
