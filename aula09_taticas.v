(** * Mais t\u00e1ticas b\u00e1sicas em Coq *)

(** Em particular, veremos:
    - provas "forward-style" e "backward-style"
    - como racicionar sobre construtores
      (fun\u00e7\u00f5es injetoras e disjuntas)
    - como fortalecer uma hip\u00f3tese de indu\u00e7\u00e3o
    - mais detalhes sobre como raciocinar por casos. *)

Set Warnings "-notation-overridden,-parsing".
Add LoadPath "/Users/marcosmonteiro/desktop/coq".
Require Export aula08_ordem.

(* ############################################### *)
(** * A t\u00e1tica [apply] *)

(** Quando o objetivo de prova \u00e9 _exatamente_ o
    mesmo de alguma hip\u00f3tese do contexto
    ou algum lemma previamente provado. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p. intros eq1 eq2.
  rewrite <- eq1.

(** Podemos terminar a prova escrevendo
    "[rewrite -> eq2. reflexivity.]". A t\u00e1tica
    [apply] gera o mesmo efeito. *)

  apply eq2.
Qed.

(** A t\u00e1tica [apply] tamb\u00e9m funciona com hip\u00f3teses
    condicionais. Se a afirma\u00e7\u00e3o sendo aplicada for
    uma implica\u00e7\u00e3o, as premissas da implica\u00e7\u00e3o
    ser\u00e3o adicionadas aos subobjetivos de prova
    a serem provados. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.
Qed.

(** Mais um exemplo a seguir. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat),
      (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.
Qed.

(** A conclus\u00e3o da afirma\u00e7\u00e3o aplicada precisa
    casar exatamente com o objetivo de prova.
    N\u00e3o funciona se o LHS e o RHS estiverem
    invertidos. Contudo, podemos usar outra
    t\u00e1tica: [symmetry]. *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H. simpl.
  try apply H. (* N\u00e3o faz nada. *)
  symmetry.
  simpl. (* Opcional, pois [apply]
         faz [simpl] se necess\u00e1rio. *)
  apply H.
Qed.

(** **** Exercise: (apply_exercise1)  *)
(** Antes, prove os seguintes resultados auxiliares. *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite app_assoc. reflexivity.
Qed.


Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' -> l' = rev l.
Proof.
  intros. rewrite H. rewrite rev_involutive. reflexivity.
Qed.


(* ############################################### *)
(** * A t\u00e1tica [apply ... with ...] *)

(** O seguinte exemplo usa [rewrite] duas vezes para
    obter [[e,f]] a partir de [[a,b]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. apply eq2.
Qed.

(** De uma forma geral, podemos provar que a
    igualdade \u00e9 transitiva. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2.
  reflexivity.
Qed.

(** Para usar trans_eq no seguinte exemplo,
    preciamos de uma varia\u00e7\u00e3o da t\u00e1tica [apply]. *)

Example trans_eq_example' :
  forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  
(** Ao aplicar [apply trans_eq], Coq n\u00e3o consegue
    identificar como instanciar [m]. Precisamos informar
    usando [with (m := [c,d])]. *)

  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

(** **** Exercise: (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros. apply trans_eq with(m:= m). apply H0. apply H.
Qed.


(* ############################################### *)
(** * A t\u00e1tica [inversion] *)

(** Lembre que construtores de um mesmo tipo s\u00e3o
    fun\u00e7\u00f5es injetoras e disjuntas. A t\u00e1tica
    [inversion] permite explorar estes dois fatos. *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.

(** Ao usar [inversion H], pedimos que Coq
    gere todas as equa\u00e7\u00f5es que ele consegue
    inferir a partir de [H], al\u00e9m de realizar
    reescrita de vari\u00e1veis a partir das equa\u00e7\u00f5es
    derivadas. *)

  inversion H.
  reflexivity.
Qed.

(** Outro exemplo. *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H.
  reflexivity. 
Qed.

(** Podemos nomear as equa\u00e7\u00f5es que [inversion]
    gera com uma cl\u00e1usula [as ...]. *)

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H. inversion H as [Hnm]. 
  reflexivity.
Qed.

(** **** Exercise: (inversion_ex3)  *)
Example inversion_ex3 : forall (X : Type)
  (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
 intros. inversion H0. reflexivity.
Qed.

(** Quando uma hip\u00f3tese considera uma igualdade
    entre construtores diferentes, a t\u00e1tica
    [inversion] resolve o objetivo de prova
    imediatamente. *)
    
Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl. intros H.

(** Ao usar [inversion] em [H],
    Coq conclui a prova. *)
    
    inversion H.
Qed.

(** Isto \u00e9 uma inst\u00e2ncia do _princ\u00edpio da explos\u00e3o_,
    que afirma que a partir de uma hip\u00f3tese
    contradit\u00f3ria, pode-se concluir qualquer fato.
    
    Em Latim: ex falso (sequitur) quodlibet (EFQ),
    Em Ingl\u00eas: from falsehood, anything (follows) *)

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra.
Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. inversion contra.
Qed.

(** **** Exercise: (inversion_ex6)  *)
Example inversion_ex6 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
 intros. inversion H.
Qed.

(** A injetividade de construtores permite concluir que
    [forall (n m : nat), S n = S m -> n = m]. O converso
    desta implica\u00e7\u00e3o \u00e9 um fato mais geral,
    que pode ser \u00fatil. *)

Theorem f_equal : forall (A B : Type)
  (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof.
  intros A B f x y eq. rewrite eq. reflexivity.
Qed.

Theorem test:
  forall (x y: nat), x = y -> S x = S y.
Proof.
  intros. apply f_equal. apply H.
Qed.

(* ############################################### *)
(** * Usando t\u00e1ticas em hip\u00f3tese *)

(** A maior parte das t\u00e1ticas possui uma variante
    que permite sua aplica\u00e7\u00e3o em uma afirma\u00e7\u00e3o
    do contexto. *)
    
Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H.
Qed.

(** Contudo, [apply L in H] funciona como "forward
    reasoning", enquanto que [apply L], como "backward
    reasoning". *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5  ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H. symmetry in H.
  apply H.
Qed.

(** Provas informais tendem a usar "forward
    reasoning". Coq tende a favorecer o uso de
    "backward reasoning". *)

(** **** Exercise: (plus_n_n_injective)  *)
(** Dica: fa\u00e7a uso de plus_n_Sm. *)

Theorem reversing : forall n m,
    n + n = m + m -> n + m = n + m.
Proof.
  intros. induction n.
  - reflexivity.
  -  reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n.
  - intros. destruct m.
    + reflexivity.
    + simpl in H. inversion H.
  - intros. destruct m.
    + simpl in H. inversion H.
    + do 2 rewrite <- plus_n_Sm in H.
      inversion H. apply IHn in H1. rewrite H1 in H.
      rewrite H1. reflexivity.
Qed.

(* ############################################### *)
(** * Variando a hip\u00f3tese indutiva *)

(** \u00c9 preciso ter cuidado com o uso de [intros];
    com o que se move do objetivo para o contexto
    antes de realizar uma prova por indu\u00e7\u00e3o. Veja
    o exemplo a seguir. *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_FAILED : forall n m,
     double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + simpl in eq. inversion eq.
  - (* n = S n' *) intros eq. destruct m as [| m'].
    + (* m = O *) simpl in eq. inversion eq.
    + (* m = S m' *) apply f_equal.

(** Neste momento, [IHn'] n\u00e3o possui [n' = m'].
    H\u00e1 um [S] extra. Logo, n\u00e3o podemos concluir
    a prova. *)

Abort.

(** O problema aconteceu ao fazer a instancia\u00e7\u00e3o
    universal de [m]. A prova acima diz para Coq
    considerar um [n] e um [m] particular, e agora
    tentar provar que, se [double n = double m] para
    estes valores particulares de [n] e [m],
    ent\u00e3o [n = m]. Pela indu\u00e7\u00e3o, tentamos provar
    que para todo [n]:

      - [P n] = "if [double n = double m], then [n = m]"

    \u00e9 verdade, mostrando que

      - [P O]

         (i.e., "if [double O = double m] then [O = m]") e

      - [P n -> P (S n)]

        (i.e., "if [double n = double m] then [n = m]"
        implies "if [double (S n) = double m]
        then [S n = m]"
    
    o que n\u00e3o faz sentido para um [m] arbitr\u00e1rio. Veja
    o seguinte exemplo ([m = 5]), temos que:

      - [Q] = "if [double n = 10] then [n = 5]"

    o que n\u00e3o ajuda a provar a pr\u00f3xima afirma\u00e7\u00e3o:

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    \u00c9 preciso fazer a indu\u00e7\u00e3o sem mover
    [m] para o contexto.
      
*)

Theorem double_injective : forall n m,
     double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.
  - (* n = S n' *) simpl.

(** Veja que o objetivo de prova e a IH
    s\u00e3o diferentes neste teorema em rela\u00e7\u00e3o
    ao anterior. *)
    
    intros m eq. destruct m as [| m'].
    + (* m = O *) inversion eq.
    + (* m = S m' *) apply f_equal.
      apply IHn'. simpl in eq. inversion eq. reflexivity.
Qed.

(** **** Exercise: (beq_nat_true)  *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n.
  - intros m. induction m.
    + simpl. reflexivity.
    + simpl. intros H. inversion H.
  - intros m. induction m.
    + simpl. intros H. inversion H.
    + simpl. intros H. apply IHn in H. apply f_equal. apply H.
Qed.

(** Nem sempre fazer menos instancia\u00e7\u00f5es universais
    (para obter IHs mais gerais) \u00e9 suficiente. Veja
    o exemplo a seguir. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m -> n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
    (* N\u00e3o temos como progredir neste ponto. *)
Abort.

(** O problema \u00e9 que para fazer indu\u00e7\u00e3o sobre [m],
    \u00e9 preciso primeiro instanciar [n]. Para resolver
    esta situa\u00e7\u00e3o, \u00e9 preciso generalizar [n], antes
    de fazer indu\u00e7\u00e3o sobre [m]. Isto \u00e9 feito pela
    t\u00e1tica [generalize dependent]. *)

Theorem double_injective_take2 : forall n m,
     double n = double m -> n = m.
Proof.
  intros n m. generalize dependent n.
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. inversion eq. reflexivity.
Qed.

(** **** Exercise: (gen_dep_practice)  *)
(** Prova com indu\u00e7\u00e3o sobre [l]. *)

Theorem nth_error_after_last:
  forall (n : nat) (X : Type) (l : list X),
     length l = n -> nth_error l n = None.
Proof.
 (* COMPLETE AQUI *) Admitted.
 
(* ############################################### *)
(** * T\u00e1tica [unfold] *)

(** Como j\u00e1 vimos, em alguns casos, precisamos
    expandir uma defini\u00e7\u00e3o para poder manipul\u00e1-la.
    A t\u00e1tica [unfold] tem este prop\u00f3sito. Considere
    o exemplo a seguir.*)

Definition square n := n * n.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. Search (_ + (_)).
    rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite mult_plus_distr_r.
    rewrite IHn'. reflexivity.
Qed.

Lemma square_mult_try1 : forall n m,
  square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  
(** [simpl] n\u00e3o tem efeito aqui. Contudo,
    ao expandir a defini\u00e7\u00e3o observamos que
    podemos usar associatividade (prova
    anterior) e comutatividade da
    multiplica\u00e7\u00e3o. *)

  unfold square.
  do 2 rewrite mult_assoc. 
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. reflexivity.
Qed.

(** T\u00e1ticas como [simpl], [reflexivity] e [apply]
    normalmente expandem defini\u00e7\u00f5es de fun\u00e7\u00f5es
    automaticamente, quando isto traz progresso
    para a prova. Veja o exemplo a seguir. *)
    
Definition foo (x: nat) := 5.

Fact silly_fact_1 :
  forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

(** Contudo, isto nem sempre acontece. *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.
  
Fact silly_fact_2_FAILED :
  forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* N\u00e3o faz nada! *)
Abort.

(** O motivo \u00e9 que, ao expandir a defini\u00e7\u00e3o de
    bar, obt\u00e9m-se um "match" envolvendo [m],
    que n\u00e3o pode ser simplificado. Coq n\u00e3o
    percebe que os casos do "match" s\u00e3o iguais.
    
    Uma possibilidade \u00e9 destruir [m] o que
    permite progresso. *)
    
Fact silly_fact_2 :
  forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** Outra possibilidade, \u00e9 usar [unfold]
    e ent\u00e3o observar que podemos usar
    destruct para terminar a prova. *)

Fact silly_fact_2' :
  forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

(* ############################################### *)
(** * Usando [destruct] em express\u00f5es compostas *)

(** \u00c9 poss\u00edvel usar [destruct] em express\u00f5es. *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    - (* beq_nat n 3 = true *)
      reflexivity.
    - (* beq_nat n 3 = false *)
      destruct (beq_nat n 5).
      + (* beq_nat n 5 = true *)
        reflexivity.
      + (* beq_nat n 5 = false *)
        reflexivity.
Qed.

(** De forma geral, seja [e] do tipo indutivo [T],
    ao fazer [destruct e], cria-se um objetivo
    para cada construtor [c] de [T], em cada um
    substituindo as ocorr\u00eancias de [e] por [c]
    (tanto no contexto como no objetivo). *)

(** **** Exercise: (combine_split)  *)
(** Seja a seguinte fun\u00e7\u00e3o [split], prove
    que [split] e [combine] s\u00e3o inversas
    no seguinte sentido. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split :
  forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2) ->
    combine l1 l2 = l.
Proof.
 (* COMPLETE AQUI *) Admitted.

(** No entanto, \u00e0s vezes, ao destruir,
    podemos perder informa\u00e7\u00e3o importante
    para concluir a prova. *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd_FAILED :
  forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  - 
  (* n\u00e3o \u00e9 poss\u00edvel progredir *)
Abort.

(** O problema neste \u00e9 caso \u00e9 que ao fazer
    [destruct (beq_nat n 3)], perdemos a
    informa\u00e7\u00e3o (beq_nat n 3) e como ela
    foi destru\u00edda. Veja como contornar
    este problema a seguir. *)

Theorem sillyfun1_odd :
  forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* Adiciona-se ao contexto a hip\u00f3tese
     Heqe3 dizendo como (beq_nat n 3)
     foi destru\u00eddo em cada caso. *)
    - (* e3 = true *)
      Print beq_nat_true.
      apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
      destruct (beq_nat n 5) eqn:Heqe5.
        + (* e5 = true *)
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) inversion eq.
Qed.

(** **** Exercise: (destruct_eqn_practice)  *)

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
 (* COMPLETE AQUI *) Admitted.

(** * Resumo das t\u00e1ticas vistas at\u00e9 o momento
      - [intros]
      - [reflexivity]
      - [apply]
      - [apply... in H]
      - [apply... with...]
      - [simpl]
      - [simpl in H]
      - [rewrite]
      - [rewrite ... in H]
      - [symmetry]
      - [symmetry in H]
      - [unfold]
      - [unfold... in H]
      - [destruct... as...]
      - [destruct... eqn:...]
      - [induction... as...]
      - [inversion]
      - [assert (H: e)]
      - [generalize dependent x] *)

(** **** Exercise: (beq_nat_sym)  *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
 (* COMPLETE AQUI *) Admitted.

(** **** Exercise: (split_combine)  *)
(** Que propriedade \u00e9 necess\u00e1ria sobre [l1] e [l2]
    para que [split] [combine l1 l2 = (l1,l2)]
    seja uma afirma\u00e7\u00e3o verdadeira?
    
    [Prop] significa que a defini\u00e7\u00e3o est\u00e1 dando
    um nome a uma proposi\u00e7\u00e3o l\u00f3gica.
    
    Complete a defini\u00e7\u00e3o de [split_combine_statement]
    com uma propriedade que diz quando [split] \u00e9 a
    inversa de [combine]. Ent\u00e3o, prove esta propriedade.
    
    Dica: deixe sua hip\u00f3tese indutiva o mais geral
    poss\u00edvel (evitando fazer [intros] mais do o
    necess\u00e1rio). *)

Definition split_combine_statement : Prop
(* SUBSTITUA COM ":= _sua_defini\u00e7\u00e3o_ ." *). Admitted.

Theorem split_combine : split_combine_statement.
Proof.
 (* COMPLETE AQUI *) Admitted.

(** **** Exercise: (filter_exercise)  *)
Theorem filter_exercise :
  forall (X : Type) (test : X -> bool)
         (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
 (* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - More basic tatics
  https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html
*)
