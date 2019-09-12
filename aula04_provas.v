(** * Provas em Coq *)

(** - Require: carrega uma biblioteca
      e.g., Require Coq.Lists.List.
    - Import: coloca as defini\u00e7\u00f5es em escopo
      (sem o Import: precisar referenciar
      os nomes pela identifica\u00e7\u00e3o completa;
      i.e., fully qualified)
      e.g., Print List.map vs. Print map
    - Require Import: carrega e coloca em escopo
      N\u00e3o se usa Require ao importar sub-m\u00f3dulos
      e.g., Import ListNotations
    - Require Export: carrega, coloca em escopo
      e torna o m\u00f3dulo vis\u00edvel onde o m\u00f3dulo
      atual for utilizado

  Mais informa\u00e7\u00f5es:
  - https://coq.inria.fr/tutorial/3-modules
  - https://stackoverflow.com/questions/47973317/require-import-require-import
*)

(** Para importar o arquivo da aula passada,
    \u00e9 preciso ter a vers\u00e3o compilada dele.
    Comando: coqc aula02_gallina.v *)
Add LoadPath "/Users/marcosmonteiro/desktop/coq".
Require Export aula03_gallina.

(* ############################################### *)
(** * Prova por simplifica\u00e7\u00e3o *)

(** Lidando com o quantificador universal:
    considerar a prova no contexto de um membro
    arbitrariamente escolhido no dom\u00ednio.

    Exemplo:
    Todos os laborat\u00f3rios possuem datashow.
    Se h\u00e1 datashow, h\u00e1 uma tela de proje\u00e7\u00e3o.
    Logo, h\u00e1 tela de proje\u00e7\u00e3o em todos os laborat\u00f3rios.

    Formaliza\u00e7\u00e3o do argumento:
    1. forall l : lab, D(l)            [premissa]
    2. forall l : lab, D(l) -> T(l)    [premissa]
    3. D(a)         [Instancia\u00e7\u00e3o Universal em 1]
    4. D(a) -> T(a) [Instancia\u00e7\u00e3o Universal em 2]
    5. T(a)               [modus ponens em 3 e 4]
    6. forall l : lab, T(l) [Gen. Universal em 5]

    Idealmente, ao instanciar, devemos usar
    um s\u00edmbolo diferente do ligado pela
    quantifica\u00e7\u00e3o universal (e.g., x vs. a).
    Na pr\u00e1tica, usa-se o mesmo s\u00edmbolo.

    1. forall l : lab, D(l)            [premissa]
    2. forall l : lab, D(l) -> T(l)    [premissa]
    3. D(l)         [Instancia\u00e7\u00e3o Universal em 1]
    4. D(l) -> T(l) [Instancia\u00e7\u00e3o Universal em 2]
    5. T(l)               [modus ponens em 3 e 4]
    6. forall l : lab, T(l) [Gen. Universal em 5]    
    
    Em Coq, a t\u00e1tica [intro] ou [intros] realiza
    IU (instancia\u00e7\u00e3o universal), enquanto que
    [generalize dependent] realiza GU
    (generaliza\u00e7\u00e3o universal). A segunda t\u00e1tica
    veremos depois.

    Uma t\u00e1tica \u00e9 um comando usado entre [Proof]
    e [Qed] para guiar o processo de provar
    alguma afirma\u00e7\u00e3o.

    Palavras [Theorem], [Example] e [Lemma]
    possuem praticamente o mesmo significado.
*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

(** [reflexivity] j\u00e1 realiza alguma simplifica\u00e7\u00e3o
    automaticamente. Mesmo assim, o uso de [simpl]
    pode ser interessante para ver o estado
    intermedi\u00e1rio da prova]. *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.
Qed.

(** Inclusive, [reflexivity] realiza algumas
    simplifica\u00e7\u00f5es adicionais; por exemplo,
    expandindo defini\u00e7\u00f5es (ver exerc\u00edcio nandb'
    da aula passada = aula02_gallina.v.

    [reflexivity] faz isto, pois se a t\u00e1tica
    funcionar, a prova \u00e9 conclu\u00edda e n\u00e3o
    precisaremos ver proposi\u00e7\u00f5es eventualmente
    mais complicadas em fun\u00e7\u00e3o do processo
    de expans\u00e3o. *)

(** Outros exemplos de prova *)

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.
Qed.

(** O sufixo [_l] significa "on the left" *)

(* ############################################### *)
(** * Prova por reescrita *)

(** Na pr\u00f3xima prova, a conclus\u00e3o s\u00f3 \u00e9 v\u00e1lida
    se [n] e [m] forem o mesmo n\u00famero (i.e., [n = m]).
    
    A t\u00e1tica [intros] tamb\u00e9m permite mover para o
    contexto esta hip\u00f3tese. Em seguida, a t\u00e1tica
    [rewrite] para reescrever o objetivo da prova
    a partir da igualdade descrita na hip\u00f3tese.

    Por padr\u00e3o, a reescrita \u00e9 da esquerda para
    a direita: ->. Logo, pode-se omitir o ->.
    No entanto, da direita para a esquerda \u00e9
    necess\u00e1rio usar o s\u00edmbolo <-.

*)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move [n] e [m] para o contexto *)
  intros n m.
  (* move o antecedente da implica\u00e7\u00e3o
     para o contexto sob o nome "H" *)
  intros H.
  (* reescreve o objetivo usando "H" *)
  rewrite -> H.
  reflexivity.
Qed.

(** **** Exercise: (plus_id_exercise)  *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros J.
  rewrite -> H.
  rewrite <- J.
  reflexivity.
Qed.

(** Lembrando que o comando [Admitted] deve
    ser removido. Ele diz para aceitar,
    no momento, que a afirma\u00e7\u00e3o \u00e9 verdadeira.
    Permite focar nos argumentos principais,
    para depois voltar para as provas auxiliares.
    Contudo, \u00e9 preciso usar com cuidado
    para n\u00e3o introduzir afirma\u00e7\u00f5es falsas como
    verdadeiras *)

(** \u00c9 poss\u00edvel usar [rewrite] considerando
    teoremas previamente provados. Se a afirma\u00e7\u00e3o
    pr\u00e9via envolver vari\u00e1veis quantificadas,
    Coq tenta instanci\u00e1-las considerando
    o objetivo de prova atual *)

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  Search (0 + _).
  rewrite -> plus_O_n.
  reflexivity.
Qed.

(** O exemplo anterior ilustra o quanto
    o comando Search pode ser \u00fatil.
    Contudo, s\u00f3 funciona nos m\u00f3dulos
    "Required".

    Possibilidades de uso:
    - procura pelo nome: Search "len".
      compare com o resultado de Search len.
    - procura por id: Search False.
    - procura por padr\u00e3o: Search (0 + _).

    Outros comandos:
    - SearchPattern: somente na conclus\u00e3o
    - SearchRewrite: conclus\u00f5es _ = _
    
    Links:
    - https://quanttype.net/posts/2016-04-19-finding-that-lemma.html
    - https://coq.inria.fr/distrib/current/refman/proof-engine/vernacular-commands.html#coq:cmd.search  
*)

(** **** Exercise: (mult_S_1)  *)
(** Prove o seguinte teorema usando [rewrite] *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  (* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** * Prova por an\u00e1lise de casos *)

(** Nem tudo pode ser provado por simplifica\u00e7\u00e3o e
    reescrita. Veja o caso a seguir. O comando
    [Abort] permite abortar uma prova *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl. (* n\u00e3o faz nada! *)
Abort.

(** Tanto [beq_nat] como [+] faz casamento
    de padr\u00e3o com o primeiro argumento *)

Print beq_nat.
Print NatPlayground2.plus.

(** Aqui, o primeiro argumento de [+] \u00e9 [n];
    e de beq_nat, a express\u00e3o [n + 1].

    Para avan\u00e7ar, \u00e9 preciso considerar as
    poss\u00edveis formas de [n] *)

Print nat.

(** Um n\u00famero ou \u00e9 O (zero) ou o sucessor
    de outro n\u00famero. A t\u00e1tica [destruct]
    cria uma an\u00e1lise de casos.

    Observe que nesta prova, [0 + 1] pode
    ser simplificado, o que permite simplificar
    beq_nat. No outro caso, beq_nat (S _ + 1) 0
    tamb\u00e9m permite simplifica\u00e7\u00e3o pela forma
    que beq_nat foi definido.
*)

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [  | n' ].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** A t\u00e1tica [destruct] permite especificar
    um padr\u00e3o de introdu\u00e7\u00e3o (_intro pattern_)
    usando a anota\u00e7\u00e3o "[as [| n']]". Este
    padr\u00e3o \u00e9 opcional.

    O que vai entre [[]] \u00e9 uma lista de lista
    de nomes, separadas por |, cada lista
    informando o nome dos elementos a serem
    introduzidos.

    No caso de nat, o primeiro construtor n\u00e3o
    recebe argumentos; logo, a lista vazia. O
    segundo construtor recebe um natural,
    denotado por n'.

    O s\u00edmbolo [-] separa os casos (sub-objetivos
    de prova). A rigor, estes podem ser omitidos,
    e os comandos ir\u00e3o atuar nos sub-objetivos
    na ordem em que foram criados. No entanto,
    \u00e9 uma boa pr\u00e1tica usuar o s\u00edmbolo [-].
*)

Print negb.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(** A prova a seguir mostra sub-objetivos
    de prova dentro de outros sub-objetivos
    de prova. *)

Print andb.

Theorem andb_commutative : forall b c,
  andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

(** S\u00edmbolos: [-], [+] e [*]. Se for preciso
    mais hierarquia, usar [{}]. *)

Theorem andb_commutative' : forall b c,
  andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

(** \u00c9 poss\u00edvel combinar [intros] com [destruct].
    No exemplo a seguir, "intros [|n].", faz o mesmo
    que "intros x y. destruct y as [|y]." *)

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

(** Se n\u00e3o houver argumentos para o [destruct],
    deve-se usar [[]]. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** **** Exercise: (andb_true_elim2)  *)
(** Prova a seguinte afirma\u00e7\u00e3o usando [destruct] *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* COMPLETE AQUI *) Admitted.

(** **** Exercise: (zero_nbeq_plus_1)  *)
(** Prova a seguinte afirma\u00e7\u00e3o usando [destruct] *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* COMPLETE AQUI *) Admitted.

(* ############################################### *)
(** ** Fixpoints e recurs\u00e3o estrutural *)

(** Toda fun\u00e7\u00e3o em Coq precisa terminar. Para ter
    esta garantia, \u00e9 necess\u00e1rio ter uma recurs\u00e3o
    estrutural em elementos progressivamente
    "menores". Veja a fun\u00e7\u00e3o "plus". *)

Print NatPlayground2.plus.

Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

(** \u00c9 poss\u00edvel ter fun\u00e7\u00f5es que sempre
    terminam, mas que Coq n\u00e3o consegue
    perceber isto. *)

Fail Fixpoint f (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match evenb (S n') with
            | false => f (n'-1)
            | true  => f (n'+2)
            end
  end.

(** Uma alternativa neste caso *)

Fixpoint f'_aux (n : nat) : bool :=
  match n with
  | O => true
  | S n' => f'_aux (n'-1)
  end.

Fixpoint f' (n : nat) : bool :=
  match n with
  | O => true
  | S n' => match evenb (S n') with
            | false => f' (n'-1)
            | true => f'_aux (n'+2)
            end
  end.

(** Outra possibilidade. Qual a
    diferen\u00e7a? *)

Fixpoint f'' (n : nat) (qtd : nat) : bool :=
  match n, qtd with
  | O, _ => true
  | _, O => false
  | S n', S qtd' => match evenb (S n') with
                    | false => f'' (n'-1) qtd'
                    | true  => f'' (n'+2) qtd'
                    end
  end.

(** Entenda as diferen\u00e7as observadas
    a seguir. *)

Compute (f' 4).
Compute (f'' 4 4).
Compute (f'' 4 3).

(** O comportamento de [f] pode ser resumido assim:
    - Se [n] for zero, ent\u00e3o o retorno \u00e9 true.
    - Se [n] for \u00edmpar, ent\u00e3o chama recursivamente
      f' (n'-1). Se [n] \u00e9 \u00edmpar, ent\u00e3o [n'-1]
      tamb\u00e9m \u00e9 \u00edmpar, uma vez que [S n = n].
      Logo, todas as pr\u00f3ximas chamadas far\u00e1 [n'-1].
    - Se [n] for par, na primeira recurs\u00e3o
      chama [f] considerando [n'+2], que \u00e9 sempre
      \u00edmpar, uma vez que [S n = n] e [n] \u00e9 par.
      Logo, caindo no caso anterior.

    Veja alguns exemplos:
    - [n = 0]
      true
    - [n = 1]
      - [f (1-1) = f 0]
      - true
    - [n = 2]
      - [f (1+2) = f 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    - [n = 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    - [n = 4]
      - [f (3+2) = f 5]
      - [f (4-1) = f 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    - [n = 5]
      - [f (4-1) = f 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    - [n = 6]
      - [f (5+2) = f 7]
      - [f (6-1) = f 5]
      - [f (4-1) = f 3]
      - [f (2-1) = f 1]
      - [f (0-1) = f 0]
      - true
    ...      

    Em resumo:
    - [n = 0], 0 recurs\u00e3o
    - [n = 1], 1 recurs\u00e3o
    - [n = 2], 3 recurs\u00f5es
    - [n = 3], 2 recurs\u00f5es
    - [n = 4], 4 recurs\u00f5es
    - [n = 5], 3 recurs\u00f5es
    - [n = 6], 5 recurs\u00f5es
    
    0, 3, 4, 5, 6, 7, ... recurs\u00f5es
    0, 2, 4, 6, 8, 10, ... valor de [n] par
    recurs\u00f5es para n = n/2 + 2, quando n > 0
    recurs\u00f5es para n = 0, quando n = 0

    1, 2, 3, 4, 5, 6, ... recurs\u00f5es
    1, 3, 5, 7, 9, 11, ... valor de [n] \u00edmpar
    recurs\u00f5es para n = (n+1 / 2)

    Veja a pr\u00f3xima defini\u00e7\u00e3o de [f'''].
    Entenda em como esta difere de chamar
    diretamente [f''].
*)

Definition f'''_aux (n : nat) : nat :=
  match n with
  | 0     => 0
  | S n'  => match evenb n with
             | false  => (Nat.div (n+1) 2)
             | true   => (Nat.div n 2) + 2
             end
  end.

Definition f''' (n : nat) : bool :=
  f'' n (f'''_aux n).

Example f'''_test0 : f''' 0 = true.
Proof. reflexivity. Qed.
Example f'''_test1 : f''' 1 = true.
Proof. reflexivity. Qed.
Example f'''_test2 : f''' 2 = true.
Proof. reflexivity. Qed.
Example f'''_test3 : f''' 3 = true.
Proof. reflexivity. Qed.
Example f'''_test4 : f''' 4 = true.
Proof. reflexivity. Qed.
Example f'''_test5 : f''' 5 = true.
Proof. reflexivity. Qed.
Example f'''_test6 : f''' 6 = true.
Proof. reflexivity. Qed.
Example f'''_test7 : f''' 7 = true.
Proof. reflexivity. Qed.
Example f'''_test8 : f''' 8 = true.
Proof. reflexivity. Qed.
Example f'''_test9 : f''' 9 = true.
Proof. reflexivity. Qed.
Example f'''_test10 : f''' 10 = true.
Proof. reflexivity. Qed.

(* ############################################### *)
(** * Leitura sugerida *)

(** Software Foundations: volume 1
  - Aspectos b\u00e1sicos (at\u00e9 o final de "Data and Functions")
  https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
*)
