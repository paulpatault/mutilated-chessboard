## Mutilated Chessboard

Projet du cours de preuves Coq ([lien](https://master.math.univ-paris-diderot.fr/modules/m2lmfi-preuveform/))
du master [LMFI](https://master.math.univ-paris-diderot.fr/annee/m2-lmfi/).

### Problème

- Question : Peut-on paver avec des dominos `2x1` un échiquier `8x8` amputé de deux coins opposés ?
- Réponse : Non c'est impossible !

## Sommaire du README

- [Problème](https://github.com/paulpatault/mutilated-chessboard#Problème)
- [Compilation](https://github.com/paulpatault/mutilated-chessboard#Compilation)
- [Organisation des fichiers](https://github.com/paulpatault/mutilated-chessboard#Organisation-des-fichiers)
- [Formalisation](https://github.com/paulpatault/mutilated-chessboard#Formalisation)
- [Lemmes importants](https://github.com/paulpatault/mutilated-chessboard#Lemmes-importants)
- [Définitions](https://github.com/paulpatault/mutilated-chessboard#Definitions)
- [Résultat principal](https://github.com/paulpatault/mutilated-chessboard#Résultat-principal)
- [Améliorations possibles](https://github.com/paulpatault/mutilated-chessboard#Améliorations-possibles)

### Compilation
```bash
$ make _CoqProject
$ make -j4
```

### Organisation des fichiers

Dans l'ordre de compilation :

- [Arith aux](./src/Arith_aux.v) : lemme arithmétique
- [Domino](./src/Domino.v) : définitions principales pour la formalisation du problème
- [Disjoint](./src/Disjoint.v) : définitions et lemmes relatifs à la propriété `disjoints`
- [WF](./src/WF.v) : définitions et lemmes relatifs à la propriété `well_formed`
- [Resoluble](./src/Resoluble.v) : définitions de ce qu'est qu'être `résoluble`
- [Lemmas](./src/Lemmas.v) : lemmes utiles pour prouver le théorème final
- [Main](./src/Main.v) : énoncé principal


### Formalisation

L'échiquer est représenté par une liste de cases :
- les cases sont des records contenant deux entiers `x` et `y` : coordonnées de la case
- l'ensemble est représenté par une liste
- les dominos seront posés soit en `Hauteur` soit en `Largeur` à partir d'une case donnée par ses coordonnées
- chaque case a une couleur en fonction de la partité de la somme des ses coordonnées (comme sur un échiquier normal)
- lorsque l'on pose un domino, on retire de notre ensemble de case les cases prises par le domino :
  (par exemple si l'on avait l'ensemble `[(0,0);(0,1);(0,7);(1,7)]` et que l'on pose le domino `Hauteur(0,0)`, 
   on obtiendrait l'ensemble `[(0,7); (1,7)]`)

### Lemmes importants

- étant données une couleur `col`, une case `a` et un état `p`, si `a ∈ p` alors le nombre de cases de couleurs
  `couleur(a)` diminue de 1 quand on retire `a` de `p` :
  ```coq
   Lemma retire_case (col : couleur) (a : coord) (p: plateau) :
     couleur_case col a ->
     List.In a p ->
     card col (p \ a) + 1 = card col p.
    ```
- si `p'` est le plateau `p` sur lequel on a posé le domino `d`, alors
  `p` a exactement une case noire (et une case blanche) de plus que `p'` :
  ```coq
  Lemma invariant : forall p p': plateau, forall d: domino,
    p' = pose_domino d p ->
    card Blanc p = card Blanc p' + 1 /\
    card Noir p  = card Noir  p' + 1.
  ```
- généralisation du lemme précédent aux liste de dominos
  ```coq
  Lemma invariant_extended_to_dominolist : forall p p': plateau, forall dl: list domino,
    pose_dominos dl p = p' ->
    card Blanc p = card Blanc p' + (List.length dl) /\
    card Noir p = card Noir p' + (List.length dl).
  ```

### Definitions

- `plateau_base` : échiquier 8x8 classique
- `plateau_coupé` : `plateau_base` duquel on a retiré les cases {0;0} et {7;7} (une paire de coins opposés)

- `solution p dl` : `dl` est une solution de `p` si en posant chaque domino de `dl` on arrive a un plateau vide
  ```coq
  Definition solution (p : plateau) (dl : list domino) :=
    pose_dominos dl p = [].
  ```
- `well_formed p` : `p` est bien formé si il ne contient pas de doublon
  ```coq
  Fixpoint well_formed (p : plateau) :=
    match p with
    | [] => True
    | hd::tl => List.count_occ eq_coord p hd = 1 /\ well_formed tl
    end.
  ```
- `resoluble p` : `p` est résoluble s'il existe une solution
  ```coq
  Definition resoluble (p : plateau) :=
    well_formed p /\
    exists dl : list domino, solution p dl /\ disjoints_dominos dl.
  ```
- Notations
  * `l \ e` : on retire `e` de la liste `l`
  * `d // p` : raccourci pour `pose_domino d p`
  * `d1 # d2` : les dominos `d1` et `d2` couvrent des cases différentes (ils sont « disjoints »)
  * `d ## dl` : signifie `∀ di ∈ dl, d # di`


### Résultat principal

- théorème : si on peut résourde `p` alors `p` contient autant de cases noires de que cases blanches
  ```coq
  Theorem resoluble_invariant : forall p, resoluble p -> card Noir p = card Blanc p.
  ```

- corrolaire du théorème : le problème initial !
  on a bien montré qu'on ne peut pas paver avec des dominos 2x1 un plateau d'échec duquel on aurait retiré deux coins opposés
  ```coq
  Corollary mutilated_board : ~ resoluble plateau_coupé.
  ```

- on peut aussi prouver assez simplement qu'un plateau d'échecs classique est résoluble
  ```coq
  Theorem classic_board_resoluble : resoluble plateau_base.
  ```

### Améliorations possibles

- finir la preuve dans `./src/WF.v`
- simplifier le modèle du plateau pour améliorer la preuve : utiliser un bibliothèque d'ensemble de la stdlib
- simplifier certaines preuves qui sont longues et répétitives (notament dans `./src/Lemmas.v`)
