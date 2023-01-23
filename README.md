## Mutilated Chessboard

Projet du cours de preuves Coq ([lien](https://master.math.univ-paris-diderot.fr/modules/m2lmfi-preuveform/))
du master [LMFI](https://master.math.univ-paris-diderot.fr/annee/m2-lmfi/).

### Compilation
```bash
$ make _CoqProject
$ make -j4
```
### Problème

Peut-on paver avec des dominos `2x1` un échiquier `8x8` amputé de deux coins opposés.
Non ! Le problème est insoluble, le fichier Coq en donne une preuve.

### Formalisation

L'échiquer est représenté par une liste de cases :
- les cases sont des records contenant deux entiers `x` et `y` : coordonnées de la case.
- l'ensemble est représenté par une liste sur laquelle on fait l'hypothèse que chaque élément qui s'y trouve est unique.
- les dominos seront posés soit en `Hauteur` soit en `Largeur` à partir d'une case donnée par ses coordonnées.
- chaque case a une couleur en fonction de la partité de la somme des ses coordonnées. (comme sur un échiquier classique)
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
    exists dl : list domino, solution p dl /\ disjoints_dominos_lo dl.
  ```
- Notations
  * `l \ e` : on retire `e` de la liste `l`
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

<!-- ### Ensemble des hypothèses

- hypothèses relative a l'ensemble représenté par une liste
- on fait aussi l'hypothèse que lorsque l'on pose un domino, celui-ci peut être posé : il ne va pas dans le vide -->

### TODO

- expliquer les notations
- finir la preuve : il reste encore 3 `admit`
- ajouter une notation `pose_domino d p = "d / p"` : `d` écrase `p` ?
