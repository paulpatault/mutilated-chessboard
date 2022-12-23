## Mutilated Chessboard

Projet du cours de preuves Coq ([lien](https://master.math.univ-paris-diderot.fr/modules/m2lmfi-preuveform/))
du master [LMFI](https://master.math.univ-paris-diderot.fr/annee/m2-lmfi/).

### Problème

Résoudre le problème de pavage avec des dominos `2x1` d'un échiquier `8x8` amputé de deux coins opposés.
Le problème est insoluble, le fichier Coq en donne une preuve.

### Formalisation

L'échiquer est représenté par un ensemble de cases :
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
- todo suite


### Ensemble des hypothèses

- hypothèses relative a l'ensemble représenté par une liste
- on fait aussi l'hypothèse que lorsque l'on pose un domino, celui peut être posé : il ne va pas dans le vide


### TODO

- [x] lemme `in_simp`
- [x] lemme `invariant_noir`
- [ ] finir formalisation du problème général (après invariant : établir la contradiction)
