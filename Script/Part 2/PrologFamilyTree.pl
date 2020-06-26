male(philip).
male(charles).
male(andrew).
male(william).
male(harry).
male(george).
male(louis).
male(harrison).
male(mark_phillips).
male(timothy_laurence).
male(edward).
male(peter_phillips).
male(mike_tindall).
male(james).

female(elizabeth_II).
female(diana).
female(camilla).
female(sarah_ferguson).
female(kate_middleton).
female(meghan_markle).
female(eugenie).
female(beatrice).
female(charlotte).
female(anne).
female(sophie_rhys-jones).
female(autumn_phillips).
female(zara_tindall).
female(lady_louise_windsor).

parent(philip, charles).
parent(elizabeth_II, charles).
parent(philip, anne).
parent(elizabeth_II, anne).
parent(philip, edward).
parent(elizabeth_II, edward).
parent(philip, andrew).
parent(elizabeth_II, andrew).

parent(charles, william).
parent(diana, william).
parent(charles, harry).
parent(diana, harry).

parent(william, george).
parent(kate_middleton, george).
parent(william, charlotte).
parent(kate_middleton, charlotte).
parent(william, louis).
parent(kate_middleton, louis).

parent(harry, harrison).
parent(meghan_markle, harrison).

parent(mark_phillips, peter_phillips).
parent(anne, peter_phillips).
parent(mark_phillips, zara_tindall).
parent(anne, zara_tindall).

parent(edward, lady_louise_windsor).
parent(sophie_rhys-jones, lady_louise_lindsor).
parent(edward, james).
parent(sophie_rhys-jones, james).

parent(andrew, eugenie).
parent(sarah_ferguson, eugenie).
parent(andrew, beatrice).
parent(sarah_ferguson, beatrice).

married(philip, elizabeth_II).
married(elizabeth_II, philip).

married(charles, camilla).
married(camilla, charles).

married(andrew, sarah_ferguson).
married(sarah_ferguson, andrew).

married(william, kate_middleton).
married(kate_middleton, william).

married(harry, meghan_markle).
married(meghan_markle, harry).

married(timothy_laurence, anne).
married(anne, timothy_laurence).

married(edward, sophie_rhys-jones).
married(sophie_rhys-jones, edward).

married(peter_phillips, autumn_phillips).
married(autumn_phillips, peter_phillips).

married(mike_tindall, zara_tindall).
married(zara_tindall, mike_tindall).

divorced(charles, diana).
divorced(diana, charles).

divorced(mark_phillips, anne).
divorced(anne, mark_phillips).

% Rules
husband(Person, Wife):-
    male(Person),
    married(Person, Wife).

wife(Person, Husband):-
    female(Person),
    married(Person, Husband).

father(Parent, Child):-
    male(Parent),
    parent(Parent, Child).

mother(Parent, Child):-
    female(Parent),
    parent(Parent, Child).

child(Child, Parent):-
    parent(Parent, Child).

son(Child, Parent):-
    male(Child),
    parent(Parent, Child).

daughter(Child, Parent):-
    female(Child),
    parent(Parent, Child).

grandparent(GP, GC):-
    parent(GP,Parent),
    parent(Parent, GC).

grandmother(GM, GC):-
    female(GM),
    grandparent(GM, GC).

grandfather(GF, GC):-
    male(GF),
    grandparent(GF, GC).

grandchild(GC, GP):-
    grandparent(GP, GC).

grandson(GS, GP):-
    male(GS),
    grandparent(GP, GS).

granddaughter(GD, GP):-
    female(GD),
    grandparent(GP, GD).

sibling(Person, Sibling):-
    father(Parent, Person),
    father(Parent, Sibling),
    Person \= Sibling.

brother(Person, Sibling):-
    male(Person),
    sibling(Person, Sibling).

sister(Person, Sibling):-
    female(Person),
    sibling(Person, Sibling).

aunt(Person, NieceNephew):-
    female(Person)
    ,
      (parent(P_NieceNephew, NieceNephew)
       ;
       (married(Y, NieceNephew),
        parent(P_NieceNephew, Y)))
    ,
      (sibling(Person, P_NieceNephew)
       ;
       (sibling(Z, P_NieceNephew),
        married(Z, Person))).


uncle(Person, NieceNephew):-
    male(Person)
    ,
      (parent(P_NieceNephew, NieceNephew)
       ;
       (married(Y, NieceNephew),
        parent(P_NieceNephew, Y)))
    ,
      (sibling(Person, P_NieceNephew)
       ;
       (sibling(Z, P_NieceNephew),
        married(Z, Person))).

niece(Person, AuntUncle):-
    female(Person)
    ,
      (parent(P_Person, Person)
       ;
       (married(Y, Person),
        parent(P_Person, Y)))
    ,
      (sibling(P_Person, AuntUncle)
       ;
       (sibling(Z, P_Person),
        married(Z, AuntUncle))).

nephew(Person, AuntUncle):-
    male(Person)
    ,
      (parent(P_Person, Person)
       ;
       (married(Y, Person),
        parent(P_Person, Y)))
    ,
      (sibling(P_Person, AuntUncle)
       ;
       (sibling(Z, P_Person),
        married(Z, AuntUncle))).
