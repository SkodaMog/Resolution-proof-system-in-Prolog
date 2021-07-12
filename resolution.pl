/*
1. YES
2. YES
3. YES
4. NO
5. YES
6. YES
7. YES
8. NO
9. NO
10. YES
*/

/* Intended for SWI-Prolog.
Try:
clauseform(((x imp y) and x) imp y, Cnf).
clauseform(((x imp y) and (y imp z)) imp (neg neg z or neg x), Cnf).
clauseform((x imp (y imp z)) equiv ((x imp y) imp z), Cnf).
clauseform((x notequiv y) equiv (y notequiv x), Cnf).
*/

?-op(140, fy, neg).
?-op(160, xfy, [and, downarrow]).
?-op(180, xfy, [or, uparrow]).
?-op(200, xfy, [imp, revimp, notimp , notrevimp]).
?-op(220, xfy, [equiv, notequiv]).

/* conjunctive (X) :- X is an alpha formula. */
conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).

/* It is possible to treat equiv and notequiv as conjunctive. */
conjunctive(_ equiv _).
conjunctive(_ notequiv _).
conjunctive(neg (_ equiv _)).
conjunctive(neg (_ notequiv _)).

/* disjunctive (X) :- X is a beta formula. */
disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).

/* unary (X) :- X is a double negation, or a negated constant. */
unary(neg neg _).
unary(neg true).
unary(neg false).

/* components (X, Y, Z) :- Y and Z are the components of the formula X, as defined in the alpha and beta table. */
components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).

components(X equiv Y, X imp Y, X revimp Y).
components(neg (X equiv Y), X or Y, X uparrow Y).
components(X notequiv Y, X or Y, X uparrow Y).
components(neg (X notequiv Y), X imp Y, X revimp Y).

/* component(X, Y) :- Y is the component of the unary formula X. */
component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* singlestep(Old, New) :- New is the result of applying a single step of the expansion process to Old, which is a generalized conjunction of generalized disjunctions. */

singlestep([Disj | Rest], New) :- select(Formula, Disj, Temp),
	unary(Formula), component(Formula, NewFormula),
	New = [[NewFormula | Temp] | Rest].

singlestep([Disj | Rest], New) :- select(Beta, Disj, Temp),
	disjunctive(Beta), components(Beta, Beta1, Beta2),
	New = [[Beta1, Beta2 | Temp] | Rest].

singlestep([Disj | Rest], [Temp | Rest]) :- select(false, Disj, Temp).

singlestep([Disj | Rest], New) :- select(Alpha, Disj, Temp),
	conjunctive(Alpha), components(Alpha, Alpha1, Alpha2),
	New = [[Alpha1 | Temp], [Alpha2 | Temp] | Rest].

singlestep([Disj | Rest], Rest) :- select(true, Disj, _).

singlestep([Disj | Rest], [Disj | NewRest]) :- singlestep(Rest, NewRest).

/* expand(Old, New) :- New is the result of applying singlestep as many times as possible, starting with Old. */
expand(Formula, NewFormula) :- singlestep(Formula, Temp), expand(Temp, NewFormula).
expand(Formula, Formula).

/* clauseform(X, Y) :- Y is the conjunctive normal form of X. */
clauseform(X, Y) :- expand([[X]], Y).

/* is_opp(X, Y) :- one of X or Y is a negation of another. */
is_opp(X, neg X).
is_opp(neg X, X).

/* true_clause(Disj) :- Disj contains two formulas one of which is a negation of another, hence Disj is always true. */
true_clause(Disj) :- member(X, Disj), is_opp(X, Y), member(Y, Disj).

/* cnf_ord(Conj, NewConj) :- NewConj is a CNF obtained from a CNF Conj by removing all elements satisfying true_clause and converting each element into an ordered set. */
cnf_ord([Disj | Rest], New) :- list_to_ord_set(Disj, OrdDisj),
	(true_clause(OrdDisj), !, New = NewRest; New = [OrdDisj | NewRest]),
	cnf_ord(Rest, NewRest).
cnf_ord([], []).

/* closed(Conj) :- Conj contains an empty clause, hence it is closed. */
closed(Conj) :- member([], Conj).

/* resolution_rule(Disj1, Disj2, NewDisj) :- NewDisj is the resolvent of Disj1 and Disj2. */
resolution_rule(Disj1, Disj2, NewDisj) :- select(Literal, Disj1, NewDisj1),
	select(neg Literal, Disj2, NewDisj2),
	ord_union(NewDisj1, NewDisj2, NewDisj).

/* resolutionstep(Conj, NewConj) :- NewConj is Conj with a resolvent added. */
resolutionstep(Conj, NewConj) :- member(Disj1, Conj), member(Disj2, Conj),
	resolution_rule(Disj1, Disj2, NewDisj),
	\+ true_clause(NewDisj), \+ member(NewDisj, Conj), NewConj = [NewDisj | Conj].

resolution(Conj, NewConj) :- resolutionstep(Conj, Temp), resolution(Temp, NewConj).
resolution(Conj, Conj).

test(Formula) :- clauseform(neg Formula, Conj),
	cnf_ord(Conj, NewConj), list_to_ord_set(NewConj, OrdConj),
	resolution(OrdConj, FinalConj), !,
	(closed(FinalConj), !, write('YES'); write('NO')), nl.
