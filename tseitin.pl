%%%%%%%%%%%%%%%%%%%%%%%%%%
% TSEITIN TRANSFORMATION %
%%%%%%%%%%%%%%%%%%%%%%%%%%

% HOW IT WORKS...
%
%
%
%
%
% Basically no preprocessing on the clause list is done. It simplifies repeated literals in a clause.

:- use_module(library(apply)).

% DYNAMIC PREDICATES:

:- dynamic nameOfFormula/2.
:- dynamic counter/1.
:- dynamic zFormula/1.
:- dynamic tFormula/1.
:- dynamic tseitin_list/1.
:- dynamic clause_list/1.

% LOGICAL OPERATORS:

:- op( 100, fy, ~ ).
:- op( 110, xfy, & ).
:- op( 120, xfy, v ).
:- op( 130, xfy, => ).
:- op( 140, xfy, <=>).

% isPermutation/2 checks if ListX is permutation of ListY

isPermutation(ListX,ListY) 
	:- msort(ListX,ListZ), msort(ListY,ListZ).

% isTaut/1 checks if clause is tautology

is_Taut([]) 
	:- fail,!.
is_Taut([~X|L]) 
	:- member(X,L),!.
is_Taut([X|L]) 
	:- member(~X,L),!.
is_Taut([_|L])
	:- is_Taut(L).

% zFormula/1 is satisfied by an atom which will be used to name formulas in the renaming.

% counter/1, increaseCounter/0 and increaseZFormula/0 are used to
% generate new atoms for zFormula/1, so that every subformula is associated with a different name.

counter(0).

zFormula(z0).

increaseCounter() 
	:- counter(X), Y is X+1, retractall(counter(_)), assert(counter(Y)).

increaseZFormula() 
	:- increaseCounter(), retractall(zFormula(_)), counter(X), atomic_list_concat([z, X], Y), assert(zFormula(Y)).

% tseitin_list/1 is satisfied by a list of tseitin formulas.

tseitin_list([]).

% clause_list/1 is satisfied by a list of clauses.

clause_list([[z0]]).

% nameSubFormulas/1
% Associates a name (which is a variable) to (for?) every nonatomic subformula of a formula.

nameSubFormulas(~X) 
	:- zFormula(Z), assert(nameOfFormula(~X, Z)), increaseZFormula, nameSubFormulas(X), !.
nameSubFormulas(X & Y) 
	:- zFormula(Z), assert(nameOfFormula(X & Y, Z)), increaseZFormula, nameSubFormulas(X), nameSubFormulas(Y), !.
nameSubFormulas(X v Y) 
	:- zFormula(Z), assert(nameOfFormula(X v Y, Z)), increaseZFormula, nameSubFormulas(X), nameSubFormulas(Y), !.
nameSubFormulas(X => Y) 
	:- zFormula(Z), assert(nameOfFormula(X => Y, Z)), increaseZFormula, nameSubFormulas(X), nameSubFormulas(Y), !.
nameSubFormulas(X <=> Y) 
	:- zFormula(Z), assert(nameOfFormula(X <=> Y, Z)), increaseZFormula, nameSubFormulas(X), nameSubFormulas(Y), !.
nameSubFormulas(X) 
	:- assert(nameOfFormula(X,X)), !.

% assert_tseitin/1
% 

assert_tseitin(~X) 
	:- nameOfFormula(~X, Z), nameOfFormula(X, Z0), tseitin_list(T_List), retractall(tseitin_list(_)), append(T_List, [Z <=> ~(Z0)], New_T_List), assert(tseitin_list(New_T_List)), assert_tseitin(X), !.

assert_tseitin(X & Y) 
	:- nameOfFormula(X & Y, Z), nameOfFormula(X, Z1), nameOfFormula(Y, Z2), tseitin_list(T_List), retractall(tseitin_list(_)), append(T_List, [Z <=> (Z1 & Z2)], New_T_List), assert(tseitin_list(New_T_List)), assert_tseitin(X), assert_tseitin(Y), !.

assert_tseitin(X v Y) 
	:- nameOfFormula(X v Y, Z), nameOfFormula(X, Z1), nameOfFormula(Y, Z2), tseitin_list(T_List), retractall(tseitin_list(_)), append(T_List, [Z <=> (Z1 v Z2)], New_T_List), assert(tseitin_list(New_T_List)), assert_tseitin(X), assert_tseitin(Y), !.

assert_tseitin(X => Y) 
	:- nameOfFormula(X => Y, Z), nameOfFormula(X, Z1), nameOfFormula(Y, Z2), tseitin_list(T_List), retractall(tseitin_list(_)), append(T_List, [Z <=> (Z1 => Z2)], New_T_List), assert(tseitin_list(New_T_List)), assert_tseitin(X), assert_tseitin(Y), !.

assert_tseitin(X <=> Y) 
	:- nameOfFormula(X <=> Y, Z), nameOfFormula(X, Z1), nameOfFormula(Y, Z2), tseitin_list(T_List), retractall(tseitin_list(_)), append(T_List, [Z <=> (Z1 <=> Z2)], New_T_List), assert(tseitin_list(New_T_List)), assert_tseitin(X), assert_tseitin(Y), !.

assert_tseitin(_) 
	:- !.

%  tseitin_to_cnf/2 is self-explanatory.

tseitin_to_cnf(X <=> ~Y, CNF) 
	:- CNF = [[~X, ~Y], [X, Y]].
tseitin_to_cnf(X <=> (Y & Z), CNF) 
	:- CNF = [[Y, ~X],[Z, ~X],[X,~Y,~Z]].
tseitin_to_cnf(X <=> (Y v Z), CNF) 
	:- CNF = [[Y, Z, ~X],[X,~Y],[X,~Z]].
tseitin_to_cnf(X <=> (Y => Z), CNF) 
	:- CNF = [[~Y, Z, ~X],[X,Y],[X,~Z]].
tseitin_to_cnf(X <=> (Y <=> Z), CNF) 
	:- CNF = [[Z,~X,~Y],[Y,~X,~Z],[X,Y,Z],[X,~Y,~Z]].

% returns true if clause is not a tautology and hasn't been asserted yet.

validate_clause(X) 
	:- is_Taut(X), !, fail.

validate_clause(X) 
	:- clause_list(C_List), member(Y, C_List), isPermutation(X, Y), !, fail.

validate_clause(X) :- is_list(X).

% clausify_cnf/1
% takes a cnf (which is a list, such as [ [p,q], [~p] ]) and puts each simplified and validated clause in the clause_list.

clausify_cnf([X|Y]) 
	:- list_to_set(X, X_set), (validate_clause(X_set) -> clause_list(C_List), retractall(clause_list(_)), append(C_List, [X_set], New_C_List), assert(clause_list(New_C_List)), clausify_cnf(Y) ; clausify_cnf(Y)).

clausify_cnf([]).

% clausify_tseitin_list
% applies clausify_cnf to the cnf of a tseitin formula

clausify_tseitin_list([X|Y]) 
	:- tseitin_to_cnf(X, X_cnf), clausify_cnf(X_cnf), clausify_tseitin_list(Y).

clausify_tseitin_list([]).

% clausify/1 
% generates a list of tseitin formulas and then transforms it into CNF.

clausify(X) :- nameSubFormulas(X), assert_tseitin(X), tseitin_list(T_List), clausify_tseitin_list(T_List).

%%%%%%%%%%%%%
% TEST AREA %
%%%%%%%%%%%%%

reset() :- 
	retractall( nameOfFormula(_,_) ),
	retractall( counter(_) ),
	retractall( zFormula(_) ),
	retractall( tseitin_list(_) ),
	retractall( clause_list(_) ),


	assert( counter(0) ), 
	assert( zFormula(z0) ),
	assert( tseitin_list([]) ),
	assert( clause_list([]) ).

% testando geração de tFormulas


teste(X) :- nameSubFormulas((p&q) => ~(q v r)), assertTFormulas((p&q) => ~(q v r)), tFormula(X).
teste2(X) :- nameSubFormulas( ~( (p v s) <=> (k & ~m) ) ), assertTFormulas( ~( (p v s) <=> (k & ~m) ) ), tFormula(X).
teste3(X) :- nameSubFormulas( ((p v q) & r) => (~s) ), assertTFormulas( ((p v q) & r) => (~s) ), tFormula(X).
teste4(X) :- nameSubFormulas( ~(~q) ), assertTFormulas( ~(~q) ), tFormula(X).
teste5(X) :- nameSubFormulas( p <=> (q <=> r) ), assertTFormulas( p <=> (q <=>r) ), tFormula(X).

% tseitin_to_cnf/2

teste6(X) :- tseitin_to_cnf( p <=> q <=> r, X).
teste7(X) :- tseitin_to_cnf( x2 <=> p v q, X).

% assert_tseitin

teste8(X) :- nameSubFormulas( p <=> (q <=> r) ), assert_tseitin( p <=> (q <=>r) ), tseitin_list(X).

% validate_clause

testevc(X) :- validate_clause(X).

