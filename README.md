# SAT-solver-project
SAT solver to substitute my previous one as a personal tool. Probably always a WORK IN PROGRESS.
It uses tseitin encoding to transform propositional formulas to CNFs.
It will soon use DPLL, CDCL (and more!) as decision algorithms to decide satisfiability of formulas.

HOW TO USE tseitin.pl

the query '? - clausify(X)' will transform the propositional formula X in CNF through tseitin encoding.
Formulas can be defined with logical operators &, v, ~, => and <=>.
To see the clauses, ask '? - clause_list(X)'.
