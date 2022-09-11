
% FILE:         loading.pl
% AUTHOR:       Robert Craven [robert.craven@imperial.ac.uk]
% LANGUAGE:     Prolog
% DATE:         11/5/2014

loadf(FileStem) :-
 preloading,
 filename(FileStem, FileName),
 assert(filestem(FileStem)),
 open(FileName, read, Fd),
 repeat,
  read(Fd, Term),
  process_fail(Term),
 !,
 close(Fd),
 postloading.

preloading :-
 user_predicate(Func, Arity),
 abolish(Func, Arity),
 fail.
preloading :-
 retractall(assumption(_)),
 retractall(branching(_,_)),
 retractall(contrary(_,_)),
 retractall(filestem(_)),
 retractall(generation_settings(_)),
 retractall(non_assumption(_)),
 retractall(proving(_)),
 retractall(rule(_,_)),
 retractall(sols(_)),
 retractall(toBeProved(_)),
 retractall(user_predicate(_,_)).

filename(FileStem, DirAndFileName) :-
 option(frameworkdir, Dir),
 atom_concat(FileStem, '.pl', FileName),
 atom_concat(Dir, FileName, DirAndFileName).

process_fail(end_of_file) :-
 !.
process_fail(:-(Body)) :-
 !,
 call(Body),
 fail.
process_fail(:-(Head, Body)) :-
 !,
 (
  input_predicate(Head, StoreHead)
  -> assert(:-(StoreHead,Body))
  ;  conj_list(Body, BodyList),
     assert(:-(rule(Head, BodyList),true))
 ),
 fail.
process_fail(Head) :-
 process_fail(:-(Head,true)).

input_predicate(:(A,S), contrary(A,S)).
input_predicate(assumption(X), assumption(X)).
input_predicate(contrary(A,S), contrary(A,S)).
input_predicate(generation_settings(X), generation_settings(X)).
input_predicate(myAsm(A), assumption(A)).
input_predicate(myRule(H,B), rule(H,B)).
input_predicate(rule(H,B), rule(H,B)).
input_predicate(toBeProved(TBP), toBeProved(TBP)).

conj_list(true, L) :-
 var(L),
 !,
 L = [].
conj_list(C, []) :-
 var(C),
 !,
 C = true.
conj_list((X,Y), [X|ListY]) :-
 !,
 conj_list(Y, ListY).
conj_list(X, [X]).

postloading :-
 add_assumptions,
 non_assumptions,
 check_input,
 branchings.

add_assumptions :-
 contrary(A, _),
 \+ assumption(A),
 assert(assumption(A)),
 fail.
add_assumptions.

non_assumptions :-
 findall(S, ((
              rule(H, Body),
              member(S, [H|Body])
              ;
              contrary(_, S)
             ),
             \+ assumption(S)
            ),
          NonAssumptions),
 list_to_ord_set(NonAssumptions, O_NonAssumptions),
 member(S, O_NonAssumptions),
 (
  non_assumption(S)
  -> true
  ;  assert(non_assumption(S))
 ),
 fail.
non_assumptions.

% checks are:
%  - every assumption has a contrary
%  - no assumption is head of a rule
%  - every contrary is of an assumption
%  - there is at least one assumption
check_input :-
 findall(A, assumption(A), Asms),
 findall(A, (assumption(A), \+ contrary(A, _)), As),
 findall((S,C), (contrary(S,C), \+ assumption(S)), ContPairs),
 findall(A, (rule(A, _), assumption(A)), Hs),
 list_to_ord_set(As, O_As),
 list_to_ord_set(Hs, O_Hs),
 list_to_ord_set(ContPairs, O_ContPairs),
 (
  Asms = [],
  format('ERROR: no assumptions~n', []),
  fail
  ;
  member(A, O_As),
  format('ERROR: ~w declared an assumption without contrary~n', [A]),
  fail
  ;
  member((S,C), O_ContPairs),
  format('ERROR: ~w declared as contrary of ~w, which is not an assumption~n', [C,S]),
  fail
  ;
  member(A, O_Hs),
  format('ERROR: ~w head of a rule but declared an assumption~n', [A]),
  fail
 ).
check_input :-
 flush_output.

