
:- use_module(library(random)).

random_strategy([TC,OSJ,PS,OS,PR]) :-
 random_choose_heuristic(turn_choice, TC),
 random_choose_heuristic(opponent_sj, OSJ),
 random_choose_heuristic(sentence, PS),
 random_choose_heuristic(sentence, OS),
 random_choose_heuristic(prop_rule, PR).

rand_strategy(St) :-
 findall(S, strategy(S), Strats),
 random_permutation(Strats, R_Strats),
 !,
 member(St, R_Strats).

strategy([TC,OSJ,PS,OS,PR]) :-
 choose_heuristic(turn_choice, TC),
 choose_heuristic(opponent_sj, OSJ),
 choose_heuristic(sentence, PS),
 choose_heuristic(sentence, OS),
 choose_heuristic(prop_rule, PR).

random_choose_heuristic(Type, Choice) :-
 choices(Type, Choices),
 random_member(Choice, Choices).

choose_heuristic(Type, Choice) :-
 choices(Type, Choices),
 member(Choice, Choices).

choices(turn_choice, [p,o,s]).
choices(opponent_sj, [n,o,s,l,lmb]).
choices(sentence,    [n,o,e,p,be,bp]).
choices(prop_rule,   [s,l1]).


