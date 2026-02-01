% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

% mmc --grade hlc.gc --make abagraph && ./abagraph.exe

:- module abagraph.
:- interface.

:- import_module constraints.
:- import_module digraph.
:- import_module int.
:- import_module list.
% Import sentence from loading.
:- import_module loading.
:- import_module map.
:- import_module pair.
:- import_module set.

:- type graph_member == pair(sentence, list(sentence)).

:- type pot_arg_graph == pair(pair(list(sentence),     % Unmarked
                                   set(sentence)),     % Marked
                                   digraph(sentence)). % Graph

:- type focussed_pot_arg_graph == pair(pair(sentence,       % Claim
                                            int),           % GId graph ID
                                            pot_arg_graph). % Potential arg graph

:- type opponent_arg_graph_set == pair(list(focussed_pot_arg_graph), % OppUnMrk
                                       set(focussed_pot_arg_graph)). % OppMrk

:- type attack == pair(sentence).

:- type step_tuple
   ---> step_tuple(pot_arg_graph,          % PROPONENT potential argument graph
                   opponent_arg_graph_set, % Opponent argument graph set
                   set(sentence),          % D (the proponent defences)
                   pair(set(sentence), map(sentence, int)), % C = Culprits-CulpritIds (the opponent culprits plus Ids (only for printing))
                   set(attack),            % Att (set of attacks, used only for printing)
                   constraint_store).       % Constraint store

:- type opponent_step_tuple
   ---> opponent_step_tuple(pot_arg_graph,          % PROPONENT potential argument graph
                            set(sentence),          % D (the proponent defences)
                            pair(set(sentence), map(sentence, int)), % C = Culprits-CulpritIds (the opponent culprits plus Ids (only for printing))
                            set(attack),            % Att
                            constraint_store).      % CS

:- type derivation_result
   ---> derivation_result(pair(set(sentence), digraph(sentence)), % PropMrk-PropG
                          set(focussed_pot_arg_graph),            % OppMrk
                          set(sentence),                          % D (the proponent defences)
                          set(sentence),                          % C (the opponent culprits)
                          set(attack),                            % Att
                          constraint_store).                      % CS

% N-Map where N is the step number (for runtime_out) and map is 
% GId -> (Map of Sentence -> SentenceId) for write_sentence/5.
:- type id_map == pair(int, map(int, map(sentence, int))).

% step_and_id_map(StepTuple, Ids, RuntimeOut).
% Print RuntimeOut to runtime_out_path before calling derivation_step again with the StepTuple.
:- type step_and_id_map ---> step_and_id_map(step_tuple, id_map, string).

% derive(S, MaxResults) = Results.
:- func derive(sentence, int) = list(derivation_result) is det.

% Get the initial list of solutions for the sentence.
:- func initial_solutions(sentence) = list(step_and_id_map) is det.

% proponent_step(S, StepAndIdMap) = Solutions.
% S should be a sentence in PropUnMrk in StepAndIdMap.
:- func proponent_step(sentence, step_and_id_map) = list(step_and_id_map) is det.

% opponent_step(OppArg, StepAndIdMap) = Solutions.
% OppArg should be a sentence in OppUnMrk in StepAndIdMap.
:- func opponent_step(focussed_pot_arg_graph, step_and_id_map) = list(step_and_id_map) is det.

:- implementation.

:- import_module bool.
:- import_module float.
:- import_module maybe.
:- import_module options.
:- import_module printing.
:- import_module require.
:- import_module solutions.
:- import_module string.

:- type turn
        ---> proponent
        ;    opponent.

:- type prop_info
   ---> prop_info(set(sentence), digraph(sentence)).

:- pred initial_derivation_tuple(set(sentence)::in, step_tuple::out) is det.
:- func derivation(list(step_and_id_map), list(derivation_result), sentence, int) = list(derivation_result) is det.
:- func derivation_step(step_and_id_map) = list(step_and_id_map) is det.
:- func step_runtime_out(set(sentence), pair(set(sentence), map(sentence, int)), constraint_store, id_map) = string is det.
:- func prepend_runtime_out(list(step_and_id_map), string) = list(step_and_id_map) is det.
:- pred proponent_asm(sentence::in, list(sentence)::in, pair(set(sentence), digraph(sentence))::in,
          opponent_arg_graph_set::in, set(sentence)::in, pair(set(sentence), map(sentence, int))::in,
          set(attack)::in, constraint_store::in, id_map::in, step_and_id_map::out) is semidet.
:- pred proponent_nonasm(sentence::in, list(sentence)::in, pair(set(sentence), digraph(sentence))::in,
          opponent_arg_graph_set::in, set(sentence)::in, pair(set(sentence), map(sentence, int))::in,
          set(attack)::in, constraint_store::in, id_map::in, step_and_id_map::out) is nondet.
:- pred opponent_i(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, id_map::in, step_and_id_map::out) is nondet.
:- pred opponent_ia(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, id_map::in, step_and_id_map::out) is semidet.
:- pred opponent_ib(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, id_map::in, step_and_id_map::out) is det.
:- pred opponent_ic(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, id_map::in, step_and_id_map::out) is semidet.
:- pred opponent_ii(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, id_map::in, step_and_id_map::out) is nondet.
:- pred iterate_bodies(list(list(sentence))::in, pair(sentence, int)::in, focussed_pot_arg_graph::in,
          opponent_arg_graph_set::in, pair(set(sentence), map(sentence, int))::in, constraint_store::in,
          constraint_store::out, opponent_arg_graph_set::out, id_map::in, string::in, id_map::out, string::out) is nondet.
:- pred update_argument_graph(sentence::in, list(sentence)::in, pair(set(sentence), digraph(sentence))::in,
          constraint_store::in, constraint_store::out, list(sentence)::out, list(sentence)::out, pair(set(sentence), digraph(sentence))::out, list(string)::out) is nondet.
:- pred filter_marked(list(sentence)::in, set(sentence)::in, constraint_store::in, list(string)::in, constraint_store::out, list(sentence)::out, list(sentence)::out, list(string)::out) is nondet.
:- pred acyclic(digraph(sentence)::in) is semidet.
:- pred graph_union(digraph(sentence)::in, digraph(sentence)::in, digraph(sentence)::out) is det.
:- pred append_element_nodup(list(T)::in, T::in, list(T)::out) is det.
:- pred append_elements_nodup(list(T)::in, list(T)::in, list(T)::out) is det.
:- pred choose_turn(pot_arg_graph::in, opponent_arg_graph_set::in, turn::out) is det.
:- pred proponent_sentence_choice(list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred opponent_abagraph_choice(list(focussed_pot_arg_graph)::in, focussed_pot_arg_graph::out,
          list(focussed_pot_arg_graph)::out) is det.
:- pred opponent_sentence_choice(focussed_pot_arg_graph::in, sentence::out, focussed_pot_arg_graph::out) is nondet.
:- pred find_first_constraint(list(sentence)::in, sentence::out, list(sentence)::out) is semidet.
:- pred rule_choice(sentence::in, list(sentence)::out, prop_info::in, id_map::in, id_map::out, string::out) is nondet.
:- pred turn_choice(turn_choice::in, pot_arg_graph::in, opponent_arg_graph_set::in, turn::out) is det.
:- pred sentence_choice(proponent_sentence_choice::in, list(sentence)::in, sentence::out,
          list(sentence)::out) is det.
:- pred sentence_choice_backtrack(opponent_sentence_choice::in, list(sentence)::in, sentence::out,
          list(sentence)::out) is nondet.
:- pred opponent_abagraph_choice(opponent_abagraph_choice::in, list(focussed_pot_arg_graph)::in,
          focussed_pot_arg_graph::out, list(focussed_pot_arg_graph)::out) is det.
:- pred get_smallest_ss(list(focussed_pot_arg_graph)::in, int::in, focussed_pot_arg_graph::in, focussed_pot_arg_graph::out) is det.
:- pred get_largest_ss(list(focussed_pot_arg_graph)::in, int::in, focussed_pot_arg_graph::in, focussed_pot_arg_graph::out) is det.
:- pred get_first_assumption_or_other(list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred get_first_nonassumption_or_other(list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred get_newest_nonassumption_or_other(list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred sort_rule_pairs(proponent_rule_choice::in, prop_info::in, list(list(sentence))::in,
          list(list(sentence))::out) is det.
:- pred rule_sort_small_bodies(list(sentence)::in, list(sentence)::in, builtin.comparison_result::out) is det.
:- pred rule_sort_look_ahead_1(prop_info::in, list(sentence)::in, list(sentence)::in,
          builtin.comparison_result::out) is det.
:- pred count_nonD_nonJsP(list(sentence)::in, set(sentence)::in, digraph(sentence)::in, int::in, int::out) is det.
:- pred find_first(pred(T)::in(pred(in) is semidet), list(T)::in, T::out, list(T)::out) is semidet.
:- pred select(T::out, list(T)::in, list(T)::out) is nondet.
:- pred select3_(list(T)::in, T::in, T::out, list(T)::out) is multi.
:- func membership(sentence, set(sentence)) = b_constraint is det.
:- pred unify(sentence::in, constraint_store::in, constraint_store::out, list(string)::out) is semidet.
:- pred excluded(sentence::in, set(sentence)::in) is semidet.
:- pred filter_constraints(list(sentence)::in, constraint_store::in, list(sentence)::out, constraint_store::out, list(string)::out) is semidet.
:- pred next_step_all_branches_int(int::out) is det.

% ("set some options" moved to options.m.)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: entry predicates

derive(S, MaxResults) = Results :-
  %retractall(proving(_)),
  %assert(proving(S)),
  %retractall(sols(_)),
  %assert(sols(1)),
  Solutions = initial_solutions(S),
  (verbose, Solutions = [step_and_id_map(InitTuple, _, _)] ->
    print_step(0, InitTuple)
  ;
    true),
  Results = derivation(Solutions, [], S, MaxResults).
  %incr_sols.

initial_solutions(S) = Solutions :-
  initial_derivation_tuple(make_singleton_set(S), InitTuple),
  (verbose ->
    IdsIn = 0-map.init,
    open(decompiled_path, "a", Fd),
    write_sentence(S, 0, Fd, Id, IdsIn, Ids1),
    close(Fd),
    format_append(runtime_out_path, 
      "%s Step 0: Case init: S: %i\n  S: %s\n\n",
      [s(now), i(Id), s(sentence_to_string(S))])
  ;
    % Put at least one key in IdsIn.
    Ids1 = 0-set(map.init, -1, map.init)),
  Solutions = [step_and_id_map(InitTuple, 1-snd(Ids1), "")].

initial_derivation_tuple(
    PropUnMrk,
    step_tuple(O_PropUnMrk-set.init-PropGr, % PropUnMrk-PropM-PropGr
               []-set.init,                 % OppUnMrk-OppM (members of each are Claim-GId-UnMrk-Mrk-Graph)
               % TODO: Support GB.
               D0,                          % D
               set.init-map.init,           % C
               set.init,                    % Att
               constraints.init)) :-        % CS
  to_sorted_list(PropUnMrk, O_PropUnMrk),
  % Instead of findall, use the set filter.
  %findall(A, (member(A, O_PropUnMrk),
  %            assumption(A)),
  %        D0),
  D0 = filter((pred(X::in) is semidet :- assumption(X)), PropUnMrk),
  PropGr = fold(func(V, GIn) = GOut :- add_vertex(V, _, GIn, GOut),
                PropUnMrk, digraph.init).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: basic control structure

% derivation(SolutionsIn, ResultsIn, S, MaxResults) = Results.
% S is the claim sentence (only for printing).
derivation(SolutionsIn, ResultsIn, S, MaxResults) = Results :-
  (SolutionsIn = [step_and_id_map(T, IdsIn, RuntimeOut)|RestIn] ->
    (length(ResultsIn) >= MaxResults ->
      Results = ResultsIn
    ;
      InN-_ = IdsIn,
      next_step_all_branches_int(StepAllBranches),
      format("*** Step %i (all branches)\n", [i(StepAllBranches - 1)]), % Debug
      (T = step_tuple([]-PropMrk-PropG, []-OppM, D, C-_, Att, CS) ->
        format("*** Step %i (all branches), %0.0f%% extra\n", [i(StepAllBranches - 1), f(100.0 * float((StepAllBranches - 1) - (InN - 1)) / float(InN - 1))]),
        Result = derivation_result(PropMrk-PropG, OppM, D, C, Att, CS),
        ((option(show_solution, "true"), \+ verbose) -> PreviousN = InN - 1, format("*** Step %i\n", [i(PreviousN)]) ; true),
        format_append(runtime_out_path, RuntimeOut, []),
        format_append(runtime_out_path, "%s ABA solution found\n", [s(now)]),
        % Add to the results and process remaining solutions (if any).
        print_result(S, Result),
        Results = derivation(RestIn, [Result|ResultsIn], S, MaxResults)
      ;
        format_append(runtime_out_path, RuntimeOut, []),
        Solutions1 = derivation_step(step_and_id_map(T, IdsIn, "")),
        % Set the next step number for all solutions.
        OutN = InN + 1,
        Solutions = map(func(step_and_id_map(T2, Ids2, R2)) = step_and_id_map(T2, OutN-snd(Ids2), R2), Solutions1),
        ([step_and_id_map(T1, Ids1, RuntimeOut1)|Rest] = Solutions ->
          (verbose ->
            print_step(InN, T1),
            open(decompiled_path, "a", Fd),
            format(Fd, "; ^^^ Step %d\n\n", [i(InN)]),
            close(Fd)
          ; true),
          % Replace the head of the solutions and continue processing.
          % If Rest is not [], it means that derivation_step added solutions.
          Results = derivation(append([step_and_id_map(T1, Ids1, RuntimeOut1)|Rest], RestIn), ResultsIn, S, MaxResults)
        ;
          % derivation_step returned no solutions for the head. Try remaining solutions.
          Results = derivation(RestIn, ResultsIn, S, MaxResults))))
  ;
    Results = ResultsIn).

derivation_step(StepAndIdMap) = Solutions :-
  step_and_id_map(step_tuple(P, O, _, _, _, _), _, _) = StepAndIdMap,
  choose_turn(P, O, Turn),
  (Turn = proponent ->
    PropUnMrk-_-_ = P,
    % Ignore PropUnMrkMinus. proponent_step will make it.
    proponent_sentence_choice(PropUnMrk, S, _),
    Solutions = proponent_step(S, StepAndIdMap)
  ;
    OppUnMrk-_ = O,
    % Ignore OppUnMrkMinus. opponent_step will make it.
    opponent_abagraph_choice(OppUnMrk, OppArg, _),
    Solutions = opponent_step(OppArg, StepAndIdMap)).

% S should be a sentence in PropUnMrk.
proponent_step(S, step_and_id_map(step_tuple(PropUnMrk-PropMrk-PropGr, O, D, C, Att, CS), IdsIn, _)) = Solutions :-
  (delete_first(PropUnMrk, S, PropUnMrkMinus) ->
    RuntimeOut1 = step_runtime_out(D, C, CS, IdsIn),
    (assumption(S) ->
      (proponent_asm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, Att, CS, IdsIn, Solution) ->
        poss_print_case("1.(i)", S),
        Solutions1 = [Solution]
      ;
        Solutions1 = [])
    ;
      %TODO: Do we need to compute and explicitly check? non_assumption(S),
      promise_equivalent_solutions[SolutionsR] (
        unsorted_solutions((pred(Solution::out) is nondet :-
                              proponent_nonasm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, Att, CS, IdsIn, Solution),
                              poss_print_case("1.(ii)", S)),
                           SolutionsR)),
      Solutions1 = reverse(SolutionsR)),
    Solutions = prepend_runtime_out(Solutions1, RuntimeOut1)
  ;
    % S was not in PropUnMrk so do nothing. (We don't expect this.)
    Solutions = [step_and_id_map(step_tuple(PropUnMrk-PropMrk-PropGr, O, D, C, Att, CS), IdsIn,
                                 "warning: proponent_step: PropUnMrk doesn't have S " ++ sentence_to_string(S) ++ "\n")]).

opponent_step(OppArg, step_and_id_map(step_tuple(P, OppUnMrk-OppMrk, D, C, Att, CS), IdsIn, _)) = Solutions :-
  (delete_first(OppUnMrk, OppArg, OppUnMrkMinus) ->
    RuntimeOut1 = step_runtime_out(D, C, CS, IdsIn),
    promise_equivalent_solutions[SolutionsR] (
      unsorted_solutions((pred(Solution::out) is nondet :-
                            opponent_sentence_choice(OppArg, S, OppArgMinus),
                            (assumption(S) ->
                              opponent_i(S, OppArgMinus, OppUnMrkMinus-OppMrk, opponent_step_tuple(P, D, C, Att, CS), IdsIn, Solution)
                            ;
                              %TODO: Do we need to compute and explicitly check? non_assumption(S),
                              opponent_ii(S, OppArgMinus, OppUnMrkMinus-OppMrk, opponent_step_tuple(P, D, C, Att, CS), IdsIn, Solution),
                              poss_print_case("2.(ii)", S))),
                         SolutionsR)),
    Solutions1 = reverse(SolutionsR),
    Solutions = prepend_runtime_out(Solutions1, RuntimeOut1)
  ;
    % OppArg was not in OppUnMrk so do nothing. (We don't expect this.)
    Solutions = [step_and_id_map(step_tuple(P, OppUnMrk-OppMrk, D, C, Att, CS), IdsIn,
                                 "warning: opponent_step: OppUnMrk doesn't have the given OppArg\n")]).

% This is a helper for proponent_step and opponent_step.
step_runtime_out(D, C, CS, IdsIn) = RuntimeOut :-
  (verbose ->
    puts("\n"),
    RuntimeOut = format(
      "%s Step %i start\n  D: %s\n  C: %s\n%s",
      [s(now), i(fst(IdsIn)), s(sentence_set_to_string(D)), s(sentence_set_to_string(fst(C))), s(to_string(CS))])
  ;
    RuntimeOut = "").

% This is a helper for proponent_step and opponent_step.
prepend_runtime_out(Solutions1, RuntimeOut) = map(func(step_and_id_map(T, Ids, R)) = step_and_id_map(T, Ids, RuntimeOut ++ R), Solutions1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CASES

%%%%%%%%%% proponent

proponent_asm(A, PropUnMrkMinus, PropMrk-PropGr, OppUnMrk-OppMrk, D, C, Att, CS, IdsIn,
              step_and_id_map(step_tuple(PropUnMrkMinus-PropMrk1-PropGr, OppUnMrk1-OppMrk, D, C, Att1, CS), IdsOut, RuntimeOut)) :-
  (verbose ->
    RuntimeOut1 = format("%s Step %i: Case 1.(i) start A: %s\n", [s(now), i(fst(IdsIn)), s(sentence_to_string(A))])
  ;
    RuntimeOut1 = ""),
  contrary(A, Contrary),
  ((\+ (member(Member1, OppUnMrk), Member1 = Contrary-_-(_-_-_)),
    \+ (member(Member2, OppMrk),   Member2 = Contrary-_-(_-_-_))) ->
    add_vertex(Contrary, _, digraph.init, GContrary),
    % The max key in IdsIn is the max graph ID which has been used so far.
    NewGId = det_max_key(snd(IdsIn)) + 1,
    append_element_nodup(OppUnMrk, Contrary-NewGId-([Contrary]-set.init-GContrary), OppUnMrk1)
  ;
    OppUnMrk1 = OppUnMrk,
    NewGId = 0),
  insert(A, PropMrk, PropMrk1),
  insert(Contrary-A, Att, Att1),
  % TODO: Support GB. gb_acyclicity_check(G, A, [Contrary], G1),
  (verbose ->
    open(decompiled_path, "a", Fd),
    write_sentence(A, 0, Fd, Id, IdsIn, Ids1),
    (NewGId > 0 ->
      write_sentence(Contrary, NewGId, Fd, ContraryId, Ids1, IdsOut)
    ;
      % TODO: Get the Contrary graph ID from OppUnMrk or OppMrk.
      ContraryId = 0,
      IdsOut = Ids1),
    close(Fd),
    (solutions((pred(X::out) is nondet :- rule(Contrary, X)), []) -> % Debug: We only need to check for one solution.
      HasBody = "N" ; HasBody = "Y"),
    RuntimeOut = RuntimeOut1 ++ format(
      "%s Step %i: Case 1.(i): A: %i, Contrary %i has body? %s, NewGId %i\n  A: %s\n  Contrary: %s\n",
      [s(now), i(fst(IdsIn)), i(Id), i(ContraryId), s(HasBody), i(NewGId),
       s(sentence_to_string(A)), s(sentence_to_string(Contrary))])
  ;
    IdsOut = IdsIn,
    RuntimeOut = RuntimeOut1).

proponent_nonasm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, Att, CS, IdsIn,
                 step_and_id_map(step_tuple(PropUnMrk1-PropMrk1-PropGr1, O, D1, C, Att, CSOut), IdsOut, RuntimeOut)) :-
  (verbose ->
    RuntimeOut1 = format("%s Step %i: Case 1.(ii) start S: %s\n", [s(now), i(fst(IdsIn)), s(sentence_to_string(S))])
  ;
    RuntimeOut1 = ""),
  rule_choice(S, Body1, prop_info(D, PropGr), IdsIn, Ids1, RuntimeOutrule_choice),
  filter_constraints(Body1, CS, Body, CS1, Descs1),
  RuntimeOut2 = RuntimeOut1 ++ RuntimeOutrule_choice,
  %\+ (member(X, Body), member(X, fst(C))),
  foldl((pred(X::in, CSIn-Debug1In::in, CSOut1-Debug1Out::out) is semidet :-
           MemberXC = membership(X, fst(C)),
           b_unify(not(MemberXC), CSIn, CSOut1, _),
           (MemberXC = f ->
             Debug1Out = Debug1In
           ;
             Debug1Out = Debug1In ++ "  " ++ b_constraint_to_string(not(MemberXC)) ++ "\n")),
        Body, CS1-"", CS2-Debug1),
  (verbose ->
    (Debug1 = "" -> true ; format_append(runtime_out_path, "%s Step %i: not(MemberXC):\n%s", [s(now), i(fst(IdsIn)), s(Debug1)]))
  ; true),
  update_argument_graph(S, Body, PropMrk-PropGr, CS2, CSOut, BodyUnMrk, BodyUnMrkAs, PropMrk1-PropGr1, Descs2),
  Descs = append_nodups(Descs1, Descs2),
  append_elements_nodup(BodyUnMrk, PropUnMrkMinus, PropUnMrk1),
  % union(list_to_set(BodyUnMrkAs), D, D1),
  foldl((pred(UnMrkA::in, DIn::in, DOut::out) is semidet :-
          % TODO: Use membership?
          DOut = insert(DIn, UnMrkA)),
        BodyUnMrkAs, D, D1),
  % TODO: Support GB. gb_acyclicity_check(G, S, Body, G1),
  (verbose ->
    MarkedBody = intersect(list_to_set(Body), PropMrk),
    UnMarkedBodyAs = list_to_set(BodyUnMrkAs),
    UnMarkedBodyNonAs = difference(list_to_set(BodyUnMrk), UnMarkedBodyAs),
    divide_by_set(list_to_set(PropUnMrkMinus), UnMarkedBodyAs, ExistingUnMarkedAs, NewUnMarkedAs),
    divide_by_set(list_to_set(PropUnMrkMinus), UnMarkedBodyNonAs, ExistingUnMarkedNonAs, NewUnMarkedNonAs),
    ExistingBody = union(union(MarkedBody, ExistingUnMarkedAs), ExistingUnMarkedNonAs),

    open(decompiled_path, "a", Fd),
    write_sentence(S, 0, Fd, Id, Ids1, Ids2),
    write_sentence_set(NewUnMarkedAs, 0, Fd, NewUnMarkedAsIds, Ids2, Ids3),
    write_sentence_set(NewUnMarkedNonAs, 0, Fd, NewUnMarkedNonAsIds, Ids3, Ids4),
    write_sentence_set(ExistingBody, 0, Fd, ExistingBodyIds, Ids4, IdsOut),
    close(Fd),
    ConstraintsRuntimeOut = foldl(func(Desc, In) = In ++ format("%s Step %i: Case 1.(iii): %s\n  S: %s\n", 
                                    [s(now), i(fst(IdsIn)), s(Desc), s(sentence_to_string(S))]),
                                  Descs, ""),
    RuntimeOut = RuntimeOut2 ++ format(
      "%s Step %i: Case 1.(ii): S: %i, NewUnMarkedAs: [%s], NewUnMarkedNonAs: [%s], ExistingBody: [%s]\n  S: %s\n  NewUnMarkedAs: %s\n  NewUnMarkedNonAs: %s\n  ExistingBody: %s\n",
      [s(now), i(fst(IdsIn)), i(Id),
       s(join_list(" ", map(int_to_string, NewUnMarkedAsIds))),
       s(join_list(" ", map(int_to_string, NewUnMarkedNonAsIds))),
       s(join_list(" ", map(int_to_string, ExistingBodyIds))), 
       s(sentence_to_string(S)),
       s(sentence_set_to_string(NewUnMarkedAs)),
       s(sentence_set_to_string(NewUnMarkedNonAs)),
       s(sentence_set_to_string(ExistingBody))])
      ++ ConstraintsRuntimeOut
  ;
    IdsOut = Ids1,
    RuntimeOut = RuntimeOut2).

%%%%%%%%%% opponent

opponent_i(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att, CS), IdsIn, step_and_id_map(T, IdsOut, RuntimeOut)) :-
  (verbose ->
    RuntimeOut1 = format("%s Step %i: Case 2 start A: %s\n", [s(now), i(fst(IdsIn)), s(sentence_to_string(A))])
  ;
    RuntimeOut1 = ""),
  MemberAD = membership(A, D),
  (verbose ->
    RuntimeOut2 = RuntimeOut1 ++ format("%s Step %i: MemberAD: %s\n", [s(now), i(fst(IdsIn)), s(b_constraint_to_string(MemberAD))])
  ;
    RuntimeOut2 = RuntimeOut1),
  ( b_unify(not(MemberAD), CS, CS1, _),
    MemberAC = membership(A, fst(C)),
    (verbose ->
      RuntimeOut3 = RuntimeOut2 ++ format("%s Step %i: MemberAC: %s\n", [s(now), i(fst(IdsIn)), s(b_constraint_to_string(MemberAC))])
    ;
      RuntimeOut3 = RuntimeOut2),
    ( b_unify(MemberAC, CS1, CS2, _),
      opponent_ib(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att, CS2), IdsIn, step_and_id_map(T, IdsOut, RuntimeOutib)),
      RuntimeOut = RuntimeOut3 ++ RuntimeOutib,
      poss_print_case("2.(ib)", A)
    ;
      b_unify(not(MemberAC), CS1, CS2, _),
      opponent_ic(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att, CS2), IdsIn, step_and_id_map(T, IdsOut, RuntimeOutic)),
      RuntimeOut = RuntimeOut3 ++ RuntimeOutic,
      poss_print_case("2.(ic)", A))
  ;
    b_unify(MemberAD, CS, CS1, _),
    opponent_ia(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att, CS1), IdsIn, step_and_id_map(T, IdsOut, RuntimeOutia)),
    RuntimeOut = RuntimeOut2 ++ RuntimeOutia,
    poss_print_case("2.(ia)", A)).

opponent_ia(A, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk,
            opponent_step_tuple(P, D, C, Att, CS), IdsIn, 
            step_and_id_map(step_tuple(P, OppUnMrkMinus1-OppMrk, D, C, Att, CSOut), IdsOut, RuntimeOut)) :-
  (verbose ->
    RuntimeOut1 = format("%s Step ?: Case 2.(ia) start\n", [s(now)])
  ;
    RuntimeOut1 = ""),
  (gb_derivation ->
    CSOut = CS,
    RuntimeOut2 = RuntimeOut1
  ;
    MemberAC = membership(A, fst(C)),  % also sound for gb? CHECK in general
    b_unify(not(MemberAC), CS, CSOut, _),
    (verbose ->
      (MemberAC = f -> RuntimeOut2 = RuntimeOut1 ; RuntimeOut2 = RuntimeOut1 ++ format("%s Step ?: not(MemberAC): %s\n", [s(now), s(b_constraint_to_string(not(MemberAC)))]))
    ;
      RuntimeOut2 = RuntimeOut1)),
  insert(A, Marked, Marked1),
  append_element_nodup(OppUnMrkMinus, Claim-GId-(UnMrkMinus-Marked1-Graph), OppUnMrkMinus1),
  (verbose ->
    open(decompiled_path, "a", Fd),
    write_sentence(A, GId, Fd, Id, IdsIn, IdsOut),
    close(Fd),
    RuntimeOut = RuntimeOut2 ++ format("%s Step %i: Case 2.(ia): A: %i, GId %i\n  A: %s\n",
      [s(now), i(fst(IdsIn)), i(Id), i(GId), s(sentence_to_string(A))])
  ; 
    IdsOut = IdsIn,
    RuntimeOut = RuntimeOut2).


opponent_ib(A, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk,
            opponent_step_tuple(P, D, C, Att, CS), IdsIn,
            step_and_id_map(step_tuple(P, OppUnMrkMinus-OppMrk1, D, C, Att, CS), IdsOut, RuntimeOut)) :-
  (verbose ->
    RuntimeOut1 = format("%s Step ?: Case 2.(ib) start\n", [s(now)])
  ;
    RuntimeOut1 = ""),
  % TODO: Support GB. contrary(A, Contrary),
  % TODO: Support GB. gb_acyclicity_check(G, Claim, [Contrary], G1),
  insert(A, Marked, Marked1),
  insert(Claim-GId-(UnMrkMinus-Marked1-Graph), OppMrk, OppMrk1),
  (verbose ->
    open(decompiled_path, "a", Fd),
    write_sentence(A, GId, Fd, Id, IdsIn, IdsOut),
    close(Fd),
    % Get the ID of the original culprit. (This is why we pass around C as a pair with the Ids.)
    (FoundId = search(snd(C), A) -> CulpritId = FoundId ; CulpritId = 0),
    RuntimeOut = RuntimeOut1 ++ format("%s Step %i: Case 2.(ib): A: %i, GId %i, Culprit %i\n  A: %s\n",
      [s(now), i(fst(IdsIn)), i(Id), i(GId), i(CulpritId), s(sentence_to_string(A))])
  ; 
    IdsOut = IdsIn,
    RuntimeOut = RuntimeOut1).


opponent_ic(A, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk,
            opponent_step_tuple(PropUnMrk-PropMrk-PropGr, D, C, Att, CS), IdsIn, 
            step_and_id_map(step_tuple(PropUnMrk1-PropMrk-PropGr1, OppUnMrkMinus-OppMrk1, D1, C1, Att1, CS), IdsOut, RuntimeOut)) :-
  (verbose ->
    RuntimeOut1 = format("%s Step %i: Case 2.(ic) start\n", [s(now), i(fst(IdsIn))])
  ;
    RuntimeOut1 = ""),
  contrary(A, Contrary),
  %(search_key(PropGr, Contrary, _) ->
  %  PropUnMrk = PropUnMrk1,
  %  PropGr = PropGr1,
  %  IsNewContrary = "N"
  %;
    append_element_nodup(PropUnMrk, Contrary, PropUnMrk1),
    PropGr = PropGr1, %add_vertex(Contrary, _, PropGr, PropGr1),
    IsNewContrary = "Y",
  (verbose ->
    open(decompiled_path, "a", Fd),
    write_sentence(A, GId, Fd, Id, IdsIn, Ids1),
    write_sentence(Contrary, 0, Fd, ContraryId, Ids1, IdsOut),
    close(Fd),
    RuntimeOut = RuntimeOut1 ++ format(
      "%s Step %i: Case 2.(ic): A: %i, GId %i, Contrary %i new? %s\n  A: %s\n  Contrary: %s\n",
      [s(now), i(fst(IdsIn)), i(Id), i(GId), i(ContraryId), s(IsNewContrary),
       s(sentence_to_string(A)), s(sentence_to_string(Contrary))])
  ; 
    Id = 0,
    IdsOut = IdsIn,
    RuntimeOut = RuntimeOut1),
  (assumption(Contrary) ->
    insert(Contrary, D, D1)
  ;
    D1 = D),
  C1 = insert(fst(C), A)-set(snd(C), A, Id),
  insert(A, Marked, Marked1),
  insert(Claim-GId-(UnMrkMinus-Marked1-Graph), OppMrk, OppMrk1),
  insert(Contrary-A, Att, Att1).
  % TODO: Support GB. gb_acyclicity_check(G, Claim, [Contrary], G1).

opponent_ii(S, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk, opponent_step_tuple(P, D, C, Att, CS), IdsIn,
            step_and_id_map(step_tuple(P, OppUnMrkMinus1-OppMrk1, D, C, Att, CSOut), IdsOut, RuntimeOut)) :-
  (verbose ->
    RuntimeOut1 = format("%s Step %i: Case 2.(ii) start S: %s\n", [s(now), i(fst(IdsIn)), s(sentence_to_string(S))])
  ;
    RuntimeOut1 = ""),
  solutions((pred(Body::out) is nondet :- rule(S, Body), \+ (member(A, Body), excluded(A, D))), Bodies1),
  % Filter constraints in each body.
  Bodies-CS1-ConstraintsRuntimeOut = foldl((
    func(Body1, BodiesIn1-CSIn1-RunOut1) = Bodies2-CS2-RunOut2 :-
      (filter_constraints(Body1, CSIn1, Body2, LocalCS2, Descs) ->
        Bodies2 = append(BodiesIn1, [Body2]),
        CS2 = LocalCS2,
        (verbose ->
          RunOut2 = RunOut1 ++ foldl(func(Desc, R) = R ++ format("%s Step %i: Case 2.(iii): %s\n  S: %s\n", 
                                       [s(now), i(fst(IdsIn)), s(Desc), s(sentence_to_string(S))]),
                                     Descs, "")
        ;
          RunOut2 = RunOut1)
      ;
        % Constraint unify failed, so skip this body
        Bodies2 = BodiesIn1,
        CS2 = CSIn1,
        RunOut2 = RunOut1)),
      Bodies1, []-CS-""),
  iterate_bodies(Bodies, S-GId, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk, C, CS1, CSOut,
                 OppUnMrkMinus1-OppMrk1, IdsIn, RuntimeOut1, IdsOut, RuntimeOut2),
  RuntimeOut = RuntimeOut2 ++ ConstraintsRuntimeOut.

% SGId is the graph ID that S came from.
iterate_bodies([], _, _, OppUnMrkMinus-OppMrk, _, CS, CS, OppUnMrkMinus-OppMrk, Ids, RuntimeOut, Ids, RuntimeOut).
iterate_bodies([Body|RestBodies], S-SGId, Claim-GId-(UnMrkMinus-Marked-Graph), InOppUnMrkMinus-InOppMrk, C, CS, CSOut,
               OppUnMrkMinus1-OppMrk1, IdsIn, RuntimeOut1, IdsOut, RuntimeOut) :-
  (verbose ->
    RuntimeOut2 = RuntimeOut1 ++ format("%s Step %i: Case 2.(ii) Rest: %i Body: %s\n", 
                  [s(now), i(fst(IdsIn)), i(length(RestBodies)), s(sentence_list_to_string(Body))])
  ;
    RuntimeOut2 = RuntimeOut1),
  update_argument_graph(S, Body, Marked-Graph, CS, CS1, UnMarked, UnMarkedAs, Marked1-Graph1, Descs),
  append_elements_nodup(UnMarked, UnMrkMinus, UnMrk1),
  (GId = 0 ->
    % We are on iteration >= 2 and need a new GId.
    NewGId = det_max_key(snd(IdsIn)) + 1,
    % Copy the Ids from the graph for S to the new graph.
    (SMap = search(snd(IdsIn), SGId) ->
      Ids1 = fst(IdsIn)-set(snd(IdsIn), NewGId, SMap)
    ;
      % This shouldn't happen since there should be entries in IdsIn for GId.
      Ids1 = IdsIn)
  ;
    % The first iteration re-uses the GId from the graph extracted by opponent_abagraph_choice.
    NewGId = GId,
    Ids1 = IdsIn),
  % TODO: Use membership
  ((\+ gb_derivation, member(A, Body), member(A, fst(C))) ->
    (NewGId = GId ->
      % Move the opponent graph to marked.
      OutOppUnMrkMinus = InOppUnMrkMinus,
      insert(Claim-NewGId-(UnMrk1-Marked1-Graph1), InOppMrk, OutOppMrk),
      MarkS = yes, MarkGraph = "Y"
    ;
      % On iteration >= 2, we don't want to create a new graph and immediately mark it.
      OutOppUnMrkMinus = InOppUnMrkMinus,
      OutOppMrk = InOppMrk,
      MarkS = no, MarkGraph = "N")
  ;
    append_element_nodup(InOppUnMrkMinus, Claim-NewGId-(UnMrk1-Marked1-Graph1), OutOppUnMrkMinus),
    OutOppMrk = InOppMrk,
    (NewGId = GId -> MarkS = yes, MarkGraph = "N" ; MarkS = no, MarkGraph = "N")),
  % TODO: Support GB. OutG = InG,
  (verbose ->
    MarkedBody = intersect(list_to_set(Body), Marked),
    UnMarkedBodyAs = list_to_set(UnMarkedAs),
    UnMarkedBodyNonAs = difference(list_to_set(UnMarked), UnMarkedBodyAs),
    divide_by_set(list_to_set(UnMrkMinus), UnMarkedBodyAs, ExistingUnMarkedAs, NewUnMarkedAs),
    divide_by_set(list_to_set(UnMrkMinus), UnMarkedBodyNonAs, ExistingUnMarkedNonAs, NewUnMarkedNonAs),
    ExistingBody = union(union(MarkedBody, ExistingUnMarkedAs), ExistingUnMarkedNonAs),

    open(decompiled_path, "a", Fd),
    write_sentence(S, NewGId, Fd, Id, Ids1, Ids2),
    write_sentence_set(NewUnMarkedAs, NewGId, Fd, NewUnMarkedAsIds, Ids2, Ids3),
    write_sentence_set(NewUnMarkedNonAs, NewGId, Fd, NewUnMarkedNonAsIds, Ids3, Ids4),
    write_sentence_set(ExistingBody, NewGId, Fd, ExistingBodyIds, Ids4, Ids5),
    close(Fd),
    (MarkS = yes ->
      RuntimeOut3 = RuntimeOut2 ++ format("%s Step %i: Case 2.(ii): S: %i, GId %i, mark graph? %s\n  S: %s\n",
        [s(now), i(fst(IdsIn)), i(Id), i(SGId), s(MarkGraph), s(sentence_to_string(S))])
    ;
      RuntimeOut3 = RuntimeOut2),
    ConstraintsRuntimeOut = foldl(func(Desc, In) = In ++ format("%s Step %i: Case 2.(iii): %s\n  S: %s\n", 
                                    [s(now), i(fst(IdsIn)), s(Desc), s(sentence_to_string(S))]),
                                  Descs, ""),
    RuntimeOut4 = RuntimeOut3 ++ format(
      "%s Step %i: Case 2.(ii): S: %i, NewGId %i, NewUnMarkedAs: [%s], NewUnMarkedNonAs: [%s], ExistingBody: [%s]\n  S: %s\n  NewUnMarkedAs: %s\n  NewUnMarkedNonAs: %s\n  ExistingBody: %s\n",
      [s(now), i(fst(IdsIn)), i(Id), i(NewGId),
       s(join_list(" ", map(int_to_string, NewUnMarkedAsIds))),
       s(join_list(" ", map(int_to_string, NewUnMarkedNonAsIds))),
       s(join_list(" ", map(int_to_string, ExistingBodyIds))), 
       s(sentence_to_string(S)),
       s(sentence_set_to_string(NewUnMarkedAs)),
       s(sentence_set_to_string(NewUnMarkedNonAs)),
       s(sentence_set_to_string(ExistingBody))])
      ++ ConstraintsRuntimeOut
  ;
    Ids5 = Ids1,
    RuntimeOut4 = RuntimeOut2),

  % For further iterations, set GId to 0 so that we mint new IDs for added graphs.
  iterate_bodies(RestBodies, S-SGId, Claim-0-(UnMrkMinus-Marked-Graph), OutOppUnMrkMinus-OutOppMrk, C, CS1, CSOut,
                 OppUnMrkMinus1-OppMrk1, Ids5, RuntimeOut4, IdsOut, RuntimeOut).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SUBSIDIARY FUNCTIONS

% update_argument_graph(S, Body, Marked-Graph, CS, CSOut, Unproved, UnprovedAs, Marked1-Graph1, Descs)
% - update graph representation of an argument with rule(S, Body)
% - check updated version for acyclicity
% - record the previously unproved sentences and assumptions from body
update_argument_graph(S, Body, Marked-Graph, CS, CSOut, UnMarked, UnMarkedAs, Marked1-Graph1, Descs) :-
  filter_marked(Body, Marked, CS, [], CSOut, UnMarked, UnMarkedAs, Descs),
  %ord_del_element(Graph, S-[], GraphMinus),
  GraphMinus = Graph, % Note: We don't need to  delete S because it will be added again below.
  insert(S, Marked, Marked1),
  list_to_set(Body, O_Body),
  %ord_add_element(GraphMinus, S-O_Body, GraphMinus1),
  GraphMinus1 = fold(func(B, GIn) = add_vertex_pair(S-B, GIn),
                     O_Body, GraphMinus),
  BodyUnMarkedGraph = fold(func(B, GIn) = GOut :-
                             (\+ search_key(GraphMinus1, B, _) ->
                               add_vertex(B, _, GIn, GOut)
                             ;
                               GOut = GIn),
                           O_Body, digraph.init),
  graph_union(GraphMinus1, BodyUnMarkedGraph, Graph1).
  %TODO: Check acyclic under constraints (acyclic(Graph1) -> true ; unexpected($file, $pred, "Graph1 not acyclic")).

% filter_marked(Body, AlreadyProved, CS, DescsIn, CSOut, Unproved, UnprovedAs, Descs)
filter_marked([], _, CS, Descs, CS, [], [], Descs).
filter_marked([S|RestBody], Proved, CS, DescsIn, CSOut, InUnproved, InUnprovedAs, Descs) :-
  (assumption(S) ->
    A = S,
    MemberAProved = membership(A, Proved),
    ( b_unify(MemberAProved, CS, CS1, Descs1),
      InUnproved = OutUnproved,
      InUnprovedAs = OutUnprovedAs,
      filter_marked(RestBody, Proved, CS1, append_nodups(DescsIn, Descs1), CSOut, OutUnproved, OutUnprovedAs, Descs)
    ;
      b_unify(not(MemberAProved), CS, CS1, Descs1),
      InUnproved = [A|OutUnproved], 
      InUnprovedAs = [A|OutUnprovedAs],
      filter_marked(RestBody, Proved, CS1, append_nodups(DescsIn, Descs1), CSOut, OutUnproved, OutUnprovedAs, Descs))
  ;
    MemberSProved = membership(S, Proved),
    ( b_unify(MemberSProved, CS, CS1, Descs1),
      InUnproved = OutUnproved,
      InUnprovedAs = OutUnprovedAs,
      filter_marked(RestBody, Proved, CS1, append_nodups(DescsIn, Descs1), CSOut, OutUnproved, OutUnprovedAs, Descs)
    ;
      b_unify(not(MemberSProved), CS, CS1, Descs1),
      InUnproved = [S|OutUnproved],
      InUnprovedAs = OutUnprovedAs,
      filter_marked(RestBody, Proved, CS1, append_nodups(DescsIn, Descs1), CSOut, OutUnproved, OutUnprovedAs, Descs))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SUBSIDIARY FUNCTIONS - GRAPH, LIST, MISC

acyclic(G) :-
  is_dag(G).

graph_union(G1, G2, G) :-
  % For each vertex V in G1, add it to G2 plus edges from V.
  G = fold((func(V, G2In) = G2Out :-
              % Add the vertex because there might not be an edge.
              add_vertex(V, _, G2In, G2InWithV),
              % Add each edge to G2.
              NeighborKeySet = lookup_from(G1, lookup_key(G1, V)),
              G2Out = fold(func(Key, G2Acc) = add_vertex_pair(V-lookup_vertex(G1, Key), G2Acc),
                           NeighborKeySet, G2InWithV)),
           vertices(G1), G2).

% append_element_nodup(L, E, Res)
% - Res is the result of adding E to the end of L, if E is not in L
% - otherwise, Res is L
append_element_nodup([], Element, [Element]).
append_element_nodup([H|T], Element, [HOut|Rest]) :-
  % TODO: Use membership?
  (H = Element ->
    HOut = Element,
    Rest = T
  ;
    HOut = H,
    append_element_nodup(T, Element, Rest)).

% append_elements_nodup(Es, L, Res)
% - Res is the result of adding all members of Es not already in L
%   to the end of L
append_elements_nodup([], Result, Result).
append_elements_nodup([Element|Elements], InList, Result) :-
 append_element_nodup(InList, Element, OutList),
 append_elements_nodup(Elements, OutList, Result).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SELECTION FUNCTIONS

choose_turn(P, O, Player) :-
  (P = []-_-_ ->
    Player = opponent
  ;(O = []-_ ->
    Player = proponent
  ;
    % get_turn_choice(TurnStrategy),
    % turn_choice(TurnStrategy, P, O, Player))).
    O = OppUnMrk-_,
    (find_first((pred(_-_-([_]-set.init-_)::in) is semidet), OppUnMrk, _, _) ->
      % There is a new opponent. Do its first expansion next (with opponent_abagraph_choice s).
      Player = opponent
    ;
      get_turn_choice(TurnStrategy),
      turn_choice(TurnStrategy, P, O, Player)))).

proponent_sentence_choice(P, S, Pminus) :-
  % Check for the head of a rule where some body has a constraint.
  (find_first((pred(H::in) is semidet :- rule(H, Body), find_first_constraint(Body, _, _)), P, S1, Pminus1) ->
    S = S1, Pminus = Pminus1
  ;
    % No constraint. Use the sentence choice.
    get_proponent_sentence_choice(PropSentenceStrategy),
    sentence_choice(PropSentenceStrategy, P, S, Pminus)).

opponent_abagraph_choice(O, JC, Ominus) :-
  get_opponent_abagraph_choice(OppJCStrategy),
  opponent_abagraph_choice(OppJCStrategy, O, JC, Ominus).

opponent_sentence_choice(Claim-(Ss-Marked-OGraph), Se, Claim-(Ssminus-Marked-OGraph)) :-
  get_opponent_sentence_choice(OppSentenceStrategy),
  sentence_choice_backtrack(OppSentenceStrategy, Ss, Se, Ssminus).

find_first_constraint(SList, SOut, SListMinus) :-
  find_first((pred(S::in) is semidet :- constraint(S)), SList, SOut, SListMinus).

% PropInfo here holds information about the current state of
% proponent's derivations.
% Omit "proponent" since it is not used.
%rule_choice(Head, Body, proponent, PropInfo) :-
rule_choice(Head, Body, prop_info(D, PropGr), IdsIn, IdsOut, RuntimeOut) :-
  solutions((pred(B::out) is nondet :- rule(Head, B), \+ (member(A, B), excluded(A, D))), RuleBodies),
  get_proponent_rule_choice(PropRuleStrategy),
  sort_rule_pairs(PropRuleStrategy, prop_info(D, PropGr), RuleBodies, SortedRuleBodies),
  % Note: The cut is not needed since the above predicates are det.
  % !,
  (verbose ->
    open(decompiled_path, "a", Fd),
    IdsOut-BodiesText = foldl((
      func(B, IdsIn1-TextIn) = IdsOut1-(TextIn ++ Text) :-
        write_sentence_list(B, 0, Fd, IdsList, IdsIn1, IdsOut1),
        Text = format(" [%s]", [s(join_list(" ", map(int_to_string, IdsList)))])),
      SortedRuleBodies, IdsIn-""),
    close(Fd),
    RuntimeOut = format("%s Step %i: Head %s Potential bodies: [%s]\n", 
      [s(now), i(fst(IdsIn)), s(sentence_to_string(Head)), s(BodiesText)])
  ;
    IdsOut = IdsIn,
    RuntimeOut = ""),
  member(Body, SortedRuleBodies).
  %rule(Head, Body).              % added to fix Fan's first bug

turn_choice(p, P-_-_, _, Player) :-
  (P \= [] ->
    Player = proponent
  ;
    Player = opponent).
turn_choice(o, _, O-_, Player) :-
  (O \= [] ->
    Player = opponent
  ;
    Player = proponent).
turn_choice(s, P-_-_, O-_, Player) :-
  length(P, PN),
  length(O, ON),
  (PN =< ON ->
    Player = proponent
  ;
    Player = opponent).

%

sentence_choice(o, Ss, S, Ssminus) :-
  ([X|Rest] = Ss ->
    S = X, Ssminus = Rest
  ;
    unexpected($file, $pred, "Ss cannot be empty")).
sentence_choice(n, Ss, S, Ssminus) :-
  (split_last(Ss, Rest, X) ->
    S = X, Ssminus = Rest
  ;
    unexpected($file, $pred, "Ss cannot be empty")).
sentence_choice(e, Ss, S, Ssminus) :-
  get_first_assumption_or_other(Ss, S, Ssminus).
sentence_choice(p, Ss, S, Ssminus) :-
  get_first_nonassumption_or_other(Ss, S, Ssminus).
sentence_choice(pn, Ss, S, Ssminus) :-
 get_newest_nonassumption_or_other(Ss, S, Ssminus).

% in the following we only need to backtrack over assumptions

sentence_choice_backtrack(p, Ss, S, Ssminus) :-
  (find_first((pred(X::in) is semidet :- \+ assumption(X)), Ss, First, SsminusS) ->
    S = First, Ssminus = SsminusS
  ;
    select(S, Ss, Ssminus)).
sentence_choice_backtrack(pn, Ss, S, Ssminus) :-
  reverse(Ss, RevSs),
  (find_first((pred(X::in) is semidet :- \+ assumption(X)), RevSs, First, SsminusS) ->
    S = First, Ssminus = SsminusS
  ;
    select(S, RevSs, Ssminus)).

%

opponent_abagraph_choice(o, [JC|Ominus], JC, Ominus).
opponent_abagraph_choice(n, [H|T], JC, Ominus) :-
  (split_last([H|T], Rest, X) ->
    JC = X, Ominus = Rest
  ;
    % We don't expect this to happen because the list is not empty.
    unexpected($file, $pred, "[H|T] cannot be empty")).
opponent_abagraph_choice(s, [Claim-(Ss-Marked-Graph)|RestJCs], JC, Ominus) :-
  length(Ss, L),
  get_smallest_ss(RestJCs, L, Claim-(Ss-Marked-Graph), JC),
  delete_all([Claim-(Ss-Marked-Graph)|RestJCs], JC, Ominus).
opponent_abagraph_choice(l, [Claim-(Ss-Marked-Graph)|RestJCs], JC, Ominus) :-
  length(Ss, L),
  get_largest_ss(RestJCs, L, Claim-(Ss-Marked-Graph), JC),
  delete_all([Claim-(Ss-Marked-Graph)|RestJCs], JC, Ominus).
opponent_abagraph_choice(_, [], _, _) :-
  unexpected($file, $pred, "O cannot be empty").

get_smallest_ss([], _, JC, JC).
get_smallest_ss([Claim-(Ss-Marked-Graph)|RestJCs], BestLSoFar, BestJCSoFar, BestJC) :-
  length(Ss, L), % if L = 1, could we stop?
  (L < BestLSoFar ->
    NewL = L,
    NewJC = Claim-(Ss-Marked-Graph)
  ;
    NewL = BestLSoFar,
    NewJC = BestJCSoFar),
  get_smallest_ss(RestJCs, NewL, NewJC, BestJC).

get_largest_ss([], _, JC, JC).
get_largest_ss([Claim-(Ss-Marked-Graph)|RestJCs], BestLSoFar, BestJCSoFar, BestJC) :-
  length(Ss, L),
  (L > BestLSoFar ->
    NewL = L,
    NewJC = Claim-(Ss-Marked-Graph)
  ;
    NewL = BestLSoFar,
    NewJC = BestJCSoFar),
  get_largest_ss(RestJCs, NewL, NewJC, BestJC).

% helpers

get_first_assumption_or_other(Ss, A, Ssminus) :-
  (find_first((pred(X::in) is semidet :- assumption(X)), Ss, First, SsminusA) ->
    A = First, Ssminus = SsminusA
  ;
    % No assumption. Get the first member.
    ([H|Rest] = Ss ->
      A = H, Ssminus = Rest
    ;
      % We don't expect this.
      unexpected($file, $pred, "Ss cannot be empty"))).

get_first_nonassumption_or_other(Ss, A, Ssminus) :-
  (find_first((pred(X::in) is semidet :- \+ assumption(X)), Ss, First, SsminusA) ->
    A = First, Ssminus = SsminusA
  ;
    % No non-assumption. Get the first member.
    ([H|Rest] = Ss ->
      A = H, Ssminus = Rest
    ;
      % We don't expect this.
      unexpected($file, $pred, "Ss cannot be empty"))).

get_newest_nonassumption_or_other(Ss, A, Ssminus) :-
  reverse(Ss, RevSs),
  (find_first((pred(X::in) is semidet :- \+ assumption(X)), RevSs, First, RevSsminus) ->
    A = First,
    reverse(RevSsminus, Ssminus)
  ;
    % No non-assumption. Get the first member.
    ([H|Rest] = Ss ->
      A = H, Ssminus = Rest
    ;
      % We don't expect this.
      unexpected($file, $pred, "Ss cannot be empty"))).

% rule sorting

sort_rule_pairs(s, _PropInfo, RuleBodies, SortedRuleBodies) :-
  sort(rule_sort_small_bodies, RuleBodies, SortedRuleBodies).
sort_rule_pairs(l1, PropInfo, RuleBodies, SortedRuleBodies) :-
  sort((pred(X::in, Y::in, R::out) is det :- rule_sort_look_ahead_1(PropInfo, X, Y, R)), RuleBodies, SortedRuleBodies).

rule_sort_small_bodies(Body1, Body2, Result) :-
  % Only count non-constraints
  builtin.compare(Result, length(negated_filter(constraint, Body1)) + 0, length(negated_filter(constraint, Body2)) + 0).

% here we minimize (Body - (D \cup JsP))
rule_sort_look_ahead_1(prop_info(D, P_Graph), Body1, Body2, Result) :-
  count_nonD_nonJsP(Body1, D, P_Graph, 0, NB1),
  count_nonD_nonJsP(Body2, D, P_Graph, 0, NB2),
  builtin.compare(Result, NB1, NB2).

count_nonD_nonJsP([], _, _, N, N).
count_nonD_nonJsP([S|Rest], D, P_Graph, N, NB) :-
  % TODO: Use membership
  (\+ member(S, D),
   % \+ member(S-[_|_], P_Graph
   \+ (search_key(P_Graph, S, SKey), is_edge(P_Graph, SKey, _)) ->
    N1 = N + 1,
    count_nonD_nonJsP(Rest, D, P_Graph, N1, NB)
  ;
    count_nonD_nonJsP(Rest, D, P_Graph, N, NB)).

%

% Find the first member in L where Pred(X) and set Lminus to L without it.
% Fail if can't find any Pred(X).
find_first(Pred, L, First, Lminus) :-
  % The accumulator state is MaybeFirst-LWithoutFirst
  yes(First)-Lminus = foldl(
    func(X, MaybeFirst-LPart) = AccOut :-
      ((MaybeFirst = no, Pred(X)) ->
        % We got the first.
        AccOut = yes(X)-LPart
      ;
        % Keep accumulating.
        AccOut = MaybeFirst-append(LPart, [X])),
    L, no-[]).

select(X, [Head|Tail], Rest) :-
  select3_(Tail, Head, X, Rest).

select3_(Tail, Head, Head, Tail).
select3_([Head2|Tail], Head, X, [Head|Rest]) :-
    select3_(Tail, Head2, X, Rest).

% Return a boolean constraint expression for the conditions when S matches any sentence in SSet.
% If no match is possible, return f.
membership(S, SSet) =
  foldl(func(S2, CIn) = COut :-
          (C1 = matches(S, S2) ->
            COut = or(CIn, C1)
          ;
            COut = CIn),
        SSet, f).

excluded(A, D) :-
  (\+ (member(ExistingA, D), (exclusive(ExistingA, A) ; exclusive(A, ExistingA))) ->
    fail ; true).

% Filter constraints from the body by unifying with the constraint store. unify may fail.
filter_constraints(Body, CS, BodyOut, CSOut, Descs) :-
  foldl((pred(S::in, Body1-CS1-Descs1::in, Body2-CS2-Descs2::out) is semidet :-
           (constraint(S) ->
             unify(S, CS1, CS2, Descs3),
             Body2 = Body1,
             Descs2 = append_nodups(Descs1, Descs3)
           ;
             CS2 = CS1,
             Body2 = append(Body1, [S]),
             Descs2 = Descs1)),
        Body, []-CS-[], BodyOut-CSOut-Descs).

% Syntactic sugar.
unify(f(C), CS, CSOut, Descs) :- var_f_unify(C, CS, CSOut, Descs).
unify(i(C), CS, CSOut, Descs) :- var_i_unify(C, CS, CSOut, Descs).
unify(s(C), CS, CSOut, Descs) :- var_s_unify(C, CS, CSOut, Descs).

:- pragma no_inline(next_step_all_branches_int/1).
:- pragma foreign_proc("C",
next_step_all_branches_int(Int::out),
[promise_pure],
"
static long long int integer = 0;
Int = ++integer;
").
