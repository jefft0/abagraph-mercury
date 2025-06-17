% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

% mmc --grade hlc.gc --make abagraph && ./abagraph.exe

:- module abagraph.
:- interface.

:- import_module constraints.
:- import_module digraph.
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

:- pred derive(sentence::in, derivation_result::out) is nondet.

:- implementation.

:- import_module bool.
:- import_module float.
:- import_module int.
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

:- type step_and_id_map ---> step_and_id_map(step_tuple, id_map).

:- pred initial_derivation_tuple(set(sentence)::in, step_tuple::out) is det.
:- pred derivation(step_tuple::in, derivation_result::out, id_map::in) is nondet.
:- pred derivation_step(step_tuple::in, id_map::in, step_and_id_map::out) is nondet.
:- pred proponent_step(step_tuple::in, id_map::in, step_and_id_map::out) is nondet.
:- pred opponent_step(step_tuple::in, id_map::in, step_and_id_map::out) is nondet.
:- pred proponent_asm(sentence::in, list(sentence)::in, pair(set(sentence), digraph(sentence))::in,
          opponent_arg_graph_set::in, set(sentence)::in, pair(set(sentence), map(sentence, int))::in,
          set(attack)::in, constraint_store::in, id_map::in, step_and_id_map::out) is semidet.
:- pred proponent_nonasm(sentence::in, list(sentence)::in, pair(set(sentence), digraph(sentence))::in,
          opponent_arg_graph_set::in, set(sentence)::in, pair(set(sentence), map(sentence, int))::in,
          set(attack)::in, constraint_store::in, id_map::in, step_and_id_map::out) is nondet.
:- pred opponent_i(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, id_map::in, step_and_id_map::out) is nondet.
:- pred opponent_ia(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, step_tuple::out) is semidet.
:- pred opponent_ib(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, step_tuple::out) is det.
:- pred opponent_ic(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, id_map::in, step_and_id_map::out) is semidet.
:- pred opponent_ii(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, id_map::in, step_and_id_map::out) is nondet.
:- pred iterate_bodies(list(list(sentence))::in, pair(sentence, int)::in, focussed_pot_arg_graph::in,
          opponent_arg_graph_set::in, pair(set(sentence), map(sentence, int))::in, constraint_store::in,
          constraint_store::out, opponent_arg_graph_set::out, id_map::in, id_map::out) is nondet.
:- pred update_argument_graph(sentence::in, list(sentence)::in, pair(set(sentence), digraph(sentence))::in,
          constraint_store::in, constraint_store::out, list(sentence)::out, list(sentence)::out, pair(set(sentence), digraph(sentence))::out) is nondet.
:- pred filter_marked(list(sentence)::in, set(sentence)::in, constraint_store::in, constraint_store::out, list(sentence)::out, list(sentence)::out) is nondet.
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
:- pred rule_choice(sentence::in, list(sentence)::out, prop_info::in, id_map::in, id_map::out) is nondet.
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
% membership(S, SSet) = C.
% Return a boolean constraint expression for the conditions when S matches any sentence in SSet.
% If no match is possible, return f.
:- func membership(sentence, set(sentence)) = b_constraint is det.
:- pred unify(sentence::in, constraint_store::in, constraint_store::out, set(string)::out) is semidet.
:- pred excluded(sentence::in, set(sentence)::in) is semidet.
:- pred next_step_all_branches_int(int::out) is det.

% ("set some options" moved to options.m.)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: entry predicates

derive(S, Result) :-
  %retractall(proving(_)),
  %assert(proving(S)),
  initial_derivation_tuple(make_singleton_set(S), InitTuple),
  (verbose ->
    IdsIn = 0-map.init,
    open(decompiled_path, "a", Fd),
    write_sentence(S, 0, Fd, Id, IdsIn, Ids1),
    close(Fd),
    format_append(runtime_out_path, 
      "%s Step 0: Case init: S: %i\n  S: %s\n\n",
      [s(now), i(Id), s(sentence_to_string(S))]),
    print_step(0, InitTuple)
  ;
    % Put at least one key in IdsIn.
    Ids1 = 0-set(map.init, -1, map.init)),
  %retractall(sols(_)),
  %assert(sols(1)),
  derivation(InitTuple, Result, 1-snd(Ids1)),
  print_result(S, Result).
  %incr_sols.

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

% derivation(T, Result, InN-IdsIn) :-
% Move the step number into Ids
derivation(T, Result, InN-IdsIn) :-
  next_step_all_branches_int(StepAllBranches),
  format("*** Step %i (all branches)\n", [i(StepAllBranches - 1)]), % Debug
  (T = step_tuple([]-PropMrk-PropG, []-OppM, D, C-_, Att, CS) ->
    format("*** Step %i (all branches), %0.0f%% extra\n", [i(StepAllBranches - 1), f(100.0 * float((StepAllBranches - 1) - (InN - 1)) / float(InN - 1))]),
    Result = derivation_result(PropMrk-PropG, OppM, D, C, Att, CS),
    ((option(show_solution, "true"), \+ verbose) -> PreviousN = InN - 1, format("*** Step %i\n", [i(PreviousN)]) ; true),
    open(runtime_out_path, "a", Fd2),
    format(Fd2, "%s ABA solution found\n", [s(now)]),
    close(Fd2)
  ;
    derivation_step(T, InN-IdsIn, step_and_id_map(T1, _-Ids1)),
    (verbose ->
      print_step(InN, T1),
      open(decompiled_path, "a", Fd),
      format(Fd, "; ^^^ Step %d\n\n", [i(InN)]),
      close(Fd)
    ; true),
    OutN = InN + 1,
    derivation(T1, Result, OutN-Ids1)).

derivation_step(step_tuple(P, O, D, C, Att, CS), IdsIn, step_and_id_map(T1, IdsOut)) :-
  (verbose ->
    puts("\n"),
    format_append(runtime_out_path,
      "%s Step %i start\n  D: %s\n  C: %s\n%s",
      [s(now), i(fst(IdsIn)), s(sentence_set_to_string(D)), s(sentence_set_to_string(fst(C))), s(to_string(CS))])
  ; true),
  choose_turn(P, O, Turn),
  (Turn = proponent ->
    proponent_step(step_tuple(P, O, D, C, Att, CS), IdsIn, step_and_id_map(T1, IdsOut))
  ;
    opponent_step(step_tuple(P, O, D, C, Att, CS), IdsIn, step_and_id_map(T1, IdsOut))).

proponent_step(step_tuple(PropUnMrk-PropMrk-PropGr, O, D, C, Att, CS), IdsIn, StepAndIdMap) :-
  proponent_sentence_choice(PropUnMrk, S, PropUnMrkMinus),
  (assumption(S) ->
    proponent_asm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, Att, CS, IdsIn, StepAndIdMap),
    poss_print_case("1.(i)", S)
  ;
    %TODO: Do we need to compute and explicitly check? non_assumption(S),
    solutions((pred(Solution::out) is nondet :-
                      proponent_nonasm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, Att, CS, IdsIn, Solution)),
              Solutions),
    member(StepAndIdMap, Solutions),
    poss_print_case("1.(ii)", S)
  ).

opponent_step(step_tuple(P, OppUnMrk-OppMrk, D, C, Att, CS), IdsIn, step_and_id_map(T1, IdsOut)) :-
  opponent_abagraph_choice(OppUnMrk, OppArg, OppUnMrkMinus),
  opponent_sentence_choice(OppArg, S, OppArgMinus),
  (assumption(S) ->
    opponent_i(S, OppArgMinus, OppUnMrkMinus-OppMrk, opponent_step_tuple(P, D, C, Att, CS), IdsIn, step_and_id_map(T1, IdsOut))
  ;
    %TODO: Do we need to compute and explicitly check? non_assumption(S),
    opponent_ii(S, OppArgMinus, OppUnMrkMinus-OppMrk, opponent_step_tuple(P, D, C, Att, CS), IdsIn, step_and_id_map(T1, IdsOut)),
    poss_print_case("2.(ii)", S)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CASES

%%%%%%%%%% proponent

proponent_asm(A, PropUnMrkMinus, PropMrk-PropGr, OppUnMrk-OppMrk, D, C, Att, CS, IdsIn,
              step_and_id_map(step_tuple(PropUnMrkMinus-PropMrk1-PropGr, OppUnMrk1-OppMrk, D, C, Att1, CS),
                              IdsOut)) :-
  (verbose ->
    format_append(runtime_out_path, "%s Step %i: Case 1.(i) start A: %s\n", [s(now), i(fst(IdsIn)), s(sentence_to_string(A))])
  ; true),
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
    format_append(runtime_out_path,
      "%s Step %i: Case 1.(i): A: %i, Contrary %i has body? %s, NewGId %i\n  A: %s\n  Contrary: %s\n",
      [s(now), i(fst(IdsIn)), i(Id), i(ContraryId), s(HasBody), i(NewGId),
       s(sentence_to_string(A)), s(sentence_to_string(Contrary))])
  ;
    IdsOut = IdsIn).

proponent_nonasm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, Att, CS, IdsIn,
                 step_and_id_map(step_tuple(PropUnMrk1-PropMrk1-PropGr1, O, D1, C, Att, CSOut), IdsOut)) :-
  (verbose ->
    format_append(runtime_out_path, "%s Step %i: Case 1.(ii) start S: %s\n", [s(now), i(fst(IdsIn)), s(sentence_to_string(S))])
  ; true),
  (constraint(S) ->
    unify(S, CS, CS1, Descs),
    Body = [],
    Ids1 = IdsIn
  ;
    Descs = set.init,
    CS1 = CS,
    rule_choice(S, Body, prop_info(D, PropGr), IdsIn, Ids1)),
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
  update_argument_graph(S, Body, PropMrk-PropGr, CS2, CSOut, BodyUnMrk, BodyUnMrkAs, PropMrk1-PropGr1),
  append_elements_nodup(BodyUnMrk, PropUnMrkMinus, PropUnMrk1),
  % union(list_to_set(BodyUnMrkAs), D, D1),
  foldl((pred(UnMrkA::in, DIn::in, DOut::out) is semidet :-
          % TODO: Use membership?
          DOut = insert(DIn, UnMrkA)),
        BodyUnMrkAs, D, D1),
  % TODO: Support GB. gb_acyclicity_check(G, S, Body, G1),
  (verbose ->
    (constraint(S) ->
      IdsOut = Ids1,
      _ = foldl(func(Desc, _) = 0 :- format_append(runtime_out_path, "%s Step %i: Case 1.(iii): %s\n  S: %s\n", 
                 [s(now), i(fst(IdsIn)), s(Desc), s(sentence_to_string(S))]),
            Descs, 0)
    ;
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
      format_append(runtime_out_path,
        "%s Step %i: Case 1.(ii): S: %i, NewUnMarkedAs: [%s], NewUnMarkedNonAs: [%s], ExistingBody: [%s]\n  S: %s\n  NewUnMarkedAs: %s\n  NewUnMarkedNonAs: %s\n  ExistingBody: %s\n",
        [s(now), i(fst(IdsIn)), i(Id),
         s(join_list(" ", map(int_to_string, NewUnMarkedAsIds))),
         s(join_list(" ", map(int_to_string, NewUnMarkedNonAsIds))),
         s(join_list(" ", map(int_to_string, ExistingBodyIds))), 
         s(sentence_to_string(S)),
         s(sentence_set_to_string(NewUnMarkedAs)),
         s(sentence_set_to_string(NewUnMarkedNonAs)),
         s(sentence_set_to_string(ExistingBody))]))
  ;
    IdsOut = Ids1).

%%%%%%%%%% opponent

opponent_i(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att, CS), IdsIn, step_and_id_map(T1, IdsOut)) :-
  (verbose ->
    format_append(runtime_out_path, "%s Step %i: Case 2 start A: %s\n", [s(now), i(fst(IdsIn)), s(sentence_to_string(A))])
  ; true),
  MemberAD = membership(A, D),
  (verbose ->
    format_append(runtime_out_path, "%s Step %i: MemberAD: %s\n", [s(now), i(fst(IdsIn)), s(b_constraint_to_string(MemberAD))])
  ; true),
  ( b_unify(not(MemberAD), CS, CS1, _),
    MemberAC = membership(A, fst(C)),
    (verbose ->
      format_append(runtime_out_path, "%s Step %i: MemberAC: %s\n", [s(now), i(fst(IdsIn)), s(b_constraint_to_string(MemberAC))])
    ; true),
    ( b_unify(MemberAC, CS1, CS2, _),
      opponent_ib(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att, CS2), T1),
      poss_print_case("2.(ib)", A),
      (verbose ->
        open(decompiled_path, "a", Fd),
        write_sentence(A, GId, Fd, Id, IdsIn, IdsOut),
        close(Fd),
        % Get the ID of the original culprit. (This is why we pass around C as a pair with the Ids.)
        (FoundId = search(snd(C), A) -> CulpritId = FoundId ; CulpritId = 0),
        format_append(runtime_out_path, "%s Step %i: Case 2.(ib): A: %i, GId %i, Culprit %i\n  A: %s\n",
          [s(now), i(fst(IdsIn)), i(Id), i(GId), i(CulpritId), s(sentence_to_string(A))])
      ; 
        IdsOut = IdsIn)
    ;
      b_unify(not(MemberAC), CS1, CS2, _),
      opponent_ic(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att, CS2), IdsIn, step_and_id_map(T1, IdsOut)),
      poss_print_case("2.(ic)", A))
  ;
    b_unify(MemberAD, CS, CS1, _),
    opponent_ia(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att, CS1), T1),
    poss_print_case("2.(ia)", A),
    (verbose ->
      open(decompiled_path, "a", Fd),
      write_sentence(A, GId, Fd, Id, IdsIn, IdsOut),
      close(Fd),
      format_append(runtime_out_path, "%s Step %i: Case 2.(ia): A: %i, GId %i\n  A: %s\n",
        [s(now), i(fst(IdsIn)), i(Id), i(GId), s(sentence_to_string(A))])
    ; 
      IdsOut = IdsIn)).

opponent_ia(A, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk,
            opponent_step_tuple(P, D, C, Att, CS), step_tuple(P, OppUnMrkMinus1-OppMrk, D, C, Att, CSOut)) :-
  (verbose ->
    format_append(runtime_out_path, "%s Step ?: Case 2.(ia) start\n", [s(now)])
  ; true),
  (gb_derivation ->
    CSOut = CS
  ;
    MemberAC = membership(A, fst(C)),  % also sound for gb? CHECK in general
    b_unify(not(MemberAC), CS, CSOut, _),
    (verbose ->
      (MemberAC = f -> true ; format_append(runtime_out_path, "%s Step ?: not(MemberAC): %s\n", [s(now), s(b_constraint_to_string(not(MemberAC)))]))
    ; true)),
  insert(A, Marked, Marked1),
  append_element_nodup(OppUnMrkMinus, Claim-GId-(UnMrkMinus-Marked1-Graph), OppUnMrkMinus1).

opponent_ib(A, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk,
            opponent_step_tuple(P, D, C, Att, CS), step_tuple(P, OppUnMrkMinus-OppMrk1, D, C, Att, CS)) :-
  (verbose ->
    format_append(runtime_out_path, "%s Step ?: Case 2.(ib) start\n", [s(now)])
  ; true),
 % TODO: Support GB. contrary(A, Contrary),
 % TODO: Support GB. gb_acyclicity_check(G, Claim, [Contrary], G1),
 insert(A, Marked, Marked1),
 insert(Claim-GId-(UnMrkMinus-Marked1-Graph), OppMrk, OppMrk1).

opponent_ic(A, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk,
            opponent_step_tuple(PropUnMrk-PropMrk-PropGr, D, C, Att, CS), IdsIn, 
            step_and_id_map(step_tuple(PropUnMrk1-PropMrk-PropGr1, OppUnMrkMinus-OppMrk1, D1, C1, Att1, CS),
                            IdsOut)) :-
  (verbose ->
    format_append(runtime_out_path, "%s Step %i: Case 2.(ic) start\n", [s(now), i(fst(IdsIn))])
  ; true),
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
    format_append(runtime_out_path,
      "%s Step %i: Case 2.(ic): A: %i, GId %i, Contrary %i new? %s\n  A: %s\n  Contrary: %s\n",
      [s(now), i(fst(IdsIn)), i(Id), i(GId), i(ContraryId), s(IsNewContrary),
       s(sentence_to_string(A)), s(sentence_to_string(Contrary))])
  ; 
    Id = 0,
    IdsOut = IdsIn),
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
            StepAndIdMap) :-
  (verbose ->
    format_append(runtime_out_path, "%s Step %i: Case 2.(ii) start S: %s\n", [s(now), i(fst(IdsIn)), s(sentence_to_string(S))])
  ; true),
  (constraint(S) ->
    (unify(S, CS, CSOutLocal, Descs) ->
      CS1 = CSOutLocal,
      Bodies = [[]],
      (verbose ->
        _ = foldl(func(Desc, _) = 0 :- format_append(runtime_out_path, "%s Step %i: Case 2.(iii): %s\n  S: %s\n", 
                   [s(now), i(fst(IdsIn)), s(Desc), s(sentence_to_string(S))]),
              Descs, 0)
      ;
        true)
    ;
      CS1 = CS,
      Bodies = [])
  ;
    CS1 = CS,
    solutions((pred(Body::out) is nondet :- rule(S, Body), \+ (member(A, Body), excluded(A, D))), Bodies)),

  solutions((pred(step_and_id_map(step_tuple(LocalP, OppUnMrkMinus1-OppMrk1, LocalD, LocalC, LocalAtt, CSOut), IdsOut)::out) is nondet :-
                    LocalP = P, LocalD = D, LocalC = C, LocalAtt = Att,
                    iterate_bodies(Bodies, S-GId, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk, C, CS1, CSOut,
                       OppUnMrkMinus1-OppMrk1, IdsIn, IdsOut)),
            Solutions),
  member(StepAndIdMap, Solutions).

% SGId is the graph ID that S came from.
iterate_bodies([], _, _, OppUnMrkMinus-OppMrk, _, CS, CS, OppUnMrkMinus-OppMrk, Ids, Ids).
iterate_bodies([Body|RestBodies], S-SGId, Claim-GId-(UnMrkMinus-Marked-Graph), InOppUnMrkMinus-InOppMrk, C, CS, CSOut,
               OppUnMrkMinus1-OppMrk1, IdsIn, IdsOut) :-
  (verbose ->
    format_append(runtime_out_path, "%s Step %i: Case 2.(ii) Rest: %i Body: %s\n", 
                  [s(now), i(fst(IdsIn)), i(length(RestBodies)), s(sentence_list_to_string(Body))])
  ; true),
  update_argument_graph(S, Body, Marked-Graph, CS, CS1, UnMarked, UnMarkedAs, Marked1-Graph1),
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
      format_append(runtime_out_path, "%s Step %i: Case 2.(ii): S: %i, GId %i, mark graph? %s\n  S: %s\n",
        [s(now), i(fst(IdsIn)), i(Id), i(SGId), s(MarkGraph), s(sentence_to_string(S))])
    ; true),
    format_append(runtime_out_path,
      "%s Step %i: Case 2.(ii): S: %i, NewGId %i, NewUnMarkedAs: [%s], NewUnMarkedNonAs: [%s], ExistingBody: [%s]\n  S: %s\n  NewUnMarkedAs: %s\n  NewUnMarkedNonAs: %s\n  ExistingBody: %s\n",
      [s(now), i(fst(IdsIn)), i(Id), i(NewGId),
       s(join_list(" ", map(int_to_string, NewUnMarkedAsIds))),
       s(join_list(" ", map(int_to_string, NewUnMarkedNonAsIds))),
       s(join_list(" ", map(int_to_string, ExistingBodyIds))), 
       s(sentence_to_string(S)),
       s(sentence_set_to_string(NewUnMarkedAs)),
       s(sentence_set_to_string(NewUnMarkedNonAs)),
       s(sentence_set_to_string(ExistingBody))])
  ;
    Ids5 = Ids1),

  % For further iterations, set GId to 0 so that we mint new IDs for added graphs.
  iterate_bodies(RestBodies, S-SGId, Claim-0-(UnMrkMinus-Marked-Graph), OutOppUnMrkMinus-OutOppMrk, C, CS1, CSOut,
                 OppUnMrkMinus1-OppMrk1, Ids5, IdsOut).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SUBSIDIARY FUNCTIONS

% update_argument_graph(S, Body, Marked-Graph, CS, CSOut, Unproved, UnprovedAs, Marked1-Graph1)
% - update graph representation of an argument with rule(S, Body)
% - check updated version for acyclicity
% - record the previously unproved sentences and assumptions from body
update_argument_graph(S, Body, Marked-Graph, CS, CSOut, UnMarked, UnMarkedAs, Marked1-Graph1) :-
  filter_marked(Body, Marked, CS, CSOut, UnMarked, UnMarkedAs),
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

% filter_marked(Body, AlreadyProved, CS, CSOut, Unproved, UnprovedAs)
filter_marked([], _, CS, CS, [], []).
filter_marked([S|RestBody], Proved, CS, CSOut, InUnproved, InUnprovedAs) :-
  (assumption(S) ->
    A = S,
    MemberAProved = membership(A, Proved),
    ( b_unify(MemberAProved, CS, CS1, _),
      InUnproved = OutUnproved,
      InUnprovedAs = OutUnprovedAs,
      filter_marked(RestBody, Proved, CS1, CSOut, OutUnproved, OutUnprovedAs)
    ;
      b_unify(not(MemberAProved), CS, CS1, _),
      InUnproved = [A|OutUnproved], 
      InUnprovedAs = [A|OutUnprovedAs],
      filter_marked(RestBody, Proved, CS1, CSOut, OutUnproved, OutUnprovedAs))
  ;
    MemberSProved = membership(S, Proved),
    ( b_unify(MemberSProved, CS, CS1, _),
      InUnproved = OutUnproved,
      InUnprovedAs = OutUnprovedAs,
      filter_marked(RestBody, Proved, CS1, CSOut, OutUnproved, OutUnprovedAs)
    ;
      b_unify(not(MemberSProved), CS, CS1, _),
      InUnproved = [S|OutUnproved],
      InUnprovedAs = OutUnprovedAs,
      filter_marked(RestBody, Proved, CS1, CSOut, OutUnproved, OutUnprovedAs))).

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
  % Process a constraint if available.
  (find_first_constraint(P, S1, Pminus1) ->
    S = S1, Pminus = Pminus1
  ;
    % % No constraint. Use the sentence choice.
    % get_proponent_sentence_choice(PropSentenceStrategy),
    % sentence_choice(PropSentenceStrategy, P, S, Pminus)).
    % No constraint. Check for the head of a rule where some body has a constraint.
    (find_first((pred(H::in) is semidet :- rule(H, Body), find_first_constraint(Body, _, _)), P, S1, Pminus1) ->
      S = S1, Pminus = Pminus1
    ;
      % No constraint. Use the sentence choice.
      get_proponent_sentence_choice(PropSentenceStrategy),
      sentence_choice(PropSentenceStrategy, P, S, Pminus))).

opponent_abagraph_choice(O, JC, Ominus) :-
  get_opponent_abagraph_choice(OppJCStrategy),
  opponent_abagraph_choice(OppJCStrategy, O, JC, Ominus).

opponent_sentence_choice(Claim-(Ss-Marked-OGraph), Se, Claim-(Ssminus-Marked-OGraph)) :-
  % Process a constraint if available.
  (find_first_constraint(Ss, Se1, Ssminus1) ->
    Se = Se1, Ssminus = Ssminus1
  ;
    % No constraint. Use the sentence choice.
    get_opponent_sentence_choice(OppSentenceStrategy),
    sentence_choice_backtrack(OppSentenceStrategy, Ss, Se, Ssminus)).

find_first_constraint(SList, SOut, SListMinus) :-
  find_first((pred(S::in) is semidet :- constraint(S)), SList, SOut, SListMinus).

% PropInfo here holds information about the current state of
% proponent's derivations.
% Omit "proponent" since it is not used.
%rule_choice(Head, Body, proponent, PropInfo) :-
rule_choice(Head, Body, prop_info(D, PropGr), IdsIn, IdsOut) :-
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
    format_append(runtime_out_path, "%s Step %i: Head %s Potential bodies: [%s]\n", 
      [s(now), i(fst(IdsIn)), s(sentence_to_string(Head)), s(BodiesText)]),
    close(Fd)
  ;
    IdsOut = IdsIn),
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
  builtin.compare(Result, length(Body1) + 0, length(Body2) + 0).

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
