% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

:- module abagraph.
:- interface.

:- import_module digraph.
:- import_module list.
% Import sentence from loading.
:- import_module loading.
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
                   set(sentence),          % C (the opponent culprits)
                   set(attack)).           % Att (set of attacks, used only for printing)

:- type opponent_step_tuple
   ---> opponent_step_tuple(pot_arg_graph,          % PROPONENT potential argument graph
                            set(sentence),          % D (the proponent defences)
                            set(sentence),          % C (the opponent culprits)
                            set(attack)).           % Att

:- type derivation_result
   ---> derivation_result(pair(set(sentence), digraph(sentence)), % PropMrk-PropG
                          set(focussed_pot_arg_graph),            % OppMrk
                          set(sentence),                          % D (the proponent defences)
                          set(sentence),                          % C (the opponent culprits)
                          set(attack)).                           % Att

:- pred derive(sentence::in, derivation_result::out) is nondet.

:- implementation.

:- import_module int.
:- import_module map.
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
:- pred derivation(step_tuple::in, int::in, derivation_result::out, int::out, id_map::in, id_map::out) is nondet.
:- pred derivation_step(step_tuple::in, step_tuple::out, id_map::in, id_map::out) is nondet.
:- pred proponent_step(step_tuple::in, step_tuple::out, id_map::in, id_map::out) is nondet.
:- pred opponent_step(step_tuple::in, step_tuple::out, id_map::in, id_map::out) is nondet.
:- pred proponent_asm(sentence::in, list(sentence)::in, pair(set(sentence), digraph(sentence))::in,
          opponent_arg_graph_set::in, set(sentence)::in, set(sentence)::in, set(attack)::in,
          step_tuple::out, id_map::in, id_map::out) is semidet.
:- pred proponent_nonasm(sentence::in, list(sentence)::in, pair(set(sentence), digraph(sentence))::in,
          opponent_arg_graph_set::in, set(sentence)::in, set(sentence)::in, set(attack)::in,
          step_tuple::out, id_map::in, id_map::out) is nondet.
:- pred opponent_i(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, step_tuple::out, id_map::in, id_map::out) is nondet.
:- pred opponent_ia(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, step_tuple::out) is semidet.
:- pred opponent_ib(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, step_tuple::out) is det.
:- pred opponent_ic(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, step_tuple::out, id_map::in, id_map::out) is semidet.
:- pred opponent_ii(sentence::in, focussed_pot_arg_graph::in, opponent_arg_graph_set::in,
          opponent_step_tuple::in, step_tuple::out, id_map::in, id_map::out) is det.
:- pred iterate_bodies(list(list(sentence))::in, sentence::in, focussed_pot_arg_graph::in,
          pair(list(focussed_pot_arg_graph), set(focussed_pot_arg_graph))::in, set(sentence)::in,
          pair(list(focussed_pot_arg_graph), set(focussed_pot_arg_graph))::out, id_map::in,
          id_map::out) is det.
:- pred update_argument_graph(sentence::in, list(sentence)::in, pair(set(sentence), digraph(sentence))::in,
          list(sentence)::out, list(sentence)::out, pair(set(sentence), digraph(sentence))::out) is semidet.
:- pred filter_marked(list(sentence)::in, set(sentence)::in, list(sentence)::out, list(sentence)::out) is det.
:- pred acyclic(digraph(sentence)::in) is semidet.
:- pred graph_union(digraph(sentence)::in, digraph(sentence)::in, digraph(sentence)::out) is det.
:- pred append_element_nodup(list(T)::in, T::in, list(T)::out) is det.
:- pred append_elements_nodup(list(T)::in, list(T)::in, list(T)::out) is det.
:- pred choose_turn(pot_arg_graph::in, opponent_arg_graph_set::in, turn::out) is det.
:- pred proponent_sentence_choice(list(sentence)::in, sentence::out, list(sentence)::out) is det.
:- pred opponent_abagraph_choice(list(focussed_pot_arg_graph)::in, focussed_pot_arg_graph::out,
          list(focussed_pot_arg_graph)::out) is det.
:- pred opponent_sentence_choice(focussed_pot_arg_graph::in, sentence::out, focussed_pot_arg_graph::out) is nondet.
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

% ("set some options" moved to options.m.)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CONTROL: entry predicates

derive(S, Result) :-
  %retractall(proving(_)),
  %assert(proving(S)),
  initial_derivation_tuple(make_singleton_set(S), InitTuple),
  IdsIn = map.init,
  (verbose ->
    open(decompiled_path, "a", Fd),
    write_sentence(S, 0, Fd, Id, IdsIn, Ids1),
    close(Fd),
    format_append(runtime_out_path, 
      "%s Case init: S: %i\n  debug_S: %s\n*** Step 0\n\n",
      [s(now), i(Id), s(sentence_to_string(S))]),
    print_step(0, InitTuple)
  ;
    Ids1 = IdsIn),
  %retractall(sols(_)),
  %assert(sols(1)),
  derivation(InitTuple, 1, Result, _, Ids1, _),
  print_result(S, Result).
  %incr_sols.

initial_derivation_tuple(
    PropUnMrk,
    step_tuple(O_PropUnMrk-set.init-PropGr, % PropUnMrk-PropM-PropGr
               []-set.init,                 % OppUnMrk-OppM (members of each are Claim-GId-UnMrk-Mrk-Graph)
               % TODO: Support GB.
               D0,                          % D
               set.init,                    % C
               set.init)) :-                % Att
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

derivation(T, InN, Result, N, IdsIn, IdsOut) :-
  (T = step_tuple([]-PropMrk-PropG, []-OppM, D, C, Att) ->
    Result = derivation_result(PropMrk-PropG, OppM, D, C, Att),
    ((option(show_solution, "true"), \+ verbose) -> PreviousN = N - 1, format("*** Step %i\n", [i(PreviousN)]) ; true),
    N = InN,
    IdsOut = IdsIn
  ;
    derivation_step(T, T1, IdsIn, Ids1),
    (verbose ->
      print_step(InN, T1),
      format_append(runtime_out_path, "*** Step %d\n\n", [i(InN)])
    ;
      true),
    OutN = InN + 1,
    derivation(T1, OutN, Result, N, Ids1, IdsOut)).

derivation_step(step_tuple(P, O, D, C, Att), T1, IdsIn, IdsOut) :-
  (verbose -> puts("\n") ; true),
  choose_turn(P, O, Turn),
  (Turn = proponent ->
    proponent_step(step_tuple(P, O, D, C, Att), T1, IdsIn, IdsOut)
  ;
    opponent_step(step_tuple(P, O, D, C, Att), T1, IdsIn, IdsOut)).

proponent_step(step_tuple(PropUnMrk-PropMrk-PropGr, O, D, C, Att), T1, IdsIn, IdsOut) :-
  proponent_sentence_choice(PropUnMrk, S, PropUnMrkMinus),
  (assumption(S) ->
    proponent_asm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, Att, T1, IdsIn, IdsOut),
    poss_print_case("1.(i)", S)
  ;
    %TODO: Do we need to compute and explicitly check? non_assumption(S),
    proponent_nonasm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, Att, T1, IdsIn, IdsOut),
    poss_print_case("1.(ii)", S)
  ).

opponent_step(step_tuple(P, OppUnMrk-OppMrk, D, C, Att), T1, IdsIn, IdsOut) :-
  opponent_abagraph_choice(OppUnMrk, OppArg, OppUnMrkMinus),
  opponent_sentence_choice(OppArg, S, OppArgMinus),
  (assumption(S) ->
    opponent_i(S, OppArgMinus, OppUnMrkMinus-OppMrk, opponent_step_tuple(P, D, C, Att), T1, IdsIn, IdsOut)
  ;
    %TODO: Do we need to compute and explicitly check? non_assumption(S),
    opponent_ii(S, OppArgMinus, OppUnMrkMinus-OppMrk, opponent_step_tuple(P, D, C, Att), T1, IdsIn, IdsOut),
    poss_print_case("2.(ii)", S)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% DERIVATION CASES

%%%%%%%%%% proponent

proponent_asm(A, PropUnMrkMinus, PropMrk-PropGr, OppUnMrk-OppMrk, D, C, Att,
              step_tuple(PropUnMrkMinus-PropMrk1-PropGr, OppUnMrk1-OppMrk, D, C, Att1),
              IdsIn, IdsOut) :-
  contrary(A, Contrary),
  ((\+ (member(Member1, OppUnMrk), Member1 = Contrary-_-(_-_-_)),
    \+ (member(Member2, OppMrk),   Member2 = Contrary-_-(_-_-_))) ->
    add_vertex(Contrary, _, digraph.init, GContrary),
    NewGId = length(OppUnMrk) + count(OppMrk) + 1,
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
    format_append(runtime_out_path,
      "%s Case 1.(i): A: %i, Contrary %i, NewGId %i\n  debug_A: %s\n  debug_Contrary: %s\n",
      [s(now), i(Id), i(ContraryId), i(NewGId),
       s(sentence_to_string(A)), s(sentence_to_string(Contrary))])
  ;
    IdsOut = IdsIn).

proponent_nonasm(S, PropUnMrkMinus, PropMrk-PropGr, O, D, C, Att,
                 step_tuple(PropUnMrk1-PropMrk1-PropGr1, O, D1, C, Att), IdsIn, IdsOut) :-
  rule_choice(S, Body, prop_info(D, PropGr), IdsIn, Ids1),
  \+ (member(X, Body), member(X, C)),
  update_argument_graph(S, Body, PropMrk-PropGr, NewUnMrk, NewUnMrkAs, PropMrk1-PropGr1),
  append_elements_nodup(NewUnMrk, PropUnMrkMinus, PropUnMrk1),
  union(list_to_set(NewUnMrkAs), D, D1),
  % TODO: Support GB. gb_acyclicity_check(G, S, Body, G1),
  (verbose ->
    NewUnMrkNonAs = difference(list_to_set(NewUnMrk), list_to_set(NewUnMrkAs)),
    MrkBody = intersect(list_to_set(Body), PropMrk),
    open(decompiled_path, "a", Fd),
    write_sentence(S, 0, Fd, Id, Ids1, Ids2),
    write_sentence_list(NewUnMrkAs, 0, Fd, NewUnMrkAsIds, Ids2, Ids3),
    write_sentence_set(NewUnMrkNonAs, 0, Fd, NewUnMrkNonAsIds, Ids3, Ids4),
    write_sentence_set(MrkBody, 0, Fd, MrkBodyIds, Ids4, IdsOut),
    close(Fd),
    format_append(runtime_out_path,
      "%s Case 1.(ii): S: %i, NewUnMrkAs: [%s], NewUnMrkNonAs: [%s], MrkBody: [%s]\n  debug_S: %s\n  debug_NewUnMrkAs: %s\n  debug_NewUnMrkNonAs: %s\n  debug_MrkBody: %s\n",
      [s(now), i(Id),
       s(join_list(" ", map(int_to_string, NewUnMrkAsIds))),
       s(join_list(" ", map(int_to_string, NewUnMrkNonAsIds))),
       s(join_list(" ", map(int_to_string, MrkBodyIds))), 
       s(sentence_to_string(S)),
       s(sentence_list_to_string(NewUnMrkAs)),
       s(sentence_set_to_string(NewUnMrkNonAs)),
       s(sentence_set_to_string(MrkBody))])
  ;
    IdsOut = Ids1).

%%%%%%%%%% opponent

opponent_i(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att), T1, IdsIn, IdsOut) :-
  (
    \+ member(A, D),
    (member(A, C) ->
      opponent_ib(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att), T1),
      poss_print_case("2.(ib)", A),
      (verbose ->
        open(decompiled_path, "a", Fd),
        write_sentence(A, GId, Fd, Id, IdsIn, IdsOut),
        close(Fd),
        format_append(runtime_out_path, "%s Case 2.(ib): A: %i, GId %i\n  debug_A: %s\n",
          [s(now), i(Id), i(GId), s(sentence_to_string(A))])
      ; 
        IdsOut = IdsIn)
    ;
      opponent_ic(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att), T1, IdsIn, IdsOut),
      poss_print_case("2.(ic)", A))
  ;
    opponent_ia(A, Claim-GId-(UnMrkMinus-Marked-Graph), OMinus, opponent_step_tuple(P, D, C, Att), T1),
    poss_print_case("2.(ia)", A),
    (verbose ->
      open(decompiled_path, "a", Fd),
      write_sentence(A, GId, Fd, Id, IdsIn, IdsOut),
      close(Fd),
      format_append(runtime_out_path, "%s Case 2.(ia): A: %i, GId %i\n  debug_A: %s\n",
        [s(now), i(Id), i(GId), s(sentence_to_string(A))])
    ; 
      IdsOut = IdsIn)).

opponent_ia(A, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk,
            opponent_step_tuple(P, D, C, Att), step_tuple(P, OppUnMrkMinus1-OppMrk, D, C, Att)) :-
  (gb_derivation ->
    true
  ;
    \+ member(A, C)),    % also sound for gb? CHECK in general
  insert(A, Marked, Marked1),
  append_element_nodup(OppUnMrkMinus, Claim-GId-(UnMrkMinus-Marked1-Graph), OppUnMrkMinus1).

opponent_ib(A, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk,
            opponent_step_tuple(P, D, C, Att), step_tuple(P, OppUnMrkMinus-OppMrk1, D, C, Att)) :-
 % TODO: Support GB. contrary(A, Contrary),
 % TODO: Support GB. gb_acyclicity_check(G, Claim, [Contrary], G1),
 insert(A, Marked, Marked1),
 insert(Claim-GId-(UnMrkMinus-Marked1-Graph), OppMrk, OppMrk1).

opponent_ic(A, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk,
            opponent_step_tuple(PropUnMrk-PropMrk-PropGr, D, C, Att),
            step_tuple(PropUnMrk1-PropMrk-PropGr1, OppUnMrkMinus-OppMrk1, D1, C1, Att1),
            IdsIn, IdsOut) :-
  contrary(A, Contrary),
  (search_key(PropGr, Contrary, _) ->
    PropUnMrk = PropUnMrk1,
    PropGr = PropGr1,
    (verbose ->
      open(decompiled_path, "a", Fd),
      write_sentence(A, GId, Fd, Id, IdsIn, IdsOut),
      close(Fd),
      format_append(runtime_out_path, "%s Case 2.(ic): A: %i, GId %i\n  debug_A: %s\n",
        [s(now), i(Id), i(GId), s(sentence_to_string(A))])
    ; 
      IdsOut = IdsIn)
  ;
    append_element_nodup(PropUnMrk, Contrary, PropUnMrk1),
    add_vertex(Contrary, _, PropGr, PropGr1),
    (verbose ->
      open(decompiled_path, "a", Fd),
      write_sentence(A, GId, Fd, Id, IdsIn, Ids1),
      write_sentence(Contrary, 0, Fd, ContraryId, Ids1, IdsOut),
      close(Fd),
      format_append(runtime_out_path,
        "%s Case 2.(ic): A: %i, GId %i, Contrary %i\n  debug_A: %s\n  debug_Contrary: %s\n",
        [s(now), i(Id), i(GId), i(ContraryId), s(sentence_to_string(A)),
         s(sentence_to_string(Contrary))])
    ; 
      IdsOut = IdsIn)),
  (assumption(Contrary) ->
    insert(Contrary, D, D1)
  ;
    D1 = D),
  insert(A, C, C1),
  insert(A, Marked, Marked1),
  insert(Claim-GId-(UnMrkMinus-Marked1-Graph), OppMrk, OppMrk1),
  insert(Contrary-A, Att, Att1).
  % TODO: Support GB. gb_acyclicity_check(G, Claim, [Contrary], G1).

opponent_ii(S, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk, opponent_step_tuple(P, D, C, Att),
            step_tuple(P, OppUnMrkMinus1-OppMrk1, D, C, Att), IdsIn, IdsOut) :-
  solutions((pred(Body::out) is nondet :- rule(S, Body)), Bodies),
  (Bodies = [] ->
    % JT: This case is not handled by iterate_bodies.
    OppUnMrkMinus1 = OppUnMrkMinus,
    OppMrk1 = insert(OppMrk, Claim-GId-(UnMrkMinus-Marked-Graph)),
    IdsOut = IdsIn
  ;
    (verbose ->
      open(decompiled_path, "a", Fd),
      write_sentence(S, GId, Fd, Id, IdsIn, Ids1),
      close(Fd),
      format_append(runtime_out_path, "%s Case 2.(ii): S: %i\n  debug_S: %s\n",
        [s(now), i(Id), s(sentence_to_string(S))])
    ; 
      Ids1 = IdsIn),
    iterate_bodies(Bodies, S, Claim-GId-(UnMrkMinus-Marked-Graph), OppUnMrkMinus-OppMrk, C,
                   OppUnMrkMinus1-OppMrk1, Ids1, IdsOut)).

iterate_bodies([], _, _, OppUnMrkMinus-OppMrk, _, OppUnMrkMinus-OppMrk, Ids, Ids).
iterate_bodies([Body|RestBodies], S, Claim-GId-(UnMrkMinus-Marked-Graph), InOppUnMrkMinus-InOppMrk, C,
               OppUnMrkMinus1-OppMrk1, IdsIn, IdsOut) :-
  (update_argument_graph(S, Body, Marked-Graph, UnMarked, UnMarkedAs, Marked1-Graph1) ->
    append_elements_nodup(UnMarked, UnMrkMinus, UnMrk1),
    (GId = 0 ->
      % We are on iteration >= 2 and need a new GId.
      NewGId = length(InOppUnMrkMinus) + count(InOppMrk) + 1
    ;
      % The first iteration re-use the GId from the graph extracted by opponent_abagraph_choice.
      NewGId = GId),
    ((\+ gb_derivation, member(A, Body), member(A, C)) ->
      OutOppUnMrkMinus = InOppUnMrkMinus,
      insert(Claim-NewGId-(UnMrk1-Marked1-Graph1), InOppMrk, OutOppMrk)
    ;
      append_element_nodup(InOppUnMrkMinus, Claim-NewGId-(UnMrk1-Marked1-Graph1), OutOppUnMrkMinus),
      OutOppMrk = InOppMrk),
    % TODO: Support GB. OutG = InG,
    (verbose ->
      UnMarkedNonAs = difference(list_to_set(UnMarked), list_to_set(UnMarkedAs)),
      MarkedBody = intersect(list_to_set(Body), Marked),
      open(decompiled_path, "a", Fd),
      write_sentence(S, NewGId, Fd, Id, IdsIn, Ids1),
      write_sentence_list(UnMarkedAs, NewGId, Fd, UnMarkedAsIds, Ids1, Ids2),
      write_sentence_set(UnMarkedNonAs, NewGId, Fd, UnMarkedNonAsIds, Ids2, Ids3),
      write_sentence_set(MarkedBody, NewGId, Fd, MarkedBodyIds, Ids3, Ids4),
      close(Fd),
      format_append(runtime_out_path,
        "%s Case 2.(ii): S: %i, GId %i, UnMarkedAs: [%s], UnMarkedNonAs: [%s], MarkedBody: [%s]\n  debug_S: %s\n  debug_UnMarkedAs: %s\n  debug_UnMarkedNonAs: %s\n  debug_MarkedBody: %s\n",
        [s(now), i(Id), i(NewGId),
         s(join_list(" ", map(int_to_string, UnMarkedAsIds))),
         s(join_list(" ", map(int_to_string, UnMarkedNonAsIds))),
         s(join_list(" ", map(int_to_string, MarkedBodyIds))), 
         s(sentence_to_string(S)),
         s(sentence_list_to_string(UnMarkedAs)),
         s(sentence_set_to_string(UnMarkedNonAs)),
         s(sentence_set_to_string(MarkedBody))])
    ;
      Ids4 = IdsIn),

    % For further iterations, set GId to 0 so that we mint new IDs for added graphs.
    iterate_bodies(RestBodies, S, Claim-0-(UnMrkMinus-Marked-Graph), OutOppUnMrkMinus-OutOppMrk, C,
                   OppUnMrkMinus1-OppMrk1, Ids4, IdsOut)
  ;
    iterate_bodies(RestBodies, S, Claim-GId-(UnMrkMinus-Marked-Graph), InOppUnMrkMinus-InOppMrk, C,
                   OppUnMrkMinus1-OppMrk1, IdsIn, IdsOut)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% SUBSIDIARY FUNCTIONS

% update_argument_graph(S, Body, Marked-Graph, Unproved, UnprovedAs, Marked1-Graph1)
% - update graph representation of an argument with rule(S, Body)
% - check updated version for acyclicity
% - record the previously unproved sentences and assumptions from body
update_argument_graph(S, Body, Marked-Graph, UnMarked, UnMarkedAs, Marked1-Graph1) :-
  filter_marked(Body, Marked, UnMarked, UnMarkedAs),
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
  graph_union(GraphMinus1, BodyUnMarkedGraph, Graph1),
  acyclic(Graph1).

% filter_marked(Body, AlreadyProved, Unproved, UnprovedAs)
filter_marked([], _, [], []).
filter_marked([S|RestBody], Proved, InUnproved, InUnprovedAs) :-
  (assumption(S) ->
    A = S,
    (member(A, Proved) ->
      InUnproved = OutUnproved,
      InUnprovedAs = OutUnprovedAs
    ;
      InUnproved = [A|OutUnproved],
      InUnprovedAs = [A|OutUnprovedAs]),
    filter_marked(RestBody, Proved, OutUnproved, OutUnprovedAs)
  ;
    (member(S, Proved) ->
      InUnproved = OutUnproved
    ;
      InUnproved = [S|OutUnproved]),
    InUnprovedAs = OutUnprovedAs,
    filter_marked(RestBody, Proved, OutUnproved, OutUnprovedAs)).

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
    get_turn_choice(TurnStrategy),
    turn_choice(TurnStrategy, P, O, Player))).

proponent_sentence_choice(P, S, Pminus) :-
  get_proponent_sentence_choice(PropSentenceStrategy),
  sentence_choice(PropSentenceStrategy, P, S, Pminus).

opponent_abagraph_choice(O, JC, Ominus) :-
  get_opponent_abagraph_choice(OppJCStrategy),
  opponent_abagraph_choice(OppJCStrategy, O, JC, Ominus).

opponent_sentence_choice(Claim-(Ss-Marked-OGraph), Se, Claim-(Ssminus-Marked-OGraph)) :-
  get_opponent_sentence_choice(OppSentenceStrategy),
  sentence_choice_backtrack(OppSentenceStrategy, Ss, Se, Ssminus).

% PropInfo here holds information about the current state of
% proponent's derivations.
% Omit "proponent" since it is not used.
%rule_choice(Head, Body, proponent, PropInfo) :-
rule_choice(Head, Body, PropInfo, IdsIn, IdsOut) :-
  solutions(pred(B::out) is nondet :- rule(Head, B), RuleBodies),
  get_proponent_rule_choice(PropRuleStrategy),
  sort_rule_pairs(PropRuleStrategy, PropInfo, RuleBodies, SortedRuleBodies),
  % Note: The cut is not needed since the above predicates are det.
  % !,
  (verbose ->
    open(decompiled_path, "a", Fd),
    IdsOut-BodiesText = foldl((
      func(B, IdsIn1-TextIn) = IdsOut1-(TextIn ++ Text) :-
        write_sentence_list(B, 0, Fd, IdsList, IdsIn1, IdsOut1),
        Text = format(" [%s]", [s(join_list(" ", map(int_to_string, IdsList)))])),
      SortedRuleBodies, IdsIn-""),
    format_append(runtime_out_path, "%s Potential bodies: [%s]\n", [s(now), s(BodiesText)]),
    close(Fd)
  ;
    IdsOut = IdsIn),
  member(Body, SortedRuleBodies),
  rule(Head, Body).              % added to fix Fan's first bug

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
  (\+ member(S, D),
   % \+ member(S-[_|_], P_Graph
   \+ (search_key(P_Graph, S, SKey), is_edge(P_Graph, SKey, _)) ->
    N1 = N + 1,
    count_nonD_nonJsP(Rest, D, P_Graph, N1, NB)
  ;
    count_nonD_nonJsP(Rest, D, P_Graph, N, NB)).

%

% First the first member in L where Pred(X) and set Lminus to L without it.
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
