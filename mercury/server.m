:- module server.
:- interface.

:- import_module io.

:- pred server(io::di, io::uo) is det.

:- implementation.

:- import_module abagraph.
:- import_module int.
:- import_module list.
% Import sentence from loading.
:- import_module loading.
:- import_module map.
:- import_module pair.
:- import_module string.

:- pred server_loop(list(pair(int, step_and_id_map))::in, int::in, map(int, string)::in, io::di, io::uo) is det.
:- pred do_step(list(pair(int, step_and_id_map))::in, int::in, map(int, string)::in,
                list(pair(int, step_and_id_map))::out, int::out, map(int, string)::out, io::di, io::uo) is det.

server(!IO) :-
  server_loop([], 1, map.init, !IO).

server_loop(SolutionsIn, MaxSolutionId, AllDecomp, !IO) :-
  io.read_line_as_string(Res, !IO),
  (
    Res = error(_),
    io.write_string("Error reading from stdin\n", !IO)
  ;
    Res = eof,
    io.write_string("EOF\n", !IO)
  ;
    Res = ok(Line0),
    Line = strip(Line0),
    (Line = "init" ->
      % TODO: Get the initial sentence from the command.
      S = fact(mkval0("s", "position", 15.0), 800, 900),
      SolutionsOut-RuntimeOut = initial_solutions(S),
      _-step_and_id_map(_, _, _, Ids) = det_head(SolutionsOut),
      io.write_string(RuntimeOut, !IO),
      MaxSolutionIdOut = 1,
      AllDecompOut = snd(Ids)
    ;
    (Line = "step" ->
      do_step(SolutionsIn, MaxSolutionId, AllDecomp, SolutionsOut, MaxSolutionIdOut, AllDecompOut, !IO)
    ;
      io.write_string("error: unknown command: " ++ Line ++ "\n", !IO),
      SolutionsOut = SolutionsIn,
      MaxSolutionIdOut = MaxSolutionId,
      AllDecompOut = AllDecomp)),

    % Finish the response and loop.
    io.write_string("\n", !IO),
    io.flush_output(!IO),
    server_loop(SolutionsOut, MaxSolutionIdOut, AllDecompOut, !IO)
  ).

do_step(SolutionsIn, MaxSolutionId, AllDecomp, SolutionsOut, MaxSolutionIdOut, AllDecompOut, !IO) :-
  (SolutionsIn = [SolutionId-step_and_id_map(T, NIn, MaxGId, IdsIn)|RestIn] ->
    (T = step_tuple([]-_-_, []-_, _, _-_, _, _) ->
      io.write_string("SolutionsIn head is complete.\n", !IO),
      SolutionsOut = SolutionsIn,
      MaxSolutionIdOut = MaxSolutionId,
      AllDecompOut = AllDecomp
    ;
      StepAndIdMap = step_and_id_map(T, NIn, MaxGId, IdsIn),
      step_and_id_map(step_tuple(P, O, _, _, _, _), _, _, _) = StepAndIdMap,
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
        Solutions = opponent_step(OppArg, opponent_sentence_choice(OppArg), StepAndIdMap)),

      ([(Solution1-RuntimeOut)|Rest] = Solutions ->
        Now = "0s:310ms:0us",  % TODO: fix
        io.write_string(format("%s Solution %i\n", [s(Now), i(SolutionId)]), !IO),
        io.write_string(RuntimeOut, !IO),
        % Replace the head of the solutions and continue processing.
        % If Rest is not [], it means that derivation_step added solutions.
        % Add to the solutions by incrementing the maximum solution ID for each one.
        HeadSolutions-MaxSolutionIdOut-RuntimeOutRest = foldl(
          (func(step_and_id_map(LocalT, LocalN, LocalMaxGId, LocalIds)-LocalRuntimeOut, SolsIn-MaxIdIn-RIn) = SolsOut-NextSolutionId-ROut :-
            NextSolutionId = MaxIdIn + 1,
            ROut = RIn ++
              format("%s Start solution %i from solution %i step %i\n", [s(Now), i(NextSolutionId), i(SolutionId), i(NIn)]) ++
              format("%s Solution %i\n", [s(Now), i(NextSolutionId)]) ++
              LocalRuntimeOut,
            SolsOut = append(SolsIn, [NextSolutionId-step_and_id_map(LocalT, LocalN, LocalMaxGId, LocalIds)])),
          Rest,
          [SolutionId-Solution1]-MaxSolutionId-""),
        io.write_string(RuntimeOutRest, !IO),
        SolutionsOut = append(HeadSolutions, RestIn),
        % Update AllDecomp from the new Ids.
        AllDecompOut = foldl(
          (func(step_and_id_map(_, _, _, LocalIds)-_, AllDecompIn) = AllDecomp1 :-
            % There shouldn't be common keys in AllDecomp and snd(IdsIn), so arbitrarily pick one.
            AllDecomp1 = det_union(func(X, _) = X is semidet, AllDecompIn, snd(LocalIds))),
          Solutions,
          AllDecomp)
      ;
        % derivation_step returned no solutions for the head. Try remaining solutions.
        io.write_string("Try again.\n", !IO),
        SolutionsOut = RestIn,
        MaxSolutionIdOut = MaxSolutionId,
        AllDecompOut = AllDecomp))
    ;
      io.write_string("SolutionsIn is empty. Do init.\n", !IO),
      SolutionsOut = SolutionsIn,
      MaxSolutionIdOut = MaxSolutionId,
      AllDecompOut = AllDecomp).
