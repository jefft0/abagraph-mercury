% Ported to Mercury from abagraph in Prolog by Robert Craven:
% http://robertcraven.org/proarg/abagraph.html

:- module printing.
:- interface.

:- import_module abagraph.
:- import_module digraph.
:- import_module list.
:- import_module loading.
:- import_module map.
:- import_module set.
:- import_module string.

:- pred poss_print_case(string::in, sentence::in) is det.
:- pred print_step(int::in, step_tuple::in) is det.
:- pred print_result(sentence::in, derivation_result::in) is det.

:- func sentence_list_to_string(list(sentence)) = string is det.
:- func sentence_set_to_string(set(sentence)) = string is det.
:- func digraph_to_list(digraph(sentence)) = list(graph_member) is det.
:- func digraph_to_string(digraph(sentence)) = string is det.
:- func focussed_pot_arg_graph_to_string(focussed_pot_arg_graph) = string is det.
% puts(S). Write the string S to stdout without a newline.
:- pred puts(string::in) is det.
% format(S, PolyTypes). Write string.format(S, PolyTypes) to stdout.
:- pred format(string::in, list(poly_type)::in) is det.
% open(Path, Mode, Fd). If Path is empty, set Fd to 0 which is ignored by fputs, etc.
:- pred open(string::in, string::in, uint64::out) is det.
% close(Fd). If Fd == 0 then do nothing.
:- pred close(uint64::in) is det.
% fputs(S, Fd). Write the string to the file at Fd without a newline. If Fd == 0, do nothing.
:- pred fputs(string::in, uint64::in) is det.
% format(Fd, S, PolyTypes). Write string.format(S, PolyTypes) to the file at Fd. If Fd == 0, do nothing.
:- pred format(uint64::in, string::in, list(poly_type)::in) is det.
% format_append(Path, S, PolyTypes). Open the Path for append and write string.format(S, PolyTypes) to the file. If Path is empty, do nothing.
:- pred format_append(string::in, string::in, list(poly_type)::in) is det.
% write_sentence_list(List, Fd, IdsList, IdsIn, IdsOut). Use write_sentence to write the List. Return the list of Ids.
% If Fd == 0, do nothing.
:- pred write_sentence_list(list(sentence)::in, uint64::in, list(int)::out, map(sentence, int)::in, map(sentence, int)::out) is det.
:- pred write_sentence_set(set(sentence)::in, uint64::in, list(int)::out, map(sentence, int)::in, map(sentence, int)::out) is det.

:- implementation.

:- import_module int.
:- import_module pair.

:- type node_info ---> node_info(sentence, int, int).

:- pred print_step_list(list(sentence)::in) is det.
:- pred print_opponent_step_list(list(focussed_pot_arg_graph)::in) is det.
:- pred show_result(derivation_result::in) is det.
:- pred print_opponent_graphs(list(focussed_pot_arg_graph)::in) is det.
:- pred graph_colour1(string::in, string::out) is semidet.
:- pred graph_colour(string::in, string::out) is det.
:- pred print_to_file(sentence::in, derivation_result::in) is det.
:- pred dot_file(sentence::in, derivation_result::in, uint64::in) is det.
:- pred dot_preliminaries(uint64::in) is det.
:- pred proponent_cluster(sentence::in, digraph(sentence)::in, uint64::in, list(node_info)::out) is det.
:- pred proponent_nodes(sentence::in, list(graph_member)::in, int::in, uint64::in,
                        list(node_info)::out) is det.
:- pred proponent_edges(list(graph_member)::in, list(node_info)::in, uint64::in) is det.
:- pred opponent_clusters(list(focussed_pot_arg_graph)::in, set(sentence)::in, set(sentence)::in,
                          list(node_info)::in, list(attack)::in, uint64::in, int::in) is det.
:- pred opponent_nodes(pair(list(graph_member), list(sentence))::in, set(sentence)::in, set(sentence)::in,
                       int::in, int::in, uint64::in, list(node_info)::in, list(node_info)::out) is det.
:- pred opponent_edges(list(graph_member)::in, set(sentence)::in, set(sentence)::in, int::in,
                       list(node_info)::in, uint64::in) is det.
:- pred body_edges(list(sentence)::in, sentence::in, int::in, list(node_info)::in, uint64::in) is semidet.
:- pred attacks(list(attack)::in, list(node_info)::in, list(node_info)::in, uint64::in) is det.
:- pred format_lines(list(string)::in, uint64::in).

:- import_module options.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: DERIVATION STEPS

poss_print_case(Case, S) :-
 (verbose ->
   format("\nCase %s: S: %s\n", [s(Case), s(sentence_to_string(S))])
 ;
   true).

print_step(N, step_tuple(PropUnMrk-PropMrk-PropGr, OppUnMrk-_OMrk, D, C, _Att)) :-
  format("*** Step %d\n", [i(N)]),
  format("P:    %s-%s-%s\n", [s(sentence_list_to_string(PropUnMrk)),
                              s(sentence_set_to_string(PropMrk)),
                              s(digraph_to_string(PropGr))]),
  format("O:    [", []),
  print_opponent_step_list(OppUnMrk),
  format("G:    []\n", []),
  % TODO: Support GB. print_step_list_brackets(G),
  format("D:    [", []),
  print_step_list(to_sorted_list(D)),
  format("C:    [", []),
  print_step_list(to_sorted_list(C)).

print_step_list([]) :-
  format("]\n", []).
print_step_list([H|T]) :-
  (T = [] ->
    format("%s]\n", [s(sentence_to_string(H))])
  ;
    format("%s,\n       ", [s(sentence_to_string(H))]),
    print_step_list(T)).

print_opponent_step_list([]) :-
  format("]\n", []).
print_opponent_step_list([H|T]) :-
  (T = [] ->
    format("%s]\n", [s(focussed_pot_arg_graph_to_string(H))])
  ;
    format("%s,\n       ", [s(focussed_pot_arg_graph_to_string(H))]),
    print_opponent_step_list(T)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: RESULTS

show_result(derivation_result(_-PGraph, OppMrk, D, C, _Att)) :-
  format("\nPGRAPH:              %s\n", [s(digraph_to_string(PGraph))]),
  format("DEFENCE:             %s\n", [s(sentence_set_to_string(D))]),
  format("OGRAPHS:             [", []),
  print_opponent_graphs(to_sorted_list(OppMrk)),
  format("CULPRITS:            %s\n\n\n\n", [s(sentence_set_to_string(C))]).
% format("ATT:                 %s\n", [Att]),
% format("GRAPH:               %s\n", [G]).

print_opponent_graphs([]) :-
  format("]\n", []).
print_opponent_graphs([H|T]) :-
  (T = [] ->
    format("%s]\n", [s(focussed_pot_arg_graph_to_string(H))])
  ;
    format("%s,\n                      ", [s(focussed_pot_arg_graph_to_string(H))]),
    print_opponent_graphs(T)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: PRINT TO FILE

graph_colour1("background",                        "#FFFFFF").

graph_colour1("proponent_justifications",          "#A2DDF3").
graph_colour1("proponent_asm_toBeProved",          "#7C0AA2").
graph_colour1("proponent_asm",                     "#117711").
graph_colour1("proponent_nonAsm_toBeProved",       "#111177").
graph_colour1("proponent_nonAsm",                  "#222222").

graph_colour1("opponent_finished_justification",   "#CCCCCC").
graph_colour1("opponent_unfinished_justification", "#FFFFFF").
graph_colour1("opponent_ms_border",                "#000000").
graph_colour1("opponent_ms_asm_culprit",           "#CC9922").
graph_colour1("opponent_ms_asm_culprit_text",      "#FFFFFF").
graph_colour1("opponent_ms_asm_defence",           "#117711").
graph_colour1("opponent_ms_asm_defence_text",      "#FFFFFF").
graph_colour1("opponent_ms_asm",                   "#77BB77").
graph_colour1("opponent_ms_asm_text",              "#000000").
graph_colour1("opponent_ms_nonAsm",                "#777777").
graph_colour1("opponent_ms_nonAsm_text",           "#FFFFFF").
graph_colour1("opponent_ums_asm_defence",          "#117711").
graph_colour1("opponent_ums_asm_defence_border",   "#117711").
graph_colour1("opponent_ums_asm_defence_text",     "#FFFFFF").
graph_colour1("opponent_ums_asm_culprit",          "#CC9922").
graph_colour1("opponent_ums_asm_culprit_border",   "#CC9922").
graph_colour1("opponent_ums_asm_culprit_text",     "#FFFFFF").
graph_colour1("opponent_ums_asm",                  "#77BB77").
graph_colour1("opponent_ums_asm_border",           "#77BB77").
graph_colour1("opponent_ums_asm_text",             "#000000").
graph_colour1("opponent_ums_nonAsm",               "#AAAAAA").
graph_colour1("opponent_ums_nonAsm_border",        "#AAAAAA").
graph_colour1("opponent_ums_nonAsm_text",          "#000000").

graph_colour1("attack_edge",                       "#BB2222").

% Make a det version.
graph_colour(Key, Val) :-
  (graph_colour1(Key, V) ->
    Val = V
  ;
    % We don't expect this to happen.
    Val = "").

%

print_result(Proving, Result) :-
  option(print_to_file, Print),
  (Print = "true" ->
    print_to_file(Proving, Result)
  ;
    true),
  option(show_solution, Show),
  (Show = "true" ->
    show_result(Result)
  ;
    true).

print_to_file(Proving, Result) :-
  % For now, we don't know the input filename.
  FileStem = "argument", %filestem(FileStem),
  % For now, write to the current directory.
  Dir = "", %option(frameworkdir, Dir),
  option(fileID, Suff),
  File = FileStem ++ Suff,
  N = 1, %TODO: Implement. sols(N),
  int_to_string(N, NCodes),
  %atom_codes(NAtom, NCodes),
  NumberedFile = File ++ NCodes,
  FileName = NumberedFile ++ ".dot",
  DirAndFileName = Dir ++ FileName,
  open(DirAndFileName, "w", Fd),
  dot_file(Proving, Result, Fd),
  close(Fd).

% the first argument has the form:
%  [P,
%   Oset,
%   G,
%   D,
%   C,
%   Att]
%
% where P has the form:             NodesP-EdgesP
% where Oset members have the form: Claim-Unmarked-Marked-Edges

dot_file(Proving, derivation_result(_PNodes-PGraph, Oset, D, C, Att), Fd) :-
  dot_preliminaries(Fd),
  proponent_cluster(Proving, PGraph, Fd, PropNodeInfo),
  opponent_clusters(to_sorted_list(Oset), D, C, PropNodeInfo, to_sorted_list(Att), Fd, 1),
  format(Fd, "\n}\n", []).

dot_preliminaries(Fd) :-
  format_lines([
    "digraph G {",
    " ",
    " ratio=\"fill\";",
    " compound=\"true\";",
    " ranksep=\"1\";",
    " rankdir=\"LR\";"], Fd),
  graph_colour("background", BGCol),
  format(Fd, " bgcolor=\"%s\";\n", [s(BGCol)]),
  format(Fd, " node [style=\"filled\",shape=\"box\",height=\"0.4\",width=\"0.6\",margin=\"0.1,0.1\"];\n", []).

%

proponent_cluster(Proving, PGraph, Fd, NodeInfo) :-
  format_lines([
    " ",
    " subgraph cluster0 {",
    "  label = \"P\";",
    "  labeljust=\"l\";",
    "  pencolor=\"#444444\";",
    "  style=\"filled\";"], Fd),
  graph_colour("proponent_justifications", PropCol),
  format(Fd, "  color=\"%s\";\n", [s(PropCol)]),
  PGraphList = digraph_to_list(PGraph),
  proponent_nodes(Proving, PGraphList, 0, Fd, NodeInfo),
  proponent_edges(PGraphList, NodeInfo, Fd),
  format(Fd, " }\n", []).

proponent_nodes(_, [], _, _, []).
proponent_nodes(Proving, [S-Neighbors|Rest], N, Fd, [node_info(S, N, 0)|RestNodes]) :-
  (Neighbors = [] ->
    A = S,
    int_to_string(N, NAtom),
    format(Fd, "  s0_%s ", [s(NAtom)]),
    (A = Proving ->
      graph_colour("proponent_asm_toBeProved", Colour)
    ;
      (is_event(A) -> Colour = "#009999" ; graph_colour("proponent_asm", Colour))),
    format(Fd, "[label=\"%s\",fillcolor=\"%s\",color=\"%s\",fontcolor=\"white\"];\n",
           [s(sentence_to_string(A)), s(Colour), s(Colour)]),
    N1 = N + 1,
    proponent_nodes(Proving, Rest, N1, Fd, RestNodes)
  ;
    int_to_string(N, NAtom),
    format(Fd, "  s0_%s ", [s(NAtom)]),
    (S = Proving ->
      graph_colour("proponent_nonAsm_toBeProved", Colour)
    ;
      graph_colour("proponent_nonAsm", Colour)),
    format(Fd, "[label=\"%s\",fillcolor=\"%s\",color=\"%s\",fontcolor=\"white\"];\n",
           [s(sentence_to_string(S)), s(Colour), s(Colour)]),
    N1 = N + 1,
    proponent_nodes(Proving, Rest, N1, Fd, RestNodes)).

proponent_edges([], _, _).
proponent_edges([S-O_Body|Rest], NodeInfo, Fd) :-
  (O_Body = [] ->
    proponent_edges(Rest, NodeInfo, Fd)
  ;
    (body_edges(O_Body, S, 0, NodeInfo, Fd) -> true ; true),
    proponent_edges(Rest, NodeInfo, Fd)).

%

opponent_clusters([], _, _, _, _, _, _).
opponent_clusters([_Claim-(Ss-_Marked-OGraph)|RestOpJs], D, C, PropNodeInfo, Att, Fd, ClusterN) :-
  format(Fd, "\n subgraph cluster%i {\n", [i(ClusterN)]),
  format(Fd, "  label = \"O%i\";\n", [i(ClusterN)]),
  format_lines([
   "  edge [color=\"#000000\"];",
   "  labeljust=\"l\";",
   "  pencolor=\"#444444\";",
   "  style=\"filled\";"], Fd),
  (Ss = [] ->
    graph_colour("opponent_finished_justification", OppClusterCol)
  ;
    graph_colour("opponent_unfinished_justification", OppClusterCol)),
  format(Fd, "  color=\"%s\";\n", [s(OppClusterCol)]),
  OGraphList = digraph_to_list(OGraph),
  opponent_nodes(OGraphList-Ss, D, C, ClusterN, 0, Fd, [], OppNodeInfo),
  opponent_edges(OGraphList, D, C, ClusterN, OppNodeInfo, Fd),
  format(Fd, " }\n", []),
  graph_colour("attack_edge", AttackCol),
  format(Fd, "\n edge [color=\"%s\"];\n", [s(AttackCol)]),
  attacks(Att, PropNodeInfo, OppNodeInfo, Fd),
  ClusterN1 = ClusterN + 1,
  opponent_clusters(RestOpJs, D, C, PropNodeInfo, Att, Fd, ClusterN1).

opponent_nodes([]-[], _, _, _, _, _, NodeInfo, NodeInfo).
opponent_nodes([Js|RestJs]-Ss, D, C, ClusterN, N, Fd, InNodeInfo, NodeInfo) :-
  (A-[] = Js, assumption(A) ->
    int_to_string(ClusterN, ClusterNAtom),
    int_to_string(N, NAtom),
    format(Fd, "  s%s_%s ", [s(ClusterNAtom), s(NAtom)]),
    (member(A, C) ->
      % MARKED SUPPORT: CULPRIT
      graph_colour("opponent_ms_asm_culprit", FillColour),
      graph_colour("opponent_ms_asm_culprit_text", Font)
    ;
    (member(A, D) ->
      % MARKED SUPPORT: DEFENCE SET
      graph_colour("opponent_ms_asm_defence", FillColour),
      graph_colour("opponent_ms_asm_defence_text", Font)
    ;
      % MARKED SUPPORT: ASSUMPTION (NOT DEFENCE, NOT CULPRIT)
      graph_colour("opponent_ms_asm", FillColour),
      graph_colour("opponent_ms_asm_text", Font))),
    graph_colour("opponent_ms_border", BorderCol),
    format(Fd, "[label=\"%s\",fillcolor=\"%s\",color=\"%s\",fontcolor=\"%s\"];\n", [s(sentence_to_string(A)), s(FillColour), s(BorderCol), s(Font)]),
    N1 = N + 1,
    opponent_nodes(RestJs-Ss, D, C, ClusterN, N1, Fd, [node_info(A,N,ClusterN)|InNodeInfo], NodeInfo)
  ;
    S-_ = Js,
    int_to_string(ClusterN, ClusterNAtom),
    int_to_string(N, NAtom),
    format(Fd, "  s%s_%s ", [s(ClusterNAtom), s(NAtom)]),
    graph_colour("opponent_ms_nonAsm", FillColour),
    graph_colour("opponent_ms_border", BorderCol),
    graph_colour("opponent_ms_nonAsm_text", Font),
    format(Fd, "[label=\"%s\",fillcolor=\"%s\",color=\"%s\",fontcolor=\"%s\"];\n", [s(sentence_to_string(S)), s(FillColour), s(BorderCol), s(Font)]),
    N1 = N + 1,
    opponent_nodes(RestJs-Ss, D, C, ClusterN, N1, Fd, [node_info(S,N,ClusterN)|InNodeInfo], NodeInfo)).
opponent_nodes([]-[S|RestSs], D, C, ClusterN, N, Fd, InNodeInfo, NodeInfo) :-
  (member(node_info(S,_,_), InNodeInfo) ->
    N1 = N,
    OutNodeInfo = InNodeInfo
  ;
    int_to_string(ClusterN, ClusterNAtom),
    int_to_string(N, NAtom),
    format(Fd, "  s%s_%s ", [s(ClusterNAtom), s(NAtom)]),
    (assumption(S) ->
      (member(S, D) ->
        % UNMARKED SUPPORT: DEFENCE SET
        graph_colour("opponent_ums_asm_defence", FillColour),
        graph_colour("opponent_ums_asm_defence_border", Colour),
        graph_colour("opponent_ums_asm_defence_text", Font)
      ;
      (member(S, C) ->
        % UNMARKED SUPPORT: CULPRIT
        graph_colour("opponent_ums_asm_culprit", FillColour),
        graph_colour("opponent_ums_asm_culprit_border", Colour),
        graph_colour("opponent_ums_asm_culprit_text", Font)
      ;
        % UNMARKED SUPPORT: NON-DEFENCE SET, NON-CULPRIT
        graph_colour("opponent_ums_asm", FillColour),
        graph_colour("opponent_ums_asm_border", Colour),
        graph_colour("opponent_ums_asm_text", Font)))
    ;
      % UNMARKED SUPPORT: NON-ASSUMPTION
      graph_colour("opponent_ums_nonAsm", FillColour),
      graph_colour("opponent_ums_nonAsm_border", Colour),
      graph_colour("opponent_ums_nonAsm_text", Font)),
    format(Fd, "[label=\"%s\",fillcolor=\"%s\",color=\"%s\",fontcolor=\"%s\"];\n", [s(sentence_to_string(S)), s(FillColour), s(Colour), s(Font)]),
    N1 = N + 1,
    OutNodeInfo = [node_info(S,N,ClusterN)|InNodeInfo]),
  opponent_nodes([]-RestSs, D, C, ClusterN, N1, Fd, OutNodeInfo, NodeInfo).

opponent_edges([], _, _, _, _, _).
opponent_edges([S-O_Body|Rest], D, C, ClusterN, NodeInfo, Fd) :-
  (assumption(S) ->
    opponent_edges(Rest, D, C, ClusterN, NodeInfo, Fd)
  ;
    (body_edges(O_Body, S, ClusterN, NodeInfo, Fd) -> true ; true),
    opponent_edges(Rest, D, C, ClusterN, NodeInfo, Fd)).

% attacks(Att, PropNodeInfo, OppNodeInfo, Fd)

attacks([], _, _, _).
attacks([FromS-ToS|RestAtt], PropNodeInfo, OppNodeInfo, Fd) :-
  (member(node_info(FromS, FromN, FromClusterN), PropNodeInfo),
   member(node_info(ToS, ToN, ToClusterN), OppNodeInfo) ->
    int_to_string(FromN, FromNAtom),
    int_to_string(FromClusterN, FromClusterNAtom),
    int_to_string(ToN, ToNAtom),
    int_to_string(ToClusterN, ToClusterNAtom),
    format(Fd, " s%s_%s -> s%s_%s;\n", [s(FromClusterNAtom), s(FromNAtom), s(ToClusterNAtom), s(ToNAtom)]),
    attacks(RestAtt, PropNodeInfo, OppNodeInfo, Fd)
  ;
  (member(node_info(FromS,FromN,FromClusterN), OppNodeInfo),
   member(node_info(ToS, ToN, ToClusterN), PropNodeInfo) ->
    int_to_string(FromN, FromNAtom),
    int_to_string(FromClusterN, FromClusterNAtom),
    int_to_string(ToN, ToNAtom),
    int_to_string(ToClusterN, ToClusterNAtom),
    format(Fd, " s%s_%s -> s%s_%s;\n", [s(FromClusterNAtom), s(FromNAtom), s(ToClusterNAtom), s(ToNAtom)]),
    attacks(RestAtt, PropNodeInfo, OppNodeInfo, Fd)
  ;
    attacks(RestAtt, PropNodeInfo, OppNodeInfo, Fd))).

%

format_lines([], _).
format_lines([Line|Rest], Fd) :-
  format(Fd, Line, []),
  format(Fd, "\n", []),
  format_lines(Rest, Fd).

body_edges([], _, _, _, _).
body_edges([SFrom|Rest], STo, ClusterN, NodeInfo, Fd) :-
  member(node_info(SFrom, NFrom, _), NodeInfo),
  member(node_info(STo, NTo, _), NodeInfo),
  int_to_string(NFrom, FromAtom),
  int_to_string(NTo, ToAtom),
  int_to_string(ClusterN, ClusterNAtom),
  format(Fd, "  s%s_%s -> s%s_%s;\n",
         [s(ClusterNAtom), s(FromAtom), s(ClusterNAtom), s(ToAtom)]),
  body_edges(Rest, STo, ClusterN, NodeInfo, Fd).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
% PRINTING: HELPERS

sentence_list_to_string(L) = format("[%s]", [s(join_list(",", map(sentence_to_string, L)))]).

sentence_set_to_string(S) = sentence_list_to_string(to_sorted_list(S)).

digraph_to_list(G) =
  map((func(V) = V-Neighbors :-
         KeySet = lookup_from(G, lookup_key(G, V)),
         Neighbors = map(func(K) = lookup_vertex(G, K), to_sorted_list(KeySet))),
      to_sorted_list(vertices(G))).

digraph_to_string(G) = Result :-
  NodeList = map(func(V-Neighbors) =
                   format("%s-%s", [s(sentence_to_string(V)), s(sentence_list_to_string(Neighbors))]),
                 digraph_to_list(G)),
  Result = format("[%s]", [s(join_list(",", NodeList))]).

focussed_pot_arg_graph_to_string(Claim-_-(UnMrk-Mrk-Graph)) =
  format("%s-%s-%s-%s", [s(sentence_to_string(Claim)),
                         s(sentence_list_to_string(UnMrk)),
                         s(sentence_set_to_string(Mrk)),
                         s(digraph_to_string(Graph))]).

:- pragma foreign_proc("C",
puts(S::in),
[promise_pure],
"
fputs(S, stdout);
").

format(S, PolyTypes) :- puts(format(S, PolyTypes)).

:- pragma foreign_proc("C",
open(Path::in, Mode::in, Fd::out),
[promise_pure],
"
if (Path[0] == 0)
  Fd = 0;
else
  Fd = (unsigned long long)fopen(Path, Mode);
").

:- pragma foreign_proc("C",
close(Fd::in),
[promise_pure],
"
if (Fd != 0)
  fclose((FILE*)Fd);
").

:- pragma foreign_proc("C",
fputs(S::in, Fd::in),
[promise_pure],
"
if (Fd != 0)
  fputs(S, (FILE*)Fd);
").

format(Fd, S, PolyTypes) :- fputs(format(S, PolyTypes), Fd).

format_append(Path, S, PolyTypes) :-
  (Path \= "" ->
    open(Path, "a", Fd),
    fputs(format(S, PolyTypes), Fd),
    close(Fd)
  ; true).

write_sentence_list(List, Fd, IdsList, IdsIn, IdsOut) :-
  IdsList-IdsOut = foldl((
    func(S, IdsListIn-IdsIn1) = IdsListOut-IdsOut1 :-
      write_sentence(S, Fd, Id, IdsIn1, IdsOut1),
      IdsListOut = append(IdsListIn, [Id])),
    List, []-IdsIn).

write_sentence_set(Set, Fd, IdsList, IdsIn, IdsOut) :-
  write_sentence_list(to_sorted_list(Set), Fd, IdsList, IdsIn, IdsOut).
