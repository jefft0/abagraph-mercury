:- module server.
:- interface.

:- import_module abagraph.
:- import_module io.
:- import_module list.
:- import_module pair.

:- pred server(list(pair(int, step_and_id_map))::in, io::di, io::uo) is det.

:- implementation.

:- import_module string.

server(SolutionsIn, !IO) :-
    io.read_line_as_string(Res, !IO),
    (
        Res = error(_),
        io.write_string("Error reading from stdin\n", !IO)
    ;
        Res = eof,
        io.write_string("EOF\n", !IO)
    ;
        Res = ok(Line),
        io.write_string("got " ++ Line, !IO),
        io.write_string("again got " ++ Line, !IO),
        % Finish response.
        io.write_string("\n", !IO),
        io.flush_output(!IO),

        server(SolutionsIn, !IO)
    ).
