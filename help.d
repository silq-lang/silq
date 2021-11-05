// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import options,util;

enum commit = tryImport!(".git/"~tryImport!(".git/HEAD","ref: ")["ref: ".length..$],"unknown commit");

// TODO: auto-format depending on size of console
enum help=`Silq type checker and simulator
Usage: silq [OPTION]... [FILE]...

The options below may be used.
--run               run main function in simulator
--trace             print statements as they run together with the program state

--summarize=...     summarize function declarations and exit (ex: --summarize=[name,arg-arity,ret-arity])
--error-json        print diagnostics in json format

--help              display this help and exit

Recognized file extensions: *.slq

Build: `~__DATE__~` `~__TIME__~`
Commit: `~commit~`
`;

// TODO: replace this by something more digestible?
enum syntax="input language syntax (example)
see 'test' directory for more examples

"~tryImport!("test/synopsis.slq","example not available for this build.")["// skipped\n\n".length..$];

