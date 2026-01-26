// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import options,util;

enum commit = tryImport!(".git/"~tryImport!(".git/HEAD","ref: ")["ref: ".length..$],"unknown commit");

// TODO: auto-format depending on size of console
enum help=`Silq type checker and simulator
Usage: silq [OPTION]... [FILE]...

The options below may be used.
--run                run main function in simulator
--run-on=exp         run main function on argument given by exp
--run-on-each=exp    run main function on each element of exp
--run=exp            run expression exp
--repeat=n           repeat the run n times
--trace              print statements as they run together with the program state
--seed=n             use a fixed random seed for repeatable experiments

--fmt=MODE           quantum state formatting: MODE = STYLE-COORDS
--style=STYLE        verbosity: compact | verbose (overrides --qfmt style)
--coords=COORDS      amplitudes: cartesian | polar (overrides --qfmt coords)
--top[=k]            sort by amplitudes [restrict to top-k]

--inference-limit=n  use at most n iterations for inferring fixed points

--summarize=...      summarize function declarations and exit (ex: --summarize=[name,arg-arity,ret-arity])
--error-json         print diagnostics in json format

--help               display this help and exit

Recognized file extensions: *.slq

Build: `~__DATE__~` `~__TIME__~`
Commit: `~commit~`
`;

// TODO: replace this by something more digestible?
enum syntax="input language syntax (example)
see 'test' directory for more examples

"~tryImport!("test/synopsis.slq","example not available for this build.")["// skipped\n\n".length..$];

