import util;

enum commit = tryImport!(".git/"~tryImport!(".git/HEAD","ref: ")["ref: ".length..$],"unknown commit");

// TODO: auto-format depending on size of console
enum help=`PSI solver
Usage: psi [OPTION]... [FILE]...

The options below may be used.
--plot           call gnuplot to plot the result (experimental)
--noboundscheck  do not check array bounds

--cdf            generate cumulative distribution function (instead of generalized probability density)
--expectation    compute expectation of result ('main' should return a single number)

--trace          print statements as they are analyzed

--raw            do not evaluate integrals
--deltas         do not evaluate continuous integrals

--gnuplot        print output in gnuplot format (experimental)
--mathematica    print output in mathematica format (experimental)
--maple          print output in maple format (experimental)

--syntax         print example demonstrating language syntax and exit
--distributions  print information about supported primitive distributions and exit
--help           display this help and exit

Recognized file extensions: *.psi, *.prb

Source code: http://psisolver.org/
Commit: `~commit~`
`;

// TODO: replace this by something more digestible?
enum syntax="input language syntax (example)
see 'test' directory for more examples

"~tryImport!("test/synopsis.prb","example not available for this build.\nConsult http://psisolver.org")["// skipped\n\n".length..$];


string computeDistributionDocString(){
	import distrib, std.range, std.algorithm, std.uni, std.ascii;
	enum names=[__traits(allMembers,distrib)].filter!(x=>x.endsWith("PDF")).map!(x=>cast(string[2])[x,capitalize(x[0..$-"PDF".length])]).array;
	enum calls={ string[][] r;
             foreach(name;ToTuple!names){
	             import std.traits;
	             r~=name[0]~[ParameterIdentifierTuple!(mixin(name[0]))[1..$]];
             }
	         return r;
		}();
	import std.conv, psi, dexpr;
	string[2][] lr;
	// TODO: domain constraints
	foreach(i,name;ToTuple!names){
		string lhs=text("x := ",name[1],"(",calls[i][1..$].join(","),");");
		string rhs=text("x ∼ ",mixin(text(name[0],`(dVar("x"),`,calls[i][1..$].map!(x=>`dVar("`~x~`")`).join(","),")")).simplify(one).toString(formatting));
		lr~=[lhs,rhs];
	}
	auto padding=lr.map!(x=>x[0].length).reduce!max+4;
	// note that count is wrong in general, as we want number of display characters (here it works)
	auto r="Supported primitive distributions\n"~lr.map!(x=>x[0]~repeat(' ').take(padding-x[0].count).to!string~"⇒   "~x[1]).join("\n\n");
	return r;
}

