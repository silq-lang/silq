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


string computeDistributionDocString(){
	import distrib, std.range, std.algorithm, std.uni, std.ascii;
	import std.conv, dexpr;
	string[3][] lrc;
	// TODO: domain constraints
	foreach(i,name;ToTuple!distribNames){
		DExpr cond=mixin(text(name~"Cond","(",paramNames!(name).map!(x=>`dVar("`~x~`")`).join(","),")")).extractConditions.simplify(one);
		string lhs=text("x := ",name,"(",paramNames!(name).join(","),");");
		string rhs=text("p(x) = ",mixin(text(name,"PDF",`(dVar("x"),`,paramNames!(name).map!(x=>`dVar("`~x~`")`).join(","),")")).simplify(cond).toString(opt.formatting));
		string cnd=text("where "~cond.toString(opt.formatting));
		lrc~=[lhs,rhs,cnd];
	}
	auto padding=lrc.map!(x=>x[0].length).reduce!max+4;
	// note that count is wrong in general, as we want number of display characters (here it works)
	auto r="Supported primitive distributions\n"~lrc.map!(x=>x[0]~repeat(' ').take(padding-x[0].count).to!string~"⇒   "~x[1]~(x[2]!="where 1"?"\n"~repeat(' ').take(padding+"⇒   p(x) = ".count).to!string~x[2]:"")).join("\n\n");
	return r;
}

