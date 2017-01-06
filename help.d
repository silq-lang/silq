// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

import options,util;

enum commit = tryImport!(".git/"~tryImport!(".git/HEAD","ref: ")["ref: ".length..$],"unknown commit");

// TODO: auto-format depending on size of console
enum help=`PSI solver
Usage: psi [OPTION]... [FILE]...

The options below may be used.
--plot              call gnuplot to plot the result (experimental)
--noboundscheck     do not check array bounds

--cdf               generate cumulative distribution function (instead of generalized probability density)
--expectation       compute expectation of result ('main' should return a single number)

--trace             print statements as they are analyzed
--raw               print only pdf, cdf or expectation
--raw-error         print only error probability

--nointegrate       do not evaluate integrals
--integratedeltas   do not evaluate continuous integrals

--gnuplot           print output in gnuplot format (experimental)
--mathematica       print output in mathematica format (experimental)
--maple             print output in maple format (experimental)

--syntax            print example demonstrating language syntax and exit
--distributions     print information about supported primitive distributions and exit
--help              display this help and exit

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
	import std.conv, dexpr;
	string[3][] lrc;
	// TODO: domain constraints
	foreach(i,name;ToTuple!distribNames){
		DExpr cond=mixin(text(uncapitalize(name)~"Cond","(",paramNames!(name).map!(x=>`dVar("`~x~`")`).join(","),")")).extractConditions.simplify(one);
		string lhs=text("x := ",name,"(",paramNames!(name).join(","),");");
		string rhs=text("p(x) = ",mixin(text(uncapitalize(name),"PDF",`(dVar("x"),`,paramNames!(name).map!(x=>`dVar("`~x~`")`).join(","),")")).simplify(cond).toString(opt.formatting));
		string cnd=text("where "~cond.toString(opt.formatting));
		lrc~=[lhs,rhs,cnd];
	}
	auto padding=lrc.map!(x=>x[0].length).reduce!max+4;
	// note that count is wrong in general, as we want number of display characters (here it works)
	auto r="Supported primitive distributions\n"~lrc.map!(x=>x[0]~repeat(' ').take(padding-x[0].count).to!string~"⇒   "~x[1]~"\n"~repeat(' ').take(padding+"⇒   p(x) = ".count).to!string~x[2]).join("\n\n");
	return r;
}

