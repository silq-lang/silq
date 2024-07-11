// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

enum ErrorFormat{
	default_,
	json,
}

enum BackendType{
	none,
	run,
}

enum OutputForm{
	default_,
	raw,
	rawError,
}

enum IntegrationLevel{
	full,
	deltas,
	none,
}

struct Options{
	BackendType backend;
	bool plot=false;
	string plotRange="[-10:10]";
	string plotFile="";
	auto errorFormat=ErrorFormat.default_;
	bool noBoundsCheck=false;
	bool trace=false;
	bool dumpReverse=false;
	string[] importPath;
	string[] summarize;
	ulong numRuns=1;
}
Options opt; // TODO: get rid of global?
