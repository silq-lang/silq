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

struct Options{
	BackendType backend;
	auto errorFormat=ErrorFormat.default_;
	bool noBoundsCheck=false;
	bool trace=false;
	bool dumpReverse=false;
	string[] importPath;
	string[] summarize;
	ulong numRuns=1;
}
Options opt; // TODO: get rid of global?
