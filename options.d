// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

enum Style{
	compact,
	verbose,
}
enum AmplitudeFormat{
	cartesian,
	polar,
}

struct Options{
	bool trace=false;
	bool check=false;
	bool projectForget=false;
	Style style=Style.verbose;
	AmplitudeFormat amplitudeFormat=AmplitudeFormat.polar;
}
Options opt; // TODO: get rid of global?
