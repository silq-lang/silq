// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

enum Style{
	compact,
	pretty,
}
enum AmplitudeFormat{
	cartesian,
	polar,
}

struct Options{
	bool trace=false;
	bool check=false;
	bool projectForget=false;
	Style style=Style.pretty;
	AmplitudeFormat amplitudeFormat=AmplitudeFormat.polar;
	bool top=false;
	size_t topk=0;
}
Options opt; // TODO: get rid of global?
