
def main[n:!ℕ](a: int[n], b: uint[n]):𝔹^n×𝔹^n×𝔹^n×𝔹^n{
	x := dup(a): 𝔹^n;
	y := dup(b): 𝔹^n;
	// n := a.length; // TODO
	return (x,y,a,b);
}
