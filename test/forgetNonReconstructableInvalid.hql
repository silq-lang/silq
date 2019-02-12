
def f0(x:𝔹){
	// break dependency
	y := dup(x);
	x := H(x);
	forget(y); // impossible because original x is missing
	return x;
}

