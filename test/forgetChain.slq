
// build a dependency chain and forget in reverse order
def f0(x:𝔹){
	// build chain
	y := dup(x);
	z := dup(y);
	// forget in reverse order
	forget(z);
	forget(y);

	return x;
}

// build a dependency chain and forget in same order
def f1(x:𝔹){
	// build chain
	y := dup(x);
	z := dup(y);

	// forget in same order
	forget(y); // should update dependency of y to x
	__show(__query("dep", z)); // should print {x}
	forget(z);

	return x;
}

// build a dependency chain and break irrelevant dependency
def f2(x:𝔹){
	// build chain
	y := dup(x);
	z := dup(y);

	// change root
	x := H(x);

	// forget should still be possible (y is still present)
	forget(z);

	return (x,y);
}

// build a dependency chain and break irrelevant dependency
def f3(x:𝔹){
	// build chain
	y := dup(x);
	z := dup(y);

	// change middle
	y := H(y);

	// forget should still be possible (via x)
	__show(__query("dep", z)); // should print {x}
	forget(z);
	
	return (x,y);
}