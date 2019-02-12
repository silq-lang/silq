
// Helper function leaving `a` const
def f(const a:𝔹,b:𝔹){
	if a{
		b := H(b);
	}
	return b;
}

// can forget variables that were left constant
def f0(){
	// create dependency chain z -> y -> x
	x := H(0:𝔹);
	y := dup(x);
	z := dup(y);

	// modify `z` but not `y`
	z := f(y,z);

	// forget `y` (cannot forget `z`)
	__show(__query("dep", y)); // should print {x}
	__show(__query("dep", z)); // should print ⊤
	forget(y);

	return (x,z);
}

