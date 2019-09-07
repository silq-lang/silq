// dependency on classical
def f0(x:int[32],y:!int[32]){
	z := x + y;

	// z should only depend on x
	__show(__query("dep", z)); // should print {x}

	// cleanup
	forget(z);

	return x;
}


// forgetting classical works implicitly
def f1(x:!int[32]){
	y := x + x;

	return x;
}


// forgetting classical explicitly is allowed
def f2(x:!int[32]){
	y := x + x;

	forget(y);

	return x;
}