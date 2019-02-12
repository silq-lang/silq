
// destroying dependency in conditional
def f0(x:𝔹,y:𝔹){
	// consume y in both branches
	if x{
		z:=y;
	}else{
		z:=H(y);
	}

	__show(__query("dep", z)); // should print ⊤
	forget(z); // error

	return (x);
}
