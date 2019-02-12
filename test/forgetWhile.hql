
// when consuming, forget is not necessary
def f0(){
	x := 0;
	y := H(0:𝔹);
	while measure(y){
		x+=1;
		y := H(0:𝔹);
	}

	return x;
}


// forget within while
def f1(){
	x := H(0:𝔹);
	while measure(x){
		x := H(0:𝔹);
		y := dup(x);
		forget(y);
	}

	return ();
}
