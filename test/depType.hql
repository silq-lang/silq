
def main(){
	n := 32;
	x := 0: !int[n]; // TODO
	n = 20; // TODO: error
}

def foo(){ // error
	n := 32;
	x := 0: !int[n]; // TODO
	return x;
}

def main2(n:!ℕ){
	x := foo();
	y := x : !int[n];
}

