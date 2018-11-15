
def main(){
	n := 32;
	x := 0: !int[n];
	n = 20; // TODO: error
}

def foo(){
	n := 32;
	x := 0: !int[n];
	return x; // TODO: error
}

def main2(n:!ℕ){
	x := foo();
	y := x : !int[n];
}

