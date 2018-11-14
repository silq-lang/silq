def main(n: ℤ){
	x := H(false);
	for i in [0..measure(n)){
		x := H(x);
	}
	return x;
}
