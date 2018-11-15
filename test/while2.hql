def main(){
	x := []:𝔹[];
	while measure(H(false)){
		z := H(false);
		y := x ~ [z];
		forget(x=y[0..y.length-1]);
		forget(z=y[y.length-1]);
		x := y;
	}
	return x;
}
