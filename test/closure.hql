def main(){
	x := 0:𝔹;
	y := dup(x);
	f := λ()mfree. y;
	if x{
		y := f();
	}else{
		f := λ()mfree. f();
		y := f();
	}
	return (x,y);
}
