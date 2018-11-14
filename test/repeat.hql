def main(){
	x := H(false);
	y := H(true);
	repeat 10{
		x := H(x);
		//y := H(y);
	}
	return (x,y);
}
