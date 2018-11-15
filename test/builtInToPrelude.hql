def main(){
	x := H(false):int[32];
	y := H(false);
	z := (0:int[32]) + y;
	//z := (0:!int[32]) + y; // TODO
	return (x,y,z);
}
