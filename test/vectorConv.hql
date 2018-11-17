def main[r:!ℕ,rrbar:!ℕ](){
	tau := vector(rrbar,0:int[r]);
	tau := tau:(B^r)^rrbar;
	return tau;
}
