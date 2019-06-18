
def toIntLifted[n:!ℕ](x:𝔹^n)lifted:int[n]{
	r:=0:int[n];
	for i in [0..n){
		r[i]=x[i];
	}
	return r;
}
def toVecLifted[n:!ℕ](x:int[n])lifted:𝔹^n{
	r:=vector(n,0:𝔹);
	for i in [0..n){
		r[i]=x[i];
	}
	return r;
}

def toInt[n:!ℕ](x:𝔹^n)qfree:int[n]{
	r:=toIntLifted(x);
	forget(x=toVecLifted(r));
	return r;
}
def toVec[n:!ℕ](x:int[n])qfree:𝔹^n{
	r:=toVecLifted(x);
	forget(x=toIntLifted(r));
	return r;
}
