
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

def toUintLifted[n:!ℕ](x:𝔹^n)lifted:uint[n]{
	r:=0:uint[n];
	for i in [0..n){
		r[i]=x[i];
	}
	return r;
}
def toVecLiftedU[n:!ℕ](x:uint[n])lifted:𝔹^n{
	r:=vector(n,0:𝔹);
	for i in [0..n){
		r[i]=x[i];
	}
	return r;
}

def toUint[n:!ℕ](x:𝔹^n)qfree:uint[n]{
	r:=toUintLifted(x);
	forget(x=toVecLiftedU(r));
	return r;
}
def toVecU[n:!ℕ](x:uint[n])qfree:𝔹^n{
	r:=toVecLiftedU(x);
	forget(x=toUintLifted(r));
	return r;
}
