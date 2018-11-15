/+
def main(x:ℕ){
	f := λ(a:𝟙,const b:𝟙)mfree. x;
	reverseM[𝟙,𝟙,ℕ](f)(1337,());
}
+/
/+
def main(x:ℕ){
	y := H(false);
	f := λ(x:ℕ,const _:𝟙)mfree.{
		y := y;
		xpy := x+y;
		forget(x=xpy-y);
		return (xpy,y);
	};
	return reverseM[ℕ,𝟙,ℕ×𝔹](f)((x,H(false)),());
}
+/
/+
def main(x:𝔹){
	if x{
		y := H(x);
	}else{
		y := H(X(x));
	}
	return y;
}
+/
/+
def main(x:𝔹){
	if x{
		measure(x);
	}else{
		measure(x);
	}
}
+/
/+
def main(){
	x := reverse;
	x = 2;
}
+/
/+
def f(x: 𝔹, y: !𝔹){
	return x;
}

def main(){
	x := (true:𝔹,false:!𝔹);
	return f(x);
}
+/

/+
def f(const x: 𝔹, const y: 𝔹)lifted{
	a:=(dup(x),1);
	return (dup(x),a);
}
+/
/+
def f(const x: 𝔹)lifted{
	y := x;
	return ()=>y;
}
+/
/+
def f(const x: 𝔹){
	y := x;
	return y;
}
+/
/+
def f(const x: 𝔹){
	f:=()=>x;
	return f;
}
+/
/+
def CNOT(x:𝔹,const y:𝔹){
	return (x,y);
}

def main(){
	k := (false,false): 𝔹×𝔹;
	return CNOT(k);
}
+/
/+
def main(x: 𝔹){
	x := x;
	return (){ x:=x; y:=x+1; forget(x=y-1); return y; }
}
+/

/+def main(const x: 𝔹){
	return x+1;
}
+/
/+def main(const x: 𝔹){
	return ()⇒x+1;
}
+/

/+
def main(const x: 𝔹){
	def f(){ def g()⇒x; return g; }
	return f;
	//return ()=>x;
}
+/

/+
def main(){
	x := false:!𝔹;
	def f(){ return x; }
	y := x;
	return (f(),f());
}
+/
/+
def main(){
	x := false:𝔹;
	f := ()=>x;
	//def f(){ return x; }
	y := x; // error
	//return f;
	return (f,f); // error
}
+/
/+
def main():!(ℕ[]){
	return dup[ℕ[]]([1,2,3]):!ℕ[];
}
+/
/+
def main():!ℕ×!ℕ{
	return dup[ℕ×ℕ](1,2);
}
+/
/+def main():!ℕ{
	return dup[ℕ](1);
}
+/
/+def main(){
	f := lambda(x:ℝ)lifted. { return x; };
	x:=2;
	return f(x);
}
+/
/+def main(x: 𝔹)mfree{
	measure(x);
}
+/

/+def foo()mfree:ℕ{
	n := 0:ℕ;
	if H(false){
		n+=foo();
	}
	return n;
}
+/

/+def main(){
	
}+/

/+
def main(x: 𝔹,y: 𝔹){
	return H(x)||H(y);
}
+/
/+
def main(x: 𝔹)mfree{
	y := dup(H(x));
	return y;
}
+/
/+def main(x: 𝔹){
	if measure(dup(x)){
		y:=H(x);
	}else{
		y:=H(x);
		//y := H(true);
		//measure(x);
		//forget(x=z);
		//z := H(x);
	}
    return y;
}
+/
/+
def main(x: !𝔹){
	/+f := lambda(i:const ℕ, ee:𝔹[][]) . {
		return (ee, tt);
	};+/
	y := 3;
	return x;
}
+/
/+def main(){
	if !x{
		
	}
	if !(triTestT == 0 && triTestTw == 0) { 
		phase(pi);
	}
}
+/

/+
rbar := 5;

def f(const x:𝔹){
	y := x;
	//if measure(x){ y:=hadamard(y); } // TODO: error
	if x{ y:=hadamard(y); } // TODO: ok
	return y; // TODO: ok
}

def main(){
	a := hadamard(false);
	b := hadamard(false);
	return f(a&&b);
}
+/

/+
//x:=2;

def main(const n: !Int[32],b:!ℤ)lifted:𝟙{
	x := false:𝔹;
	x := H(x):𝔹;
	//y := main : !Int[32]×!𝔹 →lifted 𝟙;
	//y := main : Π(consumed n: Int[32],x: !𝔹). lifted 𝟙;
	//y := main: const Int[32] × !𝔹 →mfree 𝟙;
	m := n: Int[32];
	def foo(f: !(𝔹 → 𝔹)){
		return f: (𝔹 → 𝔹);
	}
	/+y = 2;
	if x{
		
	}+/
}
+/
