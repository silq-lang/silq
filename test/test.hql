
/+
def main(x:𝔹^5){
	//x := 0:int[5];
	return x[x:int[5]];
}
+/
/+
def main(){
	x := false:𝔹;
	if x{
		z := H(false):𝔹;
	}
}
+/
/+
def flipWith_Array[l:!N](const p:𝔹^l, q:𝔹^l) mfree : 𝔹^l {
	for i in[0..l) {
		if p[i] { q[i] := X(q[i]); }
	}
	return q;
}

def a8_FetchT_Array[n:!N, rr:!N, r:!N](const i:int[r], const tt:int[n]^rr) : int[n] {
	ttd := 0:int[n];
	for j in [0..rr) {
		if i == j {
			ttd := flipWith_Array(tt[j]:B^n, ttd:B^n):int[n];
	}	}	
	return ttd;
}
+/

/+def flipWith_Array[l:!N](const p:𝔹^l, q:𝔹^l)mfree : 𝔹^l {
	for i in[0..l) {
		if p[i] { q[i] := X(q[i]); }
	}
	return q;
}

def a8_FetchT_Array[n:!N, rr:!N, r:!N](const i:int[r], const tt:int[n]^rr) : int[n] {
	ttd := 0:int[n];
	for j in [0..rr) {
		if i == j {
			ttd := flipWith_Array(tt[j]:B^n, ttd:B^n):int[n];
	}	}	
	return ttd;
}
+/

/+
def a12_FetchStoreE[rr:!N,r:!N](const i:int[r], qs: (𝔹^rr)^rr, 
	ps: 𝔹^rr) : (𝔹^rr)^rr x 𝔹^rr {

	for j in [0..rr) {
		for l in [0..j) {
			if i == j { (qs[j][l], ps[l]) := (ps[l], qs[j][l]); }
			if i == l { (qs[j][l], ps[j]) := (ps[j], qs[j][l]); }
		}
	}
	return (qs, ps);
}
+/
/+
def main(){
	y := 0:𝔹;
	x := dup(y);
	//forget(y=measure(x)+1);
	z := measure(H(false));
	//forget(y=x);
	//return x;
}
+/

/+
def main(x: 𝔹){
	y := dup(x);
	x := H(x);
	return x;
}
+/
/+def main(x: 𝔹)lifted{
	y := dup(x); // TODO: ok
	return x;
}
+/


/+def Node[k:!ℕ]lifted ⇒ int[k];

def edgeOracle_spec[k:!ℕ]lifted ⇒ ((const int[k] x const int[k] x 𝔹) !-> 𝔹);

def QWTFP_spec[k:!ℕ]lifted ⇒ (!N x !N x edgeOracle_spec[k]);

def a5_SETUP[k:!ℕ](oracle:!QWTFP_spec[k], const tt:int[2^oracle[1]]) : (𝔹^(2^oracle[1]))^(2^oracle[1]) {
    (n, r, edgeOracle) := oracle;
    rr := 2^r;
    ee := vector(2^oracle[1], vector(2^oracle[1], false:𝔹));

    // Todo: CHECK INDICES!
    for k in [0..2^r) {
        for j in [0..2^r) {
            ee[k][j] := edgeOracle(tt[j], tt[k], ee[k][j]);
    }    }

    return ee;
}
+/
/+
def a4_Hadamard_Array[k:!N](q:𝔹^k) : 𝔹^k {
    for j in [0..k) { q[j] := H(q[j]); }
    return q;
}

def a4_Hadamard_Array_Array[k:!N,l:!N](q:(𝔹^k)^l) : (𝔹^k)^l {
    for i in [0..l) {
        q[i] := a4_Hadamard_Array(q[i]);
    }
    return q;
}

// -------------------------------------------------------------

def a7_Diffuse_Array[k:!N](q:𝔹^k) : 𝔹^k {
    q := a4_Hadamard_Array(q);
    if q == array(k,false) { phase(π); }
    q := a4_Hadamard_Array(q);
	return q;
}

// -------------------------------------------------------------

def flipWith_Array[l:!N](const p: 𝔹^l, q:𝔹^l) : 𝔹^l {
    for i in[0..l) {
        if p[i] { q[i] := X(q[i]); }
    }
    return q;
}
+/


/+def QFT[n:!N]lifted(psi:uint[n]) mfree: uint[n];

def inverse[τ,χ]lifted(f: τ !→ mfree χ)lifted(x:χ)mfree ⇒ reverse(λ(x:τ,const _:𝟙)mfree. f(x))(x,());

def PeriodFinding[n:!N](f:!(uint[n] -> lifted uint[n])):!N{
    cand := 0:uint[n];
    //for k in [0..n) { cand[k] := H(cand[k]); }
    ancilla := f(cand);
	cand := inverse(QFT[n])(cand);
    measure(ancilla);
    return measure(cand):!N;
}
+/
/+
def main(){
	x := 0: !int[100];
	//x[0]⊕=1:𝔹;
	x[1]=1:!𝔹;
}
+/
/+
def main(){
	c := H(false);
	if c{
		//x := H(false);
		y := [dup(c),1,2];
	}else{
		//x := H(true);
		y := [dup(c),2];
	}
	c:=H(c);
	forget(c=false);
	return y;
}
+/
/+
def id[x](a:x):x;

def main(){
	x := id(2);
}
+/
/+
def main[n:!ℕ](x: 𝔹^n){
	//y := x[1];
	y := x;
	y[1] := true;
	return (y);
}
+/

/+
def zero(n:!ℕ):int[n]{
	return 0:int[n];
}+/

/+
def main(){
	x := 0: int[64];
	//y := true : !𝔹;
	y := x+1:ℕ;
	//z := measure(y);
	//forget(x=z-1);
}
+/

/+
def f[k:!ℕ](x: int[k]){
	return x;
}

def main(i: int[32]){
	return f(i);
}
+/


/+
def main(x:ℕ){
	f := λ(a:𝟙,const b:𝟙)mfree. x;
	g := dup(f);
	reverse[𝟙,𝟙,ℕ](f)(g((),()),());
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
	return reverse[ℕ,𝟙,ℕ×𝔹](f)((x,H(false)),());
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
