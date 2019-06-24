/+
def foo(const x:𝔹):!ℕ{
	return if x then 0 else 1; // TODO: error
}
def bar(const x:𝔹):!ℕ{
	if x { return 0; } // TODO: error
	else { return 1; }
}
+/
/+def main(){
	x:=0:𝔹;
	y:=0:𝔹;
	while(measure(H(0:𝔹))){
		x=H(dup(y)); // TODO: error
	}
	return x;
}+/
/+def main(){
	x:=H(0:𝔹);
	y:=dup(x);
	while(measure(H(0:𝔹))){
		forget(y);
		y:=dup(x); // TODO
	}
	return H(x);
}+/
/+
def main(){
	x:=0:int[32];
	for i in [0..4){ x[i]=H(x[i]); } // TODO: error
	return x;
}
+/
/+

def arcsin(q:!ℝ) lifted :!ℝ;
def sqrt(q:!ℝ) lifted :!ℝ;

def WState[n:!N](q0:𝔹,q1s:𝔹^n) {
    if n+1==1{
        q0 := X(q0);
    } else {
        theta := arcsin(1.0 / sqrt(n));
        q0 := rotY(2*theta, q0);

        if !q0{
            (q1s[0], q1s[1..n]) := WState[n-1](q1s[0], q1s[1..n]); // TODO
        }
    }
    return (q0, q1s)
}
+/

/+
def solve(f: 𝔹^2 !→lifted 𝔹){
	x:=vector(1,0:!𝔹);
	return x==vector(1,0:𝔹);
}
def main(){
	g := λ[n:!ℕ](x: 𝔹^n)lifted⇒0:𝔹;
	f := g[2];
	x:=solve(f);
	y:=solve(f);
	return (x,y);
}+/

/+def solve(f: 𝔹^0 !→lifted 𝔹){
	x:=vector(1,0:𝔹);
	return measure(x)==vector(1,0:𝔹);
}
def main(){
	g := λ[n:!ℕ](x: 𝔹^n)lifted⇒0:𝔹;
	x:=solve(g[0]); // TODO
	return x;
}+/

/+def main(){
	x:=(1,2);
	y:=H(0:𝔹):int[2];
	x[y]=3; // TODO: this shouldn't compile
	return y;
}+/

/+
def main(){
	x := 0;
	forget(x); // TODO: remove x, even if classical
	return x;  // TODO: error
}
+/
/+
def main(){
	x := 0:𝔹;
	for i in [0..10){
		forget(x); // TODO: error!
		x := H(0:𝔹);
	}
	return x;
}
+/
