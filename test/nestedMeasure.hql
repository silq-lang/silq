def main(){
	x := H(1:𝔹);
	def h()⇒measure(x);
	def f(){
		def g()⇒h();
		return g();
	}
	return f();
}
