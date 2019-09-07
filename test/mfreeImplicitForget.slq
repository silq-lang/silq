// TODO
/+
def main(x:𝔹){
	y := dup(x);
	if y { x := H(x); }
	return x;
}
+/
// y can be forgotten as follows:
/+
def main(x:𝔹){
	y := dup(x);
	if y { x := H(x); }
	// ---
	if y { x := H(x); }
	forget(y=x);
	// ---
}
+/
