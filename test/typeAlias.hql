Node := 𝔹[];
edgeOracle_spec := (const Node x const Node x 𝔹) !-> 𝔹;
def QWTFP_spec[k:!ℕ] ⇒ !int[k] x !int[k] x edgeOracle_spec;

def foo[k:!ℕ](spec: QWTFP_spec[k] ):QWTFP_spec[k]{
	(a,b,c) := spec; // TODO
	return (a,b,c);
}
