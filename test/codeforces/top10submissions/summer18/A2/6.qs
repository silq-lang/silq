namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits : Bool[]) : ()
    {
        body
        {
            mutable tmp = -1;
		    for (i in 0..Length(qs)-1)
		    {
			    if (bits[i] == true)
			    {
				    if (tmp != -1)
				    {
				        CNOT(qs[tmp], qs[i]);
				        set tmp = i;
				    }
				    if (tmp == -1)
				    {
				        H(qs[i]);
				        set tmp = i;
				    }
			    }
			}
		}
    }
}