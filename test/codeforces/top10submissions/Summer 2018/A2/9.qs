namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits : Bool[]) : ()
    {
        body
        {
			let n = Length(qs);
			mutable i = -1;
			for (j in 0..n-1)
			{
				if (bits[j] && i == -1)
				{
					set i = j;
				}
			}
			H(qs[i]);
			for (j in i+1..n-1)
			{
				if (bits[j])
				{
					CNOT(qs[i], qs[j]);
				}
			}
        }
    }
}