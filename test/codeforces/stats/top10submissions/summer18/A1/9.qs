namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : ()
    {
        body
		{
			let n = Length(qs);
			for (i in 0..n-1)
			{
				H(qs[i]);
			}
        }
    }
}