namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Math;
	open Microsoft.Quantum.Extensions.Convert;

    operation Solve (qs : Qubit[]) : ()
    {
        body
        {
            mutable N = Length(qs);

			Ry(2.0*ArcTan(1.0/Sqrt(ToDouble(N - 1))), qs[0]);

			for(i in 1..(N - 1)){
				for(j in 0..(i - 1)){
					X(qs[j]);
				}
				(Controlled Ry(2.0*ArcTan(1.0/Sqrt(ToDouble(N - 1 - i))), _))(qs[0..(i - 1)], qs[i]);
				for(j in 0..(i - 1)){
					X(qs[j]);
				}
			}
        }
    }
}