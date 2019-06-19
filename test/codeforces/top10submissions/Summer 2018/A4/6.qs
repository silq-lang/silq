namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Convert;


    operation Solve (qs : Qubit[]) : ()
    {
        body
        { 
            
            X(qs[0]);
            
            mutable t1 = 0.0;
            mutable t2 = 0.0;
            
            for (i in 0..Length(qs)-2)
            {
                set t1 = Sqrt(ToDouble(Length(qs)-i-1));
                set t2 = ArcTan(t1);
                
                Ry(t2, qs[i+1]);
                
                
                CNOT(qs[i], qs[i+1]);
                
                
                Ry(-t2, qs[i+1]);
                
                
                CNOT(qs[i], qs[i+1]);
                
                CNOT(qs[i+1], qs[i]);
            }
        }
    }
}