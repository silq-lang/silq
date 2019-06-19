namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Convert;
  open Microsoft.Quantum.Extensions.Math;
  operation Solve (x : Qubit[]) : Unit {
    let N = Length(x);
    CNOT(x[1],x[2]);
    X(x[2]);
    Controlled H( x[2..2],x[1]);
    Controlled H( x[2..2],x[0]);
    X(x[2]);
    CNOT(x[2],x[0]);
    CCNOT(x[2],x[0],x[1]);
    CNOT(x[2],x[0]);
    
    //CNOT(x[2],x[1]);
    //CNOT(x[2],x[]);
    Controlled H( x[2..2],x[0]);
    //Controlled (SWAP(x[1],_))(x[2..2],x[0]);
    CNOT(x[1],x[2]);
  }
}