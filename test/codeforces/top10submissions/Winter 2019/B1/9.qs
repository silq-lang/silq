namespace Solution{
  open Microsoft.Quantum.Primitive;
  open Microsoft.Quantum.Canon;
  open Microsoft.Quantum.Extensions.Convert;
  open Microsoft.Quantum.Extensions.Math;
  operation Solve (qs : Qubit[]) : Int{
    //Let p = PI;
    let alpha = ArcCos(Sqrt(2.0/3.0));
    let beta = (2.0 *PI())/3.0;
    R1(-2.0*beta,qs[2]);
    R1(-beta,qs[1]);
    CNOT(qs[2],qs[0]);
    Controlled H(qs[0..0],qs[2]);
    //CNOT(qs[0],qs[2]);  
    ////
    CNOT(qs[1],qs[0]);
    Ry(-2.0*alpha,qs[1]);
    //X(qs[0]);
    return MeasureInteger(LittleEndian(qs))==1?0|1;//
  }
}