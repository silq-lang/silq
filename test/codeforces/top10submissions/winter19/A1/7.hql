def solve(q0:𝔹, q1:𝔹) {
    q0 := rotY(2.000000*0.61547970867, q0);
    if !q0 {
        q1 := H(q1);
    }
    return (X(q0),q1);
}
