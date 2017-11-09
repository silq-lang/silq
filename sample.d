import std.random, std.math, std.mathspecial, std.exception;

real sampleFlip(real p){
	return uniform!"[]"(0.0L,1.0L)<=p;
}

real sampleUniformInt(real a,real b){
	enforce(ceil(a)>=long.min && floor(b)<=long.max);
	return uniform!"[]"(cast(long)ceil(a),cast(long)floor(b));
}

real sampleGauss(real μ,real ν){
	return (μ+sqrt(ν)*normalDistributionInverse(uniform!"[]"(0.0L,1.0L)));
}

real sampleUniform(real a,real b){
	return uniform!"[]"(a,b);
}

real sampleLaplace(real μ,real b){
	return μ+b*(2*.uniform!"[]"(0,1)-1)*log(uniform!"(]"(0.0L,1.0L));
}

real sampleRayleigh(real ν){
	return sqrt(-2*ν*log(.uniform!"(]"(0.0L,1.0L)));
}

real samplePareto(real a,real b){
	return b/(.uniform!"(]"(0.0L,1.0L)^^(1.0/a));
}
