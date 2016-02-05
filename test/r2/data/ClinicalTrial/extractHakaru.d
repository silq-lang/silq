
import std.stdio, f=std.file;
import std.string, std.conv;

void main(){
	auto dataControlGroup = f.readText("dataControlGroup.csv").strip().split(",");
	auto dataTreatedGroup = f.readText("dataTreatedGroup.csv").strip().split(",");
	assert(dataControlGroup.length==1000 && dataTreatedGroup.length==1000);
	int n=100;
	write("Bind(Bernoulli(1/2),isEffective,");
	write("Bind(BetaD(1,1),probControl,");
	write("Bind(BetaD(1,1),probTreated,");
	write("Bind(BetaD(1,1),probAll,");
	write("Bind(Ite(isEffective=true,");
	int toClose=0;
	foreach(i;0..n){
		write(text("Bind(Bernoulli(probControl),controlGroup_E",i,",",
				   "Observe(controlGroup_E",i,"=",dataControlGroup[i]?"true":"false"),",");
		toClose+=2;
	}
	foreach(i;0..n){
		write(text("Bind(Bernoulli(probTreated),treatedGroup_E",i,","
				   "Observe(treatedGroup_E",i,"=",dataTreatedGroup[i]?"true":"false"),",");
		toClose+=2;
	}
	write("Ret(Unit)");
	foreach(i;0..toClose) write(")");

	write(",");
	toClose=0;
	foreach(i;0..n){
		write(text("Bind(Bernoulli(probAll),controlGroup_I",i,","
				   "Observe(controlGroup_I",i,"=",dataControlGroup[i]?"true":"false"),",");
		toClose+=2;
	}
	foreach(i;0..n){
		write(text("Bind(Bernoulli(probAll),treatedGroup_I",i,","
				   "Observe(treatedGroup_I",i,"=",dataTreatedGroup[i]?"true":"false",","));
		toClose+=2;
	}
	write("Ret(Unit)");
	foreach(i;0..toClose) write(")");

	write("),unit,Ret(isEffective))))))");
}
