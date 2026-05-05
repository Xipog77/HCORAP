#include "parser.h"
#include "basiccontroller.h"
#include "HCORAPEncoding.h"
#include "HCORAPNServicesEncoding.h"
#include "solvingarguments.h"


using namespace std;
using namespace util;

enum ProgramArg {
    STRATIFIED,
    NSERVICES
};


int main(int argc, char **argv) {

    Arguments<ProgramArg> * pargs
            = new Arguments<ProgramArg>(
                    //Program arguments
                    {
                            arguments::arg("filename","Instance file path."),
                            arguments::arg("solutionname","Solution file path.")
                    },1,{
                    arguments::bop("S","strat",STRATIFIED,false,
                                           "If true, allow to not do some services (soft constraint). Default: false."),
                    arguments::bop("N","nserv",NSERVICES,false,
                                   "If true, use the encoding to maximize number of services. Default: false.")
                    },"Solve the resource location home care problem.");

    SolvingArguments * sargs = SolvingArguments::readArguments(argc,argv,pargs);

    HCORAP * instance = parser::parseHCORAP(pargs->getArgument(0));

    if(pargs->getBoolOption(NSERVICES)) {
        HCORAPNServicesEncoding *encoding =  new HCORAPNServicesEncoding(instance);
        if (pargs->getNArguments() == 1) {
            BasicController c(sargs, encoding, false, 0, INT_MAX);
            c.run();
        } else
            encoding->checkSolution(pargs->getArgument(1));
    }
    else{
        HCORAPEncoding *encoding =  new HCORAPEncoding(instance, pargs->getBoolOption(STRATIFIED));
        if (pargs->getNArguments() == 1) {
            BasicController c(sargs, encoding, false, 0, INT_MAX);
            c.run();
        } else
            encoding->checkSolution(pargs->getArgument(1));

    }

    return 0;
}
