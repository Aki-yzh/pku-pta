package pku;

import pascal.taie.World;
import pascal.taie.analysis.ProgramAnalysis;
import pascal.taie.config.AnalysisConfig;
public class PointerAnalysis extends PointerAnalysisTrivial
{
    public static final String ID = "pku-pta";

    public PointerAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public PointerAnalysisResult analyze() {
        var result = new PointerAnalysisResult();
        var preprocess = new PreprocessResult();
        var world = World.get();
        var main = world.getMainMethod();
        var jclass = main.getDeclaringClass();
        
        //directly use the result of the trivial analysis


        return super.analyze();
        // return result;
    }

}
