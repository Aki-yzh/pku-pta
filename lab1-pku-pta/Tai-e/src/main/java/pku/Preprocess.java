package pku;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.New;

public class Preprocess extends MethodAnalysis<PreprocessResult> {
    public static final String ID = "pku-pta-preprocess";
    public Preprocess(AnalysisConfig config) {
        super(config);
    }

    @Override
    public PreprocessResult analyze(IR ir) {
        var result = new PreprocessResult();
        result.analysis(ir);
        return result;
    }
    
}
