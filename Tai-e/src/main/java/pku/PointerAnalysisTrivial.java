package pku;


import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import pascal.taie.World;
import pascal.taie.analysis.ProgramAnalysis;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;


public class PointerAnalysisTrivial extends ProgramAnalysis<PointerAnalysisResult> 
{
    public static final String ID = "pku-pta-trivial";

    /**
     * Directory to dump Result.
     */
    private final File dumpPath = new File("result.txt");

    public PointerAnalysisTrivial(AnalysisConfig config) 
    {
        super(config);
        if (dumpPath.exists()) 
        {
            dumpPath.delete();
        }
    }

    @Override
    public PointerAnalysisResult analyze() 
    {
        var preprocess = new PreprocessResult();
        var result = new PointerAnalysisResult();
        var main = World.get().getMainMethod();

        AddReachable(preprocess, main);

        while (!preprocess.WL.isEmpty()) 
        {
            processWorkList(preprocess);
        }

        collectResults(preprocess, result);
        dump(result);

        return result;
    }

    private void processWorkList(PreprocessResult preprocess) 
    {
        Iterator<BaseVar> iterator = preprocess.WL.keySet().iterator();
        if (!iterator.hasNext()) 
            return;

        BaseVar n = iterator.next();
        Set<Integer> delta = new HashSet<>(preprocess.WL.get(n));
        preprocess.PT.computeIfAbsent(n, k -> new HashSet<>());
        preprocess.WL.remove(n);
        delta.removeAll(preprocess.PT.get(n));
        Propagate(preprocess, n, delta);
        if (n instanceof PtrVar ptrVar) 
        {
            processPtrVar(preprocess, ptrVar, delta);
        }
    }

    private void processPtrVar(PreprocessResult preprocess, PtrVar n, Set<Integer> delta) 
    {
        for (Integer obj : delta) 
        {
            Var x = n.v;
            processStoreFields(preprocess, x, obj);
            processStoreArrays(preprocess, x, obj);
            processLoadFields(preprocess, x, obj);
            processLoadArrays(preprocess, x, obj);
            ProcessCall(preprocess, n, obj);
        }
    }

    private void processStoreFields(PreprocessResult preprocess, Var x, Integer obj) 
    {
        x.getStoreFields().forEach(stmt -> 
        {
            if (!preprocess.S.contains(stmt)) 
                return;

            PtrVar right = new PtrVar(stmt.getRValue());
            JField field = stmt.getFieldRef().resolve();
            FieldRefVar fieldvar = new FieldRefVar(field, obj);
            preprocess.AddEdge(right, fieldvar);
        });
    }

    private void processLoadFields(PreprocessResult preprocess, Var x, Integer obj) 
    {
        x.getLoadFields().forEach(stmt -> 
        {
            if (!preprocess.S.contains(stmt)) 
                return;

            PtrVar left = new PtrVar(stmt.getLValue());
            JField field = stmt.getFieldRef().resolve(); 
            FieldRefVar fieldvar = new FieldRefVar(field, obj);
            preprocess.AddEdge(fieldvar, left);
        });
    }

    private void processLoadArrays(PreprocessResult preprocess, Var x, Integer obj) 
    {
        x.getLoadArrays().forEach(stmt -> 
        {
            if (!preprocess.S.contains(stmt)) 
                return;

            ArrayRefVar arrayvar = new ArrayRefVar(obj);
            PtrVar left = new PtrVar(stmt.getLValue()); 
            preprocess.AddEdge(arrayvar, left);
        });
    }

    private void processStoreArrays(PreprocessResult preprocess, Var x, Integer obj) 
    {
        x.getStoreArrays().forEach(stmt -> 
        {
            if (!preprocess.S.contains(stmt)) 
                return;

            ArrayRefVar arrayvar = new ArrayRefVar(obj);
            PtrVar right = new PtrVar(stmt.getRValue());
            preprocess.AddEdge(right, arrayvar);
        });
    }

    private void collectResults(PreprocessResult preprocess, PointerAnalysisResult result) 
    {
        preprocess.test_pts.forEach((test_id, pt) -> 
        {
            PtrVar ptptr = new PtrVar(pt);
            TreeSet<Integer> resultSet = new TreeSet<>();
            var ptset = preprocess.PT.get(ptptr);
            if (ptset != null)
            {
                ptset.forEach(i -> 
                {
                    if (preprocess.OBJ.containsKey(i)) 
                    {
                        resultSet.add(preprocess.OBJ.get(i));
                    }
                });
            }
            result.put(test_id, resultSet);
        });
    }

    protected void AddReachable(PreprocessResult preprocess, JMethod method)
    {
        preprocess.analysis(method.getIR());
    }

    protected void Propagate(PreprocessResult preprocess, BaseVar n, Set<Integer> pts) 
    {
        if (pts.isEmpty()) 
            return;  
        preprocess.PT.computeIfAbsent(n, k -> new HashSet<>()).addAll(pts);
        for (BaseVar s : preprocess.PFG.getSuccsOf(n)) 
        {
            preprocess.WL.computeIfAbsent(s, k -> new HashSet<>()).addAll(pts);
        }
    }

    protected void ProcessCall(PreprocessResult preprocess, PtrVar n, Integer obj)
    {
        Var x = n.v;
        x.getInvokes().forEach(stmt -> 
        {
            JMethod M = preprocess.resolveCallee(preprocess.OBJTYPE.get(obj), stmt);
            if (M == null)
                return;

            MethodRefVar m = new MethodRefVar(M, stmt.getLineNumber());
            PtrVar mthis = new PtrVar(M.getIR().getThis());
            addToWorkList(preprocess, mthis, obj);
            
            if (preprocess.CG.contains(m))
                return; 

            preprocess.CG.add(m);
            linkReturnVars(preprocess, stmt, M);
            linkArguments(preprocess, stmt, M);
            AddReachable(preprocess, M);
        });
    }
    
    private void addToWorkList(PreprocessResult preprocess, PtrVar mthis, Integer obj) 
    {
        preprocess.WL.computeIfAbsent(mthis, k -> new HashSet<>()).add(obj);
    }
    
    private void linkArguments(PreprocessResult preprocess, Invoke stmt, JMethod M) 
    {
        List<Var> params = M.getIR().getParams();
        List<Var> args = stmt.getInvokeExp().getArgs();
        for (int i = 0; i < args.size(); i++) 
        {
            PtrVar pptr = new PtrVar(params.get(i));
            PtrVar aptr = new PtrVar(args.get(i));
            preprocess.AddEdge(aptr, pptr);
        }
    }
    
    private void linkReturnVars(PreprocessResult preprocess, Invoke stmt, JMethod M) 
    {
        Var r = stmt.getLValue();
        if (r == null) 
            return;

        PtrVar rptr = new PtrVar(r);
        M.getIR().getReturnVars().forEach(mret -> 
        {
            PtrVar mretptr = new PtrVar(mret);
            preprocess.AddEdge(mretptr, rptr);
        });
    }

    protected void dump(PointerAnalysisResult result) 
    {
        try (PrintStream out = new PrintStream(new FileOutputStream(dumpPath))) 
        {
            out.println(result);
        } 
        catch (FileNotFoundException e) 
        {
            e.printStackTrace();
        }
    }
}




