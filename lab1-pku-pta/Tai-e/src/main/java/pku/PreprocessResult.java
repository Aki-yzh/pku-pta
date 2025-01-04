package pku;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import pascal.taie.World;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.graph.SimpleGraph;

class BaseVar 
{
    public Integer type;

    BaseVar(Integer t) 
    {
        type = t;
    }

    @Override
    public boolean equals(Object obj) 
    {
        if (obj instanceof BaseVar other) 
        {
            return this.type.equals(other.type) && this.equalsSpecific(other);
        }
        return false;
    }

    protected boolean equalsSpecific(BaseVar other) 
    {
        return true;
    }

    @Override
    public int hashCode() 
    {
        return type.hashCode();
    }
}

class PtrVar extends BaseVar 
{
    public Var v;

    PtrVar(Var a) 
    {
        super(0);
        v = a;
    }

    @Override
    public String toString() 
    {
        return v.toString();
    }

    @Override
    protected boolean equalsSpecific(BaseVar other) 
    {
        if (other instanceof PtrVar otherPtr) 
        {
            return this.v.equals(otherPtr.v);
        }
        return false;
    }
}

class FieldRefVar extends BaseVar 
{
    public JField field;
    public Integer o;

    FieldRefVar(JField f, Integer i) 
    {
        super(1);
        field = f;
        o = i;
    }

    @Override
    public String toString() 
    {
        return o.toString() + '.' + field.toString();
    }

    @Override
    protected boolean equalsSpecific(BaseVar other) 
    {
        if (other instanceof FieldRefVar otherFieldRef) 
        {
            return this.field.equals(otherFieldRef.field) && this.o.equals(otherFieldRef.o);
        }
        return false;
    }
}

class MethodRefVar extends BaseVar 
{
    public JMethod method;
    public Integer line;

    MethodRefVar(JMethod m, Integer l) 
    {
        super(2);
        method = m;
        line = l;
    }

    @Override
    public String toString() 
    {
        return line + " -> " + method.toString();
    }

    @Override
    protected boolean equalsSpecific(BaseVar other) 
    {
        if (other instanceof MethodRefVar otherMethodRef) 
        {
            return this.method.equals(otherMethodRef.method) && this.line.equals(otherMethodRef.line);
        }
        return false;
    }
}

class StaticFieldRefVar extends BaseVar 
{
    public JField field;
    public JClass cls;

    StaticFieldRefVar(JField f, JClass c) 
    {
        super(3);
        field = f;
        cls = c;
    }

    @Override
    public String toString() 
    {
        return cls.toString() + '.' + field.toString();
    }

    @Override
    protected boolean equalsSpecific(BaseVar other) 
    {
        if (other instanceof StaticFieldRefVar otherStaticFieldRef) 
        {
            return this.field.equals(otherStaticFieldRef.field) && this.cls.equals(otherStaticFieldRef.cls);
        }
        return false;
    }
}

class StaticMethodRefVar extends BaseVar 
{
    public JMethod method;
    public JClass cls;

    StaticMethodRefVar(JMethod m, JClass c) 
    {
        super(4);
        method = m;
        cls = c;
    }

    @Override
    public String toString() 
    {
        return cls.toString() + '.' + method.toString();
    }

    @Override
    protected boolean equalsSpecific(BaseVar other) 
    {
        if (other instanceof StaticMethodRefVar otherStaticMethodRef) 
        {
            return this.method.equals(otherStaticMethodRef.method) && this.cls.equals(otherStaticMethodRef.cls);
        }
        return false;
    }
}

class ArrayRefVar extends BaseVar 
{
    public Integer object;

    ArrayRefVar(Integer object) 
    {
        super(5);
        this.object = object;
    }

    @Override
    public String toString() 
    {
        return object.toString();
    }

    @Override
    protected boolean equalsSpecific(BaseVar other) 
    {
        if (other instanceof ArrayRefVar) 
        {
            ArrayRefVar otherArrayRef = (ArrayRefVar) other;
            return this.object.equals(otherArrayRef.object);
        }
        return false;
    }
}

public class PreprocessResult 
{
    public final Map<New, Integer> obj_ids;
    public final Map<Integer, Var> test_pts;
    public final Map<BaseVar, Set<Integer>> PT;
    public final Map<Integer, Integer> OBJ;
    public final Map<Integer, Type> OBJTYPE;
    public final Map<BaseVar, Set<Integer>> WL;
    public final SimpleGraph<BaseVar> PFG;
    public final Set<Stmt> S;
    public final Set<JMethod> RM;
    public final Set<BaseVar> CG;

    public Integer Newcnt = 0;

    public PreprocessResult() 
    {
        obj_ids = new HashMap<>();
        test_pts = new HashMap<>();
        PT = new HashMap<>();
        OBJ = new HashMap<>();
        OBJTYPE = new HashMap<>();
        WL = new HashMap<>();
        PFG = new SimpleGraph<>();
        S = new HashSet<>();
        RM = new HashSet<>();
        CG = new HashSet<>();
    }

    public void alloc(New stmt, int id) 
    {
        obj_ids.put(stmt, id);
    }

    public void test(int id, Var v) 
    {
        test_pts.put(id, v);
    }

    public int getObjIdAt(New stmt) 
    {
        return obj_ids.get(stmt);
    }

    public Var getTestPt(int id) 
    {
        return test_pts.get(id);
    }

    public void analysis(IR ir) 
    {
        var stmts = ir.getStmts();
        S.addAll(stmts);
        JMethod method = ir.getMethod();
        if (RM.contains(method)) return;
        RM.add(method);
        Integer id = 0;

        for (var stmt : stmts) 
        {
            if (stmt instanceof Invoke invoke) 
            {
                id = handleInvokeStmt(invoke, id);
            } 
            else if (stmt instanceof New newStmt) 
            {
                handleNewStmt(newStmt, id);
            } 
            else if (stmt instanceof Copy copy) 
            {
                handleCopyStmt(copy);
            } 
            else if (stmt instanceof LoadField loadField) 
            {
                handleLoadFieldStmt(loadField);
            } 
            else if (stmt instanceof StoreField storeField) 
            {
                handleStoreFieldStmt(storeField);
            }
        }
    }

    private Integer handleInvokeStmt(Invoke stmt, Integer id) 
    {
        var exp = stmt.getInvokeExp();
        if (exp instanceof InvokeStatic invokeStatic) 
        {
            var methodRef = invokeStatic.getMethodRef();
            var className = methodRef.getDeclaringClass().getName();
            var methodName = methodRef.getName();

            if (className.equals("benchmark.internal.Benchmark") || className.equals("benchmark.internal.BenchmarkN")) 
            {
                id = handleBenchmarkInvoke(methodName, invokeStatic, id);
            } 
            else 
            {
                ProcessCallStatic(stmt);
            }
        }
        return id;
    }

    private Integer handleBenchmarkInvoke(String methodName, InvokeStatic exp, Integer id) 
    {
        if (methodName.equals("alloc")) 
        {
            var lit = exp.getArg(0).getConstValue();
            assert lit instanceof IntLiteral;
            id = ((IntLiteral) lit).getNumber();
        } 
        else if (methodName.equals("test")) 
        {
            var lit = exp.getArg(0).getConstValue();
            assert lit instanceof IntLiteral;
            var test_id = ((IntLiteral) lit).getNumber();
            var pt = exp.getArg(1);
            this.test(test_id, pt);
        }
        return id;
    }

    private void handleNewStmt(New stmt, Integer id) 
    {
        LValue Left = stmt.getDef().get();
        if (Left instanceof Var var) 
        {
            PtrVar lbase = new PtrVar(var);
            if (!WL.containsKey(lbase)) 
            {
                WL.put(lbase, new HashSet<>());
            }
            WL.get(lbase).add(Newcnt);
            OBJTYPE.put(Newcnt, stmt.getRValue().getType());
            Newcnt++;
        }
        if (id != 0) 
        {
            this.alloc(stmt, id);
            OBJ.put(Newcnt - 1, id);
        }
    }

    private void handleCopyStmt(Copy stmt) 
    {
        LValue Left = stmt.getDef().get();
        stmt.getUses().forEach(Right -> 
        {
            PtrVar rbase = new PtrVar((Var) Right);
            PtrVar lbase = new PtrVar((Var) Left);
            AddEdge(rbase, lbase);
        });
    }

    private void handleLoadFieldStmt(LoadField stmt) 
    {
        if (!stmt.isStatic()) 
            return;
            
        FieldRef Right = stmt.getFieldAccess().getFieldRef();
        JField RightField = Right.resolve();
        JClass RightClass = Right.getDeclaringClass();
        StaticFieldRefVar RightVar = new StaticFieldRefVar(RightField, RightClass);
        PtrVar LeftVar = new PtrVar(stmt.getLValue());
        AddEdge(RightVar, LeftVar);
    }

    private void handleStoreFieldStmt(StoreField stmt) 
    {
        if (!stmt.isStatic()) 
            return;

        FieldRef Left = stmt.getFieldAccess().getFieldRef();
        JField LeftField = Left.resolve();
        JClass LeftClass = Left.getDeclaringClass();
        StaticFieldRefVar LeftVar = new StaticFieldRefVar(LeftField, LeftClass);
        PtrVar RightVar = new PtrVar(stmt.getRValue());
        AddEdge(RightVar, LeftVar);
    }

    public void AddEdge(BaseVar from, BaseVar to) 
    {
        if (PFG.hasEdge(from, to)) 
            return;
        
        PFG.addEdge(from, to);
        PT.computeIfAbsent(from, k -> new HashSet<>());
        
        if (PT.get(from).isEmpty()) 
            return;
        
        WL.computeIfAbsent(to, k -> new HashSet<>()).addAll(PT.get(from));
    }

    public JMethod resolveCallee(Type type, Invoke callSite) 
    {
        MethodRef methodRef = callSite.getMethodRef();
        if (callSite.isInterface() || callSite.isVirtual()) 
            return World.get().getClassHierarchy().dispatch(type, methodRef);
        if (callSite.isSpecial()) 
            return World.get().getClassHierarchy().dispatch(methodRef.getDeclaringClass(), methodRef);
        if (callSite.isStatic()) 
            return methodRef.resolveNullable();
        return null;
    }

    public void ProcessCallStatic(Invoke stmt) 
    {
        JMethod method = stmt.getMethodRef().resolve();
        MethodRefVar methodRefVar = new MethodRefVar(method, stmt.getLineNumber());

        if (CG.contains(methodRefVar)) 
            return;

        CG.add(methodRefVar);
        analysis(method.getIR());

        List<Var> args = stmt.getInvokeExp().getArgs();
        List<Var> params = method.getIR().getParams();
        int length = args.size();

        for (int i = 0; i < length; i++) 
        {
            PtrVar argPtr = new PtrVar(args.get(i));
            PtrVar paramPtr = new PtrVar(params.get(i));
            AddEdge(argPtr, paramPtr);
        }

        Var returnValue = stmt.getLValue();
        if (returnValue == null)
            return;

        PtrVar returnPtr = new PtrVar(returnValue);
        method.getIR().getReturnVars().forEach(methodReturn -> 
        {
            PtrVar methodReturnPtr = new PtrVar(methodReturn);
            AddEdge(methodReturnPtr, returnPtr);
        });
    }
}
