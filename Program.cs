using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace ValueFlowAnalyzer;

#region Abstract Domain & Value Representations

public abstract record SymbolicValue
{
    public sealed record Constant(object? Value) : SymbolicValue
    {
        public override string ToString() => Value is string s ? $"\"{s}\"" : Value?.ToString() ?? "null";
    }

    public sealed record Range(long Min, long Max) : SymbolicValue
    {
        public override string ToString() => Min == Max ? $"{Min}" : $"[{Min} .. {Max}]";
    }

    public sealed record UnknownInput(string OriginName, string Reason) : SymbolicValue
    {
        public override string ToString() => $"<ExternalInput: {OriginName} ({Reason})>";
    }

    public sealed record SymbolicExpression(string Op, ImmutableList<SymbolicValue> Operands) : SymbolicValue
    {
        public override string ToString() => $"{Op}({string.Join(", ", Operands)})";
    }
}

public record VariableState
{
    public ImmutableHashSet<SymbolicValue> PossibleValues { get; init; } = ImmutableHashSet<SymbolicValue>.Empty;

    public static VariableState Empty => new();

    public static VariableState Single(SymbolicValue value) => 
        new() { PossibleValues = ImmutableHashSet.Create(value) };

    public VariableState Union(VariableState other) => 
        new() { PossibleValues = PossibleValues.Union(other.PossibleValues) };

    public override string ToString() => 
        PossibleValues.Count == 0 ? "∅ (Unassigned)" : string.Join(" ∪ ", PossibleValues);
}

#endregion

#region Static Analysis Engine

public class IntraproceduralValueTracker
{
    private readonly Compilation _compilation;
    private readonly HashSet<IMethodSymbol> _callStack = new(SymbolEqualityComparer.Default);

    public IntraproceduralValueTracker(Compilation compilation)
    {
        _compilation = compilation;
    }

    /// <summary>
    /// Evaluates all possible values of an identifier at a specific line.
    /// </summary>
    public VariableState EvaluateVariableAt(SyntaxTree tree, string variableName, int lineNumber)
    {
        var root = tree.GetCompilationUnitRoot();
        var model = _compilation.GetSemanticModel(tree);

        var lineSpan = tree.GetText().Lines[lineNumber - 1].Span;
        var node = root.FindNode(lineSpan);

        var containingMethod = node.AncestorsAndSelf().OfType<BaseMethodDeclarationSyntax>().FirstOrDefault();
        if (containingMethod == null)
            return VariableState.Single(new SymbolicValue.UnknownInput(variableName, "Outside method scope"));

        var flowState = AnalyzeMethod(containingMethod, model, targetNode: node);
        
        return flowState.TryGetValue(variableName, out var state) 
            ? state 
            : VariableState.Single(new SymbolicValue.UnknownInput(variableName, "Unresolved / out of scope"));
    }

    private Dictionary<string, VariableState> AnalyzeMethod(
        BaseMethodDeclarationSyntax method, 
        SemanticModel model, 
        SyntaxNode? targetNode = null)
    {
        var state = new Dictionary<string, VariableState>();

        // 1. Seed parameters as external inputs or track forward
        if (method.ParameterList != null)
        {
            foreach (var param in method.ParameterList.Parameters)
            {
                var paramName = param.Identifier.Text;
                state[paramName] = VariableState.Single(new SymbolicValue.UnknownInput(paramName, "Method Parameter"));
            }
        }

        // 2. Iterate statements sequentially, handling branching and assignments
        if (method.Body != null)
        {
            AnalyzeBlock(method.Body, state, model, targetNode);
        }
        else if (method.ExpressionBody != null)
        {
            var exprVal = EvaluateExpression(method.ExpressionBody.Expression, state, model);
            state["$return"] = exprVal;
        }

        return state;
    }

    private bool AnalyzeBlock(
        BlockSyntax block, 
        Dictionary<string, VariableState> state, 
        SemanticModel model, 
        SyntaxNode? targetNode)
    {
        foreach (var statement in block.Statements)
        {
            if (targetNode != null && statement.SpanStart > targetNode.Span.End)
                return true; // Reached inspection point

            switch (statement)
            {
                case LocalDeclarationStatementSyntax decl:
                    foreach (var variable in decl.Declaration.Variables)
                    {
                        var varName = variable.Identifier.Text;
                        if (variable.Initializer != null)
                        {
                            state[varName] = EvaluateExpression(variable.Initializer.Value, state, model);
                        }
                        else
                        {
                            state[varName] = VariableState.Single(new SymbolicValue.Constant(GetDefaultValue(decl.Declaration.Type, model)));
                        }
                    }
                    break;

                case ExpressionStatementSyntax exprStmt:
                    if (exprStmt.Expression is AssignmentExpressionSyntax assign)
                    {
                        var targetName = assign.Left.ToString();
                        state[targetName] = EvaluateExpression(assign.Right, state, model);
                    }
                    break;

                case IfStatementSyntax ifStmt:
                    // Branch analysis: clone states, analyze branches, and join (union)
                    var trueState = new Dictionary<string, VariableState>(state);
                    var falseState = new Dictionary<string, VariableState>(state);

                    if (ifStmt.Statement is BlockSyntax trueBlock)
                        AnalyzeBlock(trueBlock, trueState, model, targetNode);
                    else
                        AnalyzeStatement(ifStmt.Statement, trueState, model, targetNode);

                    if (ifStmt.Else != null)
                    {
                        if (ifStmt.Else.Statement is BlockSyntax elseBlock)
                            AnalyzeBlock(elseBlock, falseState, model, targetNode);
                        else
                            AnalyzeStatement(ifStmt.Else.Statement, falseState, model, targetNode);
                    }

                    // Join states (Union of possibilities)
                    var allKeys = trueState.Keys.Union(falseState.Keys).ToList();
                    foreach (var key in allKeys)
                    {
                        trueState.TryGetValue(key, out var tVal);
                        falseState.TryGetValue(key, out var fVal);

                        tVal ??= VariableState.Empty;
                        fVal ??= VariableState.Empty;

                        state[key] = tVal.Union(fVal);
                    }
                    break;

                case ReturnStatementSyntax ret when ret.Expression != null:
                    state["$return"] = EvaluateExpression(ret.Expression, state, model);
                    break;
            }
        }
        return false;
    }

    private void AnalyzeStatement(
        StatementSyntax stmt, 
        Dictionary<string, VariableState> state, 
        SemanticModel model, 
        SyntaxNode? targetNode)
    {
        if (stmt is ExpressionStatementSyntax expr && expr.Expression is AssignmentExpressionSyntax assign)
        {
            state[assign.Left.ToString()] = EvaluateExpression(assign.Right, state, model);
        }
    }

    private VariableState EvaluateExpression(
        ExpressionSyntax expr, 
        Dictionary<string, VariableState> env, 
        SemanticModel model)
    {
        switch (expr)
        {
            case LiteralExpressionSyntax lit:
                return VariableState.Single(new SymbolicValue.Constant(lit.Token.Value));

            case IdentifierNameSyntax id:
                var name = id.Identifier.Text;
                if (env.TryGetValue(name, out var val))
                    return val;
                return VariableState.Single(new SymbolicValue.UnknownInput(name, "Unbound identifier"));

            case BinaryExpressionSyntax bin:
                var leftVals = EvaluateExpression(bin.Left, env, model);
                var rightVals = EvaluateExpression(bin.Right, env, model);
                return ComputeBinaryOp(bin.OperatorToken.Text, leftVals, rightVals);

            case InvocationExpressionSyntax inv:
                return ResolveInvocation(inv, env, model);

            case InterpolatedStringExpressionSyntax:
                return VariableState.Single(new SymbolicValue.UnknownInput(expr.ToString(), "Formatted string"));

            default:
                return VariableState.Single(new SymbolicValue.UnknownInput(expr.ToString(), "Dynamic Expression"));
        }
    }

    private VariableState ResolveInvocation(
        InvocationExpressionSyntax inv, 
        Dictionary<string, VariableState> env, 
        SemanticModel model)
    {
        var symbolInfo = model.GetSymbolInfo(inv);
        if (symbolInfo.Symbol is not IMethodSymbol methodSymbol)
        {
            return VariableState.Single(new SymbolicValue.UnknownInput(inv.ToString(), "Unresolvable invocation"));
        }

        // Trace across project boundaries if source syntax is accessible
        var syntaxRef = methodSymbol.DeclaringSyntaxReferences.FirstOrDefault();
        if (syntaxRef == null || _callStack.Contains(methodSymbol))
        {
            // Outside codebase or recursive call
            return VariableState.Single(new SymbolicValue.UnknownInput(
                $"{methodSymbol.ContainingType.Name}.{methodSymbol.Name}()", 
                syntaxRef == null ? "External Library / Assembly" : "Recursion Boundary"));
        }

        if (syntaxRef.GetSyntax() is BaseMethodDeclarationSyntax calleeDeclaration)
        {
            _callStack.Add(methodSymbol);
            var calleeModel = _compilation.GetSemanticModel(calleeDeclaration.SyntaxTree);

            // Bind argument states to callee parameters
            var calleeEnv = new Dictionary<string, VariableState>();
            for (int i = 0; i < inv.ArgumentList.Arguments.Count && i < calleeDeclaration.ParameterList.Parameters.Count; i++)
            {
                var argExpr = inv.ArgumentList.Arguments[i].Expression;
                var paramName = calleeDeclaration.ParameterList.Parameters[i].Identifier.Text;
                calleeEnv[paramName] = EvaluateExpression(argExpr, env, model);
            }

            var calleeResult = AnalyzeMethod(calleeDeclaration, calleeModel);
            _callStack.Remove(methodSymbol);

            if (calleeResult.TryGetValue("$return", out var retState))
                return retState;
        }

        return VariableState.Single(new SymbolicValue.UnknownInput(inv.ToString(), "Void or unhandled control flow"));
    }

    private VariableState ComputeBinaryOp(string op, VariableState left, VariableState right)
    {
        var results = ImmutableHashSet.CreateBuilder<SymbolicValue>();

        foreach (var l in left.PossibleValues)
        {
            foreach (var r in right.PossibleValues)
            {
                if (l is SymbolicValue.Constant { Value: long lNum } && r is SymbolicValue.Constant { Value: long rNum })
                {
                    results.Add(op switch
                    {
                        "+" => new SymbolicValue.Constant(lNum + rNum),
                        "-" => new SymbolicValue.Constant(lNum - rNum),
                        "*" => new SymbolicValue.Constant(lNum * rNum),
                        "/" when rNum != 0 => new SymbolicValue.Constant(lNum / rNum),
                        _ => new SymbolicValue.SymbolicExpression(op, ImmutableList.Create(l, r))
                    });
                }
                else if (l is SymbolicValue.Constant { Value: int lInt } && r is SymbolicValue.Constant { Value: int rInt })
                {
                    results.Add(op switch
                    {
                        "+" => new SymbolicValue.Constant(lInt + rInt),
                        "-" => new SymbolicValue.Constant(lInt - rInt),
                        "*" => new SymbolicValue.Constant(lInt * rInt),
                        "/" when rInt != 0 => new SymbolicValue.Constant(lInt / rInt),
                        _ => new SymbolicValue.SymbolicExpression(op, ImmutableList.Create(l, r))
                    });
                }
                else if (l is SymbolicValue.Constant { Value: string lStr } && r is SymbolicValue.Constant { Value: string rStr } && op == "+")
                {
                    results.Add(new SymbolicValue.Constant(lStr + rStr));
                }
                else
                {
                    // Propagate symbolic placeholder expression
                    results.Add(new SymbolicValue.SymbolicExpression(op, ImmutableList.Create(l, r)));
                }
            }
        }

        return new VariableState { PossibleValues = results.ToImmutable() };
    }

    private static object? GetDefaultValue(TypeSyntax type, SemanticModel model)
    {
        var typeInfo = model.GetTypeInfo(type);
        if (typeInfo.Type == null) return null;
        if (typeInfo.Type.IsReferenceType) return null;
        return 0;
    }
}

#endregion

#region Verification Driver

public static class Program
{
    public static void Main()
    {
        var testCode = """
        using System;

        public class OrderProcessor
        {
            public int CalculateDiscount(int customerTier, bool isHoliday)
            {
                int discountPercent = 0;

                if (isHoliday)
                {
                    discountPercent = 15;
                }
                else
                {
                    discountPercent = ComputeBaseRate(customerTier);
                }

                int finalRate = discountPercent + 5;
                return finalRate; // Line 21: Query finalRate here
            }

            private int ComputeBaseRate(int tier)
            {
                if (tier == 1)
                {
                    return 5;
                }
                return 10;
            }
        }
        """;

        var syntaxTree = CSharpSyntaxTree.ParseText(testCode);
        var mscorlib = MetadataReference.CreateFromFile(typeof(object).Assembly.Location);
        var compilation = CSharpCompilation.Create("AnalysisScope", new[] { syntaxTree }, new[] { mscorlib });

        var analyzer = new IntraproceduralValueTracker(compilation);

        Console.WriteLine("Analyzing variable 'finalRate' at line 21...\n");
        var possibleValues = analyzer.EvaluateVariableAt(syntaxTree, "finalRate", 21);

        Console.WriteLine("=== Possible Values Discovered ===");
        foreach (var val in possibleValues.PossibleValues)
        {
            Console.WriteLine($" -> {val}");
        }

        Console.WriteLine("\nAnalyzing variable 'discountPercent' at line 20...\n");
        var intermediateValues = analyzer.EvaluateVariableAt(syntaxTree, "discountPercent", 20);

        Console.WriteLine("=== Possible Values Discovered ===");
        foreach (var val in intermediateValues.PossibleValues)
        {
            Console.WriteLine($" -> {val}");
        }
    }
}

#endregion
