using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Globalization;
using System.IO;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace ValueFlowAnalyzer;

#region Abstract Domain & Symbolic Value System

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
        PossibleValues.Count == 0 ? "∅ (Unassigned)" : string.Join(", ", PossibleValues.OrderBy(v => v.ToString()));
}

#endregion

#region Static Analysis Engine

public class FolderValueTracker
{
    private readonly Compilation _compilation;
    private readonly HashSet<IMethodSymbol> _callStack = new(SymbolEqualityComparer.Default);
    private readonly List<INamedTypeSymbol> _allNamedTypes;
    private readonly List<INamedTypeSymbol> _allConcreteTypes;
    
    // Global static heap: tracks "TypeName.FieldName" => VariableState
    private Dictionary<string, VariableState> _staticHeap = new();

    public FolderValueTracker(Compilation compilation)
    {
        _compilation = compilation;
        _allNamedTypes = GetAllNamedTypes(compilation.Assembly.GlobalNamespace).ToList();
        _allConcreteTypes = _allNamedTypes.Where(t => !t.IsAbstract && t.TypeKind != TypeKind.Interface).ToList();
        
        EvaluateGlobalStaticState();
    }

    private static IEnumerable<INamedTypeSymbol> GetAllNamedTypes(INamespaceSymbol root)
    {
        foreach (var type in root.GetTypeMembers())
        {
            yield return type;
            foreach (var nested in GetNestedTypes(type))
                yield return nested;
        }

        foreach (var subNs in root.GetNamespaceMembers())
        {
            foreach (var type in GetAllNamedTypes(subNs))
                yield return type;
        }
    }

    private static IEnumerable<INamedTypeSymbol> GetNestedTypes(INamedTypeSymbol type)
    {
        foreach (var nested in type.GetTypeMembers())
        {
            yield return nested;
            foreach (var subNested in GetNestedTypes(nested))
                yield return subNested;
        }
    }

    #region Static Class Initialization & Permutations

    private record StaticClassInitializer(
        INamedTypeSymbol TypeSymbol,
        List<FieldDeclarationSyntax> StaticFields,
        ConstructorDeclarationSyntax? StaticCtor
    );

    private void EvaluateGlobalStaticState()
    {
        var staticUnits = new List<StaticClassInitializer>();

        foreach (var typeSymbol in _allNamedTypes)
        {
            var syntaxRefs = typeSymbol.DeclaringSyntaxReferences;
            if (syntaxRefs.Length == 0) continue;

            var staticFields = new List<FieldDeclarationSyntax>();
            ConstructorDeclarationSyntax? staticCtor = null;

            foreach (var syntaxRef in syntaxRefs)
            {
                var syntax = syntaxRef.GetSyntax();
                if (syntax is not TypeDeclarationSyntax typeDecl) continue;

                var fields = typeDecl.Members
                    .OfType<FieldDeclarationSyntax>()
                    .Where(f => f.Modifiers.Any(SyntaxKind.StaticKeyword))
                    .ToList();
                staticFields.AddRange(fields);

                var ctor = typeDecl.Members
                    .OfType<ConstructorDeclarationSyntax>()
                    .FirstOrDefault(c => c.Modifiers.Any(SyntaxKind.StaticKeyword));
                if (ctor != null) staticCtor = ctor;
            }

            if (staticFields.Count > 0 || staticCtor != null)
            {
                staticUnits.Add(new StaticClassInitializer(typeSymbol, staticFields, staticCtor));
            }
        }

        if (staticUnits.Count == 0) return;

        const int maxPermutations = 120;
        var permutations = GeneratePermutations(staticUnits, maxPermutations);
        var mergedStaticHeap = new Dictionary<string, VariableState>();

        foreach (var order in permutations)
        {
            var currentOrderHeap = new Dictionary<string, VariableState>();

            foreach (var unit in order)
            {
                ExecuteStaticClassInitialization(unit, currentOrderHeap);
            }

            foreach (var (key, val) in currentOrderHeap)
            {
                if (!mergedStaticHeap.TryGetValue(key, out var existing))
                    mergedStaticHeap[key] = val;
                else
                    mergedStaticHeap[key] = existing.Union(val);
            }
        }

        _staticHeap = mergedStaticHeap;
    }

    private void ExecuteStaticClassInitialization(
        StaticClassInitializer unit, 
        Dictionary<string, VariableState> currentHeap)
    {
        string typeName = unit.TypeSymbol.ToDisplayString();

        foreach (var fieldDecl in unit.StaticFields)
        {
            var fieldModel = _compilation.GetSemanticModel(fieldDecl.SyntaxTree);
            foreach (var variable in fieldDecl.Declaration.Variables)
            {
                string fieldKey = $"{typeName}.{variable.Identifier.Text}";
                if (variable.Initializer != null)
                {
                    currentHeap[fieldKey] = EvaluateExpression(
                        variable.Initializer.Value, 
                        new Dictionary<string, VariableState>(), 
                        fieldModel, 
                        currentHeap,
                        unit.TypeSymbol
                    );
                }
                else
                {
                    currentHeap[fieldKey] = VariableState.Single(new SymbolicValue.Constant(0));
                }
            }
        }

        if (unit.StaticCtor != null)
        {
            var ctorModel = _compilation.GetSemanticModel(unit.StaticCtor.SyntaxTree);
            var localScope = new Dictionary<string, VariableState>();

            if (unit.StaticCtor.Body != null)
            {
                AnalyzeBlock(unit.StaticCtor.Body, localScope, ctorModel, null, currentHeap, unit.TypeSymbol);
            }
        }
    }

    private static List<List<T>> GeneratePermutations<T>(List<T> list, int maxLimit)
    {
        var result = new List<List<T>>();
        if (list.Count == 0) return result;

        if (list.Count > 5)
        {
            result.Add(new List<T>(list));
            for (int i = 0; i < list.Count - 1 && result.Count < maxLimit; i++)
            {
                var swapped = new List<T>(list);
                (swapped[i], swapped[i + 1]) = (swapped[i + 1], swapped[i]);
                result.Add(swapped);
            }
            return result;
        }

        void Permute(List<T> current, List<T> remaining)
        {
            if (result.Count >= maxLimit) return;
            if (remaining.Count == 0)
            {
                result.Add(new List<T>(current));
                return;
            }

            for (int i = 0; i < remaining.Count; i++)
            {
                var nextCurrent = new List<T>(current) { remaining[i] };
                var nextRemaining = new List<T>(remaining);
                nextRemaining.RemoveAt(i);
                Permute(nextCurrent, nextRemaining);
            }
        }

        Permute(new List<T>(), list);
        return result;
    }

    #endregion

    public VariableState EvaluateVariableAt(SyntaxTree tree, string variableName, int lineNumber)
    {
        var root = tree.GetCompilationUnitRoot();
        var model = _compilation.GetSemanticModel(tree);
        var text = tree.GetText();

        if (lineNumber < 1 || lineNumber > text.Lines.Count)
            return VariableState.Single(new SymbolicValue.UnknownInput(variableName, "Line out of range"));

        var targetStatement = root.DescendantNodes()
            .OfType<StatementSyntax>()
            .Where(s => text.Lines.GetLinePosition(s.SpanStart).Line <= lineNumber - 1)
            .OrderByDescending(s => s.SpanStart)
            .FirstOrDefault();

        if (targetStatement == null)
            return VariableState.Single(new SymbolicValue.UnknownInput(variableName, "Statement not found"));

        var containingMethod = targetStatement.AncestorsAndSelf().OfType<BaseMethodDeclarationSyntax>().FirstOrDefault();
        if (containingMethod == null)
            return VariableState.Single(new SymbolicValue.UnknownInput(variableName, "Outside method scope"));

        var containingType = containingMethod.AncestorsAndSelf().OfType<TypeDeclarationSyntax>().FirstOrDefault();
        INamedTypeSymbol? currentTypeSymbol = containingType != null 
            ? model.GetDeclaredSymbol(containingType) as INamedTypeSymbol 
            : null;

        var flowState = AnalyzeMethod(containingMethod, model, targetStatement, new Dictionary<string, VariableState>(_staticHeap), currentTypeSymbol);

        return flowState.TryGetValue(variableName, out var state) 
            ? state 
            : VariableState.Single(new SymbolicValue.UnknownInput(variableName, "Unresolved / out of scope"));
    }

    private Dictionary<string, VariableState> AnalyzeMethod(
        BaseMethodDeclarationSyntax method, 
        SemanticModel model, 
        SyntaxNode? targetNode,
        Dictionary<string, VariableState> staticScope,
        INamedTypeSymbol? enclosingType)
    {
        var state = new Dictionary<string, VariableState>
        {
            ["$return"] = VariableState.Empty
        };

        if (method.ParameterList != null)
        {
            foreach (var param in method.ParameterList.Parameters)
            {
                var paramName = param.Identifier.Text;
                state[paramName] = VariableState.Single(new SymbolicValue.UnknownInput(paramName, "Method Parameter"));
            }
        }

        if (method.Body != null)
        {
            AnalyzeBlock(method.Body, state, model, targetNode, staticScope, enclosingType);
        }
        else if (method.ExpressionBody != null)
        {
            state["$return"] = EvaluateExpression(method.ExpressionBody.Expression, state, model, staticScope, enclosingType);
        }

        return state;
    }

    private bool AnalyzeBlock(
        BlockSyntax block, 
        Dictionary<string, VariableState> state, 
        SemanticModel model, 
        SyntaxNode? targetNode,
        Dictionary<string, VariableState> staticScope,
        INamedTypeSymbol? enclosingType)
    {
        foreach (var statement in block.Statements)
        {
            bool reachedTarget = targetNode != null && statement == targetNode;

            AnalyzeStatement(statement, state, model, targetNode, staticScope, enclosingType);

            if (reachedTarget)
                return true;

            if (state.ContainsKey("$terminated"))
                break;
        }
        return false;
    }

    private void AnalyzeStatement(
        StatementSyntax stmt, 
        Dictionary<string, VariableState> state, 
        SemanticModel model, 
        SyntaxNode? targetNode,
        Dictionary<string, VariableState> staticScope,
        INamedTypeSymbol? enclosingType)
    {
        switch (stmt)
        {
            case LocalDeclarationStatementSyntax decl:
                foreach (var variable in decl.Declaration.Variables)
                {
                    var varName = variable.Identifier.Text;
                    state[varName] = variable.Initializer != null 
                        ? EvaluateExpression(variable.Initializer.Value, state, model, staticScope, enclosingType) 
                        : VariableState.Single(new SymbolicValue.Constant(0));
                }
                break;

            case ExpressionStatementSyntax exprStmt when exprStmt.Expression is AssignmentExpressionSyntax assign:
                var assignedValue = EvaluateExpression(assign.Right, state, model, staticScope, enclosingType);
                
                var leftSymbol = model.GetSymbolInfo(assign.Left).Symbol;
                if (leftSymbol is IFieldSymbol { IsStatic: true } staticField)
                {
                    string key = $"{staticField.ContainingType.ToDisplayString()}.{staticField.Name}";
                    staticScope[key] = assignedValue;
                    if (_staticHeap.ContainsKey(key))
                        _staticHeap[key] = _staticHeap[key].Union(assignedValue);
                    else
                        _staticHeap[key] = assignedValue;
                }
                else
                {
                    state[assign.Left.ToString()] = assignedValue;
                }
                break;

            case ReturnStatementSyntax ret when ret.Expression != null:
                var retVal = EvaluateExpression(ret.Expression, state, model, staticScope, enclosingType);
                state["$return"] = state["$return"].Union(retVal);
                state["$terminated"] = VariableState.Empty;
                break;

            case IfStatementSyntax ifStmt:
                var trueState = new Dictionary<string, VariableState>(state);
                var falseState = new Dictionary<string, VariableState>(state);

                if (ifStmt.Statement is BlockSyntax trueBlock)
                    AnalyzeBlock(trueBlock, trueState, model, targetNode, staticScope, enclosingType);
                else
                    AnalyzeStatement(ifStmt.Statement, trueState, model, targetNode, staticScope, enclosingType);

                if (ifStmt.Else != null)
                {
                    if (ifStmt.Else.Statement is BlockSyntax elseBlock)
                        AnalyzeBlock(elseBlock, falseState, model, targetNode, staticScope, enclosingType);
                    else
                        AnalyzeStatement(ifStmt.Else.Statement, falseState, model, targetNode, staticScope, enclosingType);
                }

                bool bothTerminated = trueState.ContainsKey("$terminated") && falseState.ContainsKey("$terminated");

                var allKeys = trueState.Keys.Union(falseState.Keys).Where(k => k != "$terminated").ToList();
                foreach (var key in allKeys)
                {
                    trueState.TryGetValue(key, out var tVal);
                    falseState.TryGetValue(key, out var fVal);

                    tVal ??= VariableState.Empty;
                    fVal ??= VariableState.Empty;

                    state[key] = tVal.Union(fVal);
                }

                if (bothTerminated)
                    state["$terminated"] = VariableState.Empty;
                else
                    state.Remove("$terminated");

                break;
        }
    }

    private VariableState EvaluateExpression(
        ExpressionSyntax expr, 
        Dictionary<string, VariableState> env, 
        SemanticModel model,
        Dictionary<string, VariableState> staticScope,
        INamedTypeSymbol? enclosingType = null)
    {
        var constantOpt = model.GetConstantValue(expr);
        if (constantOpt.HasValue && constantOpt.Value != null)
        {
            return VariableState.Single(new SymbolicValue.Constant(constantOpt.Value));
        }

        switch (expr)
        {
            case LiteralExpressionSyntax lit:
                return VariableState.Single(new SymbolicValue.Constant(lit.Token.Value));

            case ParenthesizedExpressionSyntax paren:
                return EvaluateExpression(paren.Expression, env, model, staticScope, enclosingType);

            case ConditionalExpressionSyntax cond:
                var condVals = EvaluateExpression(cond.Condition, env, model, staticScope, enclosingType);
                var whenTrue = EvaluateExpression(cond.WhenTrue, env, model, staticScope, enclosingType);
                var whenFalse = EvaluateExpression(cond.WhenFalse, env, model, staticScope, enclosingType);

                bool hasTrue = condVals.PossibleValues.Any(v => v is SymbolicValue.Constant { Value: true });
                bool hasFalse = condVals.PossibleValues.Any(v => v is SymbolicValue.Constant { Value: false });

                if (hasTrue && !hasFalse) return whenTrue;
                if (!hasTrue && hasFalse) return whenFalse;
                return whenTrue.Union(whenFalse);

            case CastExpressionSyntax cast:
                return EvaluateExpression(cast.Expression, env, model, staticScope, enclosingType);

            case IdentifierNameSyntax id:
                var name = id.Identifier.Text;
                if (env.TryGetValue(name, out var localVal))
                    return localVal;

                var symbol = model.GetSymbolInfo(id).Symbol;
                if (symbol is IFieldSymbol { IsStatic: true } field)
                {
                    string key = $"{field.ContainingType.ToDisplayString()}.{field.Name}";
                    if (staticScope.TryGetValue(key, out var staticVal)) return staticVal;
                    if (_staticHeap.TryGetValue(key, out var heapVal)) return heapVal;
                }
                if (symbol is ILocalSymbol localSym && localSym.HasConstantValue)
                {
                    return VariableState.Single(new SymbolicValue.Constant(localSym.ConstantValue));
                }

                return VariableState.Single(new SymbolicValue.UnknownInput(name, "Unbound identifier"));

            case MemberAccessExpressionSyntax memberAccess:
                var memberSymbol = model.GetSymbolInfo(memberAccess).Symbol;
                if (memberSymbol is IFieldSymbol { IsStatic: true } sField)
                {
                    string key = $"{sField.ContainingType.ToDisplayString()}.{sField.Name}";
                    if (staticScope.TryGetValue(key, out var val)) return val;
                    if (_staticHeap.TryGetValue(key, out var heapVal)) return heapVal;
                }
                if (memberSymbol is IPropertySymbol { IsStatic: true } sProp)
                {
                    string key = $"{sProp.ContainingType.ToDisplayString()}.{sProp.Name}";
                    if (staticScope.TryGetValue(key, out var val)) return val;
                    if (_staticHeap.TryGetValue(key, out var heapVal)) return heapVal;
                }

                return VariableState.Single(new SymbolicValue.UnknownInput(memberAccess.ToString(), "External/Unresolved Member"));

            case BinaryExpressionSyntax bin:
                var leftVals = EvaluateExpression(bin.Left, env, model, staticScope, enclosingType);
                var rightVals = EvaluateExpression(bin.Right, env, model, staticScope, enclosingType);
                return ComputeBinaryOp(bin.OperatorToken.Text, leftVals, rightVals);

            case InvocationExpressionSyntax inv:
                var invokedSymbol = model.GetSymbolInfo(inv).Symbol as IMethodSymbol;
                if (invokedSymbol != null && 
                    invokedSymbol.ContainingType.SpecialType == SpecialType.System_String && 
                    invokedSymbol.Name == "Format" &&
                    inv.ArgumentList.Arguments.Count >= 2)
                {
                    return EvaluateStringFormatInvocation(inv, env, model, staticScope, enclosingType);
                }

                return ResolveInvocation(inv, env, model, staticScope);

            case InterpolatedStringExpressionSyntax interpolated:
                return EvaluateInterpolatedString(interpolated, env, model, staticScope, enclosingType);

            default:
                return VariableState.Single(new SymbolicValue.UnknownInput(expr.ToString(), "Expression"));
        }
    }

    private VariableState EvaluateInterpolatedString(
        InterpolatedStringExpressionSyntax interpolated,
        Dictionary<string, VariableState> env,
        SemanticModel model,
        Dictionary<string, VariableState> staticScope,
        INamedTypeSymbol? enclosingType)
    {
        var slicesPossibilities = new List<List<(string Rendered, bool IsSymbolic)>>();

        foreach (var content in interpolated.Contents)
        {
            switch (content)
            {
                case InterpolatedStringTextSyntax textSyntax:
                    slicesPossibilities.Add(new List<(string, bool)> 
                    { 
                        (textSyntax.TextToken.ValueText, false) 
                    });
                    break;

                case InterpolationSyntax hole:
                    var holeValues = EvaluateExpression(hole.Expression, env, model, staticScope, enclosingType);
                    var holeOptions = new List<(string Rendered, bool IsSymbolic)>();

                    string? formatString = hole.FormatClause?.FormatStringToken.ValueText;
                    int? alignment = null;
                    if (hole.AlignmentClause?.Value is LiteralExpressionSyntax { Token.Value: int alignVal })
                    {
                        alignment = alignVal;
                    }

                    foreach (var val in holeValues.PossibleValues)
                    {
                        if (val is SymbolicValue.Constant c && c.Value != null)
                        {
                            try
                            {
                                string formatted;
                                if (!string.IsNullOrEmpty(formatString))
                                {
                                    formatted = string.Format(CultureInfo.InvariantCulture, $"{{0:{formatString}}}", c.Value);
                                }
                                else
                                {
                                    formatted = c.Value.ToString() ?? "";
                                }

                                if (alignment.HasValue)
                                {
                                    formatted = string.Format(CultureInfo.InvariantCulture, $"{{0,{alignment.Value}}}", formatted);
                                }

                                holeOptions.Add((formatted, false));
                            }
                            catch
                            {
                                holeOptions.Add((c.Value.ToString() ?? "", false));
                            }
                        }
                        else
                        {
                            string repr = val.ToString() ?? "?";
                            if (!string.IsNullOrEmpty(formatString))
                                repr = $"{{{repr}:{formatString}}}";
                            else
                                repr = $"{{{repr}}}";

                            holeOptions.Add((repr, true));
                        }
                    }

                    if (holeOptions.Count == 0)
                    {
                        holeOptions.Add(("{<?>}", true));
                    }

                    slicesPossibilities.Add(holeOptions);
                    break;
            }
        }

        var combinations = CartesianProduct(slicesPossibilities);
        var results = ImmutableHashSet.CreateBuilder<SymbolicValue>();

        foreach (var combination in combinations)
        {
            bool hasAnySymbolic = combination.Any(c => c.IsSymbolic);
            string fullString = string.Concat(combination.Select(c => c.Rendered));

            if (hasAnySymbolic)
            {
                results.Add(new SymbolicValue.UnknownInput($"$\"{fullString}\"", "Interpolated Template"));
            }
            else
            {
                results.Add(new SymbolicValue.Constant(fullString));
            }
        }

        return new VariableState { PossibleValues = results.ToImmutable() };
    }

    private VariableState EvaluateStringFormatInvocation(
        InvocationExpressionSyntax inv,
        Dictionary<string, VariableState> env,
        SemanticModel model,
        Dictionary<string, VariableState> staticScope,
        INamedTypeSymbol? enclosingType)
    {
        var args = inv.ArgumentList.Arguments;
        int formatIndex = 0;

        var firstArgType = model.GetTypeInfo(args[0].Expression).Type;
        if (firstArgType != null && firstArgType.AllInterfaces.Any(i => i.Name == "IFormatProvider"))
        {
            formatIndex = 1;
        }

        if (args.Count <= formatIndex)
            return VariableState.Single(new SymbolicValue.UnknownInput(inv.ToString(), "Invalid string.Format invocation"));

        var formatPatternValues = EvaluateExpression(args[formatIndex].Expression, env, model, staticScope, enclosingType);

        var argValuesList = new List<VariableState>();
        for (int i = formatIndex + 1; i < args.Count; i++)
        {
            argValuesList.Add(EvaluateExpression(args[i].Expression, env, model, staticScope, enclosingType));
        }

        var results = ImmutableHashSet.CreateBuilder<SymbolicValue>();

        foreach (var patternVal in formatPatternValues.PossibleValues)
        {
            if (patternVal is SymbolicValue.Constant { Value: string formatPattern })
            {
                var argPermutations = CartesianProduct(argValuesList.Select(a => a.PossibleValues.ToList()).ToList());

                foreach (var argPerm in argPermutations)
                {
                    bool allConstants = argPerm.All(p => p is SymbolicValue.Constant);
                    if (allConstants)
                    {
                        var rawArgs = argPerm.Select(p => ((SymbolicValue.Constant)p).Value).ToArray();
                        try
                        {
                            string formatted = string.Format(CultureInfo.InvariantCulture, formatPattern, rawArgs);
                            results.Add(new SymbolicValue.Constant(formatted));
                        }
                        catch
                        {
                            results.Add(new SymbolicValue.UnknownInput($"string.Format(\"{formatPattern}\")", "Format error"));
                        }
                    }
                    else
                    {
                        results.Add(new SymbolicValue.UnknownInput($"string.Format(\"{formatPattern}\", {string.Join(", ", argPerm)})", "Parameterized Format"));
                    }
                }
            }
            else
            {
                results.Add(new SymbolicValue.UnknownInput(inv.ToString(), "Dynamic format string"));
            }
        }

        return new VariableState { PossibleValues = results.ToImmutable() };
    }

    private static List<List<T>> CartesianProduct<T>(List<List<T>> sequences)
    {
        var result = new List<List<T>> { new() };

        foreach (var sequence in sequences)
        {
            var next = new List<List<T>>();
            foreach (var acc in result)
            {
                foreach (var item in sequence)
                {
                    var clone = new List<T>(acc) { item };
                    next.Add(clone);
                }
            }
            result = next;
        }

        return result;
    }

    private VariableState ResolveInvocation(
        InvocationExpressionSyntax inv, 
        Dictionary<string, VariableState> env, 
        SemanticModel model,
        Dictionary<string, VariableState> staticScope)
    {
        var symbolInfo = model.GetSymbolInfo(inv);
        var targetMethod = symbolInfo.Symbol as IMethodSymbol 
            ?? symbolInfo.CandidateSymbols.OfType<IMethodSymbol>().FirstOrDefault();

        if (targetMethod == null)
            return VariableState.Single(new SymbolicValue.UnknownInput(inv.ToString(), "Unresolvable invocation"));

        var candidates = ResolveImplementationCandidates(targetMethod);

        if (candidates.Count == 0)
        {
            return VariableState.Single(new SymbolicValue.UnknownInput(
                $"{targetMethod.ContainingType?.Name}.{targetMethod.Name}()", 
                "External or Abstract with no source implementations"));
        }

        var aggregatedResult = VariableState.Empty;

        foreach (var candidate in candidates)
        {
            var syntaxRef = candidate.DeclaringSyntaxReferences.FirstOrDefault();
            if (syntaxRef == null || _callStack.Contains(candidate))
            {
                var fallback = new SymbolicValue.UnknownInput(
                    $"{candidate.ContainingType.Name}.{candidate.Name}()", 
                    syntaxRef == null ? "External Library" : "Recursion Boundary");
                aggregatedResult = aggregatedResult.Union(VariableState.Single(fallback));
                continue;
            }

            if (syntaxRef.GetSyntax() is BaseMethodDeclarationSyntax calleeDecl)
            {
                _callStack.Add(candidate);
                var calleeModel = _compilation.GetSemanticModel(calleeDecl.SyntaxTree);

                var calleeResult = AnalyzeMethod(calleeDecl, calleeModel, null, staticScope, candidate.ContainingType);
                _callStack.Remove(candidate);

                if (calleeResult.TryGetValue("$return", out var retState) && retState.PossibleValues.Count > 0)
                {
                    aggregatedResult = aggregatedResult.Union(retState);
                }
            }
        }

        return aggregatedResult.PossibleValues.Count > 0 
            ? aggregatedResult 
            : VariableState.Single(new SymbolicValue.UnknownInput(inv.ToString(), "No return value captured"));
    }

    /// <summary>
    /// Exhaustively locates all concrete implementations of an interface method, 
    /// handling open/constructed generics, explicit implementations, inherited interfaces,
    /// abstract base intermediaries, and loose signature duck-matching.
    /// </summary>
    private List<IMethodSymbol> ResolveImplementationCandidates(IMethodSymbol targetMethod)
    {
        var results = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        var containingType = targetMethod.ContainingType;

        if (containingType == null)
            return results.ToList();

        // CASE 1: Interface Call
        if (containingType.TypeKind == TypeKind.Interface)
        {
            var targetOriginalInterface = containingType.OriginalDefinition;
            var targetOriginalMethod = targetMethod.OriginalDefinition;

            foreach (var type in _allConcreteTypes)
            {
                // 1a. Standard Roslyn Interface Member mapping (handling constructed generics)
                foreach (var iface in type.AllInterfaces)
                {
                    if (SymbolEqualityComparer.Default.Equals(iface, containingType) ||
                        SymbolEqualityComparer.Default.Equals(iface.OriginalDefinition, targetOriginalInterface))
                    {
                        var impl = type.FindImplementationForInterfaceMember(targetMethod) as IMethodSymbol
                                ?? type.FindImplementationForInterfaceMember(targetOriginalMethod) as IMethodSymbol;

                        if (impl != null)
                        {
                            AddResolvedMethodAndOverrides(impl, results);
                        }
                    }
                }

                // 1b. Fallback: Explicit or Implicit name & signature matching across all methods on the type
                // Catches cases where Roslyn generic type substitution fails to map cleanly
                foreach (var member in type.GetMembers().OfType<IMethodSymbol>())
                {
                    if (member.IsAbstract) continue;

                    // Explicit interface member check:
                    if (member.ExplicitInterfaceImplementations.Any(e => 
                        SymbolEqualityComparer.Default.Equals(e, targetMethod) || 
                        SymbolEqualityComparer.Default.Equals(e.OriginalDefinition, targetOriginalMethod)))
                    {
                        AddResolvedMethodAndOverrides(member, results);
                        continue;
                    }

                    // Duck-typing / implicit match on name, parameter count, and generic arity:
                    if (member.Name == targetMethod.Name && 
                        member.Parameters.Length == targetMethod.Parameters.Length &&
                        member.Arity == targetMethod.Arity)
                    {
                        // Verify that the type actually implements this interface somewhere in its hierarchy
                        bool implementsTarget = type.AllInterfaces.Any(i => 
                            SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, targetOriginalInterface) ||
                            i.Name == containingType.Name);

                        if (implementsTarget)
                        {
                            AddResolvedMethodAndOverrides(member, results);
                        }
                    }
                }
            }

            return results.ToList();
        }

        // CASE 2: Abstract or Virtual Method Call (trace down inheritance tree)
        if (targetMethod.IsAbstract || targetMethod.IsVirtual)
        {
            AddResolvedMethodAndOverrides(targetMethod, results);
            return results.ToList();
        }

        // CASE 3: Direct concrete method
        results.Add(targetMethod);
        return results.ToList();
    }

    /// <summary>
    /// If a candidate implementation is virtual or abstract (e.g., declared on an intermediate base class),
    /// this recursively collects all concrete derived overrides across the entire solution.
    /// </summary>
    private void AddResolvedMethodAndOverrides(IMethodSymbol method, HashSet<IMethodSymbol> bucket)
    {
        if (!method.IsAbstract)
        {
            bucket.Add(method);
        }

        if (!method.IsVirtual && !method.IsAbstract && !method.IsOverride)
            return;

        var declType = method.ContainingType;

        foreach (var subType in _allConcreteTypes)
        {
            if (SymbolEqualityComparer.Default.Equals(subType, declType))
                continue;

            // Check if subType derives from declType
            var curr = subType.BaseType;
            while (curr != null)
            {
                if (SymbolEqualityComparer.Default.Equals(curr.OriginalDefinition, declType.OriginalDefinition))
                {
                    var matchingOverride = subType.GetMembers(method.Name)
                        .OfType<IMethodSymbol>()
                        .FirstOrDefault(m => m.IsOverride && 
                                             (SymbolEqualityComparer.Default.Equals(m.OverriddenMethod, method) || 
                                              SymbolEqualityComparer.Default.Equals(m.OverriddenMethod?.OriginalDefinition, method.OriginalDefinition)));

                    if (matchingOverride != null && !matchingOverride.IsAbstract)
                    {
                        bucket.Add(matchingOverride);
                    }
                    break;
                }
                curr = curr.BaseType;
            }
        }
    }

    private VariableState ComputeBinaryOp(string op, VariableState left, VariableState right)
    {
        var results = ImmutableHashSet.CreateBuilder<SymbolicValue>();

        foreach (var l in left.PossibleValues)
        {
            foreach (var r in right.PossibleValues)
            {
                if (l is SymbolicValue.Constant { Value: int lInt } && r is SymbolicValue.Constant { Value: int rInt })
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
                else if (op == "+" && (l is SymbolicValue.Constant { Value: string } || r is SymbolicValue.Constant { Value: string }))
                {
                    if (l is SymbolicValue.Constant lc && r is SymbolicValue.Constant rc)
                    {
                        results.Add(new SymbolicValue.Constant($"{lc.Value}{rc.Value}"));
                    }
                    else
                    {
                        results.Add(new SymbolicValue.SymbolicExpression(op, ImmutableList.Create(l, r)));
                    }
                }
                else
                {
                    results.Add(new SymbolicValue.SymbolicExpression(op, ImmutableList.Create(l, r)));
                }
            }
        }

        return new VariableState { PossibleValues = results.ToImmutable() };
    }
}

#endregion

#region CLI & File Crawler

public static class Program
{
    public static void Main(string[] args)
    {
        if (args.Length == 0 || args[0] is "-h" or "--help")
        {
            Console.WriteLine("Usage:");
            Console.WriteLine("  Batch scan folder:   dotnet run -- <folder_path>");
            Console.WriteLine("  Query specific var:  dotnet run -- <folder_path> <file_name> <line_number> <var_name>");
            return;
        }

        string rootDir = Path.GetFullPath(args[0]);
        if (!Directory.Exists(rootDir))
        {
            Console.ForegroundColor = ConsoleColor.Red;
            Console.WriteLine($"Error: Target directory does not exist: {rootDir}");
            Console.ResetColor();
            return;
        }

        Console.WriteLine($"[+] Scanning: {rootDir}");

        var csFiles = Directory.EnumerateFiles(rootDir, "*.cs", SearchOption.AllDirectories)
            .Where(p => !p.Split(Path.DirectorySeparatorChar)
                          .Any(seg => seg.Equals("bin", StringComparison.OrdinalIgnoreCase) || 
                                     seg.Equals("obj", StringComparison.OrdinalIgnoreCase) || 
                                     seg.Equals(".git", StringComparison.OrdinalIgnoreCase)))
            .ToList();

        if (csFiles.Count == 0)
        {
            Console.WriteLine("No .cs files found.");
            return;
        }

        Console.WriteLine($"[+] Found {csFiles.Count} source files. Parsing syntax trees...");

        var parseOptions = new CSharpParseOptions(LanguageVersion.Latest);
        var syntaxTrees = csFiles.Select(file =>
        {
            var code = File.ReadAllText(file);
            return CSharpSyntaxTree.ParseText(code, parseOptions, path: file);
        }).ToList();

        var references = LoadTrustedPlatformReferences();

        var compilation = CSharpCompilation.Create(
            assemblyName: "StaticScanCompilation",
            syntaxTrees: syntaxTrees,
            references: references,
            options: new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)
        );

        Console.WriteLine("[+] Computing static class initialization permutations and dependency graph...");
        var analyzer = new FolderValueTracker(compilation);

        // MODE 1: Targeted Query
        if (args.Length >= 4)
        {
            string targetFileFilter = args[1];
            int targetLine = int.Parse(args[2]);
            string targetVar = args[3];

            var matchedTree = syntaxTrees.FirstOrDefault(t => 
                t.FilePath.EndsWith(targetFileFilter, StringComparison.OrdinalIgnoreCase) || 
                Path.GetFileName(t.FilePath).Equals(targetFileFilter, StringComparison.OrdinalIgnoreCase));

            if (matchedTree == null)
            {
                Console.WriteLine($"[!] Could not locate file matching '{targetFileFilter}'.");
                return;
            }

            Console.WriteLine($"\n[>] Evaluating '{targetVar}' in {Path.GetFileName(matchedTree.FilePath)} at line {targetLine}:");
            var result = analyzer.EvaluateVariableAt(matchedTree, targetVar, targetLine);
            Console.WriteLine($"Result: {result}\n");
            return;
        }

        // MODE 2: Comprehensive Batch Scan
        Console.WriteLine("\n=== Exhaustive Variable Scan ===");
        foreach (var tree in syntaxTrees)
        {
            var root = tree.GetCompilationUnitRoot();
            var text = tree.GetText();
            var localDecls = root.DescendantNodes().OfType<LocalDeclarationStatementSyntax>().ToList();

            if (localDecls.Count == 0) continue;

            string relPath = Path.GetRelativePath(rootDir, tree.FilePath);
            Console.WriteLine($"\nFile: {relPath}");

            foreach (var decl in localDecls)
            {
                int line = text.Lines.GetLinePosition(decl.SpanStart).Line + 1;
                foreach (var v in decl.Declaration.Variables)
                {
                    string name = v.Identifier.Text;
                    var result = analyzer.EvaluateVariableAt(tree, name, line);
                    Console.WriteLine($"  Line {line,4} | {name,-16} => {result}");
                }
            }
        }
    }

    private static List<MetadataReference> LoadTrustedPlatformReferences()
    {
        var references = new List<MetadataReference>();
        var trustedAssemblies = AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") as string;

        if (!string.IsNullOrEmpty(trustedAssemblies))
        {
            foreach (var path in trustedAssemblies.Split(Path.PathSeparator))
            {
                if (File.Exists(path))
                    references.Add(MetadataReference.CreateFromFile(path));
            }
        }
        else
        {
            references.Add(MetadataReference.CreateFromFile(typeof(object).Assembly.Location));
        }

        return references;
    }
}

#endregion
