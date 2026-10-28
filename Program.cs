using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace ValueFlowAnalyzer;

public static class Program
{
    public static void Main(string[] args)
    {
        // Example CLI: 
        // dotnet run -- <source-directory> [relative-file-path] [line-number] [variable-name]
        string sourceDirectory = args.Length > 0 ? args[0] : @"./MyProjectSource";

        if (!Directory.Exists(sourceDirectory))
        {
            Console.ForegroundColor = ConsoleColor.Red;
            Console.WriteLine($"Error: Directory not found: {sourceDirectory}");
            Console.ResetColor();
            return;
        }

        Console.WriteLine($"[+] Scanning directory: {Path.GetFullPath(sourceDirectory)}");

        // 1. Collect all C# files recursively, ignoring build output
        var csFiles = Directory.EnumerateFiles(sourceDirectory, "*.cs", SearchOption.AllDirectories)
            .Where(path => !path.Contains($"{Path.DirectorySeparatorChar}bin{Path.DirectorySeparatorChar}") &&
                           !path.Contains($"{Path.DirectorySeparatorChar}obj{Path.DirectorySeparatorChar}") &&
                           !path.Contains($"{Path.DirectorySeparatorChar}.git{Path.DirectorySeparatorChar}"))
            .ToList();

        if (csFiles.Count == 0)
        {
            Console.WriteLine("No .cs files found to analyze.");
            return;
        }

        Console.WriteLine($"[+] Found {csFiles.Count} source file(s). Parsing syntax trees...");

        // 2. Parse all files into SyntaxTrees with persistent file paths
        var parseOptions = new CSharpParseOptions(LanguageVersion.Latest);
        var syntaxTrees = csFiles.Select(file =>
        {
            var code = File.ReadAllText(file);
            return CSharpSyntaxTree.ParseText(code, parseOptions, path: Path.GetFullPath(file));
        }).ToList();

        // 3. Collect Runtime Metadata References from the running host
        var metadataReferences = GetRuntimeMetadataReferences();

        // 4. Create single unified Compilation containing all files
        var compilation = CSharpCompilation.Create(
            assemblyName: "BatchSourceAnalysis",
            syntaxTrees: syntaxTrees,
            references: metadataReferences,
            options: new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)
        );

        var analyzer = new IntraproceduralValueTracker(compilation);

        // MODE A: Targeted query via CLI args
        if (args.Length >= 4)
        {
            string targetRelFile = args[1];
            int lineNumber = int.Parse(args[2]);
            string varName = args[3];

            var targetTree = syntaxTrees.FirstOrDefault(t => 
                t.FilePath.EndsWith(targetRelFile, StringComparison.OrdinalIgnoreCase));

            if (targetTree == null)
            {
                Console.WriteLine($"Could not locate file matching '{targetRelFile}'");
                return;
            }

            Console.WriteLine($"\n[>] Querying '{varName}' in {Path.GetFileName(targetTree.FilePath)} at line {lineNumber}:");
            var result = analyzer.EvaluateVariableAt(targetTree, varName, lineNumber);
            Console.WriteLine($"Possible values: {result}\n");
            return;
        }

        // MODE B: Scan & evaluate all local declarations in all discovered files
        Console.WriteLine("\n=== Batch Evaluating Local Variables Across Codebase ===");
        foreach (var tree in syntaxTrees)
        {
            var root = tree.GetCompilationUnitRoot();
            var text = tree.GetText();
            var localDecls = root.DescendantNodes().OfType<LocalDeclarationStatementSyntax>().ToList();

            if (localDecls.Count == 0) continue;

            string relPath = Path.GetRelativePath(sourceDirectory, tree.FilePath);
            Console.WriteLine($"\nFile: {relPath}");

            foreach (var decl in localDecls)
            {
                int line = text.Lines.GetLinePosition(decl.SpanStart).Line + 1;
                foreach (var v in decl.Declaration.Variables)
                {
                    string name = v.Identifier.Text;
                    var result = analyzer.EvaluateVariableAt(tree, name, line);
                    Console.WriteLine($"  Line {line,4} | {name,-18} => {result}");
                }
            }
        }
    }

    /// <summary>
    /// Loads runtime metadata references so BCL types (System, Linq, etc.) resolve.
    /// </summary>
    private static List<MetadataReference> GetRuntimeMetadataReferences()
    {
        var references = new List<MetadataReference>();

        // Resolves all trusted platform assemblies loaded by the current .NET runtime
        var trustedAssembliesPaths = AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") as string;
        if (!string.IsNullOrEmpty(trustedAssembliesPaths))
        {
            var paths = trustedAssembliesPaths.Split(Path.PathSeparator);
            foreach (var path in paths)
            {
                if (File.Exists(path))
                {
                    references.Add(MetadataReference.CreateFromFile(path));
                }
            }
        }
        else
        {
            // Fallback: minimal corelib reference
            references.Add(MetadataReference.CreateFromFile(typeof(object).Assembly.Location));
        }

        return references;
    }
}
