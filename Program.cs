public static class Verification
{
    public static void Main()
    {
        var testCode = """
        public interface IDiscountPolicy
        {
            int GetBaseRate();
        }

        public class StandardPolicy : IDiscountPolicy
        {
            public int GetBaseRate() => 10;
        }

        public class VipPolicy : IDiscountPolicy
        {
            public int GetBaseRate() => 25;
        }

        public class TieredPolicy : IDiscountPolicy
        {
            public int GetBaseRate()
            {
                bool specialCase = true;
                if (specialCase) return 50;
                return 5;
            }
        }

        public class CheckoutService
        {
            public int CalculateTotal(IDiscountPolicy policy)
            {
                int discount = policy.GetBaseRate();
                int total = discount + 2;
                return total; // Target Line: total
            }
        }
        """;

        var syntaxTree = CSharpSyntaxTree.ParseText(testCode);
        var mscorlib = MetadataReference.CreateFromFile(typeof(object).Assembly.Location);
        var compilation = CSharpCompilation.Create("InterfaceTest", new[] { syntaxTree }, new[] { mscorlib });

        var analyzer = new IntraproceduralValueTracker(compilation);

        Console.WriteLine("Evaluating 'discount' in CalculateTotal:");
        var discountValues = analyzer.EvaluateVariableAt(syntaxTree, "discount", 33);
        Console.WriteLine($" -> {discountValues}");

        Console.WriteLine("\nEvaluating 'total' in CalculateTotal:");
        var totalValues = analyzer.EvaluateVariableAt(syntaxTree, "total", 35);
        Console.WriteLine($" -> {totalValues}");
    }
}
