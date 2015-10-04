
namespace IronfleetTestDriver
{
    using System;
    using System.Linq;
    using System.Numerics;
    using System.Threading;
    using Common;

    class Program
    {
        static void Main(string[] args)
        {
            Profiler.Initialize();
            @_Native____Io__s.Time.Initialize();
            Console.WriteLine("Test driver started.");
            Console.WriteLine("[[READY]]");
            BigInteger @result;
            @_Main__i.@__default.IronfleetMain(out @result);
        }
    }
}
