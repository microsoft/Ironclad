using IronfleetCommon;
using MathNet.Numerics.Distributions;
using System;
using System.Linq;
using System.Numerics;
using System.Threading;

namespace IronSHTServer
{
  class Program
  {
    static void Main(string[] args)
    {
      Profiler.Initialize();
      Native____Io__s_Compile.Time.Initialize();
      Console.WriteLine("IronFleet program started.");
      Console.WriteLine("[[READY]]");
      Main__i_Compile.__default._Main();
      Console.WriteLine("[[EXIT]]");
    }
  }
}
