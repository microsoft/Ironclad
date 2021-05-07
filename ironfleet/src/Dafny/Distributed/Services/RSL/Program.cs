using IronfleetCommon;
using IronRSL;
using MathNet.Numerics.Distributions;
using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Threading;

namespace IronRSLServer
{
  class Program
  {
    static void Main(string[] args)
    {
      Profiler.Initialize();
      Native____Io__s_Compile.Time.Initialize();
      Console.WriteLine("IronRSL replica of {0} service started.", Service.Name);
      Console.WriteLine("[[READY]]");
      Main__i_Compile.__default._Main();
      Console.WriteLine("[[EXIT]]");
    }
  }
}

namespace AppStateMachine__s_Compile
{
  public partial class AppStateMachine
  {
    Service service;

    internal AppStateMachine(Service i_service)
    {
      service = i_service;
    }

    public static AppStateMachine Initialize()
    {
      return new AppStateMachine(Service.Initialize());
    }

    public static AppStateMachine Deserialize(Dafny.ISequence<byte> state)
    {
      return new AppStateMachine(Service.Deserialize(state.Elements));
    }

    public Dafny.ISequence<byte> Serialize()
    {
      return Dafny.Sequence<byte>.FromArray(service.Serialize());
    }

    public Dafny.ISequence<byte> HandleRequest(Dafny.ISequence<byte> request)
    {
      return Dafny.Sequence<byte>.FromArray(service.HandleRequest(request.Elements));
    }
  }
}
