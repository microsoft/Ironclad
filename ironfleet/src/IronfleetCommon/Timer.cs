using System;
using System.Diagnostics;

namespace IronfleetCommon
{
  public class HiResTimer
  {
    private static Stopwatch _stopWatch = null;

    public static long Ticks
    {
      get
      {
        return _stopWatch.ElapsedTicks;
      }
    }
    public static void Initialize()
    {
      _stopWatch = Stopwatch.StartNew();
    }

    public static long TicksToMilliseconds(long ticks)
    {
      return (long)(ticks * 1000.0 / Stopwatch.Frequency);
    }
  }
}
