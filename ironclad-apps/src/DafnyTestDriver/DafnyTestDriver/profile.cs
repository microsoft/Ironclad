using System;
using System.IO;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;

public class Profiler
{
    Dictionary<int, string> labels;
    Dictionary<int, int> profileMap;
    Stopwatch stopwatch;
    StreamWriter tw;

    public Profiler(StreamWriter tw)
    {
        this.tw = tw;
        labels = new Dictionary<int, string>();
        labels[1] = "TestDigits";
        labels[2] = "BigNatSub";
        labels[3] = "BigNatModExpCalls";
        labels[4] = "BigNatModExpWhileLoops";
        labels[5] = "BigNatDivCalls";
        labels[6] = "BigNatDivWhileLoops";
        labels[1000] = "Add";
        labels[1001] = "Sub";
        labels[1002] = "method_Mul";
        labels[1003] = "Mul64";
        labels[1004] = "Mul";
        labels[1005] = "Div";
        labels[1006] = "Mod";
        ResetTally();
    }
    public void ResetTally()
    {
        profileMap = new Dictionary<int, int>();
        stopwatch = new Stopwatch();
        stopwatch.Start();
    }
    public void ProfileTally(int category, int value)
    {
        if (!profileMap.ContainsKey(category))
        {
            profileMap[category] = 0;
        }
        profileMap[category] += value;
    }
    public void DisplayTally()
    {
        stopwatch.Stop();
        TimeSpan elapsed = stopwatch.Elapsed;
        foreach (int key in profileMap.Keys)
        {
            tw.WriteLine(
                String.Format("{0}: {1}", labels[key], profileMap[key]));
        }
        tw.WriteLine("ElapsedTime: " + elapsed);
        tw.WriteLine();
        tw.FlushAsync();
    }

}

public partial class @__default
{
    static Profiler profiler = new Profiler(new StreamWriter("profiler.txt"));
    public static void ResetTally()
    {
        profiler.ResetTally();
    }
    public static void ProfileTally(BigInteger _category, BigInteger _value)
    {
        profiler.ProfileTally((int) _category, (int) _value);
    }
    public static void DisplayTally()
    {
        profiler.DisplayTally();
    }
}

