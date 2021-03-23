using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using MathNet.Numerics.Distributions;

namespace Common
{
    public class Aggregator
    {
        private string name;
        private bool times;
        private long total;
        private int count;
        private double sumsq;

        public static void Initialize()
        {
        }

        public Aggregator(string i_name, bool i_times)
        {
            name = i_name;
            times = i_times;
            total = 0;
            count = 0;
            sumsq = 0;
        }

        public void AddValue(long value)
        {
            //if (CommonParams.printValues)
            //{
            //    Console.WriteLine("{0}\t{1}", name, value * 1.0 / Stopwatch.Frequency);
            //}

            total += value;
            count++;
            sumsq += (value * 1.0 * value);
        }

        public void AddTime(Stopwatch s)
        {
            AddValue(s.ElapsedTicks);
        }

        public override string ToString()
        {
            if (count < 1) { return name + ": <no data>"; }

            if (times)
            {
                double total_sec = total * 1.0 / Stopwatch.Frequency;
                if (count == 1) { return name + ": " + total_sec.ToString(); }
                double average_sec = total_sec / count;
                double sumsq_sec = sumsq / Stopwatch.Frequency / Stopwatch.Frequency;
                double variance = (sumsq_sec - total_sec * total_sec / count) / (count - 1);
                double stdev = Math.Sqrt(variance);
                double conf95 = StudentT.InvCDF(0, stdev, count-1, 0.975) / Math.Sqrt(count);
                return string.Format("Aggregate {0}: avg_usec {1} conf95plusorminus {2} stdev {3} count {4} sum {5}", name, average_sec * Math.Pow(10, 6), conf95 * Math.Pow(10, 6), stdev * Math.Pow(10, 6), count, total_sec * Math.Pow(10, 6));
            }
            else
            {
                if (count == 1) { return total.ToString(); }
                double average = total * 1.0 / count;
                double variance = (sumsq - (total * 1.0 * total) / count) / (count - 1);
                double stdev = Math.Sqrt(variance);
                double conf95 = StudentT.InvCDF(0, stdev, count - 1, 0.975) / Math.Sqrt(count);
                return string.Format("Aggregate {0}: avg_usec {1} conf95plusorminus {2} stdev {3} count {4} sum {5}", name, average * Math.Pow(10, 6), conf95 * Math.Pow(10, 6), stdev * Math.Pow(10, 6), count, total * Math.Pow(10, 6));
            }
        }
    }

    public class Profiler
    {
        static Dictionary<string, Aggregator> aggregators;
        static int count;
        static int ignore_count = 10000;    // Ignore the first ignore_count events to try to stabilize measurements
        static int print_period = 1000000;
        static bool record;

        public static void Initialize()
        {
            aggregators = new Dictionary<string, Aggregator>();
            Aggregator.Initialize();
            count = 0;
            record = false;
        }

        public static void Record(string name, long value)
        {
            if (record) {
              if (!aggregators.ContainsKey(name)) {
                aggregators[name] = new Aggregator(name, true);
              }

              aggregators[name].AddValue(value);
            }

            count++;
            if (count > ignore_count) {
              record = true;
            }
            if (count % print_period == 0) {
                Print();
            }
        }       

        public static void Print()
        {
            Console.WriteLine("Profiler statistics");
            foreach (KeyValuePair<string, Aggregator> entry in aggregators)
            {
                Console.WriteLine(entry.Value.ToString());
            }
        }
    }
}
