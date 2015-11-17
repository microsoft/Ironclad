using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Web.UI.DataVisualization.Charting;

namespace Common
{
    public class Aggregator
    {
        private static Chart chart;
        private string name;
        private bool times;
        private long total;
        private int count;
        private double sumsq;

        public static void Initialize()
        {
            chart = new Chart();
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
            if (CommonParams.printValues)
            {
                Console.WriteLine("{0}\t{1}", name, value * 1.0 / Stopwatch.Frequency);
            }

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
                double conf95 = stdev * chart.DataManipulator.Statistics.InverseTDistribution(0.05, count-1) / Math.Sqrt(count);
                return string.Format("{0}: avg_sec {1} conf95plusorminus {2} stdev {3}", name, average_sec, conf95, stdev);
            }
            else
            {
                if (count == 1) { return total.ToString(); }
                double average = total * 1.0 / count;
                double variance = (sumsq - (total * 1.0 * total) / count) / (count - 1);
                double stdev = Math.Sqrt(variance);
                double conf95 = stdev * chart.DataManipulator.Statistics.InverseTDistribution(0.05, count-1) / Math.Sqrt(count);
                return string.Format("{0}: avg {1} conf95plusorminus {2} stdev {3}", name, average, conf95, stdev);
            }
        }
    }

    public class Profiler
    {
        static Dictionary<string, Aggregator> aggregators;

        public static void Initialize()
        {
            aggregators = new Dictionary<string, Aggregator>();
            Aggregator.Initialize();
        }

        public static void Record(string name, long value)
        {
            if (!aggregators.ContainsKey(name))
            {
                aggregators[name] = new Aggregator(name, false);
            }

            aggregators[name].AddValue(value);
        }

        public static void Record(string name, Stopwatch stopwatch)
        {
            if (!aggregators.ContainsKey(name))
            {
                aggregators[name] = new Aggregator(name, true);
            }

            aggregators[name].AddValue(stopwatch.ElapsedTicks);
        }

        public static void Print()
        {
            foreach (KeyValuePair<string, Aggregator> entry in aggregators)
            {
                Console.WriteLine(entry.Value.ToString());
            }
        }
    }
}
