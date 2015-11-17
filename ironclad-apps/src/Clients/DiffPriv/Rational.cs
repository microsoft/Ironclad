using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace DiffPriv
{
    public class Rational
    {
        public UInt32 num;
        public UInt32 den;

        public Rational(UInt32 i_num, UInt32 i_den)
        {
            num = i_num;
            den = i_den;
        }

        public Rational(UInt32 value)
        {
            num = value;
            den = 1;
        }

        public double Value { get { return num * 1.0 / den; } }
    }
}
