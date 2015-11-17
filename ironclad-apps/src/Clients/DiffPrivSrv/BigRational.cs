using System;
using System.Collections.Generic;
using System.Numerics;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace DiffPrivSrv
{
    class BigRational
    {
        private BigInteger numerator;
        private BigInteger denominator;

        public BigRational(BigInteger i_numerator, BigInteger i_denominator)
        {
            numerator = i_numerator;
            denominator = i_denominator;
        }

        public BigRational(int i_numerator, int i_denominator)
        {
            numerator = new BigInteger(i_numerator);
            denominator = new BigInteger(i_denominator);
        }

        public BigRational(int value)
        {
            numerator = new BigInteger(value);
            denominator = new BigInteger(1);
        }

        public BigRational(BigInteger value)
        {
            numerator = value;
            denominator = new BigInteger(1);
        }

        public bool IsNegative()
        {
            return (numerator < 0 && denominator > 0) || (numerator > 0 && denominator < 0);
        }

        public bool IsZero()
        {
            return numerator == 0;
        }

        public bool IsPositive()
        {
            return (numerator > 0 && denominator > 0) || (numerator < 0 && denominator < 0);
        }

        public static BigRational operator +(BigRational r1, BigRational r2)
        {
            return new BigRational(r1.numerator * r2.denominator + r2.numerator * r1.denominator, r1.denominator * r2.denominator);
        }

        public static BigRational operator -(BigRational r1, BigRational r2)
        {
            return new BigRational(r1.numerator * r2.denominator - r2.numerator * r1.denominator, r1.denominator * r2.denominator);
        }

        public static BigRational operator *(BigRational r1, BigRational r2)
        {
            return new BigRational(r1.numerator * r2.numerator, r1.denominator * r2.denominator);
        }

        public static BigRational operator /(BigRational r1, BigRational r2)
        {
            return new BigRational(r1.numerator * r2.denominator, r1.denominator * r2.numerator);
        }

        public static bool operator <(BigRational r1, BigRational r2)
        {
            return (r1 - r2).IsNegative();
        }

        public static bool operator >(BigRational r1, BigRational r2)
        {
            return (r1 - r2).IsPositive();
        }

        public static bool operator ==(BigRational r1, BigRational r2)
        {
            return (r1 - r2).IsZero();
        }

        public static bool operator !=(BigRational r1, BigRational r2)
        {
            return !(r1 - r2).IsZero();
        }

        public static bool operator <=(BigRational r1, BigRational r2)
        {
            return !(r1 - r2).IsPositive();
        }

        public static bool operator >=(BigRational r1, BigRational r2)
        {
            return !(r1 - r2).IsNegative();
        }

        public override bool Equals(object obj)
        {
            return obj is BigRational && this == (BigRational)obj;
        }

        public override int GetHashCode()
        {
            return 0;
        }

        public static BigRational Power(BigRational x, UInt32 e)
        {
            BigRational x_to_e = new BigRational(1);
            while (e > 0)
            {
                x_to_e *= x;
                e -= 1;
            }
            return x_to_e;
        }
    }
}
