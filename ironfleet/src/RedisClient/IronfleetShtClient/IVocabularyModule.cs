using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace IronfleetShtClient
{
    using System.Diagnostics;
    using System.Threading;

    public interface IVocabularyModule
    {
        byte[] Pick(Random rng);
    }

    public static class VocabularyModuleExtensions
    {
        public static IEnumerable<byte[]> Series(this IVocabularyModule self, Random rng)
        {
            Debug.Assert(self != null, "self is expected to be non-null");

            while (true)
            {
                yield return self.Pick(rng);
            }
        }
        
    }
}
