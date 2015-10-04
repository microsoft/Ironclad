
namespace IronfleetShtClient
{
    using System;
    using System.CodeDom.Compiler;
    using System.Collections.Generic;
    using System.Linq;
    using System.Diagnostics;

    public class Vocabulary : IVocabularyModule
    {
        private readonly Dictionary<int, int> specs;
        private readonly ModuleMux mux;

        private class ModuleMux : IVocabularyModule
        {
            private readonly IVocabularyModule[] sources;

            public ModuleMux(IEnumerable<IVocabularyModule> sources)
            {

                if (null == sources)
                {
                    throw new ArgumentNullException("sources");
                }

                this.sources = sources.ToArray();
                if (this.sources.Length == 0)
                {
                    throw new ArgumentOutOfRangeException("sources", "sources is empty.");
                }

                if (this.sources.Contains(null))
                {
                    throw new ArgumentException("source list contains a null", "sources");
                }
            }

            public byte[] Pick(Random rng)
            {
                Debug.Assert(rng != null, "expect constructed object");
                Debug.Assert(this.sources != null, "expect constructed object");

                var i = rng.Next(this.sources.Length);
                Debug.Assert(this.sources[i] != null, "expect non-null object");
                return this.sources[i].Pick(rng);
            }
        }

        private class Page : IVocabularyModule
        {
            private readonly int entryLength = 0;
            private readonly int entryCount = 0;
            private readonly List<byte[]> entries;

            public Page(Random rng, int entryLength, int entryCount)
            {
                this.entryLength = entryLength;
                this.entryCount = entryCount;
                this.entries = Generate(rng, entryLength, entryCount);
            }

            private static List<byte[]> Generate(Random rng, int entryLength, int entryCount)
            {
                if (rng == null)
                {
                    throw new ArgumentNullException("rng");
                }

                if (entryLength < 1)
                {
                    throw new ArgumentOutOfRangeException("entryLength", "is smaller than 1");
                }

                if (entryCount < 1)
                {
                    throw new ArgumentOutOfRangeException("entryCount", "is smaller than 1");
                }

                var entries = new List<byte[]>(entryCount);
                for (var i = 0; i < entryCount; ++i)
                {
                    byte[] entry = null;
                    do
                    {
                        entry = new byte[entryLength];
                        rng.NextBytes(entry);
                    }
                    while (entries.Contains(entry));
                    entries.Add(entry);
                }

                return entries;
            }

            public byte[] Pick(Random rng)
            {
                Debug.Assert(rng != null, "expect constructed object");
                Debug.Assert(this.entries != null, "expect constructed object");

                var i = rng.Next(this.entries.Count);
                return this.entries[i];
            }
        }

        public Vocabulary(Random rng, Dictionary<int, int> specs)
        {
            this.specs = specs;
            this.mux = Generate(rng, specs);
        }

        private static ModuleMux Generate(Random rng, Dictionary<int, int> specs)
        {
            if (rng == null)
            {
                throw new ArgumentNullException("rng");
            }

            if (null == specs)
            {
                throw new ArgumentNullException("specs");
            }

            if (specs.Count == 0)
            {
                throw new ArgumentException("vocabulary specification is empty", "specs");
            }

            var pages = new List<Page>();
            foreach (var i in specs)
            {
                pages.Add(new Page(rng, i.Key, i.Value));
            }

            return new ModuleMux(pages);
        }

        public byte[] Pick(Random rng)
        {
            Debug.Assert(this.mux != null, "expect constructed and initialized object");

            return this.mux.Pick(rng);
        }
    }
}
