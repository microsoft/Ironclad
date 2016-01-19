//--
// <copyright file="CacheState.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace ItemCacheTool
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Linq;
    using System.Text;
    using System.Threading.Tasks;
    using NuBuild;

    public class CacheState
    {
        private ItemCacheCloud cloudCache;

        private ItemCacheLocal localCache;

        public CacheState()
        {
            this.cloudCache = new ItemCacheCloud();
            this.localCache = new ItemCacheLocal(
                Path.Combine(GetDefaultIronRoot(), "nucache"));
        }

        public ItemCacheCloud GetCloudCache
        {
            get { return this.cloudCache; }
        }

        public ItemCacheLocal GetLocalCache
        {
            get { return this.localCache; }
        }

        public IItemCache[] GetAllCaches
        {
            get { return new IItemCache[] { this.cloudCache, this.localCache }; }
        }

        public ItemCacheContainer[] GetAllContainers
        {
            get { return (ItemCacheContainer[])Enum.GetValues(typeof(ItemCacheContainer)); }
        }

        public IItemCache[] ParseCacheName(string input)
        {
            if (input == "*")
            {
                return this.GetAllCaches;
            }

            if (string.Equals(input, "cloud", StringComparison.CurrentCultureIgnoreCase))
            {
                return new IItemCache[] { this.cloudCache };
            }

            if (string.Equals(input, "local", StringComparison.CurrentCultureIgnoreCase))
            {
                return new IItemCache[] { this.localCache };
            }

            return null;
        }

        public ItemCacheContainer[] ParseContainerName(string input)
        {
            ItemCacheContainer container;

            if (input == "*")
            {
                return this.GetAllContainers;
            }

            if (Enum.TryParse<ItemCacheContainer>(input, true, out container))
            {
                if (Enum.IsDefined(typeof(ItemCacheContainer), container))
                {
                    return new ItemCacheContainer[] { container };
                }
            }

            return null;
        }

        /// <summary>
        /// Gets the default iron root path.
        /// </summary>
        /// <returns>String containing the default iron root path.</returns>
        private static string GetDefaultIronRoot()
        {
            string assyUri = System.Reflection.Assembly.GetExecutingAssembly().CodeBase;
            string assyPath = new Uri(assyUri).LocalPath;
            string exepath = Path.GetDirectoryName(assyPath);
            exepath = Path.GetFullPath(exepath);
            string[] parts = exepath.Split(new char[] { '\\' });
            int ironIndex = Array.IndexOf(parts, "iron");
            string rc = string.Join("\\", parts.Take(ironIndex + 1));
            return rc;
        }
    }
}
