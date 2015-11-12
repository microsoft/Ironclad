//--
// <copyright file="ItemCacheLocal.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Threading;

    /// <summary>
    /// An implementation of the item cache that uses the local file system
    /// as the backing store.
    /// </summary>
    public class ItemCacheLocal : IItemCache
    {
        /// <summary>
        /// Array of local file system paths corresponding to item cache
        /// containers.
        /// </summary>
        private readonly string[] localPaths;

        /// <summary>
        /// Lock protecting local file system state from concurrent accesses.
        /// </summary>
        private object cacheLock;

        /// <summary>
        /// Initializes a new instance of the ItemCacheLocal class.
        /// </summary>
        /// <remarks>
        /// Generates local path names corresponding to the various item cache
        /// containers, and creates local directories for each, if they don't
        /// already exit.
        /// </remarks>
        /// <param name="localCacheDirectory">Root of the local cache.</param>
        public ItemCacheLocal(string localCacheDirectory)
        {
            // -
            // Set up the local "container" directories and paths to them.
            // -
            Array containers = Enum.GetValues(typeof(ItemCacheContainer));
            this.localPaths = new string[containers.Length];
            foreach (ItemCacheContainer container in containers)
            {
                string directory = Path.Combine(
                    localCacheDirectory,
                    container.ToString());

                this.localPaths[(int)container] = directory;
                Directory.CreateDirectory(directory);
            }

            this.cacheLock = new object();
        }

        /// <summary>
        /// Gets a human-readable name for this item cache implementation.
        /// </summary>
        public string Name
        {
            get { return "Local"; }
        }

        /// <summary>
        /// Copies the given item from the cache to a new byte array.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container holding the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the desired item.
        /// </param>
        /// <returns>A byte array containing a copy of the item.</returns>
        public byte[] FetchItem(
            ItemCacheContainer container,
            string itemHash)
        {
            string itemPath = this.ItemPath(container, itemHash);

            lock (this.cacheLock)
            {
                if (!File.Exists(itemPath))
                {
                    return null;
                }

                return File.ReadAllBytes(itemPath);
            }
        }

        /// <summary>
        /// Copies the given item from the cache to the given location in the
        /// local file system.
        /// </summary>
        /// <remarks>
        /// This method is a performance optimization over getting a readable
        /// stream for the item and copying it to a local file using CopyTo().
        /// </remarks>
        /// <param name="container">
        /// Identifier for the cache container holding the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the desired item.
        /// </param>
        /// <param name="localFilesystemDestinationPath">
        /// Location in the local file system to copy the item.
        /// </param>
        public void FetchItemToFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemDestinationPath)
        {
            lock (this.cacheLock)
            {
                try
                {
                    Directory.CreateDirectory(Path.GetDirectoryName(localFilesystemDestinationPath));
                    File.Copy(this.ItemPath(container, itemHash), localFilesystemDestinationPath, true);
                }
                catch (FileNotFoundException)
                {
                    throw new ObjectMissingFromCacheException(itemHash, "Item missing from local cache.");
                }
            }
        }

        /// <summary>
        /// Copies the given byte array to the desired cache item.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container to hold the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the item.
        /// </param>
        /// <param name="contents">
        /// Byte array containing the item.
        /// </param>
        public void StoreItem(
            ItemCacheContainer container,
            string itemHash,
            byte[] contents)
        {
            string itemPath = this.ItemPath(container, itemHash);
            lock (this.cacheLock)
            {
                File.Delete(itemPath);
                File.WriteAllBytes(itemPath, contents);
            }
        }

        /// <summary>
        /// Copies the given file from the local file system into the cache.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container to hold the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the item.
        /// </param>
        /// <param name="localFilesystemSourcePath">
        /// Location in the local file system from which to source the item.
        /// </param>
        public void StoreItemFromFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemSourcePath)
        {
            string itemPath = this.ItemPath(container, itemHash);
            lock (this.cacheLock)
            {
                File.Delete(itemPath);
                File.Copy(localFilesystemSourcePath, itemPath);
            }
        }

        /// <summary>
        /// Gets a HashSet containing the hash keys of all the items in the
        /// given container.
        /// </summary>
        /// <param name="container">Identifier for the cache container.</param>
        /// <returns>A HashSet containing the hash keys.</returns>
        public HashSet<string> GetItemsInContainer(ItemCacheContainer container)
        {
            HashSet<string> itemHashes = new HashSet<string>();

            foreach (string filename in Directory.EnumerateFiles(this.localPaths[(int)container]))
            {
                itemHashes.Add(Path.GetFileName(filename));
            }

            return itemHashes;
        }

        /// <summary>
        /// Deletes an item from the cache.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container holding the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the desired item.
        /// </param>
        public void DeleteItem(
            ItemCacheContainer container,
            string itemHash)
        {
            lock (this.cacheLock)
            {
                File.Delete(this.ItemPath(container, itemHash));
            }
        }

        /// <summary>
        /// Gets the size of the item.
        /// Returns -1 if the item is absent.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container holding the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the desired item.
        /// </param>
        /// <returns>Size of the item in bytes, or -1 if item is absent.</returns>
        public long GetItemSize(
            ItemCacheContainer container,
            string itemHash)
        {
            lock (this.cacheLock)
            {
                FileInfo fileInfo = new FileInfo(this.ItemPath(container, itemHash));
                if (fileInfo.Exists)
                {
                    return fileInfo.Length;
                }

                return -1;
            }
        }

        /// <summary>
        /// Gets the last-modified time of the item.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container holding the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the desired item.
        /// </param>
        /// <returns>A DateTimeOffset containing the item's last-modified time.</returns>
        public DateTimeOffset? GetItemLastModifiedTime(
            ItemCacheContainer container,
            string itemHash)
        {
            lock (this.cacheLock)
            {
                FileInfo fileInfo = new FileInfo(this.ItemPath(container, itemHash));
                if (fileInfo.Exists)
                {
                    return fileInfo.CreationTimeUtc;
                }

                return null;
            }
        }

        /// <summary>
        /// Gets the local path name for the given item.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container holding the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the desired item.
        /// </param>
        /// <returns>Path for the item.</returns>
        private string ItemPath(ItemCacheContainer container, string itemHash)
        {
            return Path.Combine(
                this.localPaths[(int)container],
                itemHash);
        }
    }
}
