//--
// <copyright file="IItemCache.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    /// <summary>
    /// Enumeration of the containers in the item cache.
    /// </summary>
    /// <remarks>
    /// Important: The names of the values in the enumeration below become the
    /// actual names of the item cache containers.  For the Azure blob backing
    /// store, this means they must be a valid DNS name (i.e. may ONLY be
    /// comprised of letters, numbers and the dash ('-') character).
    /// </remarks>
    public enum ItemCacheContainer
    {
        /// <summary>
        /// Item cache container for source files.
        /// </summary>
        Sources = 0,

        /// <summary>
        /// Item cache container for object files.
        /// </summary>
        Objects = 1,

        /// <summary>
        /// Item cache container for (successful) result records.
        /// </summary>
        Results = 2,

        /// <summary>
        /// Item cache container for unsuccessful result records.
        /// </summary>
        FailedResults = 3
    }

    /// <summary>
    /// Definition of the interface to the item cache.
    /// </summary>
    public interface IItemCache
    {
        /// <summary>
        /// Gets a human-readable name for this item cache implementation.
        /// </summary>
        string Name
        {
            get;
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
        byte[] FetchItem(
            ItemCacheContainer container,
            string itemHash);

        /// <summary>
        /// Copies the given item from the cache to the given location in the
        /// local file system.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container holding the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the desired item.
        /// </param>
        /// <param name="localFilesystemDestinationPath">
        /// Location in the local file system to copy the item.
        /// </param>
        void FetchItemToFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemDestinationPath);

        /// <summary>
        /// Copies the given byte array to the desired cache item.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container to hold the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the item.
        /// </param>
        /// <param name="contents">Byte array containing the item.</param>
        void StoreItem(
            ItemCacheContainer container,
            string itemHash,
            byte[] contents);

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
        void StoreItemFromFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemSourcePath);

        /// <summary>
        /// Deletes an item from the cache.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container holding the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the desired item.
        /// </param>
        void DeleteItem(
            ItemCacheContainer container,
            string itemHash);

        /// <summary>
        /// Gets a HashSet containing the hash keys of all the items in the
        /// given container.
        /// </summary>
        /// <param name="container">Identifier for the cache container.</param>
        /// <returns>A HashSet containing the hash keys.</returns>
        HashSet<string> GetItemsInContainer(
            ItemCacheContainer container);

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
        long GetItemSize(
            ItemCacheContainer container,
            string itemHash);

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
        DateTimeOffset? GetItemLastModifiedTime(
            ItemCacheContainer container,
            string itemHash);
    }
}
