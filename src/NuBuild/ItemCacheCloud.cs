//--
// <copyright file="ItemCacheCloud.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Globalization;
    using System.IO;
    using Microsoft.WindowsAzure.Storage;
    using Microsoft.WindowsAzure.Storage.Blob;

    /// <summary>
    /// An implementation of the item cache that uses Azure blobs as the
    /// backing store.
    /// </summary>
    public class ItemCacheCloud : IItemCache
    {
        /// <summary>
        /// Blob client object for working with blobs.
        /// </summary>
        private readonly CloudBlobClient blobClient;

        /// <summary>
        /// Array of blob containers corresponding to item cache containers.
        /// </summary>
        private readonly CloudBlobContainer[] cloudContainers;

        /// <summary>
        /// Initializes a new instance of the ItemCacheCloud class.
        /// </summary>
        public ItemCacheCloud()
        {
            var storageAccount = NuBuildEnvironment.Options.CloudStorageAccount;

            // -
            // Create our CloudBlobClient object.
            // -
            this.blobClient = storageAccount.CreateCloudBlobClient();

            // -
            // Set up the blob storage containers.
            // -
            Array containers = Enum.GetValues(typeof(ItemCacheContainer));
            this.cloudContainers = new CloudBlobContainer[containers.Length];
            foreach (ItemCacheContainer container in containers)
            {
                CloudBlobContainer cloudContainer = this.blobClient.GetContainerReference(container.ToString().ToLower(CultureInfo.InvariantCulture));
                cloudContainer.CreateIfNotExists();
                this.cloudContainers[(int)container] = cloudContainer;
            }
        }

        /// <summary>
        /// Gets a human-readable name for this item cache implementation.
        /// </summary>
        public string Name
        {
            get { return "Cloud"; }
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            if (!cloudBlob.Exists())
            {
                return null;
            }

            using (MemoryStream memoryStream = new MemoryStream())
            {
                cloudBlob.DownloadToStream(memoryStream);
                var bytes = memoryStream.ToArray();
                var msg = string.Format("Retrieved item {0}/{1} from cloud cache.", container, itemHash);
                Logger.WriteLine(msg, new[] { "cache", "cloud" });
                return bytes;
            }
        }

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
        public void FetchItemToFile(
            ItemCacheContainer container,
            string itemHash,
            string localFilesystemDestinationPath)
        {
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            try
            {
                cloudBlob.DownloadToFile(localFilesystemDestinationPath, FileMode.Create);
                var msg = string.Format("Retrieved item {0}/{1} from cloud cache and stored as `{2}`.", container, itemHash, localFilesystemDestinationPath);
                Logger.WriteLine(msg, new[] { "cache", "cloud" });
            }
            catch (Microsoft.WindowsAzure.Storage.StorageException)
            {
                throw new ObjectMissingFromCacheException(itemHash, "Item missing from cloud cache.");
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            cloudBlob.UploadFromByteArray(contents, 0, contents.Length);
            var msg = string.Format("Wrote item {0}/{1} to cloud cache.", container, itemHash);
            Logger.WriteLine(msg, new[] { "cache", "cloud", "verbose" });
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            cloudBlob.UploadFromFile(localFilesystemSourcePath, FileMode.Open);
            var msg = string.Format("Wrote contents of `{0}` to cloud cache as item {1}/{2}.", localFilesystemSourcePath, container, itemHash);
            Logger.WriteLine(msg, new[] { "cache", "cloud", "verbose" });
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            cloudBlob.DeleteIfExists();
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

            foreach (CloudBlockBlob item in this.cloudContainers[(int)container].ListBlobs(null, true))
            {
                itemHashes.Add(item.Name);
            }

            return itemHashes;
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            if (cloudBlob.Exists())
            {
                return cloudBlob.Properties.Length;
            }

            return -1;
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
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            if (cloudBlob.Exists())
            {
                return cloudBlob.Properties.LastModified;
            }

            return null;
        }

        /// <summary>
        /// Checks whether the specified item exists in the cache.
        /// </summary>
        /// <param name="container">
        /// Identifier for the cache container holding the item.
        /// </param>
        /// <param name="itemHash">
        /// Hash key for the desired item.
        /// </param>
        /// <returns>
        /// True if the specified item is in the cache, false otherwise.
        /// </returns>
        public bool ItemExists(
            ItemCacheContainer container,
            string itemHash)
        {
            CloudBlockBlob cloudBlob = this.cloudContainers[(int)container].GetBlockBlobReference(itemHash);
            return cloudBlob.Exists();
        }
    }
}
