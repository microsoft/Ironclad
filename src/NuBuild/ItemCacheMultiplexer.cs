//--
// <copyright file="ItemCacheMultiplexer.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.IO;

    /// <summary>
    /// An implementation of the item cache that multiplexes two other
    /// backing store implementations together.
    /// </summary>
    public class ItemCacheMultiplexer : IItemCache
    {
        /// <summary>
        /// The maximum size of items to upload to the cloud.
        /// </summary>
        private const long MaxUploadSizeThreshold = 50 * (1 << 20);

        /// <summary>
        /// The underlying local item cache implementation.
        /// </summary>
        private readonly ItemCacheLocal localCache;

        /// <summary>
        /// The underlying cloud item cache implementation.
        /// </summary>
        private readonly ItemCacheCloud cloudCache;

        /// <summary>
        /// A worker thread and queue for performing background work.
        /// </summary>
        /// <remarks>
        /// While this is currently private to the multiplexer,
        /// the BackgroundWorker code is generic and could be used
        /// for other purposes.  If that happens, we should move this
        /// to the main build engine.
        /// </remarks>
        private readonly BackgroundWorker backgroundWorker;

        /// <summary>
        /// Initializes a new instance of the ItemCacheMultiplexer class.
        /// </summary>
        /// <param name="localCache">A local cache instance.</param>
        /// <param name="cloudCache">A cloud cache instance.</param>
        /// <param name="backgroundWorker">A background worker instance.</param>
        public ItemCacheMultiplexer(
            ItemCacheLocal localCache,
            ItemCacheCloud cloudCache,
            BackgroundWorker backgroundWorker)
        {
            this.localCache = localCache;
            this.cloudCache = cloudCache;
            this.backgroundWorker = backgroundWorker;
        }

        /// <summary>
        /// Gets a human-readable name for this item cache implementation.
        /// </summary>
        public string Name
        {
            get { return "Multiplexer"; }
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
            byte[] contents;

            contents = this.localCache.FetchItem(container, itemHash);
            if (contents == null)
            {
                contents = this.cloudCache.FetchItem(container, itemHash);
                if (contents == null)
                {
                    return null;
                }

                this.localCache.StoreItem(container, itemHash, contents);
            }
            else
            {
                // -
                // Schedule cloud push on successful local read.
                // REVIEW: Is this rare optimization really worth it?
                // -
                this.QueueItemForCloudSync(container, itemHash);
            }

            return contents;
        }

        /// <summary>
        /// Copies the given item from the cache to the given location in the
        /// local file system.
        /// </summary>
        /// <remarks>
        /// As with GetReadableStreamForItem, we first try locally and only
        /// go to the cloud if needed.
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
            try
            {
                this.localCache.FetchItemToFile(container, itemHash, localFilesystemDestinationPath);

                // -
                // Schedule cloud push on successful local read.
                // REVIEW: Is this rare optimization really worth it?
                // -
                this.QueueItemForCloudSync(container, itemHash);
            }
            catch (ObjectMissingFromCacheException)
            {
                // -
                // If it is missing locally, try to retrieve it from the cloud.
                // Note we stash a copy in the local cache prior to copying it
                // to the desired local file.
                // -
                byte[] temp = this.cloudCache.FetchItem(container, itemHash);
                if (temp == null)
                {
                    throw new ObjectMissingFromCacheException(itemHash, "Item missing from multiplexed cache.");
                }

                this.localCache.StoreItem(container, itemHash, temp);
                this.localCache.FetchItemToFile(container, itemHash, localFilesystemDestinationPath);
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
        /// <param name="contents">Byte array containing the item.</param>
        public void StoreItem(
            ItemCacheContainer container,
            string itemHash,
            byte[] contents)
        {
            this.localCache.StoreItem(container, itemHash, contents);
            this.QueueItemForCloudSync(container, itemHash);
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
            this.localCache.StoreItemFromFile(container, itemHash, localFilesystemSourcePath);
            this.QueueItemForCloudSync(container, itemHash);
        }

        /// <summary>
        /// Deletes an item from the cache.
        /// </summary>
        /// <remarks>
        /// Note that our cache sync code (CheckForAndOrUploadMissingItem)
        /// will fail if given an item to sync, and that item is subsequently
        /// deleted from the local cache before the sync code gets around to
        /// syncing it.  This method is really only intended for cache
        /// management purposes and not for general use.  If that changes,
        /// the cache sync code should change as well.
        /// </remarks>
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
            this.localCache.DeleteItem(container, itemHash);
            this.cloudCache.DeleteItem(container, itemHash);
        }

        /// <summary>
        /// Gets a HashSet containing the hash keys of all the items in the
        /// given container.
        /// </summary>
        /// <param name="container">Identifier for the cache container.</param>
        /// <returns>A HashSet containing the hash keys.</returns>
        public HashSet<string> GetItemsInContainer(ItemCacheContainer container)
        {
            // -
            // REVIEW: What to return here?  Both caches contents? Nothing?
            // -
            return new HashSet<string>();
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
            long size = this.localCache.GetItemSize(container, itemHash);
            if (size == -1)
            {
                size = this.cloudCache.GetItemSize(container, itemHash);
            }

            return size;
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
            DateTimeOffset? modifiedTime = this.localCache.GetItemLastModifiedTime(container, itemHash);
            if (modifiedTime == null)
            {
                modifiedTime = this.cloudCache.GetItemLastModifiedTime(container, itemHash);
            }

            return modifiedTime;
        }

        /// <summary>
        /// Public API for private CheckForAndOrUploadMissingItem method.
        /// </summary>
        /// <param name="container">
        /// Identifier for the item's cache container.
        /// </param>
        /// <param name="itemHash">Hash key for the item.</param>
        public void SyncItemToCloud(
            ItemCacheContainer container,
            string itemHash)
        {
            this.CheckForAndOrUploadMissingItem(container, itemHash);
        }

        /// <summary>
        /// Queue the given item for asynchronous cloud cache synchronization.
        /// </summary>
        /// <param name="container">
        /// Identifier for the item's cache container.
        /// </param>
        /// <param name="itemHash">Hash key for the item.</param>
        private void QueueItemForCloudSync(
            ItemCacheContainer container,
            string itemHash)
        {
            if (this.backgroundWorker != null)
            {
                this.backgroundWorker.QueueWork(this.CheckForAndOrUploadMissingItem, container, itemHash);
            }
        }

        /// <summary>
        /// Check if the given item is already present in the cloud cache,
        /// and if not, upload the local cache item to the cloud.
        /// </summary>
        /// <param name="containerObject">
        /// Identifier for the item's cache container.
        /// </param>
        /// <param name="itemHashObject">Hash key for the item.</param>
        private void CheckForAndOrUploadMissingItem(
            object containerObject,
            object itemHashObject)
        {
            ItemCacheContainer container = (ItemCacheContainer)containerObject;
            string itemHash = (string)itemHashObject;

            if (this.localCache.GetItemSize(container, itemHash) > MaxUploadSizeThreshold)
            {
                Logger.WriteLine(string.Format(
                    "Warning: skipping upload of {0} because it's really big. Compress?",
                    itemHash));
                return;
            }

            // -
            // Check if the item is already present in the cloud cache.
            // TODO present doesn't mean we don't want to overwrite it (eg when
            // replacing a Failed verification result with a succeeding one.)
            // -
            if (this.cloudCache.ItemExists(container, itemHash))
            {
                return;
            }

            // -
            // The item is missing from the cloud cache.  Upload it.
            // -
            byte[] temp = this.localCache.FetchItem(container, itemHash);
            if (temp == null)
            {
                // This should never happen barring a serious logic error.
                throw new ObjectMissingFromCacheException(itemHash, "Can't upload non-existant cache item!");
            }

            this.cloudCache.StoreItem(container, itemHash, temp);
        }

#if false
        /// <summary>
        /// A wrapper for a stream that queues up a cloud cache sync after it is
        /// closed.
        /// </summary>
        /// <remarks>
        /// REVIEW: a lot of boilerplate code just to hook one call.  Better way to do this?
        /// </remarks>
        private class MultiplexerWrappedStream : Stream
        {
            /// <summary>
            /// Flag indicating whether or not Dispose has already been called.
            /// </summary>
            private bool disposed;

            /// <summary>
            /// Stream we are wrapping.
            /// </summary>
            private Stream stream;

            /// <summary>
            /// Item cache multiplexer that holds the item behind the stream.
            /// </summary>
            private ItemCacheMultiplexer multiplexer;

            /// <summary>
            /// Item cache container for the item behind the stream.
            /// </summary>
            private ItemCacheContainer container;

            /// <summary>
            /// Item cache hash for the item behind the stream.
            /// </summary>
            private string itemHash;

            /// <summary>
            /// Initializes a new instance of the MultiplexerWrappedStream
            /// class.
            /// </summary>
            /// <param name="stream">A stream to wrap.</param>
            /// <param name="multiplexer">
            /// The multiplexer cache instance owning item.
            /// </param>
            /// <param name="container">
            /// The container for the item in the multiplexer cache.
            /// </param>
            /// <param name="itemHash">
            /// The hash for the item in the multiplexer cache.
            /// </param>
            public MultiplexerWrappedStream(
                Stream stream,
                ItemCacheMultiplexer multiplexer,
                ItemCacheContainer container,
                string itemHash)
            {
                this.stream = stream;
                this.multiplexer = multiplexer;
                this.container = container;
                this.itemHash = itemHash;
            }

            /// <summary>
            /// Gets a value indicating whether the current steam supports
            /// reading.
            /// </summary>
            public override bool CanRead
            {
                get { return this.stream.CanRead; }
            }

            /// <summary>
            /// Gets a value indicating whether the current stream supports
            /// seeking.
            /// </summary>
            public override bool CanSeek
            {
                get { return this.stream.CanSeek; }
            }

            /// <summary>
            /// Gets a value indicating whether the current stream supports
            /// writing.
            /// </summary>
            public override bool CanWrite
            {
                get { return this.stream.CanWrite; }
            }

            /// <summary>
            /// Gets the length in bytes of the stream.
            /// </summary>
            public override long Length
            {
                get { return this.stream.Length; }
            }

            /// <summary>
            /// Gets or sets the position within the current stream.
            /// </summary>
            public override long Position
            {
                get
                {
                    return this.stream.Position;
                }

                set
                {
                    this.stream.Position = value;
                }
            }

            /// <summary>
            /// Reads a sequence of bytes from the current stream and advances
            /// the position within the stream by the number of bytes read.
            /// </summary>
            /// <param name="buffer">
            /// An array of bytes.  When this method returns, the buffer
            /// contains the specified byte array with the values between
            /// offset and (offset + count - 1) replaced by the bytes read from
            /// the current source.
            /// </param>
            /// <param name="offset">
            /// The zero-based byte offset in buffer at which to begin storing
            /// the data read from the current stream.
            /// </param>
            /// <param name="count">
            /// The maximum number of bytes to be read from the current stream.
            /// </param>
            /// <returns>
            /// The total number of bytes read into the buffer.  This can be
            /// less than the number of bytes requested if that many bytes are
            /// not currently available, or zero (0) if the end of the stream
            /// has been reached.
            /// </returns>
            public override int Read(byte[] buffer, int offset, int count)
            {
                return this.stream.Read(buffer, offset, count);
            }

            /// <summary>
            /// Writes a sequence of bytes to the current stream and advances
            /// the position within this stream by the number of bytes written.
            /// </summary>
            /// <param name="buffer">
            /// An array of bytes.  This method copies count bytes from buffer
            /// to the current stream.
            /// </param>
            /// <param name="offset">
            /// The zero-based offset in buffer at which to begin copying bytes
            /// to the current stream.
            /// </param>
            /// <param name="count">
            /// The number of bytes to be written to the current stream.
            /// </param>
            public override void Write(byte[] buffer, int offset, int count)
            {
                this.stream.Write(buffer, offset, count);
            }

            /// <summary>
            /// Clears all buffers for this stream and causes any buffered data
            /// to be written to the underlying device.
            /// </summary>
            public override void Flush()
            {
                this.stream.Flush();
            }

            /// <summary>
            /// Sets the position within the current stream.
            /// </summary>
            /// <param name="offset">
            /// A byte offset relative to the origin parameter.
            /// </param>
            /// <param name="origin">
            /// A value of type SeekOrigin indicating the reference point used
            /// to obtain the new position.
            /// </param>
            /// <returns>The new position within the</returns>
            public override long Seek(long offset, SeekOrigin origin)
            {
                return this.stream.Seek(offset, origin);
            }

            /// <summary>
            /// Sets the length of the current stream.
            /// </summary>
            /// <param name="value">
            /// Desired length of the current stream in bytes.
            /// </param>
            public override void SetLength(long value)
            {
                this.stream.SetLength(value);
            }

            /// <summary>
            /// Releases unmanaged and (optionally) managed resources.
            /// </summary>
            /// <param name="disposing">
            /// Whether or not to release managed resources.
            /// </param>
            protected override void Dispose(bool disposing)
            {
                if (this.disposed)
                {
                    return;
                }

                if (disposing)
                {
                    this.stream.Dispose();
                    this.multiplexer.QueueItemForCloudSync(this.container, this.itemHash);
                }

                this.disposed = true;
                base.Dispose(disposing);
            }
        }
#endif
    }
}
