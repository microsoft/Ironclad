//--
// <copyright file="OrderPreservingSet.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Linq;

    /// <summary>
    /// Representation of an order-preserving set.
    /// </summary>
    /// <remarks>
    /// Inspired by ICollection example at 
    /// <a href="http://stackoverflow.com/questions/1552225/hashset-that-preserves-ordering"/>.
    /// </remarks>
    /// <typeparam name="T">Type of objects in the set.</typeparam>
    internal class OrderPreservingSet<T>
        : ICollection<T>
    {
        private readonly HashSet<T> membership;
        private readonly List<T> order;

        public OrderPreservingSet()
            : this(EqualityComparer<T>.Default)
        {
        }

        public OrderPreservingSet(IEqualityComparer<T> comparer)
        {
            this.membership = new HashSet<T>(comparer);
            this.order = new List<T>();
        }

        public OrderPreservingSet(IEnumerable<T> initialContents)
            : this()
        {
            this.AddRange(initialContents);
        }

        public int Count
        {
            get { return this.membership.Count(); }
        }

        int ICollection<T>.Count
        {
            get { return this.membership.Count; }
        }

        // TODO I don't know what this property is for.
        bool ICollection<T>.IsReadOnly
        {
            get { return false; }
        }

        public void Add(T item)
        {
            if (!this.membership.Contains(item))
            {
                this.membership.Add(item);
                this.order.Add(item);
            }
        }

        void ICollection<T>.Add(T item)
        {
            this.Add(item);
        }

        public void AddRange(IEnumerable<T> range)
        {
            foreach (T obj in range)
            {
                this.Add(obj);
            }
        }

        void ICollection<T>.Clear()
        {
            this.membership.Clear();
            this.order.Clear();
        }

        bool ICollection<T>.Contains(T item)
        {
            return this.membership.Contains(item);
        }

        void ICollection<T>.CopyTo(T[] array, int arrayIndex)
        {
            this.order.CopyTo(array, arrayIndex);
        }

        IEnumerator<T> IEnumerable<T>.GetEnumerator()
        {
            return this.order.GetEnumerator();
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator()
        {
            return this.order.GetEnumerator();
        }

        bool ICollection<T>.Remove(T item)
        {
            this.membership.Remove(item);
            return this.order.Remove(item);
        }
    }
}
