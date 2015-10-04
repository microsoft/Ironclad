// Dafny program Main.i.dfy compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219

using System; // for Func
using System.Numerics;

namespace Dafny
{
  using System.Collections.Generic;
// set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;

  public partial class Set<T>
  {
    readonly ImmutableHashSet<T> setImpl;
    Set(ImmutableHashSet<T> d) {
      this.setImpl = d;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty);
    public static Set<T> FromElements(params T[] values) {
      return FromElements((IEnumerable<T>)values);
    }
    public static Set<T> FromElements(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      foreach (T t in values)
        d.Add(t);
      return new Set<T>(d.ToImmutable());
    }
    public static Set<T> FromCollection(ICollection<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      foreach (T t in values)
        d.Add(t);
      return new Set<T>(d.ToImmutable());
    }
    public int Length {
      get { return this.setImpl.Count; }
    }
    public long LongLength {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".  Each set returned is the same
    /// Set<T> object (but this Set<T> object is fresh; in particular, it is not "this").
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          yield return new Set<T>(s.ToImmutable());
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
        return this.setImpl.Equals(other.setImpl);
    }
    public override bool Equals(object other) {
        var otherSet = other as Set<T>;
        return otherSet != null && Equals(otherSet);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (t.GetHashCode()+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
      foreach (var t in this.setImpl) {
        s += sep + t.ToString();
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
        return IsProperSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
        return IsSubsetOf(other);
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSupersetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSupersetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
      ImmutableHashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return this.setImpl.Contains(t);
    }
    public Set<T> Union(Set<T> other) {
        return new Set<T>(this.setImpl.Union(other.setImpl));
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl));
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl));
    }
  }
  public partial class MultiSet<T>
  {

    readonly ImmutableDictionary<T, int> dict;
    MultiSet(ImmutableDictionary<T, int> d) {
      dict = d;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, int>.Empty);
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values.Elements) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }
    public static MultiSet<T> FromSet(Set<T> values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values.Elements) {
        d[t] = 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      foreach (var kv in dict) {
        var t = kv.Key.ToString();
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t.ToString();
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return dict.ContainsKey(t);
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count == 0)
        return other;
      else if (other.dict.Count == 0)
        return this;
        var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r.ToImmutable());
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return other;
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r[t] = other.dict[t] < dict[t] ? other.dict[t] : dict[t];
        }
      }
      return new MultiSet<T>(r.ToImmutable());
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return this;
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r[t] = dict[t];
        } else if (other.dict[t] < dict[t]) {
          r[t] = dict[t] - other.dict[t];
        }
      }
      return new MultiSet<T>(r.ToImmutable());
    }
    public IEnumerable<T> Elements {
      get {
        foreach (T t in dict.Keys) {
          int n;
          dict.TryGetValue(t, out n);
          for (int i = 0; i < n; i ++) {
            yield return t;
          }
        }
      }
    }
  }

  public partial class Map<U, V>
  {
    readonly ImmutableDictionary<U, V> dict;
    Map(ImmutableDictionary<U, V> d) {
      dict = d;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty);
    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d.ToImmutable());
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d.ToImmutable());
    }
    public int Length {
      get { return dict.Count; }
    }
    public long LongLength {
      get { return dict.Count; }
    }
    public bool Equals(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        V v1, v2;
        if (!dict.TryGetValue(u, out v1)) {
          return false; // this shouldn't happen
        }
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!v1.Equals(v2)) {
          return false;
        }
      }
      foreach (U u in other.dict.Keys) {
        if (!dict.ContainsKey(u)) {
          return false; // this shouldn't happen
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      foreach (var kv in dict) {
        s += sep + kv.Key.ToString() + " := " + kv.Value.ToString();
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains(U u) {
      return dict.ContainsKey(u);
    }
    public V Select(U index) {
      return dict[index];
    }
    public Map<U, V> Update(U index, V val) {
      return new Map<U, V>(dict.SetItem(index, val));
    }
    public IEnumerable<U> Domain {
      get {
        return dict.Keys;
      }
    }
  }
#else // !def DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  public partial class Set<T>
  {
    HashSet<T> set;
    Set(HashSet<T> s) {
      this.set = s;
    }
    public static Set<T> Empty {
      get {
        return new Set<T>(new HashSet<T>());
      }
    }
    public static Set<T> FromElements(params T[] values) {
      var s = new HashSet<T>();
      foreach (T t in values)
        s.Add(t);
      return new Set<T>(s);
    }
    public static Set<T> FromCollection(ICollection<T> values) {
      HashSet<T> s = new HashSet<T>();
      foreach (T t in values)
        s.Add(t);
      return new Set<T>(s);
    }
    public int Length {
      get { return this.set.Count; }
    }
    public long LongLength {
      get { return this.set.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.set;
      }
    }
    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".  Each set returned is the same
    /// Set<T> object (but this Set<T> object is fresh; in particular, it is not "this").
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list
        var elmts = new List<T>();
        elmts.AddRange(this.set);
        var n = elmts.Count;
        var which = new bool[n];
        var s = new Set<T>(new HashSet<T>());
        while (true) {
          yield return s;
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.set.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.set.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
      return this.set.Count == other.set.Count && IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var t in this.set) {
        hashCode = hashCode * (t.GetHashCode()+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
      foreach (var t in this.set) {
        s += sep + t.ToString();
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.set.Count < other.set.Count && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
      if (other.set.Count < this.set.Count)
        return false;
      foreach (T t in this.set) {
        if (!other.set.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
      HashSet<T> a, b;
      if (this.set.Count < other.set.Count) {
        a = this.set; b = other.set;
      } else {
        a = other.set; b = this.set;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return this.set.Contains(t);
    }
    public Set<T> Union(Set<T> other) {
      if (this.set.Count == 0)
        return other;
      else if (other.set.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.set.Count < other.set.Count) {
        a = this.set; b = other.set;
      } else {
        a = other.set; b = this.set;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.set.Count == 0)
        return this;
      else if (other.set.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.set.Count < other.set.Count) {
        a = this.set; b = other.set;
      } else {
        a = other.set; b = this.set;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.set.Count == 0)
        return this;
      else if (other.set.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.set) {
        if (!other.set.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
  }
  public partial class MultiSet<T>
  {
    Dictionary<T, int> dict;
    MultiSet(Dictionary<T, int> d) {
      dict = d;
    }
    public static MultiSet<T> Empty {
      get {
        return new MultiSet<T>(new Dictionary<T, int>(0));
      }
    }
    public static MultiSet<T> FromElements(params T[] values) {
      Dictionary<T, int> d = new Dictionary<T, int>(values.Length);
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
      Dictionary<T, int> d = new Dictionary<T, int>();
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
      Dictionary<T, int> d = new Dictionary<T, int>();
      foreach (T t in values.Elements) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
      Dictionary<T, int> d = new Dictionary<T, int>();
      foreach (T t in values.Elements) {
        d[t] = 1;
      }
      return new MultiSet<T>(d);
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      foreach (var kv in dict) {
        var t = kv.Key.ToString();
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t.ToString();
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return dict.ContainsKey(t);
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count == 0)
        return other;
      else if (other.dict.Count == 0)
        return this;
      var r = new Dictionary<T, int>();
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return other;
      var r = new Dictionary<T, int>();
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return this;
      var r = new Dictionary<T, int>();
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r);
    }
    public IEnumerable<T> Elements {
      get {
        List<T> l = new List<T>();
        foreach (T t in dict.Keys) {
          int n;
          dict.TryGetValue(t, out n);
          for (int i = 0; i < n; i ++) {
            l.Add(t);
          }
        }
        return l;
      }
    }
  }

  public partial class Map<U, V>
  {
    Dictionary<U, V> dict;
    Map(Dictionary<U, V> d) {
      dict = d;
    }
    public static Map<U, V> Empty {
      get {
        return new Map<U, V>(new Dictionary<U,V>());
      }
    }
    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
      Dictionary<U, V> d = new Dictionary<U, V>(values.Length);
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d);
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
      Dictionary<U, V> d = new Dictionary<U, V>(values.Count);
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d);
    }
    public int Length {
      get { return dict.Count; }
    }
    public long LongLength {
      get { return dict.Count; }
    }
    public bool Equals(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        V v1, v2;
        if (!dict.TryGetValue(u, out v1)) {
          return false; // this shouldn't happen
        }
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!v1.Equals(v2)) {
          return false;
        }
      }
      foreach (U u in other.dict.Keys) {
        if (!dict.ContainsKey(u)) {
          return false; // this shouldn't happen
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      foreach (var kv in dict) {
        s += sep + kv.Key.ToString() + " := " + kv.Value.ToString();
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains(U u) {
      return dict.ContainsKey(u);
    }
    public V Select(U index) {
      return dict[index];
    }
    public Map<U, V> Update(U index, V val) {
      Dictionary<U, V> d = new Dictionary<U, V>(dict);
      d[index] = val;
      return new Map<U, V>(d);
    }
    public IEnumerable<U> Domain {
      get {
        return dict.Keys;
      }
    }
  }
#endif
  public partial class Sequence<T>
  {
    T[] elmts;
    public Sequence(T[] ee) {
      elmts = ee;
    }
    public static Sequence<T> Empty {
      get {
        return new Sequence<T>(new T[0]);
      }
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new Sequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new Sequence<char>(s.ToCharArray());
    }
    public int Length {
      get { return elmts.Length; }
    }
    public long LongLength {
      get { return elmts.LongLength; }
    }
    public T[] Elements {
      get {
        return elmts;
      }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(elmts);
        return st.Elements;
      }
    }
    public T Select(ulong index) {
      return elmts[index];
    }
    public T Select(long index) {
      return elmts[index];
    }
    public T Select(uint index) {
      return elmts[index];
    }
    public T Select(int index) {
      return elmts[index];
    }
    public T Select(BigInteger index) {
      return elmts[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])elmts.Clone();
      a[index] = t;
      return new Sequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = elmts.Length;
      return n == other.elmts.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ elmts[i].GetHashCode();
      }
      return hashCode;
    }
    public override string ToString() {
      if (elmts is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + t.ToString();
          sep = ", ";
        }
        return s + "]";
      }
    }
    bool EqualUntil(Sequence<T> other, int n) {
      for (int i = 0; i < n; i++) {
        if (!elmts[i].Equals(other.elmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n < other.elmts.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n <= other.elmts.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (elmts.Length == 0)
        return other;
      else if (other.elmts.Length == 0)
        return this;
      T[] a = new T[elmts.Length + other.elmts.Length];
      System.Array.Copy(elmts, 0, a, 0, elmts.Length);
      System.Array.Copy(other.elmts, 0, a, elmts.Length, other.elmts.Length);
      return new Sequence<T>(a);
    }
    public bool Contains(T t) {
      int n = elmts.Length;
      for (int i = 0; i < n; i++) {
        if (t.Equals(elmts[i]))
          return true;
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (elmts.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(elmts, a, m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[elmts.Length - m];
      System.Array.Copy(elmts, m, a, 0, elmts.Length - m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    // Computing forall/exists quantifiers
    public static bool QuantBool(bool frall, System.Predicate<bool> pred) {
      if (frall) {
        return pred(false) && pred(true);
      } else {
        return pred(false) || pred(true);
      }
    }
    public static bool QuantInt(BigInteger lo, BigInteger hi, bool frall, System.Predicate<BigInteger> pred) {
      for (BigInteger i = lo; i < hi; i++) {
        if (pred(i) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSet<U>(Dafny.Set<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantMap<U,V>(Dafny.Map<U,V> map, bool frall, System.Predicate<U> pred) {
      foreach (var u in map.Domain) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSeq<U>(Dafny.Sequence<U> seq, bool frall, System.Predicate<U> pred) {
      foreach (var u in seq.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantDatatype<U>(IEnumerable<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public delegate Dafny.Set<T> ComprehensionDelegate<T>();
    public delegate Dafny.Map<U, V> MapComprehensionDelegate<U, V>();
    public static IEnumerable<bool> AllBooleans {
      get {
        yield return false;
        yield return true;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers {
      get {
        yield return new BigInteger(0);
        for (var j = new BigInteger(1);; j++) {
          yield return j;
          yield return -j;
        }
      }
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new Sequence<T>(array);
    }
    // In .NET version 4.5, it it possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public delegate Result Function<Input,Result>(Input input);

    public static A Id<A>(A a) {
      return a;
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    BigInteger num, den;  // invariant 1 <= den
    public override string ToString() {
      return string.Format("({0}.0 / {1}.0)", num, den);
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (0 <= num) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
      var xx = a.den / gcd;
      var yy = b.den / gcd;
      // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
      aa = a.num * yy;
      bb = b.num * xx;
      dd = a.den * yy;
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return 1;
      } else if (asign <= 0 && 0 < bsign) {
        return 1;
      } else if (bsign < 0 && 0 <= asign) {
        return -1;
      } else if (bsign <= 0 && 0 < asign) {
        return -1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return 0 < a.CompareTo(b);
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return 0 <= a.CompareTo(b);
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }
}
namespace Dafny {
  public partial class Helpers {
      public static T[] InitNewArray1<T>(BigInteger size0) {
        int s0 = (int)size0;
        T[] a = new T[s0];
        BigInteger[] b = a as BigInteger[];
        if (b != null) {
          BigInteger z = new BigInteger(0);
          for (int i0 = 0; i0 < s0; i0++)
            b[i0] = z;
        }
        return a;
      }
  }
}
namespace @_System {


  public abstract class Base___tuple_h2<@T0,@T1> { }
  public partial class __tuple_h2____hMake<@T0,@T1> : Base___tuple_h2<@T0,@T1> {
    public readonly @T0 @_0;
    public readonly @T1 @_1;
    public __tuple_h2____hMake(@T0 @_0, @T1 @_1) {
      this.@_0 = @_0;
      this.@_1 = @_1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.@__tuple_h2____hMake<@T0,@T1>;
      return oth != null && this.@_0.Equals(oth.@_0) && this.@_1.Equals(oth.@_1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@_0.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@_1.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += @_0.ToString();
      s += ", ";
      s += @_1.ToString();
      s += ")";
      return s;
    }
  }
  public struct @__tuple_h2<@T0,@T1> {
    Base___tuple_h2<@T0,@T1> _d;
    public Base___tuple_h2<@T0,@T1> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @__tuple_h2(Base___tuple_h2<@T0,@T1> d) { this._d = d; }
    static Base___tuple_h2<@T0,@T1> theDefault;
    public static Base___tuple_h2<@T0,@T1> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@__tuple_h2____hMake<@T0,@T1>(default(@T0), default(@T1));
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @__tuple_h2<@T0,@T1> && _D.Equals(((@__tuple_h2<@T0,@T1>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is____hMake { get { return _D is __tuple_h2____hMake<@T0,@T1>; } }
    public @T0 dtor__0 { get { return ((__tuple_h2____hMake<@T0,@T1>)_D).@_0; } }
    public @T1 dtor__1 { get { return ((__tuple_h2____hMake<@T0,@T1>)_D).@_1; } }
  }
} // end of namespace _System
namespace @_Collections____Seqs__i_Compile {

  public partial class @__default {
  }
} // end of namespace _Collections____Seqs__i_Compile
namespace @_Math____mul__nonlinear__i_Compile {

  public partial class @__default {
  }
} // end of namespace _Math____mul__nonlinear__i_Compile
namespace @_Math____mul__auto__proofs__i_Compile {


  public partial class @__default {
  }
} // end of namespace _Math____mul__auto__proofs__i_Compile
namespace @_Math____mul__auto__i_Compile {


  public partial class @__default {
  }
} // end of namespace _Math____mul__auto__i_Compile
namespace @_Math____mul__i_Compile {



  public partial class @__default {
  }
} // end of namespace _Math____mul__i_Compile
namespace @_Math____div__nonlinear__i_Compile {

  public partial class @__default {
  }
} // end of namespace _Math____div__nonlinear__i_Compile
namespace @_Math____mod__auto__proofs__i_Compile {




  public partial class @__default {
  }
} // end of namespace _Math____mod__auto__proofs__i_Compile
namespace @_Math____mod__auto__i_Compile {


  public partial class @__default {
  }
} // end of namespace _Math____mod__auto__i_Compile
namespace @_Common____NodeIdentity__s_Compile {


  public partial class @__default {
  }
} // end of namespace _Common____NodeIdentity__s_Compile
namespace @_Common____Types__s_Compile {


  public abstract class Base_AppMessage { }
  public partial class AppMessage_AppIncrementRequest : Base_AppMessage {
    public AppMessage_AppIncrementRequest() {
    }
    public override bool Equals(object other) {
      var oth = other as _Common____Types__s_Compile.@AppMessage_AppIncrementRequest;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____Types__s_Compile.AppMessage.AppIncrementRequest";
      return s;
    }
  }
  public partial class AppMessage_AppIncrementReply : Base_AppMessage {
    public readonly BigInteger @response;
    public AppMessage_AppIncrementReply(BigInteger @response) {
      this.@response = @response;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____Types__s_Compile.@AppMessage_AppIncrementReply;
      return oth != null && this.@response.Equals(oth.@response);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@response.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____Types__s_Compile.AppMessage.AppIncrementReply";
      s += "(";
      s += @response.ToString();
      s += ")";
      return s;
    }
  }
  public partial class AppMessage_AppInvalidReply : Base_AppMessage {
    public AppMessage_AppInvalidReply() {
    }
    public override bool Equals(object other) {
      var oth = other as _Common____Types__s_Compile.@AppMessage_AppInvalidReply;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____Types__s_Compile.AppMessage.AppInvalidReply";
      return s;
    }
  }
  public struct @AppMessage {
    Base_AppMessage _d;
    public Base_AppMessage _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @AppMessage(Base_AppMessage d) { this._d = d; }
    static Base_AppMessage theDefault;
    public static Base_AppMessage Default {
      get {
        if (theDefault == null) {
          theDefault = new _Common____Types__s_Compile.@AppMessage_AppIncrementRequest();
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @AppMessage && _D.Equals(((@AppMessage)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_AppIncrementRequest { get { return _D is AppMessage_AppIncrementRequest; } }
    public bool is_AppIncrementReply { get { return _D is AppMessage_AppIncrementReply; } }
    public bool is_AppInvalidReply { get { return _D is AppMessage_AppInvalidReply; } }
    public BigInteger dtor_response { get { return ((AppMessage_AppIncrementReply)_D).@response; } }
  }

  public abstract class Base_Request { }
  public partial class Request_Request : Base_Request {
    public readonly BigInteger @client;
    public readonly BigInteger @seqno;
    public readonly @_Common____Types__s_Compile.@AppMessage @request;
    public Request_Request(BigInteger @client, BigInteger @seqno, @_Common____Types__s_Compile.@AppMessage @request) {
      this.@client = @client;
      this.@seqno = @seqno;
      this.@request = @request;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____Types__s_Compile.@Request_Request;
      return oth != null && this.@client.Equals(oth.@client) && this.@seqno.Equals(oth.@seqno) && this.@request.Equals(oth.@request);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@client.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@request.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____Types__s_Compile.Request.Request";
      s += "(";
      s += @client.ToString();
      s += ", ";
      s += @seqno.ToString();
      s += ", ";
      s += @request.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Request {
    Base_Request _d;
    public Base_Request _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Request(Base_Request d) { this._d = d; }
    static Base_Request theDefault;
    public static Base_Request Default {
      get {
        if (theDefault == null) {
          theDefault = new _Common____Types__s_Compile.@Request_Request(BigInteger.Zero, BigInteger.Zero, new @_Common____Types__s_Compile.@AppMessage());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Request && _D.Equals(((@Request)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Request { get { return _D is Request_Request; } }
    public BigInteger dtor_client { get { return ((Request_Request)_D).@client; } }
    public BigInteger dtor_seqno { get { return ((Request_Request)_D).@seqno; } }
    public @_Common____Types__s_Compile.@AppMessage dtor_request { get { return ((Request_Request)_D).@request; } }
  }

  public abstract class Base_Reply { }
  public partial class Reply_Reply : Base_Reply {
    public readonly BigInteger @client;
    public readonly BigInteger @seqno;
    public readonly @_Common____Types__s_Compile.@AppMessage @reply;
    public Reply_Reply(BigInteger @client, BigInteger @seqno, @_Common____Types__s_Compile.@AppMessage @reply) {
      this.@client = @client;
      this.@seqno = @seqno;
      this.@reply = @reply;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____Types__s_Compile.@Reply_Reply;
      return oth != null && this.@client.Equals(oth.@client) && this.@seqno.Equals(oth.@seqno) && this.@reply.Equals(oth.@reply);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@client.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@reply.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____Types__s_Compile.Reply.Reply";
      s += "(";
      s += @client.ToString();
      s += ", ";
      s += @seqno.ToString();
      s += ", ";
      s += @reply.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Reply {
    Base_Reply _d;
    public Base_Reply _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Reply(Base_Reply d) { this._d = d; }
    static Base_Reply theDefault;
    public static Base_Reply Default {
      get {
        if (theDefault == null) {
          theDefault = new _Common____Types__s_Compile.@Reply_Reply(BigInteger.Zero, BigInteger.Zero, new @_Common____Types__s_Compile.@AppMessage());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Reply && _D.Equals(((@Reply)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Reply { get { return _D is Reply_Reply; } }
    public BigInteger dtor_client { get { return ((Reply_Reply)_D).@client; } }
    public BigInteger dtor_seqno { get { return ((Reply_Reply)_D).@seqno; } }
    public @_Common____Types__s_Compile.@AppMessage dtor_reply { get { return ((Reply_Reply)_D).@reply; } }
  }


  public partial class @__default {
  }
} // end of namespace _Common____Types__s_Compile
namespace @_Common____TypesPPC__i_Compile {


  public abstract class Base_Ballot { }
  public partial class Ballot_Ballot : Base_Ballot {
    public readonly BigInteger @seqno;
    public readonly BigInteger @proposerId;
    public Ballot_Ballot(BigInteger @seqno, BigInteger @proposerId) {
      this.@seqno = @seqno;
      this.@proposerId = @proposerId;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____TypesPPC__i_Compile.@Ballot_Ballot;
      return oth != null && this.@seqno.Equals(oth.@seqno) && this.@proposerId.Equals(oth.@proposerId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@proposerId.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____TypesPPC__i_Compile.Ballot.Ballot";
      s += "(";
      s += @seqno.ToString();
      s += ", ";
      s += @proposerId.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Ballot {
    Base_Ballot _d;
    public Base_Ballot _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Ballot(Base_Ballot d) { this._d = d; }
    static Base_Ballot theDefault;
    public static Base_Ballot Default {
      get {
        if (theDefault == null) {
          theDefault = new _Common____TypesPPC__i_Compile.@Ballot_Ballot(BigInteger.Zero, BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Ballot && _D.Equals(((@Ballot)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Ballot { get { return _D is Ballot_Ballot; } }
    public BigInteger dtor_seqno { get { return ((Ballot_Ballot)_D).@seqno; } }
    public BigInteger dtor_proposerId { get { return ((Ballot_Ballot)_D).@proposerId; } }
  }





  public abstract class Base_Vote { }
  public partial class Vote_Vote : Base_Vote {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @maxVBal;
    public Vote_Vote(@_Common____TypesPPC__i_Compile.@Ballot @maxVBal) {
      this.@maxVBal = @maxVBal;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____TypesPPC__i_Compile.@Vote_Vote;
      return oth != null && this.@maxVBal.Equals(oth.@maxVBal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@maxVBal.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____TypesPPC__i_Compile.Vote.Vote";
      s += "(";
      s += @maxVBal.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Vote {
    Base_Vote _d;
    public Base_Vote _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Vote(Base_Vote d) { this._d = d; }
    static Base_Vote theDefault;
    public static Base_Vote Default {
      get {
        if (theDefault == null) {
          theDefault = new _Common____TypesPPC__i_Compile.@Vote_Vote(new @_Common____TypesPPC__i_Compile.@Ballot());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Vote && _D.Equals(((@Vote)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Vote { get { return _D is Vote_Vote; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_maxVBal { get { return ((Vote_Vote)_D).@maxVBal; } }
  }


  public partial class @__default {
  }
} // end of namespace _Common____TypesPPC__i_Compile
namespace @_RSL____Types__i_Compile {




  public partial class @__default {
  }
} // end of namespace _RSL____Types__i_Compile
namespace @_RSL____Parameters__i_Compile {

  public abstract class Base_Parameters { }
  public partial class Parameters_Parameters : Base_Parameters {
    public readonly BigInteger @maxLogLength;
    public Parameters_Parameters(BigInteger @maxLogLength) {
      this.@maxLogLength = @maxLogLength;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Parameters__i_Compile.@Parameters_Parameters;
      return oth != null && this.@maxLogLength.Equals(oth.@maxLogLength);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@maxLogLength.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Parameters__i_Compile.Parameters.Parameters";
      s += "(";
      s += @maxLogLength.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Parameters {
    Base_Parameters _d;
    public Base_Parameters _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Parameters(Base_Parameters d) { this._d = d; }
    static Base_Parameters theDefault;
    public static Base_Parameters Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Parameters__i_Compile.@Parameters_Parameters(BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Parameters && _D.Equals(((@Parameters)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Parameters { get { return _D is Parameters_Parameters; } }
    public BigInteger dtor_maxLogLength { get { return ((Parameters_Parameters)_D).@maxLogLength; } }
  }

  public partial class @__default {
  }
} // end of namespace _RSL____Parameters__i_Compile
namespace @_LiveRSL____Parameters__i_Compile {


  public abstract class Base_LParameters { }
  public partial class LParameters_LParameters : Base_LParameters {
    public readonly BigInteger @maxLogLength;
    public readonly BigInteger @baselineViewTimeoutPeriod;
    public readonly BigInteger @heartbeatPeriod;
    public readonly BigInteger @maxIntegerVal;
    public readonly BigInteger @maxBatchSize;
    public readonly BigInteger @maxBatchDelay;
    public LParameters_LParameters(BigInteger @maxLogLength, BigInteger @baselineViewTimeoutPeriod, BigInteger @heartbeatPeriod, BigInteger @maxIntegerVal, BigInteger @maxBatchSize, BigInteger @maxBatchDelay) {
      this.@maxLogLength = @maxLogLength;
      this.@baselineViewTimeoutPeriod = @baselineViewTimeoutPeriod;
      this.@heartbeatPeriod = @heartbeatPeriod;
      this.@maxIntegerVal = @maxIntegerVal;
      this.@maxBatchSize = @maxBatchSize;
      this.@maxBatchDelay = @maxBatchDelay;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Parameters__i_Compile.@LParameters_LParameters;
      return oth != null && this.@maxLogLength.Equals(oth.@maxLogLength) && this.@baselineViewTimeoutPeriod.Equals(oth.@baselineViewTimeoutPeriod) && this.@heartbeatPeriod.Equals(oth.@heartbeatPeriod) && this.@maxIntegerVal.Equals(oth.@maxIntegerVal) && this.@maxBatchSize.Equals(oth.@maxBatchSize) && this.@maxBatchDelay.Equals(oth.@maxBatchDelay);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@maxLogLength.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@baselineViewTimeoutPeriod.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@heartbeatPeriod.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxIntegerVal.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBatchSize.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBatchDelay.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Parameters__i_Compile.LParameters.LParameters";
      s += "(";
      s += @maxLogLength.ToString();
      s += ", ";
      s += @baselineViewTimeoutPeriod.ToString();
      s += ", ";
      s += @heartbeatPeriod.ToString();
      s += ", ";
      s += @maxIntegerVal.ToString();
      s += ", ";
      s += @maxBatchSize.ToString();
      s += ", ";
      s += @maxBatchDelay.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LParameters {
    Base_LParameters _d;
    public Base_LParameters _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LParameters(Base_LParameters d) { this._d = d; }
    static Base_LParameters theDefault;
    public static Base_LParameters Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Parameters__i_Compile.@LParameters_LParameters(BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LParameters && _D.Equals(((@LParameters)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LParameters { get { return _D is LParameters_LParameters; } }
    public BigInteger dtor_maxLogLength { get { return ((LParameters_LParameters)_D).@maxLogLength; } }
    public BigInteger dtor_baselineViewTimeoutPeriod { get { return ((LParameters_LParameters)_D).@baselineViewTimeoutPeriod; } }
    public BigInteger dtor_heartbeatPeriod { get { return ((LParameters_LParameters)_D).@heartbeatPeriod; } }
    public BigInteger dtor_maxIntegerVal { get { return ((LParameters_LParameters)_D).@maxIntegerVal; } }
    public BigInteger dtor_maxBatchSize { get { return ((LParameters_LParameters)_D).@maxBatchSize; } }
    public BigInteger dtor_maxBatchDelay { get { return ((LParameters_LParameters)_D).@maxBatchDelay; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Parameters__i_Compile
namespace @_RSL____StateMachine__s_Compile {




  public abstract class Base_SMState { }
  public partial class SMState_SMState : Base_SMState {
    public readonly Dafny.Set<@_Common____Types__s_Compile.@Request> @requests;
    public readonly Dafny.Set<@_Common____Types__s_Compile.@Reply> @replies;
    public readonly BigInteger @state;
    public SMState_SMState(Dafny.Set<@_Common____Types__s_Compile.@Request> @requests, Dafny.Set<@_Common____Types__s_Compile.@Reply> @replies, BigInteger @state) {
      this.@requests = @requests;
      this.@replies = @replies;
      this.@state = @state;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____StateMachine__s_Compile.@SMState_SMState;
      return oth != null && this.@requests.Equals(oth.@requests) && this.@replies.Equals(oth.@replies) && this.@state.Equals(oth.@state);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@requests.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@replies.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@state.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____StateMachine__s_Compile.SMState.SMState";
      s += "(";
      s += @requests.ToString();
      s += ", ";
      s += @replies.ToString();
      s += ", ";
      s += @state.ToString();
      s += ")";
      return s;
    }
  }
  public struct @SMState {
    Base_SMState _d;
    public Base_SMState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @SMState(Base_SMState d) { this._d = d; }
    static Base_SMState theDefault;
    public static Base_SMState Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____StateMachine__s_Compile.@SMState_SMState(Dafny.Set<@_Common____Types__s_Compile.@Request>.Empty, Dafny.Set<@_Common____Types__s_Compile.@Reply>.Empty, BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @SMState && _D.Equals(((@SMState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_SMState { get { return _D is SMState_SMState; } }
    public Dafny.Set<@_Common____Types__s_Compile.@Request> dtor_requests { get { return ((SMState_SMState)_D).@requests; } }
    public Dafny.Set<@_Common____Types__s_Compile.@Reply> dtor_replies { get { return ((SMState_SMState)_D).@replies; } }
    public BigInteger dtor_state { get { return ((SMState_SMState)_D).@state; } }
  }

  public partial class @__default {
  }
} // end of namespace _RSL____StateMachine__s_Compile
namespace @_RSL____Message__i_Compile {



  public abstract class Base_Message { }
  public partial class Message_Message__Request : Base_Message {
    public readonly BigInteger @seqno__req;
    public readonly @_Common____Types__s_Compile.@AppMessage @request;
    public Message_Message__Request(BigInteger @seqno__req, @_Common____Types__s_Compile.@AppMessage @request) {
      this.@seqno__req = @seqno__req;
      this.@request = @request;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__Request;
      return oth != null && this.@seqno__req.Equals(oth.@seqno__req) && this.@request.Equals(oth.@request);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno__req.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@request.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__Request";
      s += "(";
      s += @seqno__req.ToString();
      s += ", ";
      s += @request.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Message_Message__1a : Base_Message {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__1a;
    public Message_Message__1a(@_Common____TypesPPC__i_Compile.@Ballot @bal__1a) {
      this.@bal__1a = @bal__1a;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__1a;
      return oth != null && this.@bal__1a.Equals(oth.@bal__1a);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__1a.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__1a";
      s += "(";
      s += @bal__1a.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Message_Message__1b : Base_Message {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__1b;
    public readonly BigInteger @logTruncationPoint;
    public readonly Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> @votes;
    public Message_Message__1b(@_Common____TypesPPC__i_Compile.@Ballot @bal__1b, BigInteger @logTruncationPoint, Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> @votes) {
      this.@bal__1b = @bal__1b;
      this.@logTruncationPoint = @logTruncationPoint;
      this.@votes = @votes;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__1b;
      return oth != null && this.@bal__1b.Equals(oth.@bal__1b) && this.@logTruncationPoint.Equals(oth.@logTruncationPoint) && this.@votes.Equals(oth.@votes);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__1b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@logTruncationPoint.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@votes.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__1b";
      s += "(";
      s += @bal__1b.ToString();
      s += ", ";
      s += @logTruncationPoint.ToString();
      s += ", ";
      s += @votes.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Message_Message__2a : Base_Message {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__2a;
    public readonly BigInteger @opn__2a;
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @val__2a;
    public Message_Message__2a(@_Common____TypesPPC__i_Compile.@Ballot @bal__2a, BigInteger @opn__2a, Dafny.Sequence<@_Common____Types__s_Compile.@Request> @val__2a) {
      this.@bal__2a = @bal__2a;
      this.@opn__2a = @opn__2a;
      this.@val__2a = @val__2a;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__2a;
      return oth != null && this.@bal__2a.Equals(oth.@bal__2a) && this.@opn__2a.Equals(oth.@opn__2a) && this.@val__2a.Equals(oth.@val__2a);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__2a.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__2a.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@val__2a.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__2a";
      s += "(";
      s += @bal__2a.ToString();
      s += ", ";
      s += @opn__2a.ToString();
      s += ", ";
      s += @val__2a.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Message_Message__2b : Base_Message {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__2b;
    public readonly BigInteger @opn__2b;
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @val__2b;
    public Message_Message__2b(@_Common____TypesPPC__i_Compile.@Ballot @bal__2b, BigInteger @opn__2b, Dafny.Sequence<@_Common____Types__s_Compile.@Request> @val__2b) {
      this.@bal__2b = @bal__2b;
      this.@opn__2b = @opn__2b;
      this.@val__2b = @val__2b;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__2b;
      return oth != null && this.@bal__2b.Equals(oth.@bal__2b) && this.@opn__2b.Equals(oth.@opn__2b) && this.@val__2b.Equals(oth.@val__2b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__2b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__2b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@val__2b.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__2b";
      s += "(";
      s += @bal__2b.ToString();
      s += ", ";
      s += @opn__2b.ToString();
      s += ", ";
      s += @val__2b.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Message_Message__Decision : Base_Message {
    public readonly BigInteger @opn__d;
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @decided__value;
    public Message_Message__Decision(BigInteger @opn__d, Dafny.Sequence<@_Common____Types__s_Compile.@Request> @decided__value) {
      this.@opn__d = @opn__d;
      this.@decided__value = @decided__value;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__Decision;
      return oth != null && this.@opn__d.Equals(oth.@opn__d) && this.@decided__value.Equals(oth.@decided__value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__d.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@decided__value.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__Decision";
      s += "(";
      s += @opn__d.ToString();
      s += ", ";
      s += @decided__value.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Message_Message__Checkpointed : Base_Message {
    public readonly BigInteger @opn__ckpt;
    public Message_Message__Checkpointed(BigInteger @opn__ckpt) {
      this.@opn__ckpt = @opn__ckpt;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__Checkpointed;
      return oth != null && this.@opn__ckpt.Equals(oth.@opn__ckpt);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__ckpt.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__Checkpointed";
      s += "(";
      s += @opn__ckpt.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Message_Message__Reply : Base_Message {
    public readonly BigInteger @seqno__reply;
    public readonly @_Common____Types__s_Compile.@AppMessage @reply;
    public Message_Message__Reply(BigInteger @seqno__reply, @_Common____Types__s_Compile.@AppMessage @reply) {
      this.@seqno__reply = @seqno__reply;
      this.@reply = @reply;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__Reply;
      return oth != null && this.@seqno__reply.Equals(oth.@seqno__reply) && this.@reply.Equals(oth.@reply);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno__reply.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@reply.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__Reply";
      s += "(";
      s += @seqno__reply.ToString();
      s += ", ";
      s += @reply.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Message_Message__AppStateRequest : Base_Message {
    public readonly BigInteger @opn__state__req;
    public Message_Message__AppStateRequest(BigInteger @opn__state__req) {
      this.@opn__state__req = @opn__state__req;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__AppStateRequest;
      return oth != null && this.@opn__state__req.Equals(oth.@opn__state__req);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__state__req.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__AppStateRequest";
      s += "(";
      s += @opn__state__req.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Message_Message__AppStateSupply : Base_Message {
    public readonly BigInteger @opn__state__supply;
    public readonly BigInteger @app__state;
    public readonly Dafny.Set<@_Common____Types__s_Compile.@Reply> @reply__cache;
    public Message_Message__AppStateSupply(BigInteger @opn__state__supply, BigInteger @app__state, Dafny.Set<@_Common____Types__s_Compile.@Reply> @reply__cache) {
      this.@opn__state__supply = @opn__state__supply;
      this.@app__state = @app__state;
      this.@reply__cache = @reply__cache;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Message__i_Compile.@Message_Message__AppStateSupply;
      return oth != null && this.@opn__state__supply.Equals(oth.@opn__state__supply) && this.@app__state.Equals(oth.@app__state) && this.@reply__cache.Equals(oth.@reply__cache);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__state__supply.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@app__state.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@reply__cache.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Message__i_Compile.Message.Message__AppStateSupply";
      s += "(";
      s += @opn__state__supply.ToString();
      s += ", ";
      s += @app__state.ToString();
      s += ", ";
      s += @reply__cache.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Message {
    Base_Message _d;
    public Base_Message _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Message(Base_Message d) { this._d = d; }
    static Base_Message theDefault;
    public static Base_Message Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Message__i_Compile.@Message_Message__Request(BigInteger.Zero, new @_Common____Types__s_Compile.@AppMessage());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Message && _D.Equals(((@Message)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Message__Request { get { return _D is Message_Message__Request; } }
    public bool is_Message__1a { get { return _D is Message_Message__1a; } }
    public bool is_Message__1b { get { return _D is Message_Message__1b; } }
    public bool is_Message__2a { get { return _D is Message_Message__2a; } }
    public bool is_Message__2b { get { return _D is Message_Message__2b; } }
    public bool is_Message__Decision { get { return _D is Message_Message__Decision; } }
    public bool is_Message__Checkpointed { get { return _D is Message_Message__Checkpointed; } }
    public bool is_Message__Reply { get { return _D is Message_Message__Reply; } }
    public bool is_Message__AppStateRequest { get { return _D is Message_Message__AppStateRequest; } }
    public bool is_Message__AppStateSupply { get { return _D is Message_Message__AppStateSupply; } }
    public BigInteger dtor_seqno__req { get { return ((Message_Message__Request)_D).@seqno__req; } }
    public @_Common____Types__s_Compile.@AppMessage dtor_request { get { return ((Message_Message__Request)_D).@request; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__1a { get { return ((Message_Message__1a)_D).@bal__1a; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__1b { get { return ((Message_Message__1b)_D).@bal__1b; } }
    public BigInteger dtor_logTruncationPoint { get { return ((Message_Message__1b)_D).@logTruncationPoint; } }
    public Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> dtor_votes { get { return ((Message_Message__1b)_D).@votes; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__2a { get { return ((Message_Message__2a)_D).@bal__2a; } }
    public BigInteger dtor_opn__2a { get { return ((Message_Message__2a)_D).@opn__2a; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_val__2a { get { return ((Message_Message__2a)_D).@val__2a; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__2b { get { return ((Message_Message__2b)_D).@bal__2b; } }
    public BigInteger dtor_opn__2b { get { return ((Message_Message__2b)_D).@opn__2b; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_val__2b { get { return ((Message_Message__2b)_D).@val__2b; } }
    public BigInteger dtor_opn__d { get { return ((Message_Message__Decision)_D).@opn__d; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_decided__value { get { return ((Message_Message__Decision)_D).@decided__value; } }
    public BigInteger dtor_opn__ckpt { get { return ((Message_Message__Checkpointed)_D).@opn__ckpt; } }
    public BigInteger dtor_seqno__reply { get { return ((Message_Message__Reply)_D).@seqno__reply; } }
    public @_Common____Types__s_Compile.@AppMessage dtor_reply { get { return ((Message_Message__Reply)_D).@reply; } }
    public BigInteger dtor_opn__state__req { get { return ((Message_Message__AppStateRequest)_D).@opn__state__req; } }
    public BigInteger dtor_opn__state__supply { get { return ((Message_Message__AppStateSupply)_D).@opn__state__supply; } }
    public BigInteger dtor_app__state { get { return ((Message_Message__AppStateSupply)_D).@app__state; } }
    public Dafny.Set<@_Common____Types__s_Compile.@Reply> dtor_reply__cache { get { return ((Message_Message__AppStateSupply)_D).@reply__cache; } }
  }

  public partial class @__default {
  }
} // end of namespace _RSL____Message__i_Compile
namespace @_RSL____Configuration__i_Compile {


  public abstract class Base_Configuration { }
  public partial class Configuration_Configuration : Base_Configuration {
    public readonly Dafny.Sequence<BigInteger> @replicaIds;
    public Configuration_Configuration(Dafny.Sequence<BigInteger> @replicaIds) {
      this.@replicaIds = @replicaIds;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Configuration__i_Compile.@Configuration_Configuration;
      return oth != null && this.@replicaIds.Equals(oth.@replicaIds);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@replicaIds.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Configuration__i_Compile.Configuration.Configuration";
      s += "(";
      s += @replicaIds.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Configuration {
    Base_Configuration _d;
    public Base_Configuration _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Configuration(Base_Configuration d) { this._d = d; }
    static Base_Configuration theDefault;
    public static Base_Configuration Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Configuration__i_Compile.@Configuration_Configuration(Dafny.Sequence<BigInteger>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Configuration && _D.Equals(((@Configuration)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Configuration { get { return _D is Configuration_Configuration; } }
    public Dafny.Sequence<BigInteger> dtor_replicaIds { get { return ((Configuration_Configuration)_D).@replicaIds; } }
  }

  public partial class @__default {
  }
} // end of namespace _RSL____Configuration__i_Compile
namespace @_LiveRSL____Types__i_Compile {




  public partial class @__default {
  }
} // end of namespace _LiveRSL____Types__i_Compile
namespace @_Collections____Sets__i_Compile {

  public partial class @__default {
  }
} // end of namespace _Collections____Sets__i_Compile
namespace @_LiveRSL____Configuration__i_Compile {





  public abstract class Base_LConfiguration { }
  public partial class LConfiguration_LConfiguration : Base_LConfiguration {
    public readonly Dafny.Set<BigInteger> @clientIds;
    public readonly Dafny.Sequence<BigInteger> @replicaIds;
    public LConfiguration_LConfiguration(Dafny.Set<BigInteger> @clientIds, Dafny.Sequence<BigInteger> @replicaIds) {
      this.@clientIds = @clientIds;
      this.@replicaIds = @replicaIds;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Configuration__i_Compile.@LConfiguration_LConfiguration;
      return oth != null && this.@clientIds.Equals(oth.@clientIds) && this.@replicaIds.Equals(oth.@replicaIds);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@clientIds.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@replicaIds.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Configuration__i_Compile.LConfiguration.LConfiguration";
      s += "(";
      s += @clientIds.ToString();
      s += ", ";
      s += @replicaIds.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LConfiguration {
    Base_LConfiguration _d;
    public Base_LConfiguration _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LConfiguration(Base_LConfiguration d) { this._d = d; }
    static Base_LConfiguration theDefault;
    public static Base_LConfiguration Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Configuration__i_Compile.@LConfiguration_LConfiguration(Dafny.Set<BigInteger>.Empty, Dafny.Sequence<BigInteger>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LConfiguration && _D.Equals(((@LConfiguration)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LConfiguration { get { return _D is LConfiguration_LConfiguration; } }
    public Dafny.Set<BigInteger> dtor_clientIds { get { return ((LConfiguration_LConfiguration)_D).@clientIds; } }
    public Dafny.Sequence<BigInteger> dtor_replicaIds { get { return ((LConfiguration_LConfiguration)_D).@replicaIds; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Configuration__i_Compile
namespace @_LiveRSL____StateMachine__s_Compile {

  public partial class @__default {
  }
} // end of namespace _LiveRSL____StateMachine__s_Compile
namespace @_LiveRSL____Message__i_Compile {




  public abstract class Base_LPaxosMessage { }
  public partial class LPaxosMessage_LPaxosMessage__Request : Base_LPaxosMessage {
    public readonly BigInteger @seqno__req;
    public readonly @_Common____Types__s_Compile.@AppMessage @val;
    public LPaxosMessage_LPaxosMessage__Request(BigInteger @seqno__req, @_Common____Types__s_Compile.@AppMessage @val) {
      this.@seqno__req = @seqno__req;
      this.@val = @val;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__Request;
      return oth != null && this.@seqno__req.Equals(oth.@seqno__req) && this.@val.Equals(oth.@val);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno__req.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@val.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__Request";
      s += "(";
      s += @seqno__req.ToString();
      s += ", ";
      s += @val.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LPaxosMessage_LPaxosMessage__1a : Base_LPaxosMessage {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__1a;
    public LPaxosMessage_LPaxosMessage__1a(@_Common____TypesPPC__i_Compile.@Ballot @bal__1a) {
      this.@bal__1a = @bal__1a;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__1a;
      return oth != null && this.@bal__1a.Equals(oth.@bal__1a);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__1a.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__1a";
      s += "(";
      s += @bal__1a.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LPaxosMessage_LPaxosMessage__1b : Base_LPaxosMessage {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__1b;
    public readonly BigInteger @logTruncationPoint;
    public readonly Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> @votes;
    public LPaxosMessage_LPaxosMessage__1b(@_Common____TypesPPC__i_Compile.@Ballot @bal__1b, BigInteger @logTruncationPoint, Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> @votes) {
      this.@bal__1b = @bal__1b;
      this.@logTruncationPoint = @logTruncationPoint;
      this.@votes = @votes;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__1b;
      return oth != null && this.@bal__1b.Equals(oth.@bal__1b) && this.@logTruncationPoint.Equals(oth.@logTruncationPoint) && this.@votes.Equals(oth.@votes);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__1b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@logTruncationPoint.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@votes.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__1b";
      s += "(";
      s += @bal__1b.ToString();
      s += ", ";
      s += @logTruncationPoint.ToString();
      s += ", ";
      s += @votes.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LPaxosMessage_LPaxosMessage__2a : Base_LPaxosMessage {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__2a;
    public readonly BigInteger @opn__2a;
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @val__2a;
    public LPaxosMessage_LPaxosMessage__2a(@_Common____TypesPPC__i_Compile.@Ballot @bal__2a, BigInteger @opn__2a, Dafny.Sequence<@_Common____Types__s_Compile.@Request> @val__2a) {
      this.@bal__2a = @bal__2a;
      this.@opn__2a = @opn__2a;
      this.@val__2a = @val__2a;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__2a;
      return oth != null && this.@bal__2a.Equals(oth.@bal__2a) && this.@opn__2a.Equals(oth.@opn__2a) && this.@val__2a.Equals(oth.@val__2a);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__2a.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__2a.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@val__2a.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__2a";
      s += "(";
      s += @bal__2a.ToString();
      s += ", ";
      s += @opn__2a.ToString();
      s += ", ";
      s += @val__2a.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LPaxosMessage_LPaxosMessage__2b : Base_LPaxosMessage {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__2b;
    public readonly BigInteger @opn__2b;
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @val__2b;
    public LPaxosMessage_LPaxosMessage__2b(@_Common____TypesPPC__i_Compile.@Ballot @bal__2b, BigInteger @opn__2b, Dafny.Sequence<@_Common____Types__s_Compile.@Request> @val__2b) {
      this.@bal__2b = @bal__2b;
      this.@opn__2b = @opn__2b;
      this.@val__2b = @val__2b;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__2b;
      return oth != null && this.@bal__2b.Equals(oth.@bal__2b) && this.@opn__2b.Equals(oth.@opn__2b) && this.@val__2b.Equals(oth.@val__2b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__2b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__2b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@val__2b.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__2b";
      s += "(";
      s += @bal__2b.ToString();
      s += ", ";
      s += @opn__2b.ToString();
      s += ", ";
      s += @val__2b.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LPaxosMessage_LPaxosMessage__Heartbeat : Base_LPaxosMessage {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__heartbeat;
    public readonly bool @suspicious;
    public readonly BigInteger @opn__ckpt;
    public LPaxosMessage_LPaxosMessage__Heartbeat(@_Common____TypesPPC__i_Compile.@Ballot @bal__heartbeat, bool @suspicious, BigInteger @opn__ckpt) {
      this.@bal__heartbeat = @bal__heartbeat;
      this.@suspicious = @suspicious;
      this.@opn__ckpt = @opn__ckpt;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__Heartbeat;
      return oth != null && this.@bal__heartbeat.Equals(oth.@bal__heartbeat) && this.@suspicious.Equals(oth.@suspicious) && this.@opn__ckpt.Equals(oth.@opn__ckpt);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__heartbeat.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@suspicious.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__ckpt.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__Heartbeat";
      s += "(";
      s += @bal__heartbeat.ToString();
      s += ", ";
      s += @suspicious.ToString();
      s += ", ";
      s += @opn__ckpt.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LPaxosMessage_LPaxosMessage__Reply : Base_LPaxosMessage {
    public readonly BigInteger @seqno__reply;
    public readonly @_Common____Types__s_Compile.@AppMessage @reply;
    public LPaxosMessage_LPaxosMessage__Reply(BigInteger @seqno__reply, @_Common____Types__s_Compile.@AppMessage @reply) {
      this.@seqno__reply = @seqno__reply;
      this.@reply = @reply;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__Reply;
      return oth != null && this.@seqno__reply.Equals(oth.@seqno__reply) && this.@reply.Equals(oth.@reply);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno__reply.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@reply.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__Reply";
      s += "(";
      s += @seqno__reply.ToString();
      s += ", ";
      s += @reply.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LPaxosMessage_LPaxosMessage__AppStateRequest : Base_LPaxosMessage {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__state__req;
    public readonly BigInteger @opn__state__req;
    public LPaxosMessage_LPaxosMessage__AppStateRequest(@_Common____TypesPPC__i_Compile.@Ballot @bal__state__req, BigInteger @opn__state__req) {
      this.@bal__state__req = @bal__state__req;
      this.@opn__state__req = @opn__state__req;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__AppStateRequest;
      return oth != null && this.@bal__state__req.Equals(oth.@bal__state__req) && this.@opn__state__req.Equals(oth.@opn__state__req);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__state__req.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__state__req.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__AppStateRequest";
      s += "(";
      s += @bal__state__req.ToString();
      s += ", ";
      s += @opn__state__req.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LPaxosMessage_LPaxosMessage__AppStateSupply : Base_LPaxosMessage {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__state__supply;
    public readonly BigInteger @opn__state__supply;
    public readonly BigInteger @app__state;
    public readonly Dafny.Map<BigInteger,@_Common____Types__s_Compile.@Reply> @reply__cache;
    public LPaxosMessage_LPaxosMessage__AppStateSupply(@_Common____TypesPPC__i_Compile.@Ballot @bal__state__supply, BigInteger @opn__state__supply, BigInteger @app__state, Dafny.Map<BigInteger,@_Common____Types__s_Compile.@Reply> @reply__cache) {
      this.@bal__state__supply = @bal__state__supply;
      this.@opn__state__supply = @opn__state__supply;
      this.@app__state = @app__state;
      this.@reply__cache = @reply__cache;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__AppStateSupply;
      return oth != null && this.@bal__state__supply.Equals(oth.@bal__state__supply) && this.@opn__state__supply.Equals(oth.@opn__state__supply) && this.@app__state.Equals(oth.@app__state) && this.@reply__cache.Equals(oth.@reply__cache);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__state__supply.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__state__supply.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@app__state.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@reply__cache.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__AppStateSupply";
      s += "(";
      s += @bal__state__supply.ToString();
      s += ", ";
      s += @opn__state__supply.ToString();
      s += ", ";
      s += @app__state.ToString();
      s += ", ";
      s += @reply__cache.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LPaxosMessage_LPaxosMessage__StartingPhase2 : Base_LPaxosMessage {
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal__2;
    public readonly BigInteger @logTruncationPoint__2;
    public LPaxosMessage_LPaxosMessage__StartingPhase2(@_Common____TypesPPC__i_Compile.@Ballot @bal__2, BigInteger @logTruncationPoint__2) {
      this.@bal__2 = @bal__2;
      this.@logTruncationPoint__2 = @logTruncationPoint__2;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__StartingPhase2;
      return oth != null && this.@bal__2.Equals(oth.@bal__2) && this.@logTruncationPoint__2.Equals(oth.@logTruncationPoint__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__2.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@logTruncationPoint__2.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Message__i_Compile.LPaxosMessage.LPaxosMessage__StartingPhase2";
      s += "(";
      s += @bal__2.ToString();
      s += ", ";
      s += @logTruncationPoint__2.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LPaxosMessage {
    Base_LPaxosMessage _d;
    public Base_LPaxosMessage _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LPaxosMessage(Base_LPaxosMessage d) { this._d = d; }
    static Base_LPaxosMessage theDefault;
    public static Base_LPaxosMessage Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Message__i_Compile.@LPaxosMessage_LPaxosMessage__Request(BigInteger.Zero, new @_Common____Types__s_Compile.@AppMessage());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LPaxosMessage && _D.Equals(((@LPaxosMessage)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LPaxosMessage__Request { get { return _D is LPaxosMessage_LPaxosMessage__Request; } }
    public bool is_LPaxosMessage__1a { get { return _D is LPaxosMessage_LPaxosMessage__1a; } }
    public bool is_LPaxosMessage__1b { get { return _D is LPaxosMessage_LPaxosMessage__1b; } }
    public bool is_LPaxosMessage__2a { get { return _D is LPaxosMessage_LPaxosMessage__2a; } }
    public bool is_LPaxosMessage__2b { get { return _D is LPaxosMessage_LPaxosMessage__2b; } }
    public bool is_LPaxosMessage__Heartbeat { get { return _D is LPaxosMessage_LPaxosMessage__Heartbeat; } }
    public bool is_LPaxosMessage__Reply { get { return _D is LPaxosMessage_LPaxosMessage__Reply; } }
    public bool is_LPaxosMessage__AppStateRequest { get { return _D is LPaxosMessage_LPaxosMessage__AppStateRequest; } }
    public bool is_LPaxosMessage__AppStateSupply { get { return _D is LPaxosMessage_LPaxosMessage__AppStateSupply; } }
    public bool is_LPaxosMessage__StartingPhase2 { get { return _D is LPaxosMessage_LPaxosMessage__StartingPhase2; } }
    public BigInteger dtor_seqno__req { get { return ((LPaxosMessage_LPaxosMessage__Request)_D).@seqno__req; } }
    public @_Common____Types__s_Compile.@AppMessage dtor_val { get { return ((LPaxosMessage_LPaxosMessage__Request)_D).@val; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__1a { get { return ((LPaxosMessage_LPaxosMessage__1a)_D).@bal__1a; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__1b { get { return ((LPaxosMessage_LPaxosMessage__1b)_D).@bal__1b; } }
    public BigInteger dtor_logTruncationPoint { get { return ((LPaxosMessage_LPaxosMessage__1b)_D).@logTruncationPoint; } }
    public Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> dtor_votes { get { return ((LPaxosMessage_LPaxosMessage__1b)_D).@votes; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__2a { get { return ((LPaxosMessage_LPaxosMessage__2a)_D).@bal__2a; } }
    public BigInteger dtor_opn__2a { get { return ((LPaxosMessage_LPaxosMessage__2a)_D).@opn__2a; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_val__2a { get { return ((LPaxosMessage_LPaxosMessage__2a)_D).@val__2a; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__2b { get { return ((LPaxosMessage_LPaxosMessage__2b)_D).@bal__2b; } }
    public BigInteger dtor_opn__2b { get { return ((LPaxosMessage_LPaxosMessage__2b)_D).@opn__2b; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_val__2b { get { return ((LPaxosMessage_LPaxosMessage__2b)_D).@val__2b; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__heartbeat { get { return ((LPaxosMessage_LPaxosMessage__Heartbeat)_D).@bal__heartbeat; } }
    public bool dtor_suspicious { get { return ((LPaxosMessage_LPaxosMessage__Heartbeat)_D).@suspicious; } }
    public BigInteger dtor_opn__ckpt { get { return ((LPaxosMessage_LPaxosMessage__Heartbeat)_D).@opn__ckpt; } }
    public BigInteger dtor_seqno__reply { get { return ((LPaxosMessage_LPaxosMessage__Reply)_D).@seqno__reply; } }
    public @_Common____Types__s_Compile.@AppMessage dtor_reply { get { return ((LPaxosMessage_LPaxosMessage__Reply)_D).@reply; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__state__req { get { return ((LPaxosMessage_LPaxosMessage__AppStateRequest)_D).@bal__state__req; } }
    public BigInteger dtor_opn__state__req { get { return ((LPaxosMessage_LPaxosMessage__AppStateRequest)_D).@opn__state__req; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__state__supply { get { return ((LPaxosMessage_LPaxosMessage__AppStateSupply)_D).@bal__state__supply; } }
    public BigInteger dtor_opn__state__supply { get { return ((LPaxosMessage_LPaxosMessage__AppStateSupply)_D).@opn__state__supply; } }
    public BigInteger dtor_app__state { get { return ((LPaxosMessage_LPaxosMessage__AppStateSupply)_D).@app__state; } }
    public Dafny.Map<BigInteger,@_Common____Types__s_Compile.@Reply> dtor_reply__cache { get { return ((LPaxosMessage_LPaxosMessage__AppStateSupply)_D).@reply__cache; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal__2 { get { return ((LPaxosMessage_LPaxosMessage__StartingPhase2)_D).@bal__2; } }
    public BigInteger dtor_logTruncationPoint__2 { get { return ((LPaxosMessage_LPaxosMessage__StartingPhase2)_D).@logTruncationPoint__2; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Message__i_Compile
namespace @_Collections____Maps2__s_Compile {


  public partial class @__default {
  }
} // end of namespace _Collections____Maps2__s_Compile
namespace @_Temporal____Temporal__s_Compile {


/* Compilation error: Opaque type ('_Temporal____Temporal__s_Compile.temporal') cannot be compiled */


  public partial class @__default {
  }
} // end of namespace _Temporal____Temporal__s_Compile
namespace @_Liveness____Environment__s_Compile {



  public abstract class Base_LPacket<@IdType,@MessageType> { }
  public partial class LPacket_LPacket<@IdType,@MessageType> : Base_LPacket<@IdType,@MessageType> {
    public readonly @IdType @dst;
    public readonly @IdType @src;
    public readonly @MessageType @msg;
    public LPacket_LPacket(@IdType @dst, @IdType @src, @MessageType @msg) {
      this.@dst = @dst;
      this.@src = @src;
      this.@msg = @msg;
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LPacket_LPacket<@IdType,@MessageType>;
      return oth != null && this.@dst.Equals(oth.@dst) && this.@src.Equals(oth.@src) && this.@msg.Equals(oth.@msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@dst.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@src.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@msg.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LPacket.LPacket";
      s += "(";
      s += @dst.ToString();
      s += ", ";
      s += @src.ToString();
      s += ", ";
      s += @msg.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LPacket<@IdType,@MessageType> {
    Base_LPacket<@IdType,@MessageType> _d;
    public Base_LPacket<@IdType,@MessageType> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LPacket(Base_LPacket<@IdType,@MessageType> d) { this._d = d; }
    static Base_LPacket<@IdType,@MessageType> theDefault;
    public static Base_LPacket<@IdType,@MessageType> Default {
      get {
        if (theDefault == null) {
          theDefault = new _Liveness____Environment__s_Compile.@LPacket_LPacket<@IdType,@MessageType>(default(@IdType), default(@IdType), default(@MessageType));
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LPacket<@IdType,@MessageType> && _D.Equals(((@LPacket<@IdType,@MessageType>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LPacket { get { return _D is LPacket_LPacket<@IdType,@MessageType>; } }
    public @IdType dtor_dst { get { return ((LPacket_LPacket<@IdType,@MessageType>)_D).@dst; } }
    public @IdType dtor_src { get { return ((LPacket_LPacket<@IdType,@MessageType>)_D).@src; } }
    public @MessageType dtor_msg { get { return ((LPacket_LPacket<@IdType,@MessageType>)_D).@msg; } }
  }

  public abstract class Base_LIoOp<@IdType,@MessageType> { }
  public partial class LIoOp_LIoOpSend<@IdType,@MessageType> : Base_LIoOp<@IdType,@MessageType> {
    public readonly @_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType> @s;
    public LIoOp_LIoOpSend(@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType> @s) {
      this.@s = @s;
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LIoOp_LIoOpSend<@IdType,@MessageType>;
      return oth != null && this.@s.Equals(oth.@s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@s.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LIoOp.LIoOpSend";
      s += "(";
      s += @s.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LIoOp_LIoOpReceive<@IdType,@MessageType> : Base_LIoOp<@IdType,@MessageType> {
    public readonly @_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType> @r;
    public LIoOp_LIoOpReceive(@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType> @r) {
      this.@r = @r;
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LIoOp_LIoOpReceive<@IdType,@MessageType>;
      return oth != null && this.@r.Equals(oth.@r);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@r.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LIoOp.LIoOpReceive";
      s += "(";
      s += @r.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LIoOp_LIoOpTimeoutReceive<@IdType,@MessageType> : Base_LIoOp<@IdType,@MessageType> {
    public LIoOp_LIoOpTimeoutReceive() {
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LIoOp_LIoOpTimeoutReceive<@IdType,@MessageType>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LIoOp.LIoOpTimeoutReceive";
      return s;
    }
  }
  public partial class LIoOp_LIoOpReadClock<@IdType,@MessageType> : Base_LIoOp<@IdType,@MessageType> {
    public readonly BigInteger @min;
    public readonly BigInteger @max;
    public LIoOp_LIoOpReadClock(BigInteger @min, BigInteger @max) {
      this.@min = @min;
      this.@max = @max;
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LIoOp_LIoOpReadClock<@IdType,@MessageType>;
      return oth != null && this.@min.Equals(oth.@min) && this.@max.Equals(oth.@max);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@min.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@max.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LIoOp.LIoOpReadClock";
      s += "(";
      s += @min.ToString();
      s += ", ";
      s += @max.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LIoOp<@IdType,@MessageType> {
    Base_LIoOp<@IdType,@MessageType> _d;
    public Base_LIoOp<@IdType,@MessageType> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LIoOp(Base_LIoOp<@IdType,@MessageType> d) { this._d = d; }
    static Base_LIoOp<@IdType,@MessageType> theDefault;
    public static Base_LIoOp<@IdType,@MessageType> Default {
      get {
        if (theDefault == null) {
          theDefault = new _Liveness____Environment__s_Compile.@LIoOp_LIoOpSend<@IdType,@MessageType>(new @_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType>());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LIoOp<@IdType,@MessageType> && _D.Equals(((@LIoOp<@IdType,@MessageType>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LIoOpSend { get { return _D is LIoOp_LIoOpSend<@IdType,@MessageType>; } }
    public bool is_LIoOpReceive { get { return _D is LIoOp_LIoOpReceive<@IdType,@MessageType>; } }
    public bool is_LIoOpTimeoutReceive { get { return _D is LIoOp_LIoOpTimeoutReceive<@IdType,@MessageType>; } }
    public bool is_LIoOpReadClock { get { return _D is LIoOp_LIoOpReadClock<@IdType,@MessageType>; } }
    public @_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType> dtor_s { get { return ((LIoOp_LIoOpSend<@IdType,@MessageType>)_D).@s; } }
    public @_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType> dtor_r { get { return ((LIoOp_LIoOpReceive<@IdType,@MessageType>)_D).@r; } }
    public BigInteger dtor_min { get { return ((LIoOp_LIoOpReadClock<@IdType,@MessageType>)_D).@min; } }
    public BigInteger dtor_max { get { return ((LIoOp_LIoOpReadClock<@IdType,@MessageType>)_D).@max; } }
  }

  public abstract class Base_LEnvStep<@IdType,@MessageType> { }
  public partial class LEnvStep_LEnvStepHostIos<@IdType,@MessageType> : Base_LEnvStep<@IdType,@MessageType> {
    public readonly @IdType @actor;
    public readonly Dafny.Sequence<@_Liveness____Environment__s_Compile.@LIoOp<@IdType,@MessageType>> @ios;
    public LEnvStep_LEnvStepHostIos(@IdType @actor, Dafny.Sequence<@_Liveness____Environment__s_Compile.@LIoOp<@IdType,@MessageType>> @ios) {
      this.@actor = @actor;
      this.@ios = @ios;
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LEnvStep_LEnvStepHostIos<@IdType,@MessageType>;
      return oth != null && this.@actor.Equals(oth.@actor) && this.@ios.Equals(oth.@ios);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@actor.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@ios.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LEnvStep.LEnvStepHostIos";
      s += "(";
      s += @actor.ToString();
      s += ", ";
      s += @ios.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LEnvStep_LEnvStepDeliverPacket<@IdType,@MessageType> : Base_LEnvStep<@IdType,@MessageType> {
    public readonly @_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType> @p;
    public LEnvStep_LEnvStepDeliverPacket(@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType> @p) {
      this.@p = @p;
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LEnvStep_LEnvStepDeliverPacket<@IdType,@MessageType>;
      return oth != null && this.@p.Equals(oth.@p);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@p.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LEnvStep.LEnvStepDeliverPacket";
      s += "(";
      s += @p.ToString();
      s += ")";
      return s;
    }
  }
  public partial class LEnvStep_LEnvStepAdvanceTime<@IdType,@MessageType> : Base_LEnvStep<@IdType,@MessageType> {
    public LEnvStep_LEnvStepAdvanceTime() {
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LEnvStep_LEnvStepAdvanceTime<@IdType,@MessageType>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LEnvStep.LEnvStepAdvanceTime";
      return s;
    }
  }
  public partial class LEnvStep_LEnvStepStutter<@IdType,@MessageType> : Base_LEnvStep<@IdType,@MessageType> {
    public LEnvStep_LEnvStepStutter() {
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LEnvStep_LEnvStepStutter<@IdType,@MessageType>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LEnvStep.LEnvStepStutter";
      return s;
    }
  }
  public struct @LEnvStep<@IdType,@MessageType> {
    Base_LEnvStep<@IdType,@MessageType> _d;
    public Base_LEnvStep<@IdType,@MessageType> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LEnvStep(Base_LEnvStep<@IdType,@MessageType> d) { this._d = d; }
    static Base_LEnvStep<@IdType,@MessageType> theDefault;
    public static Base_LEnvStep<@IdType,@MessageType> Default {
      get {
        if (theDefault == null) {
          theDefault = new _Liveness____Environment__s_Compile.@LEnvStep_LEnvStepHostIos<@IdType,@MessageType>(default(@IdType), Dafny.Sequence<@_Liveness____Environment__s_Compile.@LIoOp<@IdType,@MessageType>>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LEnvStep<@IdType,@MessageType> && _D.Equals(((@LEnvStep<@IdType,@MessageType>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LEnvStepHostIos { get { return _D is LEnvStep_LEnvStepHostIos<@IdType,@MessageType>; } }
    public bool is_LEnvStepDeliverPacket { get { return _D is LEnvStep_LEnvStepDeliverPacket<@IdType,@MessageType>; } }
    public bool is_LEnvStepAdvanceTime { get { return _D is LEnvStep_LEnvStepAdvanceTime<@IdType,@MessageType>; } }
    public bool is_LEnvStepStutter { get { return _D is LEnvStep_LEnvStepStutter<@IdType,@MessageType>; } }
    public @IdType dtor_actor { get { return ((LEnvStep_LEnvStepHostIos<@IdType,@MessageType>)_D).@actor; } }
    public Dafny.Sequence<@_Liveness____Environment__s_Compile.@LIoOp<@IdType,@MessageType>> dtor_ios { get { return ((LEnvStep_LEnvStepHostIos<@IdType,@MessageType>)_D).@ios; } }
    public @_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType> dtor_p { get { return ((LEnvStep_LEnvStepDeliverPacket<@IdType,@MessageType>)_D).@p; } }
  }

  public abstract class Base_LHostInfo<@IdType,@MessageType> { }
  public partial class LHostInfo_LHostInfo<@IdType,@MessageType> : Base_LHostInfo<@IdType,@MessageType> {
    public readonly Dafny.Sequence<@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType>> @queue;
    public LHostInfo_LHostInfo(Dafny.Sequence<@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType>> @queue) {
      this.@queue = @queue;
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LHostInfo_LHostInfo<@IdType,@MessageType>;
      return oth != null && this.@queue.Equals(oth.@queue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@queue.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LHostInfo.LHostInfo";
      s += "(";
      s += @queue.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LHostInfo<@IdType,@MessageType> {
    Base_LHostInfo<@IdType,@MessageType> _d;
    public Base_LHostInfo<@IdType,@MessageType> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LHostInfo(Base_LHostInfo<@IdType,@MessageType> d) { this._d = d; }
    static Base_LHostInfo<@IdType,@MessageType> theDefault;
    public static Base_LHostInfo<@IdType,@MessageType> Default {
      get {
        if (theDefault == null) {
          theDefault = new _Liveness____Environment__s_Compile.@LHostInfo_LHostInfo<@IdType,@MessageType>(Dafny.Sequence<@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType>>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LHostInfo<@IdType,@MessageType> && _D.Equals(((@LHostInfo<@IdType,@MessageType>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LHostInfo { get { return _D is LHostInfo_LHostInfo<@IdType,@MessageType>; } }
    public Dafny.Sequence<@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType>> dtor_queue { get { return ((LHostInfo_LHostInfo<@IdType,@MessageType>)_D).@queue; } }
  }

  public abstract class Base_LEnvironment<@IdType,@MessageType> { }
  public partial class LEnvironment_LEnvironment<@IdType,@MessageType> : Base_LEnvironment<@IdType,@MessageType> {
    public readonly BigInteger @time;
    public readonly Dafny.Set<@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType>> @sentPackets;
    public readonly Dafny.Map<@IdType,@_Liveness____Environment__s_Compile.@LHostInfo<@IdType,@MessageType>> @hostInfo;
    public readonly @_Liveness____Environment__s_Compile.@LEnvStep<@IdType,@MessageType> @nextStep;
    public LEnvironment_LEnvironment(BigInteger @time, Dafny.Set<@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType>> @sentPackets, Dafny.Map<@IdType,@_Liveness____Environment__s_Compile.@LHostInfo<@IdType,@MessageType>> @hostInfo, @_Liveness____Environment__s_Compile.@LEnvStep<@IdType,@MessageType> @nextStep) {
      this.@time = @time;
      this.@sentPackets = @sentPackets;
      this.@hostInfo = @hostInfo;
      this.@nextStep = @nextStep;
    }
    public override bool Equals(object other) {
      var oth = other as _Liveness____Environment__s_Compile.@LEnvironment_LEnvironment<@IdType,@MessageType>;
      return oth != null && this.@time.Equals(oth.@time) && this.@sentPackets.Equals(oth.@sentPackets) && this.@hostInfo.Equals(oth.@hostInfo) && this.@nextStep.Equals(oth.@nextStep);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@time.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@sentPackets.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@hostInfo.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@nextStep.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Liveness____Environment__s_Compile.LEnvironment.LEnvironment";
      s += "(";
      s += @time.ToString();
      s += ", ";
      s += @sentPackets.ToString();
      s += ", ";
      s += @hostInfo.ToString();
      s += ", ";
      s += @nextStep.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LEnvironment<@IdType,@MessageType> {
    Base_LEnvironment<@IdType,@MessageType> _d;
    public Base_LEnvironment<@IdType,@MessageType> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LEnvironment(Base_LEnvironment<@IdType,@MessageType> d) { this._d = d; }
    static Base_LEnvironment<@IdType,@MessageType> theDefault;
    public static Base_LEnvironment<@IdType,@MessageType> Default {
      get {
        if (theDefault == null) {
          theDefault = new _Liveness____Environment__s_Compile.@LEnvironment_LEnvironment<@IdType,@MessageType>(BigInteger.Zero, Dafny.Set<@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType>>.Empty, Dafny.Map<@IdType,@_Liveness____Environment__s_Compile.@LHostInfo<@IdType,@MessageType>>.Empty, new @_Liveness____Environment__s_Compile.@LEnvStep<@IdType,@MessageType>());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LEnvironment<@IdType,@MessageType> && _D.Equals(((@LEnvironment<@IdType,@MessageType>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LEnvironment { get { return _D is LEnvironment_LEnvironment<@IdType,@MessageType>; } }
    public BigInteger dtor_time { get { return ((LEnvironment_LEnvironment<@IdType,@MessageType>)_D).@time; } }
    public Dafny.Set<@_Liveness____Environment__s_Compile.@LPacket<@IdType,@MessageType>> dtor_sentPackets { get { return ((LEnvironment_LEnvironment<@IdType,@MessageType>)_D).@sentPackets; } }
    public Dafny.Map<@IdType,@_Liveness____Environment__s_Compile.@LHostInfo<@IdType,@MessageType>> dtor_hostInfo { get { return ((LEnvironment_LEnvironment<@IdType,@MessageType>)_D).@hostInfo; } }
    public @_Liveness____Environment__s_Compile.@LEnvStep<@IdType,@MessageType> dtor_nextStep { get { return ((LEnvironment_LEnvironment<@IdType,@MessageType>)_D).@nextStep; } }
  }

  public partial class @__default {
  }
} // end of namespace _Liveness____Environment__s_Compile
namespace @_LiveRSL____Environment__i_Compile {







  public partial class @__default {
  }
} // end of namespace _LiveRSL____Environment__i_Compile
namespace @_LiveRSL____BoundedClock__i_Compile {

  public abstract class Base_BoundedClock { }
  public partial class BoundedClock_BoundedClock : Base_BoundedClock {
    public readonly BigInteger @min;
    public readonly BigInteger @max;
    public BoundedClock_BoundedClock(BigInteger @min, BigInteger @max) {
      this.@min = @min;
      this.@max = @max;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____BoundedClock__i_Compile.@BoundedClock_BoundedClock;
      return oth != null && this.@min.Equals(oth.@min) && this.@max.Equals(oth.@max);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@min.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@max.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____BoundedClock__i_Compile.BoundedClock.BoundedClock";
      s += "(";
      s += @min.ToString();
      s += ", ";
      s += @max.ToString();
      s += ")";
      return s;
    }
  }
  public struct @BoundedClock {
    Base_BoundedClock _d;
    public Base_BoundedClock _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @BoundedClock(Base_BoundedClock d) { this._d = d; }
    static Base_BoundedClock theDefault;
    public static Base_BoundedClock Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____BoundedClock__i_Compile.@BoundedClock_BoundedClock(BigInteger.Zero, BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @BoundedClock && _D.Equals(((@BoundedClock)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_BoundedClock { get { return _D is BoundedClock_BoundedClock; } }
    public BigInteger dtor_min { get { return ((BoundedClock_BoundedClock)_D).@min; } }
    public BigInteger dtor_max { get { return ((BoundedClock_BoundedClock)_D).@max; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____BoundedClock__i_Compile
namespace @_RSL____Constants__i_Compile {



  public abstract class Base_Constants { }
  public partial class Constants_Constants : Base_Constants {
    public readonly @_RSL____Configuration__i_Compile.@Configuration @config;
    public readonly @_RSL____Parameters__i_Compile.@Parameters @params;
    public Constants_Constants(@_RSL____Configuration__i_Compile.@Configuration @config, @_RSL____Parameters__i_Compile.@Parameters @params) {
      this.@config = @config;
      this.@params = @params;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Constants__i_Compile.@Constants_Constants;
      return oth != null && this.@config.Equals(oth.@config) && this.@params.Equals(oth.@params);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@config.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@params.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Constants__i_Compile.Constants.Constants";
      s += "(";
      s += @config.ToString();
      s += ", ";
      s += @params.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Constants {
    Base_Constants _d;
    public Base_Constants _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Constants(Base_Constants d) { this._d = d; }
    static Base_Constants theDefault;
    public static Base_Constants Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Constants__i_Compile.@Constants_Constants(new @_RSL____Configuration__i_Compile.@Configuration(), new @_RSL____Parameters__i_Compile.@Parameters());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Constants && _D.Equals(((@Constants)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Constants { get { return _D is Constants_Constants; } }
    public @_RSL____Configuration__i_Compile.@Configuration dtor_config { get { return ((Constants_Constants)_D).@config; } }
    public @_RSL____Parameters__i_Compile.@Parameters dtor_params { get { return ((Constants_Constants)_D).@params; } }
  }

  public abstract class Base_ReplicaConstants { }
  public partial class ReplicaConstants_ReplicaConstants : Base_ReplicaConstants {
    public readonly BigInteger @me;
    public readonly BigInteger @myIndex;
    public readonly @_RSL____Constants__i_Compile.@Constants @all;
    public ReplicaConstants_ReplicaConstants(BigInteger @me, BigInteger @myIndex, @_RSL____Constants__i_Compile.@Constants @all) {
      this.@me = @me;
      this.@myIndex = @myIndex;
      this.@all = @all;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Constants__i_Compile.@ReplicaConstants_ReplicaConstants;
      return oth != null && this.@me.Equals(oth.@me) && this.@myIndex.Equals(oth.@myIndex) && this.@all.Equals(oth.@all);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@me.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@myIndex.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@all.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Constants__i_Compile.ReplicaConstants.ReplicaConstants";
      s += "(";
      s += @me.ToString();
      s += ", ";
      s += @myIndex.ToString();
      s += ", ";
      s += @all.ToString();
      s += ")";
      return s;
    }
  }
  public struct @ReplicaConstants {
    Base_ReplicaConstants _d;
    public Base_ReplicaConstants _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ReplicaConstants(Base_ReplicaConstants d) { this._d = d; }
    static Base_ReplicaConstants theDefault;
    public static Base_ReplicaConstants Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Constants__i_Compile.@ReplicaConstants_ReplicaConstants(BigInteger.Zero, BigInteger.Zero, new @_RSL____Constants__i_Compile.@Constants());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ReplicaConstants && _D.Equals(((@ReplicaConstants)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_ReplicaConstants { get { return _D is ReplicaConstants_ReplicaConstants; } }
    public BigInteger dtor_me { get { return ((ReplicaConstants_ReplicaConstants)_D).@me; } }
    public BigInteger dtor_myIndex { get { return ((ReplicaConstants_ReplicaConstants)_D).@myIndex; } }
    public @_RSL____Constants__i_Compile.@Constants dtor_all { get { return ((ReplicaConstants_ReplicaConstants)_D).@all; } }
  }

  public partial class @__default {
  }
} // end of namespace _RSL____Constants__i_Compile
namespace @_LiveRSL____Constants__i_Compile {




  public abstract class Base_LConstants { }
  public partial class LConstants_LConstants : Base_LConstants {
    public readonly @_LiveRSL____Configuration__i_Compile.@LConfiguration @config;
    public readonly @_LiveRSL____Parameters__i_Compile.@LParameters @params;
    public LConstants_LConstants(@_LiveRSL____Configuration__i_Compile.@LConfiguration @config, @_LiveRSL____Parameters__i_Compile.@LParameters @params) {
      this.@config = @config;
      this.@params = @params;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Constants__i_Compile.@LConstants_LConstants;
      return oth != null && this.@config.Equals(oth.@config) && this.@params.Equals(oth.@params);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@config.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@params.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Constants__i_Compile.LConstants.LConstants";
      s += "(";
      s += @config.ToString();
      s += ", ";
      s += @params.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LConstants {
    Base_LConstants _d;
    public Base_LConstants _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LConstants(Base_LConstants d) { this._d = d; }
    static Base_LConstants theDefault;
    public static Base_LConstants Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Constants__i_Compile.@LConstants_LConstants(new @_LiveRSL____Configuration__i_Compile.@LConfiguration(), new @_LiveRSL____Parameters__i_Compile.@LParameters());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LConstants && _D.Equals(((@LConstants)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LConstants { get { return _D is LConstants_LConstants; } }
    public @_LiveRSL____Configuration__i_Compile.@LConfiguration dtor_config { get { return ((LConstants_LConstants)_D).@config; } }
    public @_LiveRSL____Parameters__i_Compile.@LParameters dtor_params { get { return ((LConstants_LConstants)_D).@params; } }
  }

  public abstract class Base_LReplicaConstants { }
  public partial class LReplicaConstants_LReplicaConstants : Base_LReplicaConstants {
    public readonly BigInteger @myIndex;
    public readonly @_LiveRSL____Constants__i_Compile.@LConstants @all;
    public LReplicaConstants_LReplicaConstants(BigInteger @myIndex, @_LiveRSL____Constants__i_Compile.@LConstants @all) {
      this.@myIndex = @myIndex;
      this.@all = @all;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Constants__i_Compile.@LReplicaConstants_LReplicaConstants;
      return oth != null && this.@myIndex.Equals(oth.@myIndex) && this.@all.Equals(oth.@all);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@myIndex.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@all.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Constants__i_Compile.LReplicaConstants.LReplicaConstants";
      s += "(";
      s += @myIndex.ToString();
      s += ", ";
      s += @all.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LReplicaConstants {
    Base_LReplicaConstants _d;
    public Base_LReplicaConstants _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LReplicaConstants(Base_LReplicaConstants d) { this._d = d; }
    static Base_LReplicaConstants theDefault;
    public static Base_LReplicaConstants Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Constants__i_Compile.@LReplicaConstants_LReplicaConstants(BigInteger.Zero, new @_LiveRSL____Constants__i_Compile.@LConstants());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LReplicaConstants && _D.Equals(((@LReplicaConstants)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LReplicaConstants { get { return _D is LReplicaConstants_LReplicaConstants; } }
    public BigInteger dtor_myIndex { get { return ((LReplicaConstants_LReplicaConstants)_D).@myIndex; } }
    public @_LiveRSL____Constants__i_Compile.@LConstants dtor_all { get { return ((LReplicaConstants_LReplicaConstants)_D).@all; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Constants__i_Compile
namespace @_LiveRSL____Broadcast__i_Compile {



  public partial class @__default {
  }
} // end of namespace _LiveRSL____Broadcast__i_Compile
namespace @_LiveRSL____Election__i_Compile {





  public abstract class Base_ElectionState { }
  public partial class ElectionState_ElectionState : Base_ElectionState {
    public readonly @_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants;
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @currentView;
    public readonly Dafny.Set<BigInteger> @currentViewSuspectors;
    public readonly BigInteger @epochEndTime;
    public readonly BigInteger @epochLength;
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @requestsReceivedThisEpoch;
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @requestsReceivedPrevEpochs;
    public ElectionState_ElectionState(@_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants, @_Common____TypesPPC__i_Compile.@Ballot @currentView, Dafny.Set<BigInteger> @currentViewSuspectors, BigInteger @epochEndTime, BigInteger @epochLength, Dafny.Sequence<@_Common____Types__s_Compile.@Request> @requestsReceivedThisEpoch, Dafny.Sequence<@_Common____Types__s_Compile.@Request> @requestsReceivedPrevEpochs) {
      this.@constants = @constants;
      this.@currentView = @currentView;
      this.@currentViewSuspectors = @currentViewSuspectors;
      this.@epochEndTime = @epochEndTime;
      this.@epochLength = @epochLength;
      this.@requestsReceivedThisEpoch = @requestsReceivedThisEpoch;
      this.@requestsReceivedPrevEpochs = @requestsReceivedPrevEpochs;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Election__i_Compile.@ElectionState_ElectionState;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@currentView.Equals(oth.@currentView) && this.@currentViewSuspectors.Equals(oth.@currentViewSuspectors) && this.@epochEndTime.Equals(oth.@epochEndTime) && this.@epochLength.Equals(oth.@epochLength) && this.@requestsReceivedThisEpoch.Equals(oth.@requestsReceivedThisEpoch) && this.@requestsReceivedPrevEpochs.Equals(oth.@requestsReceivedPrevEpochs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@currentView.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@currentViewSuspectors.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@epochEndTime.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@epochLength.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@requestsReceivedThisEpoch.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@requestsReceivedPrevEpochs.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Election__i_Compile.ElectionState.ElectionState";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @currentView.ToString();
      s += ", ";
      s += @currentViewSuspectors.ToString();
      s += ", ";
      s += @epochEndTime.ToString();
      s += ", ";
      s += @epochLength.ToString();
      s += ", ";
      s += @requestsReceivedThisEpoch.ToString();
      s += ", ";
      s += @requestsReceivedPrevEpochs.ToString();
      s += ")";
      return s;
    }
  }
  public struct @ElectionState {
    Base_ElectionState _d;
    public Base_ElectionState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ElectionState(Base_ElectionState d) { this._d = d; }
    static Base_ElectionState theDefault;
    public static Base_ElectionState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Election__i_Compile.@ElectionState_ElectionState(new @_LiveRSL____Constants__i_Compile.@LReplicaConstants(), new @_Common____TypesPPC__i_Compile.@Ballot(), Dafny.Set<BigInteger>.Empty, BigInteger.Zero, BigInteger.Zero, Dafny.Sequence<@_Common____Types__s_Compile.@Request>.Empty, Dafny.Sequence<@_Common____Types__s_Compile.@Request>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ElectionState && _D.Equals(((@ElectionState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_ElectionState { get { return _D is ElectionState_ElectionState; } }
    public @_LiveRSL____Constants__i_Compile.@LReplicaConstants dtor_constants { get { return ((ElectionState_ElectionState)_D).@constants; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_currentView { get { return ((ElectionState_ElectionState)_D).@currentView; } }
    public Dafny.Set<BigInteger> dtor_currentViewSuspectors { get { return ((ElectionState_ElectionState)_D).@currentViewSuspectors; } }
    public BigInteger dtor_epochEndTime { get { return ((ElectionState_ElectionState)_D).@epochEndTime; } }
    public BigInteger dtor_epochLength { get { return ((ElectionState_ElectionState)_D).@epochLength; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_requestsReceivedThisEpoch { get { return ((ElectionState_ElectionState)_D).@requestsReceivedThisEpoch; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_requestsReceivedPrevEpochs { get { return ((ElectionState_ElectionState)_D).@requestsReceivedPrevEpochs; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Election__i_Compile
namespace @_RSL____Network__i_Compile {


  public abstract class Base_Packet { }
  public partial class Packet_Packet : Base_Packet {
    public readonly BigInteger @dst;
    public readonly BigInteger @src;
    public readonly @_RSL____Message__i_Compile.@Message @msg;
    public Packet_Packet(BigInteger @dst, BigInteger @src, @_RSL____Message__i_Compile.@Message @msg) {
      this.@dst = @dst;
      this.@src = @src;
      this.@msg = @msg;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Network__i_Compile.@Packet_Packet;
      return oth != null && this.@dst.Equals(oth.@dst) && this.@src.Equals(oth.@src) && this.@msg.Equals(oth.@msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@dst.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@src.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@msg.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Network__i_Compile.Packet.Packet";
      s += "(";
      s += @dst.ToString();
      s += ", ";
      s += @src.ToString();
      s += ", ";
      s += @msg.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Packet {
    Base_Packet _d;
    public Base_Packet _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Packet(Base_Packet d) { this._d = d; }
    static Base_Packet theDefault;
    public static Base_Packet Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Network__i_Compile.@Packet_Packet(BigInteger.Zero, BigInteger.Zero, new @_RSL____Message__i_Compile.@Message());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Packet && _D.Equals(((@Packet)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Packet { get { return _D is Packet_Packet; } }
    public BigInteger dtor_dst { get { return ((Packet_Packet)_D).@dst; } }
    public BigInteger dtor_src { get { return ((Packet_Packet)_D).@src; } }
    public @_RSL____Message__i_Compile.@Message dtor_msg { get { return ((Packet_Packet)_D).@msg; } }
  }


  public partial class @__default {
  }
} // end of namespace _RSL____Network__i_Compile
namespace @_RSL____Broadcast__i_Compile {



  public partial class @__default {
  }
} // end of namespace _RSL____Broadcast__i_Compile
namespace @_Collections____Maps__i_Compile {

  public partial class @__default {
    public static Dafny.Set<@U> @domain<@U,@V>(Dafny.Map<@U,@V> @m) {
      return ((Dafny.Helpers.ComprehensionDelegate<@U>)delegate() { var _coll = new System.Collections.Generic.List<@U>(); foreach (var @_24590_s in (@m).Domain) { if ((@m).Contains(@_24590_s)) { _coll.Add(@_24590_s); }}return Dafny.Set<@U>.FromCollection(_coll); })();
    }
    public static Dafny.Map<@U,@V> @RemoveElt<@U,@V>(Dafny.Map<@U,@V> @m, @U @elt) {
      Dafny.Map<@U,@V> @_24591_m_k = ((Dafny.Helpers.MapComprehensionDelegate<@U,@V>)delegate() { var _coll = new System.Collections.Generic.List<Dafny.Pair<@U,@V>>(); foreach (var @_24592_elt_k in (@m).Domain) { if (((@m).Contains(@_24592_elt_k)) && (!(@_24592_elt_k).@Equals(@elt))) { _coll.Add(new Dafny.Pair<@U,@V>(@_24592_elt_k,(@m).Select(@_24592_elt_k))); }}return Dafny.Map<@U,@V>.FromCollection(_coll); })();
      return @_24591_m_k;
    }
  }
} // end of namespace _Collections____Maps__i_Compile
namespace @_Collections____Maps2__i_Compile {


  public partial class @__default {
  }
} // end of namespace _Collections____Maps2__i_Compile
namespace @_RSL____Acceptor__i_Compile {








  public abstract class Base_Acceptor { }
  public partial class Acceptor_Acceptor : Base_Acceptor {
    public readonly @_RSL____Constants__i_Compile.@ReplicaConstants @constants;
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @maxBal;
    public readonly Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> @votes;
    public readonly Dafny.Map<BigInteger,BigInteger> @lastCheckpointedOperation;
    public readonly BigInteger @logTruncationPoint;
    public Acceptor_Acceptor(@_RSL____Constants__i_Compile.@ReplicaConstants @constants, @_Common____TypesPPC__i_Compile.@Ballot @maxBal, Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> @votes, Dafny.Map<BigInteger,BigInteger> @lastCheckpointedOperation, BigInteger @logTruncationPoint) {
      this.@constants = @constants;
      this.@maxBal = @maxBal;
      this.@votes = @votes;
      this.@lastCheckpointedOperation = @lastCheckpointedOperation;
      this.@logTruncationPoint = @logTruncationPoint;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Acceptor__i_Compile.@Acceptor_Acceptor;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@maxBal.Equals(oth.@maxBal) && this.@votes.Equals(oth.@votes) && this.@lastCheckpointedOperation.Equals(oth.@lastCheckpointedOperation) && this.@logTruncationPoint.Equals(oth.@logTruncationPoint);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBal.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@votes.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@lastCheckpointedOperation.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@logTruncationPoint.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Acceptor__i_Compile.Acceptor.Acceptor";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @maxBal.ToString();
      s += ", ";
      s += @votes.ToString();
      s += ", ";
      s += @lastCheckpointedOperation.ToString();
      s += ", ";
      s += @logTruncationPoint.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Acceptor {
    Base_Acceptor _d;
    public Base_Acceptor _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Acceptor(Base_Acceptor d) { this._d = d; }
    static Base_Acceptor theDefault;
    public static Base_Acceptor Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Acceptor__i_Compile.@Acceptor_Acceptor(new @_RSL____Constants__i_Compile.@ReplicaConstants(), new @_Common____TypesPPC__i_Compile.@Ballot(), Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote>.Empty, Dafny.Map<BigInteger,BigInteger>.Empty, BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Acceptor && _D.Equals(((@Acceptor)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Acceptor { get { return _D is Acceptor_Acceptor; } }
    public @_RSL____Constants__i_Compile.@ReplicaConstants dtor_constants { get { return ((Acceptor_Acceptor)_D).@constants; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_maxBal { get { return ((Acceptor_Acceptor)_D).@maxBal; } }
    public Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> dtor_votes { get { return ((Acceptor_Acceptor)_D).@votes; } }
    public Dafny.Map<BigInteger,BigInteger> dtor_lastCheckpointedOperation { get { return ((Acceptor_Acceptor)_D).@lastCheckpointedOperation; } }
    public BigInteger dtor_logTruncationPoint { get { return ((Acceptor_Acceptor)_D).@logTruncationPoint; } }
  }

  public partial class @__default {
  }
} // end of namespace _RSL____Acceptor__i_Compile
namespace @_Collections____CountMatches__i_Compile {

  public partial class @__default {
  }
} // end of namespace _Collections____CountMatches__i_Compile
namespace @_LiveRSL____Acceptor__i_Compile {







  public abstract class Base_LAcceptor { }
  public partial class LAcceptor_LAcceptor : Base_LAcceptor {
    public readonly @_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants;
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @maxBal;
    public readonly Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> @votes;
    public readonly Dafny.Sequence<BigInteger> @lastCheckpointedOperation;
    public readonly BigInteger @logTruncationPoint;
    public LAcceptor_LAcceptor(@_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants, @_Common____TypesPPC__i_Compile.@Ballot @maxBal, Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> @votes, Dafny.Sequence<BigInteger> @lastCheckpointedOperation, BigInteger @logTruncationPoint) {
      this.@constants = @constants;
      this.@maxBal = @maxBal;
      this.@votes = @votes;
      this.@lastCheckpointedOperation = @lastCheckpointedOperation;
      this.@logTruncationPoint = @logTruncationPoint;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Acceptor__i_Compile.@LAcceptor_LAcceptor;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@maxBal.Equals(oth.@maxBal) && this.@votes.Equals(oth.@votes) && this.@lastCheckpointedOperation.Equals(oth.@lastCheckpointedOperation) && this.@logTruncationPoint.Equals(oth.@logTruncationPoint);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBal.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@votes.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@lastCheckpointedOperation.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@logTruncationPoint.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Acceptor__i_Compile.LAcceptor.LAcceptor";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @maxBal.ToString();
      s += ", ";
      s += @votes.ToString();
      s += ", ";
      s += @lastCheckpointedOperation.ToString();
      s += ", ";
      s += @logTruncationPoint.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LAcceptor {
    Base_LAcceptor _d;
    public Base_LAcceptor _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LAcceptor(Base_LAcceptor d) { this._d = d; }
    static Base_LAcceptor theDefault;
    public static Base_LAcceptor Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Acceptor__i_Compile.@LAcceptor_LAcceptor(new @_LiveRSL____Constants__i_Compile.@LReplicaConstants(), new @_Common____TypesPPC__i_Compile.@Ballot(), Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote>.Empty, Dafny.Sequence<BigInteger>.Empty, BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LAcceptor && _D.Equals(((@LAcceptor)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LAcceptor { get { return _D is LAcceptor_LAcceptor; } }
    public @_LiveRSL____Constants__i_Compile.@LReplicaConstants dtor_constants { get { return ((LAcceptor_LAcceptor)_D).@constants; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_maxBal { get { return ((LAcceptor_LAcceptor)_D).@maxBal; } }
    public Dafny.Map<BigInteger,@_Common____TypesPPC__i_Compile.@Vote> dtor_votes { get { return ((LAcceptor_LAcceptor)_D).@votes; } }
    public Dafny.Sequence<BigInteger> dtor_lastCheckpointedOperation { get { return ((LAcceptor_LAcceptor)_D).@lastCheckpointedOperation; } }
    public BigInteger dtor_logTruncationPoint { get { return ((LAcceptor_LAcceptor)_D).@logTruncationPoint; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Acceptor__i_Compile
namespace @_LiveRSL____Proposer__i_Compile {







  public abstract class Base_IncompleteBatchTimer { }
  public partial class IncompleteBatchTimer_IncompleteBatchTimerOn : Base_IncompleteBatchTimer {
    public readonly BigInteger @when;
    public IncompleteBatchTimer_IncompleteBatchTimerOn(BigInteger @when) {
      this.@when = @when;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Proposer__i_Compile.@IncompleteBatchTimer_IncompleteBatchTimerOn;
      return oth != null && this.@when.Equals(oth.@when);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@when.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Proposer__i_Compile.IncompleteBatchTimer.IncompleteBatchTimerOn";
      s += "(";
      s += @when.ToString();
      s += ")";
      return s;
    }
  }
  public partial class IncompleteBatchTimer_IncompleteBatchTimerOff : Base_IncompleteBatchTimer {
    public IncompleteBatchTimer_IncompleteBatchTimerOff() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Proposer__i_Compile.@IncompleteBatchTimer_IncompleteBatchTimerOff;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Proposer__i_Compile.IncompleteBatchTimer.IncompleteBatchTimerOff";
      return s;
    }
  }
  public struct @IncompleteBatchTimer {
    Base_IncompleteBatchTimer _d;
    public Base_IncompleteBatchTimer _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @IncompleteBatchTimer(Base_IncompleteBatchTimer d) { this._d = d; }
    static Base_IncompleteBatchTimer theDefault;
    public static Base_IncompleteBatchTimer Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Proposer__i_Compile.@IncompleteBatchTimer_IncompleteBatchTimerOn(BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @IncompleteBatchTimer && _D.Equals(((@IncompleteBatchTimer)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_IncompleteBatchTimerOn { get { return _D is IncompleteBatchTimer_IncompleteBatchTimerOn; } }
    public bool is_IncompleteBatchTimerOff { get { return _D is IncompleteBatchTimer_IncompleteBatchTimerOff; } }
    public BigInteger dtor_when { get { return ((IncompleteBatchTimer_IncompleteBatchTimerOn)_D).@when; } }
  }

  public abstract class Base_LProposer { }
  public partial class LProposer_LProposer : Base_LProposer {
    public readonly @_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants;
    public readonly BigInteger @currentState;
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @requestQueue;
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @maxBallotISent1a;
    public readonly BigInteger @nextOperationNumberToPropose;
    public readonly Dafny.Set<@_Liveness____Environment__s_Compile.@LPacket<BigInteger,@_LiveRSL____Message__i_Compile.@LPaxosMessage>> @received1bPackets;
    public readonly Dafny.Map<BigInteger,BigInteger> @highestSeqnoRequestedByClientThisView;
    public readonly @_LiveRSL____Proposer__i_Compile.@IncompleteBatchTimer @incompleteBatchTimer;
    public readonly @_LiveRSL____Election__i_Compile.@ElectionState @electionState;
    public readonly Dafny.Set<@_Common____Types__s_Compile.@Request> @requestedValues;
    public readonly Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>> @myProposedValues;
    public LProposer_LProposer(@_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants, BigInteger @currentState, Dafny.Sequence<@_Common____Types__s_Compile.@Request> @requestQueue, @_Common____TypesPPC__i_Compile.@Ballot @maxBallotISent1a, BigInteger @nextOperationNumberToPropose, Dafny.Set<@_Liveness____Environment__s_Compile.@LPacket<BigInteger,@_LiveRSL____Message__i_Compile.@LPaxosMessage>> @received1bPackets, Dafny.Map<BigInteger,BigInteger> @highestSeqnoRequestedByClientThisView, @_LiveRSL____Proposer__i_Compile.@IncompleteBatchTimer @incompleteBatchTimer, @_LiveRSL____Election__i_Compile.@ElectionState @electionState, Dafny.Set<@_Common____Types__s_Compile.@Request> @requestedValues, Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>> @myProposedValues) {
      this.@constants = @constants;
      this.@currentState = @currentState;
      this.@requestQueue = @requestQueue;
      this.@maxBallotISent1a = @maxBallotISent1a;
      this.@nextOperationNumberToPropose = @nextOperationNumberToPropose;
      this.@received1bPackets = @received1bPackets;
      this.@highestSeqnoRequestedByClientThisView = @highestSeqnoRequestedByClientThisView;
      this.@incompleteBatchTimer = @incompleteBatchTimer;
      this.@electionState = @electionState;
      this.@requestedValues = @requestedValues;
      this.@myProposedValues = @myProposedValues;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Proposer__i_Compile.@LProposer_LProposer;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@currentState.Equals(oth.@currentState) && this.@requestQueue.Equals(oth.@requestQueue) && this.@maxBallotISent1a.Equals(oth.@maxBallotISent1a) && this.@nextOperationNumberToPropose.Equals(oth.@nextOperationNumberToPropose) && this.@received1bPackets.Equals(oth.@received1bPackets) && this.@highestSeqnoRequestedByClientThisView.Equals(oth.@highestSeqnoRequestedByClientThisView) && this.@incompleteBatchTimer.Equals(oth.@incompleteBatchTimer) && this.@electionState.Equals(oth.@electionState) && this.@requestedValues.Equals(oth.@requestedValues) && this.@myProposedValues.Equals(oth.@myProposedValues);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@currentState.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@requestQueue.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBallotISent1a.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@nextOperationNumberToPropose.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@received1bPackets.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@highestSeqnoRequestedByClientThisView.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@incompleteBatchTimer.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@electionState.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@requestedValues.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@myProposedValues.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Proposer__i_Compile.LProposer.LProposer";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @currentState.ToString();
      s += ", ";
      s += @requestQueue.ToString();
      s += ", ";
      s += @maxBallotISent1a.ToString();
      s += ", ";
      s += @nextOperationNumberToPropose.ToString();
      s += ", ";
      s += @received1bPackets.ToString();
      s += ", ";
      s += @highestSeqnoRequestedByClientThisView.ToString();
      s += ", ";
      s += @incompleteBatchTimer.ToString();
      s += ", ";
      s += @electionState.ToString();
      s += ", ";
      s += @requestedValues.ToString();
      s += ", ";
      s += @myProposedValues.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LProposer {
    Base_LProposer _d;
    public Base_LProposer _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LProposer(Base_LProposer d) { this._d = d; }
    static Base_LProposer theDefault;
    public static Base_LProposer Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Proposer__i_Compile.@LProposer_LProposer(new @_LiveRSL____Constants__i_Compile.@LReplicaConstants(), BigInteger.Zero, Dafny.Sequence<@_Common____Types__s_Compile.@Request>.Empty, new @_Common____TypesPPC__i_Compile.@Ballot(), BigInteger.Zero, Dafny.Set<@_Liveness____Environment__s_Compile.@LPacket<BigInteger,@_LiveRSL____Message__i_Compile.@LPaxosMessage>>.Empty, Dafny.Map<BigInteger,BigInteger>.Empty, new @_LiveRSL____Proposer__i_Compile.@IncompleteBatchTimer(), new @_LiveRSL____Election__i_Compile.@ElectionState(), Dafny.Set<@_Common____Types__s_Compile.@Request>.Empty, Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LProposer && _D.Equals(((@LProposer)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LProposer { get { return _D is LProposer_LProposer; } }
    public @_LiveRSL____Constants__i_Compile.@LReplicaConstants dtor_constants { get { return ((LProposer_LProposer)_D).@constants; } }
    public BigInteger dtor_currentState { get { return ((LProposer_LProposer)_D).@currentState; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_requestQueue { get { return ((LProposer_LProposer)_D).@requestQueue; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_maxBallotISent1a { get { return ((LProposer_LProposer)_D).@maxBallotISent1a; } }
    public BigInteger dtor_nextOperationNumberToPropose { get { return ((LProposer_LProposer)_D).@nextOperationNumberToPropose; } }
    public Dafny.Set<@_Liveness____Environment__s_Compile.@LPacket<BigInteger,@_LiveRSL____Message__i_Compile.@LPaxosMessage>> dtor_received1bPackets { get { return ((LProposer_LProposer)_D).@received1bPackets; } }
    public Dafny.Map<BigInteger,BigInteger> dtor_highestSeqnoRequestedByClientThisView { get { return ((LProposer_LProposer)_D).@highestSeqnoRequestedByClientThisView; } }
    public @_LiveRSL____Proposer__i_Compile.@IncompleteBatchTimer dtor_incompleteBatchTimer { get { return ((LProposer_LProposer)_D).@incompleteBatchTimer; } }
    public @_LiveRSL____Election__i_Compile.@ElectionState dtor_electionState { get { return ((LProposer_LProposer)_D).@electionState; } }
    public Dafny.Set<@_Common____Types__s_Compile.@Request> dtor_requestedValues { get { return ((LProposer_LProposer)_D).@requestedValues; } }
    public Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>> dtor_myProposedValues { get { return ((LProposer_LProposer)_D).@myProposedValues; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Proposer__i_Compile
namespace @_RSL____Executor__i_Compile {








  public abstract class Base_Executor { }
  public partial class Executor_Executor : Base_Executor {
    public readonly @_RSL____Constants__i_Compile.@ReplicaConstants @constants;
    public readonly BigInteger @app;
    public readonly BigInteger @opsComplete;
    public readonly Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>> @outstandingOps;
    public readonly Dafny.Set<@_Common____Types__s_Compile.@Reply> @replyCache;
    public Executor_Executor(@_RSL____Constants__i_Compile.@ReplicaConstants @constants, BigInteger @app, BigInteger @opsComplete, Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>> @outstandingOps, Dafny.Set<@_Common____Types__s_Compile.@Reply> @replyCache) {
      this.@constants = @constants;
      this.@app = @app;
      this.@opsComplete = @opsComplete;
      this.@outstandingOps = @outstandingOps;
      this.@replyCache = @replyCache;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Executor__i_Compile.@Executor_Executor;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@app.Equals(oth.@app) && this.@opsComplete.Equals(oth.@opsComplete) && this.@outstandingOps.Equals(oth.@outstandingOps) && this.@replyCache.Equals(oth.@replyCache);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@app.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opsComplete.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@outstandingOps.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@replyCache.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Executor__i_Compile.Executor.Executor";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @app.ToString();
      s += ", ";
      s += @opsComplete.ToString();
      s += ", ";
      s += @outstandingOps.ToString();
      s += ", ";
      s += @replyCache.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Executor {
    Base_Executor _d;
    public Base_Executor _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Executor(Base_Executor d) { this._d = d; }
    static Base_Executor theDefault;
    public static Base_Executor Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Executor__i_Compile.@Executor_Executor(new @_RSL____Constants__i_Compile.@ReplicaConstants(), BigInteger.Zero, BigInteger.Zero, Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>>.Empty, Dafny.Set<@_Common____Types__s_Compile.@Reply>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Executor && _D.Equals(((@Executor)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Executor { get { return _D is Executor_Executor; } }
    public @_RSL____Constants__i_Compile.@ReplicaConstants dtor_constants { get { return ((Executor_Executor)_D).@constants; } }
    public BigInteger dtor_app { get { return ((Executor_Executor)_D).@app; } }
    public BigInteger dtor_opsComplete { get { return ((Executor_Executor)_D).@opsComplete; } }
    public Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>> dtor_outstandingOps { get { return ((Executor_Executor)_D).@outstandingOps; } }
    public Dafny.Set<@_Common____Types__s_Compile.@Reply> dtor_replyCache { get { return ((Executor_Executor)_D).@replyCache; } }
  }

  public partial class @__default {
  }
} // end of namespace _RSL____Executor__i_Compile
namespace @_LiveRSL____Executor__i_Compile {









  public abstract class Base_OutstandingOperation { }
  public partial class OutstandingOperation_OutstandingOpKnown : Base_OutstandingOperation {
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @v;
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @bal;
    public OutstandingOperation_OutstandingOpKnown(Dafny.Sequence<@_Common____Types__s_Compile.@Request> @v, @_Common____TypesPPC__i_Compile.@Ballot @bal) {
      this.@v = @v;
      this.@bal = @bal;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Executor__i_Compile.@OutstandingOperation_OutstandingOpKnown;
      return oth != null && this.@v.Equals(oth.@v) && this.@bal.Equals(oth.@bal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@v.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@bal.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Executor__i_Compile.OutstandingOperation.OutstandingOpKnown";
      s += "(";
      s += @v.ToString();
      s += ", ";
      s += @bal.ToString();
      s += ")";
      return s;
    }
  }
  public partial class OutstandingOperation_OutstandingOpUnknown : Base_OutstandingOperation {
    public OutstandingOperation_OutstandingOpUnknown() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Executor__i_Compile.@OutstandingOperation_OutstandingOpUnknown;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Executor__i_Compile.OutstandingOperation.OutstandingOpUnknown";
      return s;
    }
  }
  public struct @OutstandingOperation {
    Base_OutstandingOperation _d;
    public Base_OutstandingOperation _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @OutstandingOperation(Base_OutstandingOperation d) { this._d = d; }
    static Base_OutstandingOperation theDefault;
    public static Base_OutstandingOperation Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Executor__i_Compile.@OutstandingOperation_OutstandingOpKnown(Dafny.Sequence<@_Common____Types__s_Compile.@Request>.Empty, new @_Common____TypesPPC__i_Compile.@Ballot());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @OutstandingOperation && _D.Equals(((@OutstandingOperation)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_OutstandingOpKnown { get { return _D is OutstandingOperation_OutstandingOpKnown; } }
    public bool is_OutstandingOpUnknown { get { return _D is OutstandingOperation_OutstandingOpUnknown; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_v { get { return ((OutstandingOperation_OutstandingOpKnown)_D).@v; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_bal { get { return ((OutstandingOperation_OutstandingOpKnown)_D).@bal; } }
  }

  public abstract class Base_LExecutor { }
  public partial class LExecutor_LExecutor : Base_LExecutor {
    public readonly @_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants;
    public readonly BigInteger @app;
    public readonly BigInteger @opsComplete;
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @maxBalReflected;
    public readonly @_LiveRSL____Executor__i_Compile.@OutstandingOperation @nextOpToExecute;
    public readonly Dafny.Map<BigInteger,@_Common____Types__s_Compile.@Reply> @replyCache;
    public readonly Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>> @outstandingOps;
    public LExecutor_LExecutor(@_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants, BigInteger @app, BigInteger @opsComplete, @_Common____TypesPPC__i_Compile.@Ballot @maxBalReflected, @_LiveRSL____Executor__i_Compile.@OutstandingOperation @nextOpToExecute, Dafny.Map<BigInteger,@_Common____Types__s_Compile.@Reply> @replyCache, Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>> @outstandingOps) {
      this.@constants = @constants;
      this.@app = @app;
      this.@opsComplete = @opsComplete;
      this.@maxBalReflected = @maxBalReflected;
      this.@nextOpToExecute = @nextOpToExecute;
      this.@replyCache = @replyCache;
      this.@outstandingOps = @outstandingOps;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Executor__i_Compile.@LExecutor_LExecutor;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@app.Equals(oth.@app) && this.@opsComplete.Equals(oth.@opsComplete) && this.@maxBalReflected.Equals(oth.@maxBalReflected) && this.@nextOpToExecute.Equals(oth.@nextOpToExecute) && this.@replyCache.Equals(oth.@replyCache) && this.@outstandingOps.Equals(oth.@outstandingOps);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@app.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opsComplete.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBalReflected.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@nextOpToExecute.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@replyCache.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@outstandingOps.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Executor__i_Compile.LExecutor.LExecutor";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @app.ToString();
      s += ", ";
      s += @opsComplete.ToString();
      s += ", ";
      s += @maxBalReflected.ToString();
      s += ", ";
      s += @nextOpToExecute.ToString();
      s += ", ";
      s += @replyCache.ToString();
      s += ", ";
      s += @outstandingOps.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LExecutor {
    Base_LExecutor _d;
    public Base_LExecutor _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LExecutor(Base_LExecutor d) { this._d = d; }
    static Base_LExecutor theDefault;
    public static Base_LExecutor Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Executor__i_Compile.@LExecutor_LExecutor(new @_LiveRSL____Constants__i_Compile.@LReplicaConstants(), BigInteger.Zero, BigInteger.Zero, new @_Common____TypesPPC__i_Compile.@Ballot(), new @_LiveRSL____Executor__i_Compile.@OutstandingOperation(), Dafny.Map<BigInteger,@_Common____Types__s_Compile.@Reply>.Empty, Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LExecutor && _D.Equals(((@LExecutor)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LExecutor { get { return _D is LExecutor_LExecutor; } }
    public @_LiveRSL____Constants__i_Compile.@LReplicaConstants dtor_constants { get { return ((LExecutor_LExecutor)_D).@constants; } }
    public BigInteger dtor_app { get { return ((LExecutor_LExecutor)_D).@app; } }
    public BigInteger dtor_opsComplete { get { return ((LExecutor_LExecutor)_D).@opsComplete; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_maxBalReflected { get { return ((LExecutor_LExecutor)_D).@maxBalReflected; } }
    public @_LiveRSL____Executor__i_Compile.@OutstandingOperation dtor_nextOpToExecute { get { return ((LExecutor_LExecutor)_D).@nextOpToExecute; } }
    public Dafny.Map<BigInteger,@_Common____Types__s_Compile.@Reply> dtor_replyCache { get { return ((LExecutor_LExecutor)_D).@replyCache; } }
    public Dafny.Map<BigInteger,Dafny.Sequence<@_Common____Types__s_Compile.@Request>> dtor_outstandingOps { get { return ((LExecutor_LExecutor)_D).@outstandingOps; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Executor__i_Compile
namespace @_RSL____Learner__i_Compile {







  public abstract class Base_LearnerTuple { }
  public partial class LearnerTuple_LearnerTuple : Base_LearnerTuple {
    public readonly Dafny.Set<BigInteger> @received2bMessageSenders;
    public readonly Dafny.Sequence<@_Common____Types__s_Compile.@Request> @candidateLearnedValue;
    public LearnerTuple_LearnerTuple(Dafny.Set<BigInteger> @received2bMessageSenders, Dafny.Sequence<@_Common____Types__s_Compile.@Request> @candidateLearnedValue) {
      this.@received2bMessageSenders = @received2bMessageSenders;
      this.@candidateLearnedValue = @candidateLearnedValue;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Learner__i_Compile.@LearnerTuple_LearnerTuple;
      return oth != null && this.@received2bMessageSenders.Equals(oth.@received2bMessageSenders) && this.@candidateLearnedValue.Equals(oth.@candidateLearnedValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@received2bMessageSenders.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@candidateLearnedValue.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Learner__i_Compile.LearnerTuple.LearnerTuple";
      s += "(";
      s += @received2bMessageSenders.ToString();
      s += ", ";
      s += @candidateLearnedValue.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LearnerTuple {
    Base_LearnerTuple _d;
    public Base_LearnerTuple _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LearnerTuple(Base_LearnerTuple d) { this._d = d; }
    static Base_LearnerTuple theDefault;
    public static Base_LearnerTuple Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Learner__i_Compile.@LearnerTuple_LearnerTuple(Dafny.Set<BigInteger>.Empty, Dafny.Sequence<@_Common____Types__s_Compile.@Request>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LearnerTuple && _D.Equals(((@LearnerTuple)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LearnerTuple { get { return _D is LearnerTuple_LearnerTuple; } }
    public Dafny.Set<BigInteger> dtor_received2bMessageSenders { get { return ((LearnerTuple_LearnerTuple)_D).@received2bMessageSenders; } }
    public Dafny.Sequence<@_Common____Types__s_Compile.@Request> dtor_candidateLearnedValue { get { return ((LearnerTuple_LearnerTuple)_D).@candidateLearnedValue; } }
  }


  public abstract class Base_Learner { }
  public partial class Learner_Learner : Base_Learner {
    public readonly @_RSL____Constants__i_Compile.@ReplicaConstants @constants;
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @maxBallotSeen;
    public readonly Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple> @learnerState;
    public Learner_Learner(@_RSL____Constants__i_Compile.@ReplicaConstants @constants, @_Common____TypesPPC__i_Compile.@Ballot @maxBallotSeen, Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple> @learnerState) {
      this.@constants = @constants;
      this.@maxBallotSeen = @maxBallotSeen;
      this.@learnerState = @learnerState;
    }
    public override bool Equals(object other) {
      var oth = other as _RSL____Learner__i_Compile.@Learner_Learner;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@maxBallotSeen.Equals(oth.@maxBallotSeen) && this.@learnerState.Equals(oth.@learnerState);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBallotSeen.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@learnerState.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_RSL____Learner__i_Compile.Learner.Learner";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @maxBallotSeen.ToString();
      s += ", ";
      s += @learnerState.ToString();
      s += ")";
      return s;
    }
  }
  public struct @Learner {
    Base_Learner _d;
    public Base_Learner _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Learner(Base_Learner d) { this._d = d; }
    static Base_Learner theDefault;
    public static Base_Learner Default {
      get {
        if (theDefault == null) {
          theDefault = new _RSL____Learner__i_Compile.@Learner_Learner(new @_RSL____Constants__i_Compile.@ReplicaConstants(), new @_Common____TypesPPC__i_Compile.@Ballot(), Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Learner && _D.Equals(((@Learner)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Learner { get { return _D is Learner_Learner; } }
    public @_RSL____Constants__i_Compile.@ReplicaConstants dtor_constants { get { return ((Learner_Learner)_D).@constants; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_maxBallotSeen { get { return ((Learner_Learner)_D).@maxBallotSeen; } }
    public Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple> dtor_learnerState { get { return ((Learner_Learner)_D).@learnerState; } }
  }

  public partial class @__default {
  }
} // end of namespace _RSL____Learner__i_Compile
namespace @_LiveRSL____Learner__i_Compile {








  public abstract class Base_LLearner { }
  public partial class LLearner_LLearner : Base_LLearner {
    public readonly @_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants;
    public readonly @_Common____TypesPPC__i_Compile.@Ballot @maxBallotSeen;
    public readonly Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple> @unexecutedLearnerState;
    public readonly Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple> @learnerState;
    public LLearner_LLearner(@_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants, @_Common____TypesPPC__i_Compile.@Ballot @maxBallotSeen, Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple> @unexecutedLearnerState, Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple> @learnerState) {
      this.@constants = @constants;
      this.@maxBallotSeen = @maxBallotSeen;
      this.@unexecutedLearnerState = @unexecutedLearnerState;
      this.@learnerState = @learnerState;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Learner__i_Compile.@LLearner_LLearner;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@maxBallotSeen.Equals(oth.@maxBallotSeen) && this.@unexecutedLearnerState.Equals(oth.@unexecutedLearnerState) && this.@learnerState.Equals(oth.@learnerState);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBallotSeen.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@unexecutedLearnerState.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@learnerState.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Learner__i_Compile.LLearner.LLearner";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @maxBallotSeen.ToString();
      s += ", ";
      s += @unexecutedLearnerState.ToString();
      s += ", ";
      s += @learnerState.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LLearner {
    Base_LLearner _d;
    public Base_LLearner _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LLearner(Base_LLearner d) { this._d = d; }
    static Base_LLearner theDefault;
    public static Base_LLearner Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Learner__i_Compile.@LLearner_LLearner(new @_LiveRSL____Constants__i_Compile.@LReplicaConstants(), new @_Common____TypesPPC__i_Compile.@Ballot(), Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple>.Empty, Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LLearner && _D.Equals(((@LLearner)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LLearner { get { return _D is LLearner_LLearner; } }
    public @_LiveRSL____Constants__i_Compile.@LReplicaConstants dtor_constants { get { return ((LLearner_LLearner)_D).@constants; } }
    public @_Common____TypesPPC__i_Compile.@Ballot dtor_maxBallotSeen { get { return ((LLearner_LLearner)_D).@maxBallotSeen; } }
    public Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple> dtor_unexecutedLearnerState { get { return ((LLearner_LLearner)_D).@unexecutedLearnerState; } }
    public Dafny.Map<BigInteger,@_RSL____Learner__i_Compile.@LearnerTuple> dtor_learnerState { get { return ((LLearner_LLearner)_D).@learnerState; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Learner__i_Compile
namespace @_LiveRSL____Replica__i_Compile {










  public abstract class Base_LReplica { }
  public partial class LReplica_LReplica : Base_LReplica {
    public readonly @_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants;
    public readonly BigInteger @nextHeartbeatTime;
    public readonly @_LiveRSL____Proposer__i_Compile.@LProposer @proposer;
    public readonly @_LiveRSL____Acceptor__i_Compile.@LAcceptor @acceptor;
    public readonly @_LiveRSL____Learner__i_Compile.@LLearner @learner;
    public readonly @_LiveRSL____Executor__i_Compile.@LExecutor @executor;
    public LReplica_LReplica(@_LiveRSL____Constants__i_Compile.@LReplicaConstants @constants, BigInteger @nextHeartbeatTime, @_LiveRSL____Proposer__i_Compile.@LProposer @proposer, @_LiveRSL____Acceptor__i_Compile.@LAcceptor @acceptor, @_LiveRSL____Learner__i_Compile.@LLearner @learner, @_LiveRSL____Executor__i_Compile.@LExecutor @executor) {
      this.@constants = @constants;
      this.@nextHeartbeatTime = @nextHeartbeatTime;
      this.@proposer = @proposer;
      this.@acceptor = @acceptor;
      this.@learner = @learner;
      this.@executor = @executor;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Replica__i_Compile.@LReplica_LReplica;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@nextHeartbeatTime.Equals(oth.@nextHeartbeatTime) && this.@proposer.Equals(oth.@proposer) && this.@acceptor.Equals(oth.@acceptor) && this.@learner.Equals(oth.@learner) && this.@executor.Equals(oth.@executor);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@nextHeartbeatTime.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@proposer.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@acceptor.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@learner.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@executor.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Replica__i_Compile.LReplica.LReplica";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @nextHeartbeatTime.ToString();
      s += ", ";
      s += @proposer.ToString();
      s += ", ";
      s += @acceptor.ToString();
      s += ", ";
      s += @learner.ToString();
      s += ", ";
      s += @executor.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LReplica {
    Base_LReplica _d;
    public Base_LReplica _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LReplica(Base_LReplica d) { this._d = d; }
    static Base_LReplica theDefault;
    public static Base_LReplica Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Replica__i_Compile.@LReplica_LReplica(new @_LiveRSL____Constants__i_Compile.@LReplicaConstants(), BigInteger.Zero, new @_LiveRSL____Proposer__i_Compile.@LProposer(), new @_LiveRSL____Acceptor__i_Compile.@LAcceptor(), new @_LiveRSL____Learner__i_Compile.@LLearner(), new @_LiveRSL____Executor__i_Compile.@LExecutor());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LReplica && _D.Equals(((@LReplica)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LReplica { get { return _D is LReplica_LReplica; } }
    public @_LiveRSL____Constants__i_Compile.@LReplicaConstants dtor_constants { get { return ((LReplica_LReplica)_D).@constants; } }
    public BigInteger dtor_nextHeartbeatTime { get { return ((LReplica_LReplica)_D).@nextHeartbeatTime; } }
    public @_LiveRSL____Proposer__i_Compile.@LProposer dtor_proposer { get { return ((LReplica_LReplica)_D).@proposer; } }
    public @_LiveRSL____Acceptor__i_Compile.@LAcceptor dtor_acceptor { get { return ((LReplica_LReplica)_D).@acceptor; } }
    public @_LiveRSL____Learner__i_Compile.@LLearner dtor_learner { get { return ((LReplica_LReplica)_D).@learner; } }
    public @_LiveRSL____Executor__i_Compile.@LExecutor dtor_executor { get { return ((LReplica_LReplica)_D).@executor; } }
  }

  public abstract class Base_LScheduler { }
  public partial class LScheduler_LScheduler : Base_LScheduler {
    public readonly @_LiveRSL____Replica__i_Compile.@LReplica @replica;
    public readonly BigInteger @nextActionIndex;
    public LScheduler_LScheduler(@_LiveRSL____Replica__i_Compile.@LReplica @replica, BigInteger @nextActionIndex) {
      this.@replica = @replica;
      this.@nextActionIndex = @nextActionIndex;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____Replica__i_Compile.@LScheduler_LScheduler;
      return oth != null && this.@replica.Equals(oth.@replica) && this.@nextActionIndex.Equals(oth.@nextActionIndex);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@replica.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@nextActionIndex.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____Replica__i_Compile.LScheduler.LScheduler";
      s += "(";
      s += @replica.ToString();
      s += ", ";
      s += @nextActionIndex.ToString();
      s += ")";
      return s;
    }
  }
  public struct @LScheduler {
    Base_LScheduler _d;
    public Base_LScheduler _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @LScheduler(Base_LScheduler d) { this._d = d; }
    static Base_LScheduler theDefault;
    public static Base_LScheduler Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____Replica__i_Compile.@LScheduler_LScheduler(new @_LiveRSL____Replica__i_Compile.@LReplica(), BigInteger.Zero);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @LScheduler && _D.Equals(((@LScheduler)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_LScheduler { get { return _D is LScheduler_LScheduler; } }
    public @_LiveRSL____Replica__i_Compile.@LReplica dtor_replica { get { return ((LScheduler_LScheduler)_D).@replica; } }
    public BigInteger dtor_nextActionIndex { get { return ((LScheduler_LScheduler)_D).@nextActionIndex; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____Replica__i_Compile
namespace @_Native____NativeTypes__s_Compile {













  public partial class @__default {
  }
} // end of namespace _Native____NativeTypes__s_Compile
namespace @_Logic____Option__i_Compile {

  public abstract class Base_Option<@T> { }
  public partial class Option_Some<@T> : Base_Option<@T> {
    public readonly @T @v;
    public Option_Some(@T @v) {
      this.@v = @v;
    }
    public override bool Equals(object other) {
      var oth = other as _Logic____Option__i_Compile.@Option_Some<@T>;
      return oth != null && this.@v.Equals(oth.@v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@v.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Logic____Option__i_Compile.Option.Some";
      s += "(";
      s += @v.ToString();
      s += ")";
      return s;
    }
  }
  public partial class Option_None<@T> : Base_Option<@T> {
    public Option_None() {
    }
    public override bool Equals(object other) {
      var oth = other as _Logic____Option__i_Compile.@Option_None<@T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Logic____Option__i_Compile.Option.None";
      return s;
    }
  }
  public struct @Option<@T> {
    Base_Option<@T> _d;
    public Base_Option<@T> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @Option(Base_Option<@T> d) { this._d = d; }
    static Base_Option<@T> theDefault;
    public static Base_Option<@T> Default {
      get {
        if (theDefault == null) {
          theDefault = new _Logic____Option__i_Compile.@Option_Some<@T>(default(@T));
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @Option<@T> && _D.Equals(((@Option<@T>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Some { get { return _D is Option_Some<@T>; } }
    public bool is_None { get { return _D is Option_None<@T>; } }
    public @T dtor_v { get { return ((Option_Some<@T>)_D).@v; } }
  }

  public partial class @__default {
  }
} // end of namespace _Logic____Option__i_Compile
namespace @_Native____NativeTypes__i_Compile {


  public partial class @__default {
    public static ulong @Uint64Size() {
      return 8UL;
    }
    public static ulong @Uint32Size() {
      return 4UL;
    }
    public static ulong @Uint16Size() {
      return 2UL;
    }
  }
} // end of namespace _Native____NativeTypes__i_Compile
namespace @_Native____Io__s_Compile {



  public partial class @HostEnvironment {
  }

  public partial class @HostConstants {
  }

  public partial class @OkState {
  }

  public partial class @NowState {
  }

  public partial class @Time {
  }

  public abstract class Base_EndPoint { }
  public partial class EndPoint_EndPoint : Base_EndPoint {
    public readonly Dafny.Sequence<byte> @addr;
    public readonly ushort @port;
    public EndPoint_EndPoint(Dafny.Sequence<byte> @addr, ushort @port) {
      this.@addr = @addr;
      this.@port = @port;
    }
    public override bool Equals(object other) {
      var oth = other as _Native____Io__s_Compile.@EndPoint_EndPoint;
      return oth != null && this.@addr.Equals(oth.@addr) && this.@port.Equals(oth.@port);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@addr.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@port.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Native____Io__s_Compile.EndPoint.EndPoint";
      s += "(";
      s += @addr.ToString();
      s += ", ";
      s += @port.ToString();
      s += ")";
      return s;
    }
  }
  public struct @EndPoint {
    Base_EndPoint _d;
    public Base_EndPoint _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @EndPoint(Base_EndPoint d) { this._d = d; }
    static Base_EndPoint theDefault;
    public static Base_EndPoint Default {
      get {
        if (theDefault == null) {
          theDefault = new _Native____Io__s_Compile.@EndPoint_EndPoint(Dafny.Sequence<byte>.Empty, 0);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @EndPoint && _D.Equals(((@EndPoint)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_EndPoint { get { return _D is EndPoint_EndPoint; } }
    public Dafny.Sequence<byte> dtor_addr { get { return ((EndPoint_EndPoint)_D).@addr; } }
    public ushort dtor_port { get { return ((EndPoint_EndPoint)_D).@port; } }
  }



  public partial class @UdpState {
  }

  public partial class @IPEndPoint {
  }

  public partial class @UdpClient {
  }

  public partial class @FileSystemState {
  }

  public partial class @__default {
  }
} // end of namespace _Native____Io__s_Compile
namespace @_Libraries____base__s_Compile {

  public partial class @__default {
  }
} // end of namespace _Libraries____base__s_Compile
namespace @_Math____power2__s_Compile {


  public partial class @__default {
  }
} // end of namespace _Math____power2__s_Compile
namespace @_Math____power__s_Compile {

  public partial class @__default {
  }
} // end of namespace _Math____power__s_Compile
namespace @_Math____power__i_Compile {



  public partial class @__default {
  }
} // end of namespace _Math____power__i_Compile
namespace @_Math____div__def__i_Compile {

  public partial class @__default {
  }
} // end of namespace _Math____div__def__i_Compile
namespace @_Math____div__boogie__i_Compile {



  public partial class @__default {
  }
} // end of namespace _Math____div__boogie__i_Compile
namespace @_Math____div__auto__proofs__i_Compile {


  public partial class @__default {
  }
} // end of namespace _Math____div__auto__proofs__i_Compile
namespace @_Math____div__auto__i_Compile {



  public partial class @__default {
  }
} // end of namespace _Math____div__auto__i_Compile
namespace @_Math____div__i_Compile {







  public partial class @__default {
  }
} // end of namespace _Math____div__i_Compile
namespace @_Util____bytes__and__words__s_Compile {


  public partial class @__default {
  }
} // end of namespace _Util____bytes__and__words__s_Compile
namespace @_Util____be__sequences__s_Compile {



  public partial class @__default {
  }
} // end of namespace _Util____be__sequences__s_Compile
namespace @_CPU____assembly__s_Compile {



  public partial class @__default {
  }
} // end of namespace _CPU____assembly__s_Compile
namespace @_Util____seqs__simple__i_Compile {

  public partial class @__default {
  }
} // end of namespace _Util____seqs__simple__i_Compile
namespace @_Util____repeat__digit__i_Compile {




  public partial class @__default {
    public static void @SequenceOfZerosIterative(BigInteger @n, out Dafny.Sequence<BigInteger> @Z)
    {
      @Z = Dafny.Sequence<BigInteger>.Empty;
    TAIL_CALL_START: ;
      { }
      BigInteger @_24593_num__zeros = BigInteger.Zero;
      @_24593_num__zeros = new BigInteger(0);
      Dafny.Sequence<BigInteger> @_24594_z = Dafny.Sequence<BigInteger>.Empty;
      @_24594_z = Dafny.Sequence<BigInteger>.FromElements();
      while ((@_24593_num__zeros) < (@n))
      {
        @_24594_z = (@_24594_z).@Concat(Dafny.Sequence<BigInteger>.FromElements(new BigInteger(0)));
        @_24593_num__zeros = (@_24593_num__zeros) + (new BigInteger(1));
      }
      @Z = @_24594_z;
    }
    public static void @RepeatDigit__impl(BigInteger @digit, BigInteger @count, out Dafny.Sequence<BigInteger> @os)
    {
      @os = Dafny.Sequence<BigInteger>.Empty;
    TAIL_CALL_START: ;
      @os = Dafny.Sequence<BigInteger>.FromElements();
      if ((@count) < (new BigInteger(0)))
      {
        return;
      }
      BigInteger @_24595_i = BigInteger.Zero;
      @_24595_i = new BigInteger(0);
      while ((@_24595_i) < (@count))
      {
        @os = (@os).@Concat(Dafny.Sequence<BigInteger>.FromElements(@digit));
        @_24595_i = (@_24595_i) + (new BigInteger(1));
      }
    }
    public static void @RepeatDigit__impl__arrays(BigInteger @digit, BigInteger @count, out BigInteger[] @os)
    {
      @os = (BigInteger[])null;
    TAIL_CALL_START: ;
      if ((@count) < (new BigInteger(0)))
      {
        @os = Dafny.Helpers.InitNewArray1<BigInteger>((new BigInteger(0)));
        return;
      }
      @os = Dafny.Helpers.InitNewArray1<BigInteger>((@count));
      BigInteger @_24596_i = BigInteger.Zero;
      @_24596_i = new BigInteger(0);
      while ((@_24596_i) < (@count))
      {
        (@os)[(int)(@_24596_i)] = @digit;
        @_24596_i = (@_24596_i) + (new BigInteger(1));
      }
    }
  }
} // end of namespace _Util____repeat__digit__i_Compile
namespace @_Math____power2__i_Compile {







  public partial class @__default {
  }
} // end of namespace _Math____power2__i_Compile
namespace @_Common____Util__i_Compile {




  public partial class @__default {
    public static void @seqToArray__slow<@A>(Dafny.Sequence<@A> @s, out @A[] @a)
    {
      @a = (@A[])null;
    TAIL_CALL_START: ;
      BigInteger @_24597_len = BigInteger.Zero;
      @_24597_len = new BigInteger((@s).Length);
      @a = Dafny.Helpers.InitNewArray1<@A>((@_24597_len));
      BigInteger @_24598_i = BigInteger.Zero;
      @_24598_i = new BigInteger(0);
      while ((@_24598_i) < (@_24597_len))
      {
        (@a)[(int)(@_24598_i)] = (@s).Select(@_24598_i);
        @_24598_i = (@_24598_i) + (new BigInteger(1));
      }
    }
    public static void @seqIntoArray__slow<@A>(Dafny.Sequence<@A> @s, @A[] @a, BigInteger @index)
    {
    TAIL_CALL_START: ;
      BigInteger @_24599_i = BigInteger.Zero;
      @_24599_i = @index;
      while ((@_24599_i) < ((@index) + (new BigInteger((@s).Length))))
      {
        (@a)[(int)(@_24599_i)] = (@s).Select((@_24599_i) - (@index));
        @_24599_i = (@_24599_i) + (new BigInteger(1));
        { }
      }
    }
    public static void @seqIntoArrayOpt<@A>(Dafny.Sequence<@A> @s, @A[] @a)
    {
    TAIL_CALL_START: ;
      ulong @_24600_i = 0;
      @_24600_i = 0UL;
      while ((@_24600_i) < ((ulong)(@s).LongLength))
      {
        (@a)[(int)(@_24600_i)] = (@s).Select(@_24600_i);
        @_24600_i = (@_24600_i) + (1UL);
      }
    }
    public static void @seqToArrayOpt<@A>(Dafny.Sequence<@A> @s, out @A[] @a)
    {
      @a = (@A[])null;
    TAIL_CALL_START: ;
      @a = Dafny.Helpers.InitNewArray1<@A>(((ulong)(@s).LongLength));
      @_Common____Util__i_Compile.@__default.@seqIntoArrayOpt(@s, @a);
    }
    public static void @seqIntoArrayChar(Dafny.Sequence<char> @s, char[] @a)
    {
    TAIL_CALL_START: ;
      ulong @_24601_i = 0;
      @_24601_i = 0UL;
      while ((@_24601_i) < ((ulong)(@s).LongLength))
      {
        (@a)[(int)(@_24601_i)] = (@s).Select(@_24601_i);
        @_24601_i = (@_24601_i) + (1UL);
      }
    }
    public static void @RecordTimingSeq(Dafny.Sequence<char> @name, ulong @start, ulong @end)
    {
    TAIL_CALL_START: ;
      char[] @_24602_name__array = (char[])null;
      @_24602_name__array = new char[(int)(new BigInteger((@name).Length))];
      @_Common____Util__i_Compile.@__default.@seqIntoArrayChar(@name, @_24602_name__array);
      ulong @_24603_time = 0;
      if ((@start) <= (@end))
      {
        @_24603_time = (@end) - (@start);
      }
      else
      {
        @_24603_time = 18446744073709551615UL;
      }
      @_Native____Io__s_Compile.@Time.@RecordTiming(@_24602_name__array, @_24603_time);
    }
    public static ulong @SeqByteToUint64(Dafny.Sequence<byte> @bs) {
      return ((((((((((((ulong)((@bs).Select((ulong)(0UL)))) * (256UL)) * (256UL)) * (256UL)) * (4294967296UL)) + (((((ulong)((@bs).Select((ulong)(1UL)))) * (256UL)) * (256UL)) * (4294967296UL))) + ((((ulong)((@bs).Select((ulong)(2UL)))) * (256UL)) * (4294967296UL))) + (((ulong)((@bs).Select((ulong)(3UL)))) * (4294967296UL))) + (((((ulong)((@bs).Select((ulong)(4UL)))) * (256UL)) * (256UL)) * (256UL))) + ((((ulong)((@bs).Select((ulong)(5UL)))) * (256UL)) * (256UL))) + (((ulong)((@bs).Select((ulong)(6UL)))) * (256UL))) + ((ulong)((@bs).Select((ulong)(7UL))));
    }
    public static Dafny.Sequence<byte> @Uint64ToSeqByte(ulong @u) {
      Dafny.Sequence<byte> @_24604_bs = Dafny.Sequence<byte>.FromElements((byte)((@u) / (72057594037927936UL)), (byte)(((@u) / (281474976710656UL)) % (256UL)), (byte)(((@u) / (1099511627776UL)) % (256UL)), (byte)(((@u) / (4294967296UL)) % (256UL)), (byte)(((@u) / (16777216UL)) % (256UL)), (byte)(((@u) / (65536UL)) % (256UL)), (byte)(((@u) / (256UL)) % (256UL)), (byte)((@u) % (256UL)));
      BigInteger @_24605_u__int = new BigInteger(@u);
      return @_24604_bs;
    }
    public static ushort @SeqByteToUint16(Dafny.Sequence<byte> @bs) {
      return (ushort)(((ushort)(((ushort)((@bs).Select((ulong)(0UL)))) * (256))) + ((ushort)((@bs).Select((ulong)(1UL)))));
    }
    public static Dafny.Sequence<byte> @Uint16ToSeqByte(ushort @u) {
      Dafny.Sequence<byte> @_24606_s = Dafny.Sequence<byte>.FromElements((byte)((ushort)(((ushort)((@u) / (256))) % (256))), (byte)((ushort)((@u) % (256))));
      BigInteger @_24607_u__int = new BigInteger(@u);
      return @_24606_s;
    }
  }
} // end of namespace _Common____Util__i_Compile
namespace @_Common____MarshallInt__i_Compile {



  public partial class @__default {
    public static void @MarshallUint64__guts(ulong @n, byte[] @data, ulong @index)
    {
    TAIL_CALL_START: ;
      (@data)[(int)(@index)] = (byte)((@n) / (72057594037927936UL));
      (@data)[(int)((@index) + (1UL))] = (byte)(((@n) / (281474976710656UL)) % (256UL));
      (@data)[(int)((@index) + (2UL))] = (byte)(((@n) / (1099511627776UL)) % (256UL));
      (@data)[(int)((@index) + (3UL))] = (byte)(((@n) / (4294967296UL)) % (256UL));
      (@data)[(int)((@index) + (4UL))] = (byte)(((@n) / (16777216UL)) % (256UL));
      (@data)[(int)((@index) + (5UL))] = (byte)(((@n) / (65536UL)) % (256UL));
      (@data)[(int)((@index) + (6UL))] = (byte)(((@n) / (256UL)) % (256UL));
      (@data)[(int)((@index) + (7UL))] = (byte)((@n) % (256UL));
      { }
      { }
      { }
    }
  }
} // end of namespace _Common____MarshallInt__i_Compile
namespace @_Common____GenericMarshalling__i_Compile {






  public abstract class Base_G { }
  public partial class G_GUint64 : Base_G {
    public G_GUint64() {
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@G_GUint64;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.G.GUint64";
      return s;
    }
  }
  public partial class G_GArray : Base_G {
    public readonly @_Common____GenericMarshalling__i_Compile.@G @elt;
    public G_GArray(@_Common____GenericMarshalling__i_Compile.@G @elt) {
      this.@elt = @elt;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@G_GArray;
      return oth != null && this.@elt.Equals(oth.@elt);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@elt.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.G.GArray";
      s += "(";
      s += @elt.ToString();
      s += ")";
      return s;
    }
  }
  public partial class G_GTuple : Base_G {
    public readonly Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @t;
    public G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @t) {
      this.@t = @t;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@G_GTuple;
      return oth != null && this.@t.Equals(oth.@t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@t.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.G.GTuple";
      s += "(";
      s += @t.ToString();
      s += ")";
      return s;
    }
  }
  public partial class G_GByteArray : Base_G {
    public G_GByteArray() {
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@G_GByteArray;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.G.GByteArray";
      return s;
    }
  }
  public partial class G_GTaggedUnion : Base_G {
    public readonly Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @cases;
    public G_GTaggedUnion(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @cases) {
      this.@cases = @cases;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@G_GTaggedUnion;
      return oth != null && this.@cases.Equals(oth.@cases);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@cases.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.G.GTaggedUnion";
      s += "(";
      s += @cases.ToString();
      s += ")";
      return s;
    }
  }
  public struct @G {
    Base_G _d;
    public Base_G _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @G(Base_G d) { this._d = d; }
    static Base_G theDefault;
    public static Base_G Default {
      get {
        if (theDefault == null) {
          theDefault = new _Common____GenericMarshalling__i_Compile.@G_GUint64();
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @G && _D.Equals(((@G)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_GUint64 { get { return _D is G_GUint64; } }
    public bool is_GArray { get { return _D is G_GArray; } }
    public bool is_GTuple { get { return _D is G_GTuple; } }
    public bool is_GByteArray { get { return _D is G_GByteArray; } }
    public bool is_GTaggedUnion { get { return _D is G_GTaggedUnion; } }
    public @_Common____GenericMarshalling__i_Compile.@G dtor_elt { get { return ((G_GArray)_D).@elt; } }
    public Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> dtor_t { get { return ((G_GTuple)_D).@t; } }
    public Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> dtor_cases { get { return ((G_GTaggedUnion)_D).@cases; } }
  }

  public abstract class Base_V { }
  public partial class V_VUint64 : Base_V {
    public readonly ulong @u;
    public V_VUint64(ulong @u) {
      this.@u = @u;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@V_VUint64;
      return oth != null && this.@u.Equals(oth.@u);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@u.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.V.VUint64";
      s += "(";
      s += @u.ToString();
      s += ")";
      return s;
    }
  }
  public partial class V_VArray : Base_V {
    public readonly Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @a;
    public V_VArray(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @a) {
      this.@a = @a;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@V_VArray;
      return oth != null && this.@a.Equals(oth.@a);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@a.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.V.VArray";
      s += "(";
      s += @a.ToString();
      s += ")";
      return s;
    }
  }
  public partial class V_VTuple : Base_V {
    public readonly Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @t;
    public V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @t) {
      this.@t = @t;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@V_VTuple;
      return oth != null && this.@t.Equals(oth.@t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@t.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.V.VTuple";
      s += "(";
      s += @t.ToString();
      s += ")";
      return s;
    }
  }
  public partial class V_VByteArray : Base_V {
    public readonly Dafny.Sequence<byte> @b;
    public V_VByteArray(Dafny.Sequence<byte> @b) {
      this.@b = @b;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@V_VByteArray;
      return oth != null && this.@b.Equals(oth.@b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@b.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.V.VByteArray";
      s += "(";
      s += @b.ToString();
      s += ")";
      return s;
    }
  }
  public partial class V_VCase : Base_V {
    public readonly ulong @c;
    public readonly @_Common____GenericMarshalling__i_Compile.@V @val;
    public V_VCase(ulong @c, @_Common____GenericMarshalling__i_Compile.@V @val) {
      this.@c = @c;
      this.@val = @val;
    }
    public override bool Equals(object other) {
      var oth = other as _Common____GenericMarshalling__i_Compile.@V_VCase;
      return oth != null && this.@c.Equals(oth.@c) && this.@val.Equals(oth.@val);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@c.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@val.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_Common____GenericMarshalling__i_Compile.V.VCase";
      s += "(";
      s += @c.ToString();
      s += ", ";
      s += @val.ToString();
      s += ")";
      return s;
    }
  }
  public struct @V {
    Base_V _d;
    public Base_V _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @V(Base_V d) { this._d = d; }
    static Base_V theDefault;
    public static Base_V Default {
      get {
        if (theDefault == null) {
          theDefault = new _Common____GenericMarshalling__i_Compile.@V_VUint64(0);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @V && _D.Equals(((@V)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_VUint64 { get { return _D is V_VUint64; } }
    public bool is_VArray { get { return _D is V_VArray; } }
    public bool is_VTuple { get { return _D is V_VTuple; } }
    public bool is_VByteArray { get { return _D is V_VByteArray; } }
    public bool is_VCase { get { return _D is V_VCase; } }
    public ulong dtor_u { get { return ((V_VUint64)_D).@u; } }
    public Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> dtor_a { get { return ((V_VArray)_D).@a; } }
    public Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> dtor_t { get { return ((V_VTuple)_D).@t; } }
    public Dafny.Sequence<byte> dtor_b { get { return ((V_VByteArray)_D).@b; } }
    public ulong dtor_c { get { return ((V_VCase)_D).@c; } }
    public @_Common____GenericMarshalling__i_Compile.@V dtor_val { get { return ((V_VCase)_D).@val; } }
  }

  public partial class @__default {
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> @parse__Uint64(Dafny.Sequence<byte> @data) {
      if (((ulong)(@data).LongLength) >= (@_Native____NativeTypes__i_Compile.@__default.@Uint64Size())) {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_Some<@_Common____GenericMarshalling__i_Compile.@V>(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64(@_Common____Util__i_Compile.@__default.@SeqByteToUint64((@data).Take(@_Native____NativeTypes__i_Compile.@__default.@Uint64Size())))))), (@data).Drop(@_Native____NativeTypes__i_Compile.@__default.@Uint64Size())));
      } else {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_None<@_Common____GenericMarshalling__i_Compile.@V>()), Dafny.Sequence<byte>.FromElements()));
      }
    }
    public static void @ParseUint64(byte[] @data, ulong @index, out bool @success, out @_Common____GenericMarshalling__i_Compile.@V @v, out ulong @rest__index)
    {
      @success = false;
      @v = new @_Common____GenericMarshalling__i_Compile.@V();
      @rest__index = 0;
    TAIL_CALL_START: ;
      { }
      if ((((ulong)(@data).LongLength) >= (8UL)) && ((@index) <= (((ulong)(@data).LongLength) - (8UL))))
      {
        ulong @_24608_result = 0;
        @_24608_result = ((((((((((((ulong)((@data)[(int)((@index) + ((ulong)(0UL)))])) * (256UL)) * (256UL)) * (256UL)) * (4294967296UL)) + (((((ulong)((@data)[(int)((@index) + ((ulong)(1UL)))])) * (256UL)) * (256UL)) * (4294967296UL))) + ((((ulong)((@data)[(int)((@index) + ((ulong)(2UL)))])) * (256UL)) * (4294967296UL))) + (((ulong)((@data)[(int)((@index) + ((ulong)(3UL)))])) * (4294967296UL))) + (((((ulong)((@data)[(int)((@index) + ((ulong)(4UL)))])) * (256UL)) * (256UL)) * (256UL))) + ((((ulong)((@data)[(int)((@index) + ((ulong)(5UL)))])) * (256UL)) * (256UL))) + (((ulong)((@data)[(int)((@index) + ((ulong)(6UL)))])) * (256UL))) + ((ulong)((@data)[(int)((@index) + ((ulong)(7UL)))]));
        @success = true;
        @v = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64(@_24608_result));
        @rest__index = (@index) + (@_Native____NativeTypes__i_Compile.@__default.@Uint64Size());
      }
      else
      {
        @success = false;
        @rest__index = (ulong)(@data).LongLength;
      }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>> @parse__Array__contents(Dafny.Sequence<byte> @data, @_Common____GenericMarshalling__i_Compile.@G @eltType, ulong @len) {
      return @_Common____GenericMarshalling__i_Compile.@__default.@_hparse__Array__contents__FULL(@data, @eltType, @len);
    }
    public static void @ParseArrayContents(byte[] @data, ulong @index, @_Common____GenericMarshalling__i_Compile.@G @eltType, ulong @len, out bool @success, out Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @v, out ulong @rest__index)
    {
      @success = false;
      @v = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.Empty;
      @rest__index = 0;
      { }
      if ((@len).@Equals(0UL))
      {
        @success = true;
        @v = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements();
        @rest__index = @index;
      }
      else
      {
        bool @_24609_some1 = false;
        @_Common____GenericMarshalling__i_Compile.@V @_24610_val = new @_Common____GenericMarshalling__i_Compile.@V();
        ulong @_24611_rest1 = 0;
        bool _out0;
        @_Common____GenericMarshalling__i_Compile.@V _out1;
        ulong _out2;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseVal(@data, @index, @eltType, out _out0, out _out1, out _out2);
        @_24609_some1 = _out0;
        @_24610_val = _out1;
        @_24611_rest1 = _out2;
        bool @_24612_some2 = false;
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24613_others = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.Empty;
        ulong @_24614_rest2 = 0;
        bool _out3;
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> _out4;
        ulong _out5;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseArrayContents(@data, @_24611_rest1, @eltType, (@len) - (1UL), out _out3, out _out4, out _out5);
        @_24612_some2 = _out3;
        @_24613_others = _out4;
        @_24614_rest2 = _out5;
        if ((@_24609_some1) && (@_24612_some2))
        {
          @success = true;
          @v = (Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24610_val)).@Concat(@_24613_others);
          @rest__index = @_24614_rest2;
        }
        else
        {
          @success = false;
          @rest__index = (ulong)(@data).LongLength;
        }
      }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> @parse__Array(Dafny.Sequence<byte> @data, @_Common____GenericMarshalling__i_Compile.@G @eltType) {
      @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> _let_tmp_rhs0 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Uint64(@data);
      @_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V> @_24615_len = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs0)._D).@_0;
      Dafny.Sequence<byte> @_24616_rest = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs0)._D).@_1;
      if (!((@_24615_len).@is_None)) {
        @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>> _let_tmp_rhs1 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Array__contents(@_24616_rest, @eltType, ((@_24615_len).@dtor_v).@dtor_u);
        @_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>> @_24617_contents = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>)(_let_tmp_rhs1)._D).@_0;
        Dafny.Sequence<byte> @_24618_remainder = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>)(_let_tmp_rhs1)._D).@_1;
        if (!((@_24617_contents).@is_None)) {
          return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_Some<@_Common____GenericMarshalling__i_Compile.@V>(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray((@_24617_contents).@dtor_v)))), @_24618_remainder));
        } else {
          return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_None<@_Common____GenericMarshalling__i_Compile.@V>()), Dafny.Sequence<byte>.FromElements()));
        }
      } else {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_None<@_Common____GenericMarshalling__i_Compile.@V>()), Dafny.Sequence<byte>.FromElements()));
      }
    }
    public static void @ParseArray(byte[] @data, ulong @index, @_Common____GenericMarshalling__i_Compile.@G @eltType, out bool @success, out @_Common____GenericMarshalling__i_Compile.@V @v, out ulong @rest__index)
    {
      @success = false;
      @v = new @_Common____GenericMarshalling__i_Compile.@V();
      @rest__index = 0;
      bool @_24619_some1 = false;
      @_Common____GenericMarshalling__i_Compile.@V @_24620_len = new @_Common____GenericMarshalling__i_Compile.@V();
      ulong @_24621_rest = 0;
      bool _out6;
      @_Common____GenericMarshalling__i_Compile.@V _out7;
      ulong _out8;
      @_Common____GenericMarshalling__i_Compile.@__default.@ParseUint64(@data, @index, out _out6, out _out7, out _out8);
      @_24619_some1 = _out6;
      @_24620_len = _out7;
      @_24621_rest = _out8;
      if (@_24619_some1)
      {
        bool @_24622_some2 = false;
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24623_contents = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.Empty;
        ulong @_24624_remainder = 0;
        bool _out9;
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> _out10;
        ulong _out11;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseArrayContents(@data, @_24621_rest, @eltType, (@_24620_len).@dtor_u, out _out9, out _out10, out _out11);
        @_24622_some2 = _out9;
        @_24623_contents = _out10;
        @_24624_remainder = _out11;
        if (@_24622_some2)
        {
          @success = true;
          @v = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray(@_24623_contents));
          @rest__index = @_24624_remainder;
        }
        else
        {
          @success = false;
          @rest__index = (ulong)(@data).LongLength;
        }
      }
      else
      {
        @success = false;
        @rest__index = (ulong)(@data).LongLength;
      }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>> @parse__Tuple__contents(Dafny.Sequence<byte> @data, Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @eltTypes) {
      return @_Common____GenericMarshalling__i_Compile.@__default.@_hparse__Tuple__contents__FULL(@data, @eltTypes);
    }
    public static void @ParseTupleContents(byte[] @data, ulong @index, Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @eltTypes, out bool @success, out Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @v, out ulong @rest__index)
    {
      @success = false;
      @v = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.Empty;
      @rest__index = 0;
      { }
      if ((@eltTypes).@Equals(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements()))
      {
        @success = true;
        @v = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements();
        @rest__index = @index;
      }
      else
      {
        bool @_24625_some1 = false;
        @_Common____GenericMarshalling__i_Compile.@V @_24626_val = new @_Common____GenericMarshalling__i_Compile.@V();
        ulong @_24627_rest1 = 0;
        bool _out12;
        @_Common____GenericMarshalling__i_Compile.@V _out13;
        ulong _out14;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseVal(@data, @index, (@eltTypes).Select((ulong)(0UL)), out _out12, out _out13, out _out14);
        @_24625_some1 = _out12;
        @_24626_val = _out13;
        @_24627_rest1 = _out14;
        bool @_24628_some2 = false;
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24629_others = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.Empty;
        ulong @_24630_rest2 = 0;
        bool _out15;
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> _out16;
        ulong _out17;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseTupleContents(@data, @_24627_rest1, (@eltTypes).Drop((ulong)(1UL)), out _out15, out _out16, out _out17);
        @_24628_some2 = _out15;
        @_24629_others = _out16;
        @_24630_rest2 = _out17;
        if ((@_24625_some1) && (@_24628_some2))
        {
          @success = true;
          @v = (Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24626_val)).@Concat(@_24629_others);
          @rest__index = @_24630_rest2;
        }
        else
        {
          @success = false;
          @rest__index = (ulong)(@data).LongLength;
        }
      }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> @parse__Tuple(Dafny.Sequence<byte> @data, Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @eltTypes) {
      @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>> _let_tmp_rhs2 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Tuple__contents(@data, @eltTypes);
      @_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>> @_24631_contents = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>)(_let_tmp_rhs2)._D).@_0;
      Dafny.Sequence<byte> @_24632_rest = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>)(_let_tmp_rhs2)._D).@_1;
      if (!((@_24631_contents).@is_None)) {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_Some<@_Common____GenericMarshalling__i_Compile.@V>(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple((@_24631_contents).@dtor_v)))), @_24632_rest));
      } else {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_None<@_Common____GenericMarshalling__i_Compile.@V>()), Dafny.Sequence<byte>.FromElements()));
      }
    }
    public static void @ParseTuple(byte[] @data, ulong @index, Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @eltTypes, out bool @success, out @_Common____GenericMarshalling__i_Compile.@V @v, out ulong @rest__index)
    {
      @success = false;
      @v = new @_Common____GenericMarshalling__i_Compile.@V();
      @rest__index = 0;
      bool @_24633_some = false;
      Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24634_contents = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.Empty;
      ulong @_24635_rest = 0;
      bool _out18;
      Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> _out19;
      ulong _out20;
      @_Common____GenericMarshalling__i_Compile.@__default.@ParseTupleContents(@data, @index, @eltTypes, out _out18, out _out19, out _out20);
      @_24633_some = _out18;
      @_24634_contents = _out19;
      @_24635_rest = _out20;
      if (@_24633_some)
      {
        @success = true;
        @v = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(@_24634_contents));
        @rest__index = @_24635_rest;
      }
      else
      {
        @success = false;
        @rest__index = (ulong)(@data).LongLength;
      }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> @parse__ByteArray(Dafny.Sequence<byte> @data) {
      @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> _let_tmp_rhs3 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Uint64(@data);
      @_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V> @_24636_len = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs3)._D).@_0;
      Dafny.Sequence<byte> @_24637_rest = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs3)._D).@_1;
      if ((!((@_24636_len).@is_None)) && ((((@_24636_len).@dtor_v).@dtor_u) <= ((ulong)(@_24637_rest).LongLength))) {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_Some<@_Common____GenericMarshalling__i_Compile.@V>(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VByteArray((@_24637_rest).Take(((@_24636_len).@dtor_v).@dtor_u).Drop((ulong)(0UL)))))), (@_24637_rest).Drop(((@_24636_len).@dtor_v).@dtor_u)));
      } else {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_None<@_Common____GenericMarshalling__i_Compile.@V>()), Dafny.Sequence<byte>.FromElements()));
      }
    }
    public static void @ParseByteArray(byte[] @data, ulong @index, out bool @success, out @_Common____GenericMarshalling__i_Compile.@V @v, out ulong @rest__index)
    {
      @success = false;
      @v = new @_Common____GenericMarshalling__i_Compile.@V();
      @rest__index = 0;
    TAIL_CALL_START: ;
      bool @_24638_some = false;
      @_Common____GenericMarshalling__i_Compile.@V @_24639_len = new @_Common____GenericMarshalling__i_Compile.@V();
      ulong @_24640_rest = 0;
      bool _out21;
      @_Common____GenericMarshalling__i_Compile.@V _out22;
      ulong _out23;
      @_Common____GenericMarshalling__i_Compile.@__default.@ParseUint64(@data, @index, out _out21, out _out22, out _out23);
      @_24638_some = _out21;
      @_24639_len = _out22;
      @_24640_rest = _out23;
      if ((@_24638_some) && (((@_24639_len).@dtor_u) <= (((ulong)(@data).LongLength) - (@_24640_rest))))
      {
        Dafny.Sequence<byte> @_24641_rest__seq = Dafny.Sequence<byte>.Empty;
        @_24641_rest__seq = Dafny.Helpers.SeqFromArray(@data).Drop(@_24640_rest);
        { }
        { }
        @success = true;
        @v = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VByteArray(Dafny.Helpers.SeqFromArray(@data).Take((@_24640_rest) + ((@_24639_len).@dtor_u)).Drop(@_24640_rest)));
        @rest__index = (@_24640_rest) + ((@_24639_len).@dtor_u);
      }
      else
      {
        @success = false;
        @rest__index = (ulong)(@data).LongLength;
      }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> @parse__Case(Dafny.Sequence<byte> @data, Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @cases) {
      @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> _let_tmp_rhs4 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Uint64(@data);
      @_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V> @_24642_caseID = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs4)._D).@_0;
      Dafny.Sequence<byte> @_24643_rest1 = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs4)._D).@_1;
      if ((!((@_24642_caseID).@is_None)) && ((((@_24642_caseID).@dtor_v).@dtor_u) < ((ulong)(@cases).LongLength))) {
        @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> _let_tmp_rhs5 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Val(@_24643_rest1, (@cases).Select(((@_24642_caseID).@dtor_v).@dtor_u));
        @_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V> @_24644_val = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs5)._D).@_0;
        Dafny.Sequence<byte> @_24645_rest2 = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs5)._D).@_1;
        if (!((@_24644_val).@is_None)) {
          return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_Some<@_Common____GenericMarshalling__i_Compile.@V>(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(((@_24642_caseID).@dtor_v).@dtor_u, (@_24644_val).@dtor_v)))), @_24645_rest2));
        } else {
          return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_None<@_Common____GenericMarshalling__i_Compile.@V>()), Dafny.Sequence<byte>.FromElements()));
        }
      } else {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>(new _Logic____Option__i_Compile.@Option_None<@_Common____GenericMarshalling__i_Compile.@V>()), Dafny.Sequence<byte>.FromElements()));
      }
    }
    public static void @ParseCase(byte[] @data, ulong @index, Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @cases, out bool @success, out @_Common____GenericMarshalling__i_Compile.@V @v, out ulong @rest__index)
    {
      @success = false;
      @v = new @_Common____GenericMarshalling__i_Compile.@V();
      @rest__index = 0;
      bool @_24646_some1 = false;
      @_Common____GenericMarshalling__i_Compile.@V @_24647_caseID = new @_Common____GenericMarshalling__i_Compile.@V();
      ulong @_24648_rest1 = 0;
      bool _out24;
      @_Common____GenericMarshalling__i_Compile.@V _out25;
      ulong _out26;
      @_Common____GenericMarshalling__i_Compile.@__default.@ParseUint64(@data, @index, out _out24, out _out25, out _out26);
      @_24646_some1 = _out24;
      @_24647_caseID = _out25;
      @_24648_rest1 = _out26;
      if ((@_24646_some1) && (((@_24647_caseID).@dtor_u) < ((ulong)(@cases).LongLength)))
      {
        bool @_24649_some2 = false;
        @_Common____GenericMarshalling__i_Compile.@V @_24650_val = new @_Common____GenericMarshalling__i_Compile.@V();
        ulong @_24651_rest2 = 0;
        bool _out27;
        @_Common____GenericMarshalling__i_Compile.@V _out28;
        ulong _out29;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseVal(@data, @_24648_rest1, (@cases).Select((@_24647_caseID).@dtor_u), out _out27, out _out28, out _out29);
        @_24649_some2 = _out27;
        @_24650_val = _out28;
        @_24651_rest2 = _out29;
        if (@_24649_some2)
        {
          @success = true;
          @v = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase((@_24647_caseID).@dtor_u, @_24650_val));
          @rest__index = @_24651_rest2;
        }
        else
        {
          @success = false;
          @rest__index = (ulong)(@data).LongLength;
        }
      }
      else
      {
        @success = false;
        @rest__index = (ulong)(@data).LongLength;
      }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> @parse__Val(Dafny.Sequence<byte> @data, @_Common____GenericMarshalling__i_Compile.@G @grammar) {
      return @_Common____GenericMarshalling__i_Compile.@__default.@_hparse__Val__FULL(@data, @grammar);
    }
    public static void @ParseVal(byte[] @data, ulong @index, @_Common____GenericMarshalling__i_Compile.@G @grammar, out bool @success, out @_Common____GenericMarshalling__i_Compile.@V @v, out ulong @rest__index)
    {
      @success = false;
      @v = new @_Common____GenericMarshalling__i_Compile.@V();
      @rest__index = 0;
      { }
      @_Common____GenericMarshalling__i_Compile.@G _source0 = @grammar;
      if (_source0.is_GUint64) {
        bool _out30;
        @_Common____GenericMarshalling__i_Compile.@V _out31;
        ulong _out32;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseUint64(@data, @index, out _out30, out _out31, out _out32);
        @success = _out30;
        @v = _out31;
        @rest__index = _out32;
      } else if (_source0.is_GArray) {
        @_Common____GenericMarshalling__i_Compile.@G @_24652_elt = ((_Common____GenericMarshalling__i_Compile.@G_GArray)_source0._D).@elt;
        bool _out33;
        @_Common____GenericMarshalling__i_Compile.@V _out34;
        ulong _out35;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseArray(@data, @index, @_24652_elt, out _out33, out _out34, out _out35);
        @success = _out33;
        @v = _out34;
        @rest__index = _out35;
      } else if (_source0.is_GTuple) {
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @_24653_t = ((_Common____GenericMarshalling__i_Compile.@G_GTuple)_source0._D).@t;
        bool _out36;
        @_Common____GenericMarshalling__i_Compile.@V _out37;
        ulong _out38;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseTuple(@data, @index, @_24653_t, out _out36, out _out37, out _out38);
        @success = _out36;
        @v = _out37;
        @rest__index = _out38;
      } else if (_source0.is_GByteArray) {
        bool _out39;
        @_Common____GenericMarshalling__i_Compile.@V _out40;
        ulong _out41;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseByteArray(@data, @index, out _out39, out _out40, out _out41);
        @success = _out39;
        @v = _out40;
        @rest__index = _out41;
      } else if (true) {
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @_24654_cases = ((_Common____GenericMarshalling__i_Compile.@G_GTaggedUnion)_source0._D).@cases;
        bool _out42;
        @_Common____GenericMarshalling__i_Compile.@V _out43;
        ulong _out44;
        @_Common____GenericMarshalling__i_Compile.@__default.@ParseCase(@data, @index, @_24654_cases, out _out42, out _out43, out _out44);
        @success = _out42;
        @v = _out43;
        @rest__index = _out44;
      }
    }
    public static void @Demarshall(byte[] @data, @_Common____GenericMarshalling__i_Compile.@G @grammar, out @_Common____GenericMarshalling__i_Compile.@V @v)
    {
      @v = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      bool @_24655_success = false;
      @_Common____GenericMarshalling__i_Compile.@V @_24656_val = new @_Common____GenericMarshalling__i_Compile.@V();
      ulong @_24657_rest = 0;
      bool _out45;
      @_Common____GenericMarshalling__i_Compile.@V _out46;
      ulong _out47;
      @_Common____GenericMarshalling__i_Compile.@__default.@ParseVal(@data, 0UL, @grammar, out _out45, out _out46, out _out47);
      @_24655_success = _out45;
      @_24656_val = _out46;
      @_24657_rest = _out47;
      @v = @_24656_val;
    }
    public static void @ComputeSeqSum(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @s, out ulong @size)
    {
      @size = 0;
      { }
      if (((ulong)(@s).LongLength).@Equals(0UL))
      {
        @size = 0UL;
      }
      else
      {
        ulong @_24658_v__size = 0;
        ulong _out48;
        @_Common____GenericMarshalling__i_Compile.@__default.@ComputeSizeOf((@s).Select((ulong)(0UL)), out _out48);
        @_24658_v__size = _out48;
        ulong @_24659_rest__size = 0;
        ulong _out49;
        @_Common____GenericMarshalling__i_Compile.@__default.@ComputeSeqSum((@s).Drop((ulong)(1UL)), out _out49);
        @_24659_rest__size = _out49;
        @size = (@_24658_v__size) + (@_24659_rest__size);
      }
    }
    public static void @ComputeSizeOf(@_Common____GenericMarshalling__i_Compile.@V @val, out ulong @size)
    {
      @size = 0;
      @_Common____GenericMarshalling__i_Compile.@V _source1 = @val;
      if (_source1.is_VUint64) {
        ulong @_24660___v28 = ((_Common____GenericMarshalling__i_Compile.@V_VUint64)_source1._D).@u;
        @size = 8UL;
      } else if (_source1.is_VArray) {
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24661_a = ((_Common____GenericMarshalling__i_Compile.@V_VArray)_source1._D).@a;
        ulong @_24662_v = 0;
        ulong _out50;
        @_Common____GenericMarshalling__i_Compile.@__default.@ComputeSeqSum(@_24661_a, out _out50);
        @_24662_v = _out50;
        if ((@_24662_v).@Equals(0UL))
        {
          @size = 8UL;
        }
        else
        {
          @size = (8UL) + (@_24662_v);
        }
      } else if (_source1.is_VTuple) {
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24663_t = ((_Common____GenericMarshalling__i_Compile.@V_VTuple)_source1._D).@t;
        ulong _out51;
        @_Common____GenericMarshalling__i_Compile.@__default.@ComputeSeqSum(@_24663_t, out _out51);
        @size = _out51;
      } else if (_source1.is_VByteArray) {
        Dafny.Sequence<byte> @_24664_b = ((_Common____GenericMarshalling__i_Compile.@V_VByteArray)_source1._D).@b;
        @size = (8UL) + ((ulong)(@_24664_b).LongLength);
      } else if (true) {
        ulong @_24665_c = ((_Common____GenericMarshalling__i_Compile.@V_VCase)_source1._D).@c;
        @_Common____GenericMarshalling__i_Compile.@V @_24666_val = ((_Common____GenericMarshalling__i_Compile.@V_VCase)_source1._D).@val;
        ulong @_24667_v = 0;
        ulong _out52;
        @_Common____GenericMarshalling__i_Compile.@__default.@ComputeSizeOf(@_24666_val, out _out52);
        @_24667_v = _out52;
        @size = (8UL) + (@_24667_v);
      }
    }
    public static void @MarshallUint64(ulong @n, byte[] @data, ulong @index)
    {
    TAIL_CALL_START: ;
      @_Common____MarshallInt__i_Compile.@__default.@MarshallUint64__guts(@n, @data, @index);
    }
    public static void @MarshallArrayContents(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @contents, @_Common____GenericMarshalling__i_Compile.@G @eltType, byte[] @data, ulong @index)
    {
      if (((ulong)(@contents).LongLength) > (0UL))
      {
        { }
        { }
        @_Common____GenericMarshalling__i_Compile.@__default.@MarshallVal((@contents).Select((ulong)(0UL)), @eltType, @data, @index);
        { }
        { }
        ulong @_24668_size = 0;
        ulong _out53;
        @_Common____GenericMarshalling__i_Compile.@__default.@ComputeSizeOf((@contents).Select((ulong)(0UL)), out _out53);
        @_24668_size = _out53;
        { }
        ulong @_24669_new__index = 0;
        @_24669_new__index = (@index) + (@_24668_size);
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24670_new__seq = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.Empty;
        @_24670_new__seq = (@contents).Drop((ulong)(1UL));
        @_Common____GenericMarshalling__i_Compile.@__default.@MarshallArrayContents(@_24670_new__seq, @eltType, @data, @_24669_new__index);
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
      }
      else
      { }
    }
    public static void @MarshallArray(@_Common____GenericMarshalling__i_Compile.@V @val, @_Common____GenericMarshalling__i_Compile.@G @grammar, byte[] @data, ulong @index)
    {
      { }
      @_Common____GenericMarshalling__i_Compile.@__default.@MarshallUint64((ulong)((@val).@dtor_a).LongLength, @data, @index);
      { }
      { }
      { }
      { }
      @_Common____GenericMarshalling__i_Compile.@__default.@MarshallArrayContents((@val).@dtor_a, (@grammar).@dtor_elt, @data, (@index) + (@_Native____NativeTypes__i_Compile.@__default.@Uint64Size()));
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @MarshallTupleContents(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @contents, Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @eltTypes, byte[] @data, ulong @index)
    {
      if (((ulong)(@contents).LongLength) > (0UL))
      {
        { }
        { }
        @_Common____GenericMarshalling__i_Compile.@__default.@MarshallVal((@contents).Select((ulong)(0UL)), (@eltTypes).Select((ulong)(0UL)), @data, @index);
        { }
        { }
        ulong @_24671_size = 0;
        ulong _out54;
        @_Common____GenericMarshalling__i_Compile.@__default.@ComputeSizeOf((@contents).Select((ulong)(0UL)), out _out54);
        @_24671_size = _out54;
        { }
        ulong @_24672_new__index = 0;
        @_24672_new__index = (@index) + (@_24671_size);
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24673_new__seq = Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.Empty;
        @_24673_new__seq = (@contents).Drop((ulong)(1UL));
        @_Common____GenericMarshalling__i_Compile.@__default.@MarshallTupleContents(@_24673_new__seq, (@eltTypes).Drop((ulong)(1UL)), @data, @_24672_new__index);
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
      }
      else
      { }
    }
    public static void @MarshallTuple(@_Common____GenericMarshalling__i_Compile.@V @val, @_Common____GenericMarshalling__i_Compile.@G @grammar, byte[] @data, ulong @index)
    {
      @_Common____GenericMarshalling__i_Compile.@__default.@MarshallTupleContents((@val).@dtor_t, (@grammar).@dtor_t, @data, @index);
      { }
    }
    public static void @MarshallBytes(Dafny.Sequence<byte> @bytes, byte[] @data, ulong @index)
    {
    TAIL_CALL_START: ;
      ulong @_24674_j = 0;
      @_24674_j = 0UL;
      while ((@_24674_j) < ((ulong)(@bytes).LongLength))
      {
        (@data)[(int)((@index) + (@_24674_j))] = (@bytes).Select(@_24674_j);
        @_24674_j = (@_24674_j) + (1UL);
      }
    }
    public static void @MarshallByteArray(@_Common____GenericMarshalling__i_Compile.@V @val, @_Common____GenericMarshalling__i_Compile.@G @grammar, byte[] @data, ulong @index)
    {
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@__default.@MarshallUint64((ulong)((@val).@dtor_b).LongLength, @data, @index);
      { }
      @_Common____GenericMarshalling__i_Compile.@__default.@MarshallBytes((@val).@dtor_b, @data, (@index) + (8UL));
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @MarshallCase(@_Common____GenericMarshalling__i_Compile.@V @val, @_Common____GenericMarshalling__i_Compile.@G @grammar, byte[] @data, ulong @index)
    {
      @_Common____GenericMarshalling__i_Compile.@__default.@MarshallUint64((@val).@dtor_c, @data, @index);
      @_Common____GenericMarshalling__i_Compile.@__default.@MarshallVal((@val).@dtor_val, ((@grammar).@dtor_cases).Select((@val).@dtor_c), @data, (@index) + (8UL));
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @MarshallVUint64(@_Common____GenericMarshalling__i_Compile.@V @val, @_Common____GenericMarshalling__i_Compile.@G @grammar, byte[] @data, ulong @index)
    {
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@__default.@MarshallUint64((@val).@dtor_u, @data, @index);
      { }
    }
    public static void @MarshallVal(@_Common____GenericMarshalling__i_Compile.@V @val, @_Common____GenericMarshalling__i_Compile.@G @grammar, byte[] @data, ulong @index)
    {
      @_Common____GenericMarshalling__i_Compile.@V _source2 = @val;
      if (_source2.is_VUint64) {
        ulong @_24675___v29 = ((_Common____GenericMarshalling__i_Compile.@V_VUint64)_source2._D).@u;
        @_Common____GenericMarshalling__i_Compile.@__default.@MarshallVUint64(@val, @grammar, @data, @index);
      } else if (_source2.is_VArray) {
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24676___v30 = ((_Common____GenericMarshalling__i_Compile.@V_VArray)_source2._D).@a;
        @_Common____GenericMarshalling__i_Compile.@__default.@MarshallArray(@val, @grammar, @data, @index);
      } else if (_source2.is_VTuple) {
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V> @_24677___v31 = ((_Common____GenericMarshalling__i_Compile.@V_VTuple)_source2._D).@t;
        @_Common____GenericMarshalling__i_Compile.@__default.@MarshallTuple(@val, @grammar, @data, @index);
      } else if (_source2.is_VByteArray) {
        Dafny.Sequence<byte> @_24678___v32 = ((_Common____GenericMarshalling__i_Compile.@V_VByteArray)_source2._D).@b;
        @_Common____GenericMarshalling__i_Compile.@__default.@MarshallByteArray(@val, @grammar, @data, @index);
      } else if (true) {
        ulong @_24679___v33 = ((_Common____GenericMarshalling__i_Compile.@V_VCase)_source2._D).@c;
        @_Common____GenericMarshalling__i_Compile.@V @_24680___v34 = ((_Common____GenericMarshalling__i_Compile.@V_VCase)_source2._D).@val;
        @_Common____GenericMarshalling__i_Compile.@__default.@MarshallCase(@val, @grammar, @data, @index);
      }
    }
    public static void @Marshall(@_Common____GenericMarshalling__i_Compile.@V @val, @_Common____GenericMarshalling__i_Compile.@G @grammar, out byte[] @data)
    {
      @data = (byte[])null;
    TAIL_CALL_START: ;
      ulong @_24681_size = 0;
      ulong _out55;
      @_Common____GenericMarshalling__i_Compile.@__default.@ComputeSizeOf(@val, out _out55);
      @_24681_size = _out55;
      @data = new byte[(int)(@_24681_size)];
      @_Common____GenericMarshalling__i_Compile.@__default.@MarshallVal(@val, @grammar, @data, 0UL);
      { }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>> @_hparse__Array__contents__FULL(Dafny.Sequence<byte> @data, @_Common____GenericMarshalling__i_Compile.@G @eltType, ulong @len) {
      if ((@len).@Equals(0UL)) {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>(new _Logic____Option__i_Compile.@Option_Some<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements())), @data));
      } else {
        @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> _let_tmp_rhs6 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Val(@data, @eltType);
        @_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V> @_24682_val = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs6)._D).@_0;
        Dafny.Sequence<byte> @_24683_rest1 = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs6)._D).@_1;
        @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>> _let_tmp_rhs7 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Array__contents(@_24683_rest1, @eltType, (@len) - (1UL));
        @_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>> @_24684_others = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>)(_let_tmp_rhs7)._D).@_0;
        Dafny.Sequence<byte> @_24685_rest2 = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>)(_let_tmp_rhs7)._D).@_1;
        if ((!((@_24682_val).@is_None)) && (!((@_24684_others).@is_None))) {
          return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>(new _Logic____Option__i_Compile.@Option_Some<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>((Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements((@_24682_val).@dtor_v)).@Concat((@_24684_others).@dtor_v))), @_24685_rest2));
        } else {
          return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>(new _Logic____Option__i_Compile.@Option_None<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>()), Dafny.Sequence<byte>.FromElements()));
        }
      }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>> @_hparse__Tuple__contents__FULL(Dafny.Sequence<byte> @data, Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @eltTypes) {
      if ((@eltTypes).@Equals(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements())) {
        return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>(new _Logic____Option__i_Compile.@Option_Some<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements())), @data));
      } else {
        @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> _let_tmp_rhs8 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Val(@data, (@eltTypes).Select((ulong)(0UL)));
        @_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V> @_24686_val = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs8)._D).@_0;
        Dafny.Sequence<byte> @_24687_rest1 = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>>)(_let_tmp_rhs8)._D).@_1;
        @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>> _let_tmp_rhs9 = @_Common____GenericMarshalling__i_Compile.@__default.@parse__Tuple__contents(@_24687_rest1, (@eltTypes).Drop((ulong)(1UL)));
        @_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>> @_24688_contents = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>)(_let_tmp_rhs9)._D).@_0;
        Dafny.Sequence<byte> @_24689_rest2 = ((_System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>)(_let_tmp_rhs9)._D).@_1;
        if ((!((@_24686_val).@is_None)) && (!((@_24688_contents).@is_None))) {
          return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>(new _Logic____Option__i_Compile.@Option_Some<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>((Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements((@_24686_val).@dtor_v)).@Concat((@_24688_contents).@dtor_v))), @_24689_rest2));
        } else {
          return new _System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<@_Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>,Dafny.Sequence<byte>>(new _Logic____Option__i_Compile.@Option<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>(new _Logic____Option__i_Compile.@Option_None<Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>>()), Dafny.Sequence<byte>.FromElements()));
        }
      }
    }
    public static @_System.@__tuple_h2<@_Logic____Option__i_Compile.@Option<@_Common____GenericMarshalling__i_Compile.@V>,Dafny.Sequence<byte>> @_hparse__Val__FULL(Dafny.Sequence<byte> @data, @_Common____GenericMarshalling__i_Compile.@G @grammar) {
      @_Common____GenericMarshalling__i_Compile.@G _source3 = @grammar;
      if (_source3.is_GUint64) {
        return @_Common____GenericMarshalling__i_Compile.@__default.@parse__Uint64(@data);
      } else if (_source3.is_GArray) {
        @_Common____GenericMarshalling__i_Compile.@G @_24690_elt = ((_Common____GenericMarshalling__i_Compile.@G_GArray)_source3._D).@elt;
        return @_Common____GenericMarshalling__i_Compile.@__default.@parse__Array(@data, @_24690_elt);
      } else if (_source3.is_GTuple) {
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @_24691_t = ((_Common____GenericMarshalling__i_Compile.@G_GTuple)_source3._D).@t;
        return @_Common____GenericMarshalling__i_Compile.@__default.@parse__Tuple(@data, @_24691_t);
      } else if (_source3.is_GByteArray) {
        return @_Common____GenericMarshalling__i_Compile.@__default.@parse__ByteArray(@data);
      } else if (true) {
        Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G> @_24692_cases = ((_Common____GenericMarshalling__i_Compile.@G_GTaggedUnion)_source3._D).@cases;
        return @_Common____GenericMarshalling__i_Compile.@__default.@parse__Case(@data, @_24692_cases);
      }
    }
  }
} // end of namespace _Common____GenericMarshalling__i_Compile
namespace @_Common____UdpClient__i_Compile {


  public partial class @__default {
    public static bool @EndPointIsValidIPV4(@_Native____Io__s_Compile.@EndPoint @endPoint) {
      return ((new BigInteger(((@endPoint).@dtor_addr).Length)).@Equals(new BigInteger(4))) && (((0) <= ((@endPoint).@dtor_port)) && (((@endPoint).@dtor_port) <= (65535)));
    }
  }
} // end of namespace _Common____UdpClient__i_Compile
namespace @_Common____SeqIsUnique__s_Compile {

  public partial class @__default {
  }
} // end of namespace _Common____SeqIsUnique__s_Compile
namespace @_Common____SeqIsUnique__i_Compile {



  public partial class @__default {
    public static void @SeqToSetConstruct<@X>(Dafny.Sequence<@X> @xs, out Dafny.Set<@X> @s)
    {
      @s = Dafny.Set<@X>.Empty;
    TAIL_CALL_START: ;
      { }
      @s = Dafny.Set<@X>.FromElements();
      BigInteger @_24693_i = BigInteger.Zero;
      @_24693_i = new BigInteger(0);
      while ((@_24693_i) < (new BigInteger((@xs).Length)))
      {
        @s = (@s).@Union(Dafny.Set<@X>.FromElements((@xs).Select(@_24693_i)));
        @_24693_i = (@_24693_i) + (new BigInteger(1));
      }
    }
    public static void @SetToUniqueSeqConstruct<@X>(Dafny.Set<@X> @s, out Dafny.Sequence<@X> @xs)
    {
      @xs = Dafny.Sequence<@X>.Empty;
      @X[] @_24694_arr = (@X[])null;
      @_24694_arr = Dafny.Helpers.InitNewArray1<@X>((new BigInteger((@s).Length)));
      Dafny.Set<@X> @_24695_s1 = Dafny.Set<@X>.Empty;
      @_24695_s1 = @s;
      { }
      { }
      while (!(new BigInteger((@_24695_s1).Length)).@Equals(new BigInteger(0)))
      {
        { }
        { }
        @X @_24696_x = default(@X);
        foreach (var _assign_such_that_0 in (@_24695_s1).Elements) { @_24696_x = _assign_such_that_0;
          if ((@_24695_s1).Contains(@_24696_x)) {
            goto _ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 9807)");
        _ASSIGN_SUCH_THAT_0: ;
        { }
        { }
        (@_24694_arr)[(int)((new BigInteger((@s).Length)) - (new BigInteger((@_24695_s1).Length)))] = @_24696_x;
        @_24695_s1 = (@_24695_s1).@Difference(Dafny.Set<@X>.FromElements(@_24696_x));
        { }
        { }
        { }
      }
      @xs = Dafny.Helpers.SeqFromArray(@_24694_arr);
      { }
    }
    public static void @SubsequenceConstruct<@X>(Dafny.Sequence<@X> @xs, @Func<@X,bool> @f, out Dafny.Sequence<@X> @xs_k)
    {
      @xs_k = Dafny.Sequence<@X>.Empty;
    TAIL_CALL_START: ;
      { }
      @X[] @_24697_arr = (@X[])null;
      @_24697_arr = Dafny.Helpers.InitNewArray1<@X>((new BigInteger((@xs).Length)));
      BigInteger @_24698_i = BigInteger.Zero;
      @_24698_i = new BigInteger(0);
      BigInteger @_24699_j = BigInteger.Zero;
      @_24699_j = new BigInteger(0);
      while ((@_24698_i) < (new BigInteger((@xs).Length)))
      {
        { }
        { }
        if (Dafny.Helpers.Id<@Func<@X,bool>>(@f)((@xs).Select(@_24698_i)))
        {
          { }
          (@_24697_arr)[(int)(@_24699_j)] = (@xs).Select(@_24698_i);
          @_24699_j = (@_24699_j) + (new BigInteger(1));
          { }
        }
        @_24698_i = (@_24698_i) + (new BigInteger(1));
        { }
      }
      @xs_k = Dafny.Helpers.SeqFromArray(@_24697_arr).Take(@_24699_j);
    }
    public static void @UniqueSubsequenceConstruct<@X>(Dafny.Sequence<@X> @xs, @Func<@X,bool> @f, out Dafny.Sequence<@X> @xs_k)
    {
      @xs_k = Dafny.Sequence<@X>.Empty;
    TAIL_CALL_START: ;
      Dafny.Set<@X> @_24700_s = Dafny.Set<@X>.Empty;
      @_24700_s = ((Dafny.Helpers.ComprehensionDelegate<@X>)delegate() { var _coll = new System.Collections.Generic.List<@X>(); foreach (var @_24701_x in (@xs).Elements) { if (((@xs).Contains(@_24701_x)) && (Dafny.Helpers.Id<@Func<@X,bool>>(@f)(@_24701_x))) { _coll.Add(@_24701_x); }}return Dafny.Set<@X>.FromCollection(_coll); })();
      Dafny.Sequence<@X> _out56;
      @_Common____SeqIsUnique__i_Compile.@__default.@SetToUniqueSeqConstruct(@_24700_s, out _out56);
      @xs_k = _out56;
    }
    public static Dafny.Sequence<@X> @AppendToUniqueSeq<@X>(Dafny.Sequence<@X> @xs, @X @x) {
      Dafny.Sequence<@X> @_24702_xs_k = (@xs).@Concat(Dafny.Sequence<@X>.FromElements(@x));
      return @_24702_xs_k;
    }
    public static Dafny.Sequence<@X> @AppendToUniqueSeqMaybe<@X>(Dafny.Sequence<@X> @xs, @X @x) {
      if ((@xs).Contains(@x)) {
        return @xs;
      } else {
        Dafny.Sequence<@X> @_24703_xs_k = (@xs).@Concat(Dafny.Sequence<@X>.FromElements(@x));
        return @_24703_xs_k;
      }
    }
  }
} // end of namespace _Common____SeqIsUnique__i_Compile
namespace @_GenericRefinement__i_Compile {



  public partial class @__default {
  }
} // end of namespace _GenericRefinement__i_Compile
namespace @_Common____NodeIdentity__i_Compile {







  public partial class @__default {
    public static Dafny.Sequence<byte> @ConvertEndPointToSeqByte(@_Native____Io__s_Compile.@EndPoint @e) {
      return @_Common____NodeIdentity__i_Compile.@__default.@_hConvertEndPointToSeqByte__FULL(@e);
    }
    public static @_Native____Io__s_Compile.@EndPoint @ConvertSeqByteToEndPoint(Dafny.Sequence<byte> @s) {
      return @_Common____NodeIdentity__i_Compile.@__default.@_hConvertSeqByteToEndPoint__FULL(@s);
    }
    public static ulong @ConvertEndPointToUint64(@_Native____Io__s_Compile.@EndPoint @e) {
      return @_Common____NodeIdentity__i_Compile.@__default.@_hConvertEndPointToUint64__FULL(@e);
    }
    public static @_Native____Io__s_Compile.@EndPoint @ConvertUint64ToEndPoint(ulong @u) {
      return @_Common____NodeIdentity__i_Compile.@__default.@_hConvertUint64ToEndPoint__FULL(@u);
    }
    public static void @FindMinEndPoint(Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @endpoints, out @_Native____Io__s_Compile.@EndPoint @min__e)
    {
      @min__e = new @_Native____Io__s_Compile.@EndPoint();
      { }
      if (((ulong)(@endpoints).LongLength).@Equals(1UL))
      {
        @min__e = (@endpoints).Select((ulong)(0UL));
        { }
        { }
        { }
        { }
      }
      else
      {
        @_Native____Io__s_Compile.@EndPoint @_24704_first = new @_Native____Io__s_Compile.@EndPoint();
        @_24704_first = (@endpoints).Select((ulong)(0UL));
        ulong @_24705_first64 = 0;
        @_24705_first64 = @_Common____NodeIdentity__i_Compile.@__default.@ConvertEndPointToUint64(@_24704_first);
        { }
        @_Native____Io__s_Compile.@EndPoint @_24706_min__others = new @_Native____Io__s_Compile.@EndPoint();
        @_Native____Io__s_Compile.@EndPoint _out57;
        @_Common____NodeIdentity__i_Compile.@__default.@FindMinEndPoint((@endpoints).Drop((ulong)(1UL)), out _out57);
        @_24706_min__others = _out57;
        ulong @_24707_min__others64 = 0;
        @_24707_min__others64 = @_Common____NodeIdentity__i_Compile.@__default.@ConvertEndPointToUint64(@_24706_min__others);
        @min__e = ((@_24705_first64) < (@_24707_min__others64)) ? (@_24704_first) : (@_24706_min__others);
        { }
        { }
        { }
        { }
        { }
      }
    }
    public static Dafny.Sequence<byte> @_hConvertEndPointToSeqByte__FULL(@_Native____Io__s_Compile.@EndPoint @e) {
      return ((Dafny.Sequence<byte>.FromElements(0, 0)).@Concat((@e).@dtor_addr)).@Concat(@_Common____Util__i_Compile.@__default.@Uint16ToSeqByte((@e).@dtor_port));
    }
    public static @_Native____Io__s_Compile.@EndPoint @_hConvertSeqByteToEndPoint__FULL(Dafny.Sequence<byte> @s) {
      return new _Native____Io__s_Compile.@EndPoint(new _Native____Io__s_Compile.@EndPoint_EndPoint((@s).Take((ulong)(6UL)).Drop((ulong)(2UL)), @_Common____Util__i_Compile.@__default.@SeqByteToUint16((@s).Drop((ulong)(6UL)))));
    }
    public static ulong @_hConvertEndPointToUint64__FULL(@_Native____Io__s_Compile.@EndPoint @e) {
      return @_Common____Util__i_Compile.@__default.@SeqByteToUint64(@_Common____NodeIdentity__i_Compile.@__default.@ConvertEndPointToSeqByte(@e));
    }
    public static @_Native____Io__s_Compile.@EndPoint @_hConvertUint64ToEndPoint__FULL(ulong @u) {
      return @_Common____NodeIdentity__i_Compile.@__default.@ConvertSeqByteToEndPoint(@_Common____Util__i_Compile.@__default.@Uint64ToSeqByte(@u));
    }
  }
} // end of namespace _Common____NodeIdentity__i_Compile
namespace @_LiveRSL____AppInterface__i_Compile {









  public abstract class Base_CAppMessage { }
  public partial class CAppMessage_CAppIncrement : Base_CAppMessage {
    public CAppMessage_CAppIncrement() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppIncrement;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____AppInterface__i_Compile.CAppMessage.CAppIncrement";
      return s;
    }
  }
  public partial class CAppMessage_CAppReply : Base_CAppMessage {
    public readonly ulong @response;
    public CAppMessage_CAppReply(ulong @response) {
      this.@response = @response;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppReply;
      return oth != null && this.@response.Equals(oth.@response);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@response.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____AppInterface__i_Compile.CAppMessage.CAppReply";
      s += "(";
      s += @response.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CAppMessage_CAppInvalid : Base_CAppMessage {
    public CAppMessage_CAppInvalid() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppInvalid;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____AppInterface__i_Compile.CAppMessage.CAppInvalid";
      return s;
    }
  }
  public struct @CAppMessage {
    Base_CAppMessage _d;
    public Base_CAppMessage _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CAppMessage(Base_CAppMessage d) { this._d = d; }
    static Base_CAppMessage theDefault;
    public static Base_CAppMessage Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppIncrement();
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CAppMessage && _D.Equals(((@CAppMessage)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CAppIncrement { get { return _D is CAppMessage_CAppIncrement; } }
    public bool is_CAppReply { get { return _D is CAppMessage_CAppReply; } }
    public bool is_CAppInvalid { get { return _D is CAppMessage_CAppInvalid; } }
    public ulong dtor_response { get { return ((CAppMessage_CAppReply)_D).@response; } }
  }

  public partial class @__default {
    public static @_Common____GenericMarshalling__i_Compile.@G @CAppState__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64());
    }
    public static ulong @parse__AppState(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return (ulong)((@val).@dtor_u);
    }
    public static bool @AppStateMarshallable(ulong @msg) {
      return true;
    }
    public static void @MarshallAppState(ulong @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64(@c));
    }
    public static bool @ValidAppMessage(@_LiveRSL____AppInterface__i_Compile.@CAppMessage @c) {
      return true;
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CAppMessage__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTaggedUnion(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()), new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()), new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()))));
    }
    public static @_LiveRSL____AppInterface__i_Compile.@CAppMessage @parse__AppMessage(@_Common____GenericMarshalling__i_Compile.@V @val) {
      if (((@val).@dtor_c).@Equals(0UL)) {
        return new _LiveRSL____AppInterface__i_Compile.@CAppMessage(new _LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppIncrement());
      } else {
        if (((@val).@dtor_c).@Equals(1UL)) {
          return new _LiveRSL____AppInterface__i_Compile.@CAppMessage(new _LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppReply(((@val).@dtor_val).@dtor_u));
        } else {
          return new _LiveRSL____AppInterface__i_Compile.@CAppMessage(new _LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppInvalid());
        }
      }
    }
    public static void @MarshallAppMessage(@_LiveRSL____AppInterface__i_Compile.@CAppMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_LiveRSL____AppInterface__i_Compile.@CAppMessage _source4 = @c;
      if (_source4.is_CAppIncrement) {
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(0UL, new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64(42UL))));
      } else if (_source4.is_CAppReply) {
        ulong @_24708_response = ((_LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppReply)_source4._D).@response;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(1UL, new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64(@_24708_response))));
      } else if (true) {
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(2UL, new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64(42UL))));
      }
    }
    public static void @CAppState__Init(out ulong @s)
    {
      @s = 0;
    TAIL_CALL_START: ;
      @s = 0UL;
    }
    public static void @CappedIncrImpl(ulong @v, out ulong @v_k)
    {
      @v_k = 0;
    TAIL_CALL_START: ;
      if ((@v).@Equals(18446744073709551615UL))
      {
        @v_k = @v;
      }
      else
      {
        @v_k = (@v) + (1UL);
      }
    }
    public static void @HandleAppRequest(ulong @appState, @_LiveRSL____AppInterface__i_Compile.@CAppMessage @request, out ulong @appState_k, out @_LiveRSL____AppInterface__i_Compile.@CAppMessage @reply)
    {
      @appState_k = 0;
      @reply = new @_LiveRSL____AppInterface__i_Compile.@CAppMessage();
    TAIL_CALL_START: ;
      if ((@request).@is_CAppIncrement)
      {
        ulong _out58;
        @_LiveRSL____AppInterface__i_Compile.@__default.@CappedIncrImpl(@appState, out _out58);
        @appState_k = _out58;
        @reply = new _LiveRSL____AppInterface__i_Compile.@CAppMessage(new _LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppReply(@appState_k));
      }
      else
      {
        @appState_k = @appState;
        @reply = new _LiveRSL____AppInterface__i_Compile.@CAppMessage(new _LiveRSL____AppInterface__i_Compile.@CAppMessage_CAppInvalid());
      }
    }
  }
} // end of namespace _LiveRSL____AppInterface__i_Compile
namespace @_LiveRSL____CTypes__i_Compile {










  public abstract class Base_CBallot { }
  public partial class CBallot_CBallot : Base_CBallot {
    public readonly ulong @seqno;
    public readonly ulong @proposerId;
    public CBallot_CBallot(ulong @seqno, ulong @proposerId) {
      this.@seqno = @seqno;
      this.@proposerId = @proposerId;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CTypes__i_Compile.@CBallot_CBallot;
      return oth != null && this.@seqno.Equals(oth.@seqno) && this.@proposerId.Equals(oth.@proposerId);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@proposerId.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CTypes__i_Compile.CBallot.CBallot";
      s += "(";
      s += @seqno.ToString();
      s += ", ";
      s += @proposerId.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CBallot {
    Base_CBallot _d;
    public Base_CBallot _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CBallot(Base_CBallot d) { this._d = d; }
    static Base_CBallot theDefault;
    public static Base_CBallot Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot(0, 0);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CBallot && _D.Equals(((@CBallot)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CBallot { get { return _D is CBallot_CBallot; } }
    public ulong dtor_seqno { get { return ((CBallot_CBallot)_D).@seqno; } }
    public ulong dtor_proposerId { get { return ((CBallot_CBallot)_D).@proposerId; } }
  }

  public abstract class Base_COperationNumber { }
  public partial class COperationNumber_COperationNumber : Base_COperationNumber {
    public readonly ulong @n;
    public COperationNumber_COperationNumber(ulong @n) {
      this.@n = @n;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber;
      return oth != null && this.@n.Equals(oth.@n);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@n.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CTypes__i_Compile.COperationNumber.COperationNumber";
      s += "(";
      s += @n.ToString();
      s += ")";
      return s;
    }
  }
  public struct @COperationNumber {
    Base_COperationNumber _d;
    public Base_COperationNumber _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @COperationNumber(Base_COperationNumber d) { this._d = d; }
    static Base_COperationNumber theDefault;
    public static Base_COperationNumber Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @COperationNumber && _D.Equals(((@COperationNumber)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_COperationNumber { get { return _D is COperationNumber_COperationNumber; } }
    public ulong dtor_n { get { return ((COperationNumber_COperationNumber)_D).@n; } }
  }

  public abstract class Base_CRequest { }
  public partial class CRequest_CRequest : Base_CRequest {
    public readonly @_Native____Io__s_Compile.@EndPoint @client;
    public readonly ulong @seqno;
    public readonly @_LiveRSL____AppInterface__i_Compile.@CAppMessage @request;
    public CRequest_CRequest(@_Native____Io__s_Compile.@EndPoint @client, ulong @seqno, @_LiveRSL____AppInterface__i_Compile.@CAppMessage @request) {
      this.@client = @client;
      this.@seqno = @seqno;
      this.@request = @request;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CTypes__i_Compile.@CRequest_CRequest;
      return oth != null && this.@client.Equals(oth.@client) && this.@seqno.Equals(oth.@seqno) && this.@request.Equals(oth.@request);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@client.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@request.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CTypes__i_Compile.CRequest.CRequest";
      s += "(";
      s += @client.ToString();
      s += ", ";
      s += @seqno.ToString();
      s += ", ";
      s += @request.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CRequest {
    Base_CRequest _d;
    public Base_CRequest _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CRequest(Base_CRequest d) { this._d = d; }
    static Base_CRequest theDefault;
    public static Base_CRequest Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CTypes__i_Compile.@CRequest_CRequest(new @_Native____Io__s_Compile.@EndPoint(), 0, new @_LiveRSL____AppInterface__i_Compile.@CAppMessage());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CRequest && _D.Equals(((@CRequest)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CRequest { get { return _D is CRequest_CRequest; } }
    public @_Native____Io__s_Compile.@EndPoint dtor_client { get { return ((CRequest_CRequest)_D).@client; } }
    public ulong dtor_seqno { get { return ((CRequest_CRequest)_D).@seqno; } }
    public @_LiveRSL____AppInterface__i_Compile.@CAppMessage dtor_request { get { return ((CRequest_CRequest)_D).@request; } }
  }


  public abstract class Base_CReply { }
  public partial class CReply_CReply : Base_CReply {
    public readonly @_Native____Io__s_Compile.@EndPoint @client;
    public readonly ulong @seqno;
    public readonly @_LiveRSL____AppInterface__i_Compile.@CAppMessage @reply;
    public CReply_CReply(@_Native____Io__s_Compile.@EndPoint @client, ulong @seqno, @_LiveRSL____AppInterface__i_Compile.@CAppMessage @reply) {
      this.@client = @client;
      this.@seqno = @seqno;
      this.@reply = @reply;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CTypes__i_Compile.@CReply_CReply;
      return oth != null && this.@client.Equals(oth.@client) && this.@seqno.Equals(oth.@seqno) && this.@reply.Equals(oth.@reply);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@client.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@reply.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CTypes__i_Compile.CReply.CReply";
      s += "(";
      s += @client.ToString();
      s += ", ";
      s += @seqno.ToString();
      s += ", ";
      s += @reply.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CReply {
    Base_CReply _d;
    public Base_CReply _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CReply(Base_CReply d) { this._d = d; }
    static Base_CReply theDefault;
    public static Base_CReply Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CTypes__i_Compile.@CReply_CReply(new @_Native____Io__s_Compile.@EndPoint(), 0, new @_LiveRSL____AppInterface__i_Compile.@CAppMessage());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CReply && _D.Equals(((@CReply)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CReply { get { return _D is CReply_CReply; } }
    public @_Native____Io__s_Compile.@EndPoint dtor_client { get { return ((CReply_CReply)_D).@client; } }
    public ulong dtor_seqno { get { return ((CReply_CReply)_D).@seqno; } }
    public @_LiveRSL____AppInterface__i_Compile.@CAppMessage dtor_reply { get { return ((CReply_CReply)_D).@reply; } }
  }


  public abstract class Base_CVote { }
  public partial class CVote_CVote : Base_CVote {
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @maxVBal;
    public readonly Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @maxVal;
    public CVote_CVote(@_LiveRSL____CTypes__i_Compile.@CBallot @maxVBal, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @maxVal) {
      this.@maxVBal = @maxVBal;
      this.@maxVal = @maxVal;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CTypes__i_Compile.@CVote_CVote;
      return oth != null && this.@maxVBal.Equals(oth.@maxVBal) && this.@maxVal.Equals(oth.@maxVal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@maxVBal.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxVal.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CTypes__i_Compile.CVote.CVote";
      s += "(";
      s += @maxVBal.ToString();
      s += ", ";
      s += @maxVal.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CVote {
    Base_CVote _d;
    public Base_CVote _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CVote(Base_CVote d) { this._d = d; }
    static Base_CVote theDefault;
    public static Base_CVote Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CTypes__i_Compile.@CVote_CVote(new @_LiveRSL____CTypes__i_Compile.@CBallot(), Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CVote && _D.Equals(((@CVote)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CVote { get { return _D is CVote_CVote; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_maxVBal { get { return ((CVote_CVote)_D).@maxVBal; } }
    public Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> dtor_maxVal { get { return ((CVote_CVote)_D).@maxVal; } }
  }

  public abstract class Base_CVotes { }
  public partial class CVotes_CVotes : Base_CVotes {
    public readonly Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> @v;
    public CVotes_CVotes(Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> @v) {
      this.@v = @v;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CTypes__i_Compile.@CVotes_CVotes;
      return oth != null && this.@v.Equals(oth.@v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@v.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CTypes__i_Compile.CVotes.CVotes";
      s += "(";
      s += @v.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CVotes {
    Base_CVotes _d;
    public Base_CVotes _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CVotes(Base_CVotes d) { this._d = d; }
    static Base_CVotes theDefault;
    public static Base_CVotes Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CTypes__i_Compile.@CVotes_CVotes(Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CVotes && _D.Equals(((@CVotes)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CVotes { get { return _D is CVotes_CVotes; } }
    public Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> dtor_v { get { return ((CVotes_CVotes)_D).@v; } }
  }

  public abstract class Base_OptionOpn { }
  public partial class OptionOpn_ExistsOperation : Base_OptionOpn {
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn;
    public OptionOpn_ExistsOperation(@_LiveRSL____CTypes__i_Compile.@COperationNumber @opn) {
      this.@opn = @opn;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CTypes__i_Compile.@OptionOpn_ExistsOperation;
      return oth != null && this.@opn.Equals(oth.@opn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@opn.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CTypes__i_Compile.OptionOpn.ExistsOperation";
      s += "(";
      s += @opn.ToString();
      s += ")";
      return s;
    }
  }
  public partial class OptionOpn_NotExistsOperation : Base_OptionOpn {
    public OptionOpn_NotExistsOperation() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CTypes__i_Compile.@OptionOpn_NotExistsOperation;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CTypes__i_Compile.OptionOpn.NotExistsOperation";
      return s;
    }
  }
  public struct @OptionOpn {
    Base_OptionOpn _d;
    public Base_OptionOpn _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @OptionOpn(Base_OptionOpn d) { this._d = d; }
    static Base_OptionOpn theDefault;
    public static Base_OptionOpn Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CTypes__i_Compile.@OptionOpn_ExistsOperation(new @_LiveRSL____CTypes__i_Compile.@COperationNumber());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @OptionOpn && _D.Equals(((@OptionOpn)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_ExistsOperation { get { return _D is OptionOpn_ExistsOperation; } }
    public bool is_NotExistsOperation { get { return _D is OptionOpn_NotExistsOperation; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_opn { get { return ((OptionOpn_ExistsOperation)_D).@opn; } }
  }

  public partial class @__default {
    public static ulong @BallotSize() {
      return (@_Native____NativeTypes__i_Compile.@__default.@Uint64Size()) + (@_Native____NativeTypes__i_Compile.@__default.@Uint64Size());
    }
    public static bool @CBallot__IsLessThan(@_LiveRSL____CTypes__i_Compile.@CBallot @lhs, @_LiveRSL____CTypes__i_Compile.@CBallot @rhs) {
      return (((@lhs).@dtor_seqno) < ((@rhs).@dtor_seqno)) || ((((@lhs).@dtor_seqno).@Equals((@rhs).@dtor_seqno)) && (((@lhs).@dtor_proposerId) < ((@rhs).@dtor_proposerId)));
    }
    public static bool @CBallot__IsNotGreaterThan(@_LiveRSL____CTypes__i_Compile.@CBallot @lhs, @_LiveRSL____CTypes__i_Compile.@CBallot @rhs) {
      return (((@lhs).@dtor_seqno) < ((@rhs).@dtor_seqno)) || ((((@lhs).@dtor_seqno).@Equals((@rhs).@dtor_seqno)) && (((@lhs).@dtor_proposerId) <= ((@rhs).@dtor_proposerId)));
    }
    public static void @CBalLeq(@_LiveRSL____CTypes__i_Compile.@CBallot @ba, @_LiveRSL____CTypes__i_Compile.@CBallot @bb, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      if ((((@ba).@dtor_seqno) < ((@bb).@dtor_seqno)) || ((((@ba).@dtor_seqno).@Equals((@bb).@dtor_seqno)) && (((@ba).@dtor_proposerId) <= ((@bb).@dtor_proposerId))))
      {
        @b = true;
      }
      else
      {
        @b = false;
      }
    }
    public static void @CBalLt(@_LiveRSL____CTypes__i_Compile.@CBallot @ba, @_LiveRSL____CTypes__i_Compile.@CBallot @bb, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      if ((((@ba).@dtor_seqno) < ((@bb).@dtor_seqno)) || ((((@ba).@dtor_seqno).@Equals((@bb).@dtor_seqno)) && (((@ba).@dtor_proposerId) < ((@bb).@dtor_proposerId))))
      {
        @b = true;
      }
      else
      {
        @b = false;
      }
    }
    public static ulong @OpNumSize() {
      return @_Native____NativeTypes__i_Compile.@__default.@Uint64Size();
    }
    public static bool @ValidRequest(@_LiveRSL____CTypes__i_Compile.@CRequest @c) {
      return !((@c).@is_CRequest) || ((@_Common____UdpClient__i_Compile.@__default.@EndPointIsValidIPV4((@c).@dtor_client)) && (@_LiveRSL____AppInterface__i_Compile.@__default.@ValidAppMessage((@c).@dtor_request)));
    }
    public static bool @ValidRequestBatch(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @c) {
      return (Dafny.Helpers.QuantSeq(@c, true, @_24709_cr => !((@c).Contains(@_24709_cr)) || (@_LiveRSL____CTypes__i_Compile.@__default.@ValidRequest(@_24709_cr)))) && ((new BigInteger((@c).Length)) < (new BigInteger(65536)));
    }
    public static bool @ValidReply(@_LiveRSL____CTypes__i_Compile.@CReply @c) {
      return !((@c).@is_CReply) || ((@_Common____UdpClient__i_Compile.@__default.@EndPointIsValidIPV4((@c).@dtor_client)) && (@_LiveRSL____AppInterface__i_Compile.@__default.@ValidAppMessage((@c).@dtor_reply)));
    }
    public static BigInteger @max__val__len() {
      return new BigInteger(16777216);
    }
  }
} // end of namespace _LiveRSL____CTypes__i_Compile
namespace @_LiveRSL____CMessage__i_Compile {


  public abstract class Base_CMessage { }
  public partial class CMessage_CMessage__Request : Base_CMessage {
    public readonly bool @retrans;
    public readonly ulong @seqno;
    public readonly @_LiveRSL____AppInterface__i_Compile.@CAppMessage @val;
    public CMessage_CMessage__Request(bool @retrans, ulong @seqno, @_LiveRSL____AppInterface__i_Compile.@CAppMessage @val) {
      this.@retrans = @retrans;
      this.@seqno = @seqno;
      this.@val = @val;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Request;
      return oth != null && this.@retrans.Equals(oth.@retrans) && this.@seqno.Equals(oth.@seqno) && this.@val.Equals(oth.@val);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@retrans.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@val.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__Request";
      s += "(";
      s += @retrans.ToString();
      s += ", ";
      s += @seqno.ToString();
      s += ", ";
      s += @val.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CMessage_CMessage__1a : Base_CMessage {
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @bal__1a;
    public CMessage_CMessage__1a(@_LiveRSL____CTypes__i_Compile.@CBallot @bal__1a) {
      this.@bal__1a = @bal__1a;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__1a;
      return oth != null && this.@bal__1a.Equals(oth.@bal__1a);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__1a.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__1a";
      s += "(";
      s += @bal__1a.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CMessage_CMessage__1b : Base_CMessage {
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @bal__1b;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint;
    public readonly @_LiveRSL____CTypes__i_Compile.@CVotes @votes;
    public CMessage_CMessage__1b(@_LiveRSL____CTypes__i_Compile.@CBallot @bal__1b, @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint, @_LiveRSL____CTypes__i_Compile.@CVotes @votes) {
      this.@bal__1b = @bal__1b;
      this.@logTruncationPoint = @logTruncationPoint;
      this.@votes = @votes;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__1b;
      return oth != null && this.@bal__1b.Equals(oth.@bal__1b) && this.@logTruncationPoint.Equals(oth.@logTruncationPoint) && this.@votes.Equals(oth.@votes);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__1b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@logTruncationPoint.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@votes.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__1b";
      s += "(";
      s += @bal__1b.ToString();
      s += ", ";
      s += @logTruncationPoint.ToString();
      s += ", ";
      s += @votes.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CMessage_CMessage__2a : Base_CMessage {
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @bal__2a;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__2a;
    public readonly Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @val__2a;
    public CMessage_CMessage__2a(@_LiveRSL____CTypes__i_Compile.@CBallot @bal__2a, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__2a, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @val__2a) {
      this.@bal__2a = @bal__2a;
      this.@opn__2a = @opn__2a;
      this.@val__2a = @val__2a;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__2a;
      return oth != null && this.@bal__2a.Equals(oth.@bal__2a) && this.@opn__2a.Equals(oth.@opn__2a) && this.@val__2a.Equals(oth.@val__2a);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__2a.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__2a.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@val__2a.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__2a";
      s += "(";
      s += @bal__2a.ToString();
      s += ", ";
      s += @opn__2a.ToString();
      s += ", ";
      s += @val__2a.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CMessage_CMessage__2b : Base_CMessage {
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @bal__2b;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__2b;
    public readonly Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @val__2b;
    public CMessage_CMessage__2b(@_LiveRSL____CTypes__i_Compile.@CBallot @bal__2b, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__2b, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @val__2b) {
      this.@bal__2b = @bal__2b;
      this.@opn__2b = @opn__2b;
      this.@val__2b = @val__2b;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__2b;
      return oth != null && this.@bal__2b.Equals(oth.@bal__2b) && this.@opn__2b.Equals(oth.@opn__2b) && this.@val__2b.Equals(oth.@val__2b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__2b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__2b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@val__2b.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__2b";
      s += "(";
      s += @bal__2b.ToString();
      s += ", ";
      s += @opn__2b.ToString();
      s += ", ";
      s += @val__2b.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CMessage_CMessage__Heartbeat : Base_CMessage {
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @bal__heartbeat;
    public readonly bool @suspicious;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__ckpt;
    public CMessage_CMessage__Heartbeat(@_LiveRSL____CTypes__i_Compile.@CBallot @bal__heartbeat, bool @suspicious, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__ckpt) {
      this.@bal__heartbeat = @bal__heartbeat;
      this.@suspicious = @suspicious;
      this.@opn__ckpt = @opn__ckpt;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Heartbeat;
      return oth != null && this.@bal__heartbeat.Equals(oth.@bal__heartbeat) && this.@suspicious.Equals(oth.@suspicious) && this.@opn__ckpt.Equals(oth.@opn__ckpt);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__heartbeat.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@suspicious.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__ckpt.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__Heartbeat";
      s += "(";
      s += @bal__heartbeat.ToString();
      s += ", ";
      s += @suspicious.ToString();
      s += ", ";
      s += @opn__ckpt.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CMessage_CMessage__Reply : Base_CMessage {
    public readonly ulong @seqno__reply;
    public readonly @_LiveRSL____AppInterface__i_Compile.@CAppMessage @reply;
    public CMessage_CMessage__Reply(ulong @seqno__reply, @_LiveRSL____AppInterface__i_Compile.@CAppMessage @reply) {
      this.@seqno__reply = @seqno__reply;
      this.@reply = @reply;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Reply;
      return oth != null && this.@seqno__reply.Equals(oth.@seqno__reply) && this.@reply.Equals(oth.@reply);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@seqno__reply.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@reply.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__Reply";
      s += "(";
      s += @seqno__reply.ToString();
      s += ", ";
      s += @reply.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CMessage_CMessage__AppStateRequest : Base_CMessage {
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @bal__state__req;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__state__req;
    public CMessage_CMessage__AppStateRequest(@_LiveRSL____CTypes__i_Compile.@CBallot @bal__state__req, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__state__req) {
      this.@bal__state__req = @bal__state__req;
      this.@opn__state__req = @opn__state__req;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__AppStateRequest;
      return oth != null && this.@bal__state__req.Equals(oth.@bal__state__req) && this.@opn__state__req.Equals(oth.@opn__state__req);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__state__req.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__state__req.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__AppStateRequest";
      s += "(";
      s += @bal__state__req.ToString();
      s += ", ";
      s += @opn__state__req.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CMessage_CMessage__AppStateSupply : Base_CMessage {
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @bal__state__supply;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__state__supply;
    public readonly ulong @app__state;
    public readonly Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @reply__cache;
    public CMessage_CMessage__AppStateSupply(@_LiveRSL____CTypes__i_Compile.@CBallot @bal__state__supply, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn__state__supply, ulong @app__state, Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @reply__cache) {
      this.@bal__state__supply = @bal__state__supply;
      this.@opn__state__supply = @opn__state__supply;
      this.@app__state = @app__state;
      this.@reply__cache = @reply__cache;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__AppStateSupply;
      return oth != null && this.@bal__state__supply.Equals(oth.@bal__state__supply) && this.@opn__state__supply.Equals(oth.@opn__state__supply) && this.@app__state.Equals(oth.@app__state) && this.@reply__cache.Equals(oth.@reply__cache);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__state__supply.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn__state__supply.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@app__state.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@reply__cache.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__AppStateSupply";
      s += "(";
      s += @bal__state__supply.ToString();
      s += ", ";
      s += @opn__state__supply.ToString();
      s += ", ";
      s += @app__state.ToString();
      s += ", ";
      s += @reply__cache.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CMessage_CMessage__StartingPhase2 : Base_CMessage {
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @bal__2;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint__2;
    public CMessage_CMessage__StartingPhase2(@_LiveRSL____CTypes__i_Compile.@CBallot @bal__2, @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint__2) {
      this.@bal__2 = @bal__2;
      this.@logTruncationPoint__2 = @logTruncationPoint__2;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__StartingPhase2;
      return oth != null && this.@bal__2.Equals(oth.@bal__2) && this.@logTruncationPoint__2.Equals(oth.@logTruncationPoint__2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@bal__2.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@logTruncationPoint__2.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CMessage.CMessage__StartingPhase2";
      s += "(";
      s += @bal__2.ToString();
      s += ", ";
      s += @logTruncationPoint__2.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CMessage {
    Base_CMessage _d;
    public Base_CMessage _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CMessage(Base_CMessage d) { this._d = d; }
    static Base_CMessage theDefault;
    public static Base_CMessage Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Request(false, 0, new @_LiveRSL____AppInterface__i_Compile.@CAppMessage());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CMessage && _D.Equals(((@CMessage)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CMessage__Request { get { return _D is CMessage_CMessage__Request; } }
    public bool is_CMessage__1a { get { return _D is CMessage_CMessage__1a; } }
    public bool is_CMessage__1b { get { return _D is CMessage_CMessage__1b; } }
    public bool is_CMessage__2a { get { return _D is CMessage_CMessage__2a; } }
    public bool is_CMessage__2b { get { return _D is CMessage_CMessage__2b; } }
    public bool is_CMessage__Heartbeat { get { return _D is CMessage_CMessage__Heartbeat; } }
    public bool is_CMessage__Reply { get { return _D is CMessage_CMessage__Reply; } }
    public bool is_CMessage__AppStateRequest { get { return _D is CMessage_CMessage__AppStateRequest; } }
    public bool is_CMessage__AppStateSupply { get { return _D is CMessage_CMessage__AppStateSupply; } }
    public bool is_CMessage__StartingPhase2 { get { return _D is CMessage_CMessage__StartingPhase2; } }
    public bool dtor_retrans { get { return ((CMessage_CMessage__Request)_D).@retrans; } }
    public ulong dtor_seqno { get { return ((CMessage_CMessage__Request)_D).@seqno; } }
    public @_LiveRSL____AppInterface__i_Compile.@CAppMessage dtor_val { get { return ((CMessage_CMessage__Request)_D).@val; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_bal__1a { get { return ((CMessage_CMessage__1a)_D).@bal__1a; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_bal__1b { get { return ((CMessage_CMessage__1b)_D).@bal__1b; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_logTruncationPoint { get { return ((CMessage_CMessage__1b)_D).@logTruncationPoint; } }
    public @_LiveRSL____CTypes__i_Compile.@CVotes dtor_votes { get { return ((CMessage_CMessage__1b)_D).@votes; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_bal__2a { get { return ((CMessage_CMessage__2a)_D).@bal__2a; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_opn__2a { get { return ((CMessage_CMessage__2a)_D).@opn__2a; } }
    public Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> dtor_val__2a { get { return ((CMessage_CMessage__2a)_D).@val__2a; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_bal__2b { get { return ((CMessage_CMessage__2b)_D).@bal__2b; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_opn__2b { get { return ((CMessage_CMessage__2b)_D).@opn__2b; } }
    public Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> dtor_val__2b { get { return ((CMessage_CMessage__2b)_D).@val__2b; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_bal__heartbeat { get { return ((CMessage_CMessage__Heartbeat)_D).@bal__heartbeat; } }
    public bool dtor_suspicious { get { return ((CMessage_CMessage__Heartbeat)_D).@suspicious; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_opn__ckpt { get { return ((CMessage_CMessage__Heartbeat)_D).@opn__ckpt; } }
    public ulong dtor_seqno__reply { get { return ((CMessage_CMessage__Reply)_D).@seqno__reply; } }
    public @_LiveRSL____AppInterface__i_Compile.@CAppMessage dtor_reply { get { return ((CMessage_CMessage__Reply)_D).@reply; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_bal__state__req { get { return ((CMessage_CMessage__AppStateRequest)_D).@bal__state__req; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_opn__state__req { get { return ((CMessage_CMessage__AppStateRequest)_D).@opn__state__req; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_bal__state__supply { get { return ((CMessage_CMessage__AppStateSupply)_D).@bal__state__supply; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_opn__state__supply { get { return ((CMessage_CMessage__AppStateSupply)_D).@opn__state__supply; } }
    public ulong dtor_app__state { get { return ((CMessage_CMessage__AppStateSupply)_D).@app__state; } }
    public Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> dtor_reply__cache { get { return ((CMessage_CMessage__AppStateSupply)_D).@reply__cache; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_bal__2 { get { return ((CMessage_CMessage__StartingPhase2)_D).@bal__2; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_logTruncationPoint__2 { get { return ((CMessage_CMessage__StartingPhase2)_D).@logTruncationPoint__2; } }
  }

  public abstract class Base_CPacket { }
  public partial class CPacket_CPacket : Base_CPacket {
    public readonly @_Native____Io__s_Compile.@EndPoint @dst;
    public readonly @_Native____Io__s_Compile.@EndPoint @src;
    public readonly @_LiveRSL____CMessage__i_Compile.@CMessage @msg;
    public CPacket_CPacket(@_Native____Io__s_Compile.@EndPoint @dst, @_Native____Io__s_Compile.@EndPoint @src, @_LiveRSL____CMessage__i_Compile.@CMessage @msg) {
      this.@dst = @dst;
      this.@src = @src;
      this.@msg = @msg;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CPacket_CPacket;
      return oth != null && this.@dst.Equals(oth.@dst) && this.@src.Equals(oth.@src) && this.@msg.Equals(oth.@msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@dst.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@src.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@msg.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CPacket.CPacket";
      s += "(";
      s += @dst.ToString();
      s += ", ";
      s += @src.ToString();
      s += ", ";
      s += @msg.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CPacket {
    Base_CPacket _d;
    public Base_CPacket _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CPacket(Base_CPacket d) { this._d = d; }
    static Base_CPacket theDefault;
    public static Base_CPacket Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CMessage__i_Compile.@CPacket_CPacket(new @_Native____Io__s_Compile.@EndPoint(), new @_Native____Io__s_Compile.@EndPoint(), new @_LiveRSL____CMessage__i_Compile.@CMessage());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CPacket && _D.Equals(((@CPacket)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CPacket { get { return _D is CPacket_CPacket; } }
    public @_Native____Io__s_Compile.@EndPoint dtor_dst { get { return ((CPacket_CPacket)_D).@dst; } }
    public @_Native____Io__s_Compile.@EndPoint dtor_src { get { return ((CPacket_CPacket)_D).@src; } }
    public @_LiveRSL____CMessage__i_Compile.@CMessage dtor_msg { get { return ((CPacket_CPacket)_D).@msg; } }
  }

  public abstract class Base_CBroadcast { }
  public partial class CBroadcast_CBroadcast : Base_CBroadcast {
    public readonly @_Native____Io__s_Compile.@EndPoint @src;
    public readonly Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @dsts;
    public readonly @_LiveRSL____CMessage__i_Compile.@CMessage @msg;
    public CBroadcast_CBroadcast(@_Native____Io__s_Compile.@EndPoint @src, Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @dsts, @_LiveRSL____CMessage__i_Compile.@CMessage @msg) {
      this.@src = @src;
      this.@dsts = @dsts;
      this.@msg = @msg;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcast;
      return oth != null && this.@src.Equals(oth.@src) && this.@dsts.Equals(oth.@dsts) && this.@msg.Equals(oth.@msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@src.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@dsts.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@msg.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CBroadcast.CBroadcast";
      s += "(";
      s += @src.ToString();
      s += ", ";
      s += @dsts.ToString();
      s += ", ";
      s += @msg.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CBroadcast_CBroadcastNop : Base_CBroadcast {
    public CBroadcast_CBroadcastNop() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.CBroadcast.CBroadcastNop";
      return s;
    }
  }
  public struct @CBroadcast {
    Base_CBroadcast _d;
    public Base_CBroadcast _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CBroadcast(Base_CBroadcast d) { this._d = d; }
    static Base_CBroadcast theDefault;
    public static Base_CBroadcast Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcast(new @_Native____Io__s_Compile.@EndPoint(), Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.Empty, new @_LiveRSL____CMessage__i_Compile.@CMessage());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CBroadcast && _D.Equals(((@CBroadcast)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CBroadcast { get { return _D is CBroadcast_CBroadcast; } }
    public bool is_CBroadcastNop { get { return _D is CBroadcast_CBroadcastNop; } }
    public @_Native____Io__s_Compile.@EndPoint dtor_src { get { return ((CBroadcast_CBroadcast)_D).@src; } }
    public Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> dtor_dsts { get { return ((CBroadcast_CBroadcast)_D).@dsts; } }
    public @_LiveRSL____CMessage__i_Compile.@CMessage dtor_msg { get { return ((CBroadcast_CBroadcast)_D).@msg; } }
  }

  public abstract class Base_OutboundPackets { }
  public partial class OutboundPackets_Broadcast : Base_OutboundPackets {
    public readonly @_LiveRSL____CMessage__i_Compile.@CBroadcast @broadcast;
    public OutboundPackets_Broadcast(@_LiveRSL____CMessage__i_Compile.@CBroadcast @broadcast) {
      this.@broadcast = @broadcast;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast;
      return oth != null && this.@broadcast.Equals(oth.@broadcast);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@broadcast.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.OutboundPackets.Broadcast";
      s += "(";
      s += @broadcast.ToString();
      s += ")";
      return s;
    }
  }
  public partial class OutboundPackets_OutboundPacket : Base_OutboundPackets {
    public readonly @_Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket> @p;
    public OutboundPackets_OutboundPacket(@_Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket> @p) {
      this.@p = @p;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@OutboundPackets_OutboundPacket;
      return oth != null && this.@p.Equals(oth.@p);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@p.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.OutboundPackets.OutboundPacket";
      s += "(";
      s += @p.ToString();
      s += ")";
      return s;
    }
  }
  public partial class OutboundPackets_PacketSequence : Base_OutboundPackets {
    public readonly Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> @s;
    public OutboundPackets_PacketSequence(Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> @s) {
      this.@s = @s;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CMessage__i_Compile.@OutboundPackets_PacketSequence;
      return oth != null && this.@s.Equals(oth.@s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@s.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CMessage__i_Compile.OutboundPackets.PacketSequence";
      s += "(";
      s += @s.ToString();
      s += ")";
      return s;
    }
  }
  public struct @OutboundPackets {
    Base_OutboundPackets _d;
    public Base_OutboundPackets _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @OutboundPackets(Base_OutboundPackets d) { this._d = d; }
    static Base_OutboundPackets theDefault;
    public static Base_OutboundPackets Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new @_LiveRSL____CMessage__i_Compile.@CBroadcast());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @OutboundPackets && _D.Equals(((@OutboundPackets)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Broadcast { get { return _D is OutboundPackets_Broadcast; } }
    public bool is_OutboundPacket { get { return _D is OutboundPackets_OutboundPacket; } }
    public bool is_PacketSequence { get { return _D is OutboundPackets_PacketSequence; } }
    public @_LiveRSL____CMessage__i_Compile.@CBroadcast dtor_broadcast { get { return ((OutboundPackets_Broadcast)_D).@broadcast; } }
    public @_Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket> dtor_p { get { return ((OutboundPackets_OutboundPacket)_D).@p; } }
    public Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> dtor_s { get { return ((OutboundPackets_PacketSequence)_D).@s; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____CMessage__i_Compile
namespace @_LiveRSL____CMessageRefinements__i_Compile {







  public partial class @__default {
  }
} // end of namespace _LiveRSL____CMessageRefinements__i_Compile
namespace @_LiveRSL____PacketParsing__i_Compile {











  public partial class @__default {
    public static @_Common____GenericMarshalling__i_Compile.@G @EndPoint__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64());
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CRequest__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@EndPoint__grammar(), new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()), @_LiveRSL____AppInterface__i_Compile.@__default.@CAppMessage__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CRequestBatch__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GArray(@_LiveRSL____PacketParsing__i_Compile.@__default.@CRequest__grammar()));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CReply__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@EndPoint__grammar(), new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()), @_LiveRSL____AppInterface__i_Compile.@__default.@CAppMessage__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CBallot__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()), new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()))));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @COperationNumber__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64());
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CVote__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@CBallot__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CRequestBatch__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMap__grammar(@_Common____GenericMarshalling__i_Compile.@G @key, @_Common____GenericMarshalling__i_Compile.@G @val) {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GArray(new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@key, @val)))));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CVotes__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GArray(new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@COperationNumber__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CVote__grammar())))));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CReplyCache__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GArray(new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@EndPoint__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CReply__grammar())))));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__Request__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()), new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()), @_LiveRSL____AppInterface__i_Compile.@__default.@CAppMessage__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__1a__grammar() {
      return @_LiveRSL____PacketParsing__i_Compile.@__default.@CBallot__grammar();
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__1b__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@CBallot__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@COperationNumber__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CVotes__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__2a__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@CBallot__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@COperationNumber__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CRequestBatch__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__2b__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@CBallot__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@COperationNumber__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CRequestBatch__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__Heartbeat__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@CBallot__grammar(), new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()), @_LiveRSL____PacketParsing__i_Compile.@__default.@COperationNumber__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__Reply__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GUint64()), @_LiveRSL____AppInterface__i_Compile.@__default.@CAppMessage__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__AppStateRequest__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@CBallot__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@COperationNumber__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__AppStateSupply__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@CBallot__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@COperationNumber__grammar(), @_LiveRSL____AppInterface__i_Compile.@__default.@CAppState__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CReplyCache__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__StartingPhase2__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@CBallot__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@COperationNumber__grammar())));
    }
    public static @_Common____GenericMarshalling__i_Compile.@G @CMessage__grammar() {
      return new _Common____GenericMarshalling__i_Compile.@G(new _Common____GenericMarshalling__i_Compile.@G_GTaggedUnion(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@G>.FromElements(@_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__Request__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__1a__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__1b__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__2a__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__2b__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__Heartbeat__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__Reply__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__AppStateRequest__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__AppStateSupply__grammar(), @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__StartingPhase2__grammar())));
    }
    public static @_Native____Io__s_Compile.@EndPoint @parse__EndPoint(@_Common____GenericMarshalling__i_Compile.@V @val) {
      if (((@val).@dtor_u) <= (281474976710655UL)) {
        return @_Common____NodeIdentity__i_Compile.@__default.@ConvertUint64ToEndPoint((@val).@dtor_u);
      } else {
        return new _Native____Io__s_Compile.@EndPoint(new _Native____Io__s_Compile.@EndPoint_EndPoint(Dafny.Sequence<byte>.FromElements(0, 0, 0, 0), 0));
      }
    }
    public static @_LiveRSL____CTypes__i_Compile.@CRequest @parse__Request(@_Common____GenericMarshalling__i_Compile.@V @val) {
      @_Native____Io__s_Compile.@EndPoint @_24710_ep = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__EndPoint(((@val).@dtor_t).Select(new BigInteger(0)));
      return new _LiveRSL____CTypes__i_Compile.@CRequest(new _LiveRSL____CTypes__i_Compile.@CRequest_CRequest(@_24710_ep, (((@val).@dtor_t).Select(new BigInteger(1))).@dtor_u, @_LiveRSL____AppInterface__i_Compile.@__default.@parse__AppMessage(((@val).@dtor_t).Select(new BigInteger(2)))));
    }
    public static Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @parse__RequestBatch(@_Common____GenericMarshalling__i_Compile.@V @val) {
      if ((new BigInteger(((@val).@dtor_a).Length)).@Equals(new BigInteger(0))) {
        return Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements();
      } else {
        @_LiveRSL____CTypes__i_Compile.@CRequest @_24711_req = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Request(((@val).@dtor_a).Select(new BigInteger(0)));
        @_Common____GenericMarshalling__i_Compile.@V @_24712_restVal = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray(((@val).@dtor_a).Drop(new BigInteger(1))));
        Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_24713_rest = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__RequestBatch(@_24712_restVal);
        return (Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements(@_24711_req)).@Concat(@_24713_rest);
      }
    }
    public static @_LiveRSL____CTypes__i_Compile.@CReply @parse__Reply(@_Common____GenericMarshalling__i_Compile.@V @val) {
      @_Native____Io__s_Compile.@EndPoint @_24714_ep = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__EndPoint(((@val).@dtor_t).Select(new BigInteger(0)));
      return new _LiveRSL____CTypes__i_Compile.@CReply(new _LiveRSL____CTypes__i_Compile.@CReply_CReply(@_24714_ep, (((@val).@dtor_t).Select(new BigInteger(1))).@dtor_u, @_LiveRSL____AppInterface__i_Compile.@__default.@parse__AppMessage(((@val).@dtor_t).Select(new BigInteger(2)))));
    }
    public static @_LiveRSL____CTypes__i_Compile.@CBallot @parse__Ballot(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CTypes__i_Compile.@CBallot(new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot((((@val).@dtor_t).Select((ulong)(0UL))).@dtor_u, (((@val).@dtor_t).Select((ulong)(1UL))).@dtor_u));
    }
    public static @_LiveRSL____CTypes__i_Compile.@COperationNumber @parse__OperationNumber(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber((@val).@dtor_u));
    }
    public static @_LiveRSL____CTypes__i_Compile.@CVote @parse__Vote(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CTypes__i_Compile.@CVote(new _LiveRSL____CTypes__i_Compile.@CVote_CVote(@_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Ballot(((@val).@dtor_t).Select((ulong)(0UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__RequestBatch(((@val).@dtor_t).Select((ulong)(1UL)))));
    }
    public static Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @parse__ReplyCache(@_Common____GenericMarshalling__i_Compile.@V @val) {
      if ((new BigInteger(((@val).@dtor_a).Length)).@Equals(new BigInteger(0))) {
        return Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>.FromElements();
      } else {
        @_Common____GenericMarshalling__i_Compile.@V @_24715_tuple = ((@val).@dtor_a).Select(new BigInteger(0));
        @_Native____Io__s_Compile.@EndPoint @_24716_e = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__EndPoint(((@_24715_tuple).@dtor_t).Select(new BigInteger(0)));
        @_LiveRSL____CTypes__i_Compile.@CReply @_24717_reply = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Reply(((@_24715_tuple).@dtor_t).Select(new BigInteger(1)));
        Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @_24718_others = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__ReplyCache(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray(((@val).@dtor_a).Drop(new BigInteger(1)))));
        Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @_24719_m = (@_24718_others).Update(@_24716_e, @_24717_reply);
        return @_24719_m;
      }
    }
    public static @_LiveRSL____CTypes__i_Compile.@CVotes @parse__Votes(@_Common____GenericMarshalling__i_Compile.@V @val) {
      if ((new BigInteger(((@val).@dtor_a).Length)).@Equals(new BigInteger(0))) {
        return new _LiveRSL____CTypes__i_Compile.@CVotes(new _LiveRSL____CTypes__i_Compile.@CVotes_CVotes(Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.FromElements()));
      } else {
        @_Common____GenericMarshalling__i_Compile.@V @_24720_tuple = ((@val).@dtor_a).Select((ulong)(0UL));
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24721_op = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__OperationNumber(((@_24720_tuple).@dtor_t).Select((ulong)(0UL)));
        @_LiveRSL____CTypes__i_Compile.@CVote @_24722_vote = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Vote(((@_24720_tuple).@dtor_t).Select((ulong)(1UL)));
        @_LiveRSL____CTypes__i_Compile.@CVotes @_24723_others = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Votes(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray(((@val).@dtor_a).Drop((ulong)(1UL)))));
        Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> @_24724_m = ((@_24723_others).@dtor_v).Update(@_24721_op, @_24722_vote);
        return new _LiveRSL____CTypes__i_Compile.@CVotes(new _LiveRSL____CTypes__i_Compile.@CVotes_CVotes(@_24724_m));
      }
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__Request(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Request(!((((@val).@dtor_t).Select((ulong)(0UL))).@dtor_u).@Equals(0UL), (((@val).@dtor_t).Select((ulong)(1UL))).@dtor_u, @_LiveRSL____AppInterface__i_Compile.@__default.@parse__AppMessage(((@val).@dtor_t).Select((ulong)(2UL)))));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__1a(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__1a(@_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Ballot(@val)));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__1b(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__1b(@_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Ballot(((@val).@dtor_t).Select((ulong)(0UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__OperationNumber(((@val).@dtor_t).Select((ulong)(1UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Votes(((@val).@dtor_t).Select((ulong)(2UL)))));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__2a(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__2a(@_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Ballot(((@val).@dtor_t).Select((ulong)(0UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__OperationNumber(((@val).@dtor_t).Select((ulong)(1UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__RequestBatch(((@val).@dtor_t).Select((ulong)(2UL)))));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__2b(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__2b(@_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Ballot(((@val).@dtor_t).Select((ulong)(0UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__OperationNumber(((@val).@dtor_t).Select((ulong)(1UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__RequestBatch(((@val).@dtor_t).Select((ulong)(2UL)))));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__Heartbeat(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Heartbeat(@_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Ballot(((@val).@dtor_t).Select((ulong)(0UL))), !((((@val).@dtor_t).Select((ulong)(1UL))).@dtor_u).@Equals(0UL), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__OperationNumber(((@val).@dtor_t).Select((ulong)(2UL)))));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__Reply(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Reply((((@val).@dtor_t).Select(new BigInteger(0))).@dtor_u, @_LiveRSL____AppInterface__i_Compile.@__default.@parse__AppMessage(((@val).@dtor_t).Select(new BigInteger(1)))));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__AppStateRequest(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__AppStateRequest(@_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Ballot(((@val).@dtor_t).Select((ulong)(0UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__OperationNumber(((@val).@dtor_t).Select((ulong)(1UL)))));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__AppStateSupply(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__AppStateSupply(@_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Ballot(((@val).@dtor_t).Select((ulong)(0UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__OperationNumber(((@val).@dtor_t).Select((ulong)(1UL))), @_LiveRSL____AppInterface__i_Compile.@__default.@parse__AppState(((@val).@dtor_t).Select((ulong)(2UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__ReplyCache(((@val).@dtor_t).Select((ulong)(3UL)))));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message__StartingPhase2(@_Common____GenericMarshalling__i_Compile.@V @val) {
      return new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__StartingPhase2(@_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Ballot(((@val).@dtor_t).Select((ulong)(0UL))), @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__OperationNumber(((@val).@dtor_t).Select((ulong)(1UL)))));
    }
    public static @_LiveRSL____CMessage__i_Compile.@CMessage @parse__Message(@_Common____GenericMarshalling__i_Compile.@V @val) {
      if (((@val).@dtor_c).@Equals(0UL)) {
        return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__Request((@val).@dtor_val);
      } else {
        if (((@val).@dtor_c).@Equals(1UL)) {
          return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__1a((@val).@dtor_val);
        } else {
          if (((@val).@dtor_c).@Equals(2UL)) {
            return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__1b((@val).@dtor_val);
          } else {
            if (((@val).@dtor_c).@Equals(3UL)) {
              return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__2a((@val).@dtor_val);
            } else {
              if (((@val).@dtor_c).@Equals(4UL)) {
                return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__2b((@val).@dtor_val);
              } else {
                if (((@val).@dtor_c).@Equals(5UL)) {
                  return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__Heartbeat((@val).@dtor_val);
                } else {
                  if (((@val).@dtor_c).@Equals(6UL)) {
                    return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__Reply((@val).@dtor_val);
                  } else {
                    if (((@val).@dtor_c).@Equals(7UL)) {
                      return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__AppStateRequest((@val).@dtor_val);
                    } else {
                      if (((@val).@dtor_c).@Equals(8UL)) {
                        return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__AppStateSupply((@val).@dtor_val);
                      } else {
                        if (((@val).@dtor_c).@Equals(9UL)) {
                          return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__StartingPhase2((@val).@dtor_val);
                        } else {
                          return @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message__Request(@val);
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    public static void @PaxosDemarshallDataMethod(byte[] @data, out @_LiveRSL____CMessage__i_Compile.@CMessage @msg)
    {
      @msg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
    TAIL_CALL_START: ;
      { }
      @_Common____GenericMarshalling__i_Compile.@V @_24725_val = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out59;
      @_Common____GenericMarshalling__i_Compile.@__default.@Demarshall(@data, @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__grammar(), out _out59);
      @_24725_val = _out59;
      { }
      @msg = @_LiveRSL____PacketParsing__i_Compile.@__default.@parse__Message(@_24725_val);
    }
    public static void @MarshallEndPoint(@_Native____Io__s_Compile.@EndPoint @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64(@_Common____NodeIdentity__i_Compile.@__default.@ConvertEndPointToUint64(@c)));
      { }
    }
    public static void @MarshallRequest(@_LiveRSL____CTypes__i_Compile.@CRequest @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24726_marshalled__app__message = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out60;
      @_LiveRSL____AppInterface__i_Compile.@__default.@MarshallAppMessage((@c).@dtor_request, out _out60);
      @_24726_marshalled__app__message = _out60;
      @_Common____GenericMarshalling__i_Compile.@V @_24727_marshalled__ep = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out61;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallEndPoint((@c).@dtor_client, out _out61);
      @_24727_marshalled__ep = _out61;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24727_marshalled__ep, new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64((@c).@dtor_seqno)), @_24726_marshalled__app__message)));
      { }
      { }
      { }
      { }
    }
    public static void @MarshallRequestBatch(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
      if ((new BigInteger((@c).Length)).@Equals(new BigInteger(0)))
      {
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements()));
      }
      else
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24728_single = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out62;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallRequest((@c).Select(new BigInteger(0)), out _out62);
        @_24728_single = _out62;
        { }
        @_Common____GenericMarshalling__i_Compile.@V @_24729_rest = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out63;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallRequestBatch((@c).Drop(new BigInteger(1)), out _out63);
        @_24729_rest = _out63;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray((Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24728_single)).@Concat((@_24729_rest).@dtor_a)));
      }
    }
    public static void @MarshallReply(@_LiveRSL____CTypes__i_Compile.@CReply @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24730_marshalled__app__message = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out64;
      @_LiveRSL____AppInterface__i_Compile.@__default.@MarshallAppMessage((@c).@dtor_reply, out _out64);
      @_24730_marshalled__app__message = _out64;
      @_Common____GenericMarshalling__i_Compile.@V @_24731_marshalled__ep = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out65;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallEndPoint((@c).@dtor_client, out _out65);
      @_24731_marshalled__ep = _out65;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24731_marshalled__ep, new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64((@c).@dtor_seqno)), @_24730_marshalled__app__message)));
      { }
      { }
      { }
      { }
    }
    public static void @MarshallBallot(@_LiveRSL____CTypes__i_Compile.@CBallot @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64((@c).@dtor_seqno)), new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64((@c).@dtor_proposerId)))));
    }
    public static void @MarshallOperationNumber(@_LiveRSL____CTypes__i_Compile.@COperationNumber @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64((@c).@dtor_n));
    }
    public static void @MarshallVote(@_LiveRSL____CTypes__i_Compile.@CVote @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24732_bal = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out66;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallBallot((@c).@dtor_maxVBal, out _out66);
      @_24732_bal = _out66;
      @_Common____GenericMarshalling__i_Compile.@V @_24733_v = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out67;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallRequestBatch((@c).@dtor_maxVal, out _out67);
      @_24733_v = _out67;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24732_bal, @_24733_v)));
    }
    public static void @MarshallReplyCache(Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
      if (((ulong)(@c).LongLength).@Equals(0UL))
      {
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements()));
        { }
      }
      else
      {
        @_Native____Io__s_Compile.@EndPoint @_24734_ep = new @_Native____Io__s_Compile.@EndPoint();
        foreach (var _assign_such_that_1 in (@c).Domain) { @_24734_ep = _assign_such_that_1;
          if ((@c).Contains(@_24734_ep)) {
            goto _ASSIGN_SUCH_THAT_1;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 12382)");
        _ASSIGN_SUCH_THAT_1: ;
        @_Common____GenericMarshalling__i_Compile.@V @_24735_marshalled__ep = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out68;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallEndPoint(@_24734_ep, out _out68);
        @_24735_marshalled__ep = _out68;
        @_Common____GenericMarshalling__i_Compile.@V @_24736_marshalled__reply = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out69;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallReply((@c).Select(@_24734_ep), out _out69);
        @_24736_marshalled__reply = _out69;
        Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @_24737_remainder = Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>.Empty;
        @_24737_remainder = @_Collections____Maps__i_Compile.@__default.@RemoveElt<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>(@c, @_24734_ep);
        @_Common____GenericMarshalling__i_Compile.@V @_24738_marshalled__remainder = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out70;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallReplyCache(@_24737_remainder, out _out70);
        @_24738_marshalled__remainder = _out70;
        { }
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray((Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24735_marshalled__ep, @_24736_marshalled__reply))))).@Concat((@_24738_marshalled__remainder).@dtor_a)));
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
      }
    }
    public static void @MarshallVotes(@_LiveRSL____CTypes__i_Compile.@CVotes @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
      if (((ulong)((@c).@dtor_v).LongLength).@Equals(0UL))
      {
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements()));
        { }
      }
      else
      {
        { }
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24739_op = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        foreach (var _assign_such_that_2 in ((@c).@dtor_v).Domain) { @_24739_op = _assign_such_that_2;
          if (((@c).@dtor_v).Contains(@_24739_op)) {
            goto _ASSIGN_SUCH_THAT_2;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 12440)");
        _ASSIGN_SUCH_THAT_2: ;
        @_Common____GenericMarshalling__i_Compile.@V @_24740_marshalled__op = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out71;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallOperationNumber(@_24739_op, out _out71);
        @_24740_marshalled__op = _out71;
        @_Common____GenericMarshalling__i_Compile.@V @_24741_marshalled__vote = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out72;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallVote(((@c).@dtor_v).Select(@_24739_op), out _out72);
        @_24741_marshalled__vote = _out72;
        Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> @_24742_remainder = Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.Empty;
        @_24742_remainder = @_Collections____Maps__i_Compile.@__default.@RemoveElt<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>((@c).@dtor_v, @_24739_op);
        @_Common____GenericMarshalling__i_Compile.@V @_24743_marshalled__remainder = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out73;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallVotes(new _LiveRSL____CTypes__i_Compile.@CVotes(new _LiveRSL____CTypes__i_Compile.@CVotes_CVotes(@_24742_remainder)), out _out73);
        @_24743_marshalled__remainder = _out73;
        { }
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VArray((Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24740_marshalled__op, @_24741_marshalled__vote))))).@Concat((@_24743_marshalled__remainder).@dtor_a)));
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
      }
    }
    public static void @MarshallMessage__Request(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24744_v = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out74;
      @_LiveRSL____AppInterface__i_Compile.@__default.@MarshallAppMessage((@c).@dtor_val, out _out74);
      @_24744_v = _out74;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64(((@c).@dtor_retrans) ? (1UL) : (0UL))), new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64((@c).@dtor_seqno)), @_24744_v)));
    }
    public static void @MarshallMessage__1a(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V _out75;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallBallot((@c).@dtor_bal__1a, out _out75);
      @val = _out75;
    }
    public static void @MarshallMessage__1b(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24745_bal = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out76;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallBallot((@c).@dtor_bal__1b, out _out76);
      @_24745_bal = _out76;
      @_Common____GenericMarshalling__i_Compile.@V @_24746_logTruncationPoint = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out77;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallOperationNumber((@c).@dtor_logTruncationPoint, out _out77);
      @_24746_logTruncationPoint = _out77;
      @_Common____GenericMarshalling__i_Compile.@V @_24747_votes = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out78;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallVotes((@c).@dtor_votes, out _out78);
      @_24747_votes = _out78;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24745_bal, @_24746_logTruncationPoint, @_24747_votes)));
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @MarshallMessage__2a(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24748_bal = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out79;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallBallot((@c).@dtor_bal__2a, out _out79);
      @_24748_bal = _out79;
      @_Common____GenericMarshalling__i_Compile.@V @_24749_op = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out80;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallOperationNumber((@c).@dtor_opn__2a, out _out80);
      @_24749_op = _out80;
      @_Common____GenericMarshalling__i_Compile.@V @_24750_v = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out81;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallRequestBatch((@c).@dtor_val__2a, out _out81);
      @_24750_v = _out81;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24748_bal, @_24749_op, @_24750_v)));
      { }
      { }
      { }
      { }
    }
    public static void @MarshallMessage__2b(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24751_bal = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out82;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallBallot((@c).@dtor_bal__2b, out _out82);
      @_24751_bal = _out82;
      @_Common____GenericMarshalling__i_Compile.@V @_24752_op = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out83;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallOperationNumber((@c).@dtor_opn__2b, out _out83);
      @_24752_op = _out83;
      @_Common____GenericMarshalling__i_Compile.@V @_24753_v = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out84;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallRequestBatch((@c).@dtor_val__2b, out _out84);
      @_24753_v = _out84;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24751_bal, @_24752_op, @_24753_v)));
      { }
      { }
      { }
      { }
    }
    public static void @MarshallMessage__Heartbeat(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24754_ballot = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out85;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallBallot((@c).@dtor_bal__heartbeat, out _out85);
      @_24754_ballot = _out85;
      @_Common____GenericMarshalling__i_Compile.@V @_24755_op = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out86;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallOperationNumber((@c).@dtor_opn__ckpt, out _out86);
      @_24755_op = _out86;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24754_ballot, new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64(((@c).@dtor_suspicious) ? (1UL) : (0UL))), @_24755_op)));
    }
    public static void @MarshallMessage__Reply(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24756_app__val = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out87;
      @_LiveRSL____AppInterface__i_Compile.@__default.@MarshallAppMessage((@c).@dtor_reply, out _out87);
      @_24756_app__val = _out87;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VUint64((@c).@dtor_seqno__reply)), @_24756_app__val)));
    }
    public static void @MarshallMessage__AppStateRequest(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24757_ballot = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out88;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallBallot((@c).@dtor_bal__state__req, out _out88);
      @_24757_ballot = _out88;
      @_Common____GenericMarshalling__i_Compile.@V @_24758_opn = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out89;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallOperationNumber((@c).@dtor_opn__state__req, out _out89);
      @_24758_opn = _out89;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24757_ballot, @_24758_opn)));
    }
    public static void @MarshallMessage__AppStateSupply(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24759_ballot = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out90;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallBallot((@c).@dtor_bal__state__supply, out _out90);
      @_24759_ballot = _out90;
      @_Common____GenericMarshalling__i_Compile.@V @_24760_opn__state__supply = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out91;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallOperationNumber((@c).@dtor_opn__state__supply, out _out91);
      @_24760_opn__state__supply = _out91;
      @_Common____GenericMarshalling__i_Compile.@V @_24761_app__state = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out92;
      @_LiveRSL____AppInterface__i_Compile.@__default.@MarshallAppState((@c).@dtor_app__state, out _out92);
      @_24761_app__state = _out92;
      @_Common____GenericMarshalling__i_Compile.@V @_24762_reply__cache = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out93;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallReplyCache((@c).@dtor_reply__cache, out _out93);
      @_24762_reply__cache = _out93;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24759_ballot, @_24760_opn__state__supply, @_24761_app__state, @_24762_reply__cache)));
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @MarshallMessage__StartingPhase2(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24763_bal = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out94;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallBallot((@c).@dtor_bal__2, out _out94);
      @_24763_bal = _out94;
      @_Common____GenericMarshalling__i_Compile.@V @_24764_op = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out95;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallOperationNumber((@c).@dtor_logTruncationPoint__2, out _out95);
      @_24764_op = _out95;
      @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VTuple(Dafny.Sequence<@_Common____GenericMarshalling__i_Compile.@V>.FromElements(@_24763_bal, @_24764_op)));
    }
    public static void @MarshallMessage(@_LiveRSL____CMessage__i_Compile.@CMessage @c, out @_Common____GenericMarshalling__i_Compile.@V @val)
    {
      @val = new @_Common____GenericMarshalling__i_Compile.@V();
    TAIL_CALL_START: ;
      if ((@c).@is_CMessage__Request)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24765_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out96;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__Request(@c, out _out96);
        @_24765_msg = _out96;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(0UL, @_24765_msg));
      }
      else
      if ((@c).@is_CMessage__1a)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24766_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out97;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__1a(@c, out _out97);
        @_24766_msg = _out97;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(1UL, @_24766_msg));
      }
      else
      if ((@c).@is_CMessage__1b)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24767_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out98;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__1b(@c, out _out98);
        @_24767_msg = _out98;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(2UL, @_24767_msg));
      }
      else
      if ((@c).@is_CMessage__2a)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24768_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out99;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__2a(@c, out _out99);
        @_24768_msg = _out99;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(3UL, @_24768_msg));
      }
      else
      if ((@c).@is_CMessage__2b)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24769_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out100;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__2b(@c, out _out100);
        @_24769_msg = _out100;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(4UL, @_24769_msg));
      }
      else
      if ((@c).@is_CMessage__Heartbeat)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24770_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out101;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__Heartbeat(@c, out _out101);
        @_24770_msg = _out101;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(5UL, @_24770_msg));
      }
      else
      if ((@c).@is_CMessage__Reply)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24771_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out102;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__Reply(@c, out _out102);
        @_24771_msg = _out102;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(6UL, @_24771_msg));
        { }
      }
      else
      if ((@c).@is_CMessage__AppStateRequest)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24772_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out103;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__AppStateRequest(@c, out _out103);
        @_24772_msg = _out103;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(7UL, @_24772_msg));
      }
      else
      if ((@c).@is_CMessage__AppStateSupply)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24773_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out104;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__AppStateSupply(@c, out _out104);
        @_24773_msg = _out104;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(8UL, @_24773_msg));
      }
      else
      if ((@c).@is_CMessage__StartingPhase2)
      {
        @_Common____GenericMarshalling__i_Compile.@V @_24774_msg = new @_Common____GenericMarshalling__i_Compile.@V();
        @_Common____GenericMarshalling__i_Compile.@V _out105;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage__StartingPhase2(@c, out _out105);
        @_24774_msg = _out105;
        @val = new _Common____GenericMarshalling__i_Compile.@V(new _Common____GenericMarshalling__i_Compile.@V_VCase(9UL, @_24774_msg));
      }
    }
    public static void @PaxosMarshall(@_LiveRSL____CMessage__i_Compile.@CMessage @msg, out byte[] @data)
    {
      @data = (byte[])null;
    TAIL_CALL_START: ;
      @_Common____GenericMarshalling__i_Compile.@V @_24775_val = new @_Common____GenericMarshalling__i_Compile.@V();
      @_Common____GenericMarshalling__i_Compile.@V _out106;
      @_LiveRSL____PacketParsing__i_Compile.@__default.@MarshallMessage(@msg, out _out106);
      @_24775_val = _out106;
      { }
      { }
      byte[] _out107;
      @_Common____GenericMarshalling__i_Compile.@__default.@Marshall(@_24775_val, @_LiveRSL____PacketParsing__i_Compile.@__default.@CMessage__grammar(), out _out107);
      @data = _out107;
      { }
      { }
    }
  }
} // end of namespace _LiveRSL____PacketParsing__i_Compile
namespace @_LiveRSL____ParametersState__i_Compile {



  public abstract class Base_ParametersState { }
  public partial class ParametersState_ParametersState : Base_ParametersState {
    public readonly ulong @maxLogLength;
    public readonly ulong @baselineViewTimeoutPeriod;
    public readonly ulong @heartbeatPeriod;
    public readonly ulong @maxIntegerVal;
    public readonly ulong @maxBatchSize;
    public readonly ulong @maxBatchDelay;
    public ParametersState_ParametersState(ulong @maxLogLength, ulong @baselineViewTimeoutPeriod, ulong @heartbeatPeriod, ulong @maxIntegerVal, ulong @maxBatchSize, ulong @maxBatchDelay) {
      this.@maxLogLength = @maxLogLength;
      this.@baselineViewTimeoutPeriod = @baselineViewTimeoutPeriod;
      this.@heartbeatPeriod = @heartbeatPeriod;
      this.@maxIntegerVal = @maxIntegerVal;
      this.@maxBatchSize = @maxBatchSize;
      this.@maxBatchDelay = @maxBatchDelay;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ParametersState__i_Compile.@ParametersState_ParametersState;
      return oth != null && this.@maxLogLength.Equals(oth.@maxLogLength) && this.@baselineViewTimeoutPeriod.Equals(oth.@baselineViewTimeoutPeriod) && this.@heartbeatPeriod.Equals(oth.@heartbeatPeriod) && this.@maxIntegerVal.Equals(oth.@maxIntegerVal) && this.@maxBatchSize.Equals(oth.@maxBatchSize) && this.@maxBatchDelay.Equals(oth.@maxBatchDelay);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@maxLogLength.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@baselineViewTimeoutPeriod.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@heartbeatPeriod.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxIntegerVal.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBatchSize.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBatchDelay.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ParametersState__i_Compile.ParametersState.ParametersState";
      s += "(";
      s += @maxLogLength.ToString();
      s += ", ";
      s += @baselineViewTimeoutPeriod.ToString();
      s += ", ";
      s += @heartbeatPeriod.ToString();
      s += ", ";
      s += @maxIntegerVal.ToString();
      s += ", ";
      s += @maxBatchSize.ToString();
      s += ", ";
      s += @maxBatchDelay.ToString();
      s += ")";
      return s;
    }
  }
  public struct @ParametersState {
    Base_ParametersState _d;
    public Base_ParametersState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ParametersState(Base_ParametersState d) { this._d = d; }
    static Base_ParametersState theDefault;
    public static Base_ParametersState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____ParametersState__i_Compile.@ParametersState_ParametersState(0, 0, 0, 0, 0, 0);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ParametersState && _D.Equals(((@ParametersState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_ParametersState { get { return _D is ParametersState_ParametersState; } }
    public ulong dtor_maxLogLength { get { return ((ParametersState_ParametersState)_D).@maxLogLength; } }
    public ulong dtor_baselineViewTimeoutPeriod { get { return ((ParametersState_ParametersState)_D).@baselineViewTimeoutPeriod; } }
    public ulong dtor_heartbeatPeriod { get { return ((ParametersState_ParametersState)_D).@heartbeatPeriod; } }
    public ulong dtor_maxIntegerVal { get { return ((ParametersState_ParametersState)_D).@maxIntegerVal; } }
    public ulong dtor_maxBatchSize { get { return ((ParametersState_ParametersState)_D).@maxBatchSize; } }
    public ulong dtor_maxBatchDelay { get { return ((ParametersState_ParametersState)_D).@maxBatchDelay; } }
  }

  public partial class @__default {
    public static void @LCappedAdditionImpl(ulong @x, ulong @y, @_LiveRSL____ParametersState__i_Compile.@ParametersState @p, out ulong @z)
    {
      @z = 0;
    TAIL_CALL_START: ;
      if ((@x) < (((@p).@dtor_maxIntegerVal) - (@y)))
      {
        @z = (@x) + (@y);
      }
      else
      {
        @z = (@p).@dtor_maxIntegerVal;
      }
    }
    public static ulong @CCappedAddition(ulong @x, ulong @y, @_LiveRSL____ParametersState__i_Compile.@ParametersState @p) {
      return @_LiveRSL____ParametersState__i_Compile.@__default.@_hCCappedAddition__FULL(@x, @y, @p);
    }
    public static ulong @_hCCappedAddition__FULL(ulong @x, ulong @y, @_LiveRSL____ParametersState__i_Compile.@ParametersState @p) {
      if (((@y) <= ((@p).@dtor_maxIntegerVal)) && ((@x) < (((@p).@dtor_maxIntegerVal) - (@y)))) {
        return (@x) + (@y);
      } else {
        return (@p).@dtor_maxIntegerVal;
      }
    }
  }
} // end of namespace _LiveRSL____ParametersState__i_Compile
namespace @_LiveRSL____PaxosConcreteConfiguration__i_Compile {





  public abstract class Base_PaxosConcreteConfiguration { }
  public partial class PaxosConcreteConfiguration_PaxosConcreteConfiguration : Base_PaxosConcreteConfiguration {
    public readonly Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @replicaIds;
    public PaxosConcreteConfiguration_PaxosConcreteConfiguration(Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @replicaIds) {
      this.@replicaIds = @replicaIds;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration_PaxosConcreteConfiguration;
      return oth != null && this.@replicaIds.Equals(oth.@replicaIds);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@replicaIds.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____PaxosConcreteConfiguration__i_Compile.PaxosConcreteConfiguration.PaxosConcreteConfiguration";
      s += "(";
      s += @replicaIds.ToString();
      s += ")";
      return s;
    }
  }
  public struct @PaxosConcreteConfiguration {
    Base_PaxosConcreteConfiguration _d;
    public Base_PaxosConcreteConfiguration _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @PaxosConcreteConfiguration(Base_PaxosConcreteConfiguration d) { this._d = d; }
    static Base_PaxosConcreteConfiguration theDefault;
    public static Base_PaxosConcreteConfiguration Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration_PaxosConcreteConfiguration(Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @PaxosConcreteConfiguration && _D.Equals(((@PaxosConcreteConfiguration)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_PaxosConcreteConfiguration { get { return _D is PaxosConcreteConfiguration_PaxosConcreteConfiguration; } }
    public Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> dtor_replicaIds { get { return ((PaxosConcreteConfiguration_PaxosConcreteConfiguration)_D).@replicaIds; } }
  }

  public partial class @__default {
    public static bool @PaxosEndPointIsValid(@_Native____Io__s_Compile.@EndPoint @endPoint, @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config) {
      return @_Common____UdpClient__i_Compile.@__default.@EndPointIsValidIPV4(@endPoint);
    }
    public static void @CGetReplicaIndex(@_Native____Io__s_Compile.@EndPoint @replica, @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config, out bool @found, out ulong @index)
    {
      @found = false;
      @index = 0;
    TAIL_CALL_START: ;
      ulong @_24776_i = 0;
      @_24776_i = 0UL;
      { }
      while ((@_24776_i) < ((ulong)((@config).@dtor_replicaIds).LongLength))
      {
        if ((@replica).@Equals(((@config).@dtor_replicaIds).Select(@_24776_i)))
        {
          @found = true;
          @index = @_24776_i;
          { }
          { }
          { }
          { }
          { }
          { }
          { }
          { }
          return;
        }
        if ((@_24776_i).@Equals(((ulong)((@config).@dtor_replicaIds).LongLength) - (1UL)))
        {
          @found = false;
          return;
        }
        @_24776_i = (@_24776_i) + (1UL);
      }
      @found = false;
    }
  }
} // end of namespace _LiveRSL____PaxosConcreteConfiguration__i_Compile
namespace @_LiveRSL____ConstantsState__i_Compile {


  public abstract class Base_ConstantsState { }
  public partial class ConstantsState_ConstantsState : Base_ConstantsState {
    public readonly @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config;
    public readonly @_LiveRSL____ParametersState__i_Compile.@ParametersState @params;
    public ConstantsState_ConstantsState(@_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config, @_LiveRSL____ParametersState__i_Compile.@ParametersState @params) {
      this.@config = @config;
      this.@params = @params;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ConstantsState__i_Compile.@ConstantsState_ConstantsState;
      return oth != null && this.@config.Equals(oth.@config) && this.@params.Equals(oth.@params);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@config.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@params.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ConstantsState__i_Compile.ConstantsState.ConstantsState";
      s += "(";
      s += @config.ToString();
      s += ", ";
      s += @params.ToString();
      s += ")";
      return s;
    }
  }
  public struct @ConstantsState {
    Base_ConstantsState _d;
    public Base_ConstantsState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ConstantsState(Base_ConstantsState d) { this._d = d; }
    static Base_ConstantsState theDefault;
    public static Base_ConstantsState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____ConstantsState__i_Compile.@ConstantsState_ConstantsState(new @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration(), new @_LiveRSL____ParametersState__i_Compile.@ParametersState());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ConstantsState && _D.Equals(((@ConstantsState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_ConstantsState { get { return _D is ConstantsState_ConstantsState; } }
    public @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration dtor_config { get { return ((ConstantsState_ConstantsState)_D).@config; } }
    public @_LiveRSL____ParametersState__i_Compile.@ParametersState dtor_params { get { return ((ConstantsState_ConstantsState)_D).@params; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____ConstantsState__i_Compile
namespace @_LiveRSL____PaxosWorldState__i_Compile {


  public abstract class Base_ActionStatus { }
  public partial class ActionStatus_Ok : Base_ActionStatus {
    public ActionStatus_Ok() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____PaxosWorldState__i_Compile.@ActionStatus_Ok;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____PaxosWorldState__i_Compile.ActionStatus.Ok";
      return s;
    }
  }
  public partial class ActionStatus_Ignore : Base_ActionStatus {
    public ActionStatus_Ignore() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____PaxosWorldState__i_Compile.@ActionStatus_Ignore;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____PaxosWorldState__i_Compile.ActionStatus.Ignore";
      return s;
    }
  }
  public partial class ActionStatus_Fail : Base_ActionStatus {
    public ActionStatus_Fail() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____PaxosWorldState__i_Compile.@ActionStatus_Fail;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____PaxosWorldState__i_Compile.ActionStatus.Fail";
      return s;
    }
  }
  public struct @ActionStatus {
    Base_ActionStatus _d;
    public Base_ActionStatus _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ActionStatus(Base_ActionStatus d) { this._d = d; }
    static Base_ActionStatus theDefault;
    public static Base_ActionStatus Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____PaxosWorldState__i_Compile.@ActionStatus_Ok();
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ActionStatus && _D.Equals(((@ActionStatus)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_Ok { get { return _D is ActionStatus_Ok; } }
    public bool is_Ignore { get { return _D is ActionStatus_Ignore; } }
    public bool is_Fail { get { return _D is ActionStatus_Fail; } }
    public static System.Collections.Generic.IEnumerable<@ActionStatus> AllSingletonConstructors {
      get {
        yield return new @ActionStatus(new ActionStatus_Ok());
        yield return new @ActionStatus(new ActionStatus_Ignore());
        yield return new @ActionStatus(new ActionStatus_Fail());
        yield break;
      }
    }
  }

  public abstract class Base_PaxosWorldState { }
  public partial class PaxosWorldState_PaxosWorldState : Base_PaxosWorldState {
    public readonly bool @good;
    public readonly @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config;
    public PaxosWorldState_PaxosWorldState(bool @good, @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config) {
      this.@good = @good;
      this.@config = @config;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState_PaxosWorldState;
      return oth != null && this.@good.Equals(oth.@good) && this.@config.Equals(oth.@config);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@good.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@config.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____PaxosWorldState__i_Compile.PaxosWorldState.PaxosWorldState";
      s += "(";
      s += @good.ToString();
      s += ", ";
      s += @config.ToString();
      s += ")";
      return s;
    }
  }
  public struct @PaxosWorldState {
    Base_PaxosWorldState _d;
    public Base_PaxosWorldState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @PaxosWorldState(Base_PaxosWorldState d) { this._d = d; }
    static Base_PaxosWorldState theDefault;
    public static Base_PaxosWorldState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState_PaxosWorldState(false, new @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @PaxosWorldState && _D.Equals(((@PaxosWorldState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_PaxosWorldState { get { return _D is PaxosWorldState_PaxosWorldState; } }
    public bool dtor_good { get { return ((PaxosWorldState_PaxosWorldState)_D).@good; } }
    public @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration dtor_config { get { return ((PaxosWorldState_PaxosWorldState)_D).@config; } }
  }

  public partial class @__default {
    public static ulong @f__max__uint64() {
      return 18446744073709551615UL;
    }
    public static void @UpdatePaxosWorld(@_LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState @world, @_LiveRSL____PaxosWorldState__i_Compile.@ActionStatus @status, out @_LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState @world_k)
    {
      @world_k = new @_LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState();
    TAIL_CALL_START: ;
      if ((@status).@is_Fail)
      {
        @world_k = Dafny.Helpers.Let<@_LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState,@_LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState>(@world, _pat_let0_0 => Dafny.Helpers.Let<@_LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState,@_LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState>(_pat_let0_0, @_24777_dt__update__tmp_h0 => new _LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState(new _LiveRSL____PaxosWorldState__i_Compile.@PaxosWorldState_PaxosWorldState(false, (@_24777_dt__update__tmp_h0).@dtor_config))));
      }
      else
      {
        @world_k = @world;
      }
    }
  }
} // end of namespace _LiveRSL____PaxosWorldState__i_Compile
namespace @_LiveRSL____ReplicaConstantsState__i_Compile {



  public abstract class Base_ReplicaConstantsState { }
  public partial class ReplicaConstantsState_ReplicaConstantsState : Base_ReplicaConstantsState {
    public readonly ulong @myIndex;
    public readonly @_LiveRSL____ConstantsState__i_Compile.@ConstantsState @all;
    public ReplicaConstantsState_ReplicaConstantsState(ulong @myIndex, @_LiveRSL____ConstantsState__i_Compile.@ConstantsState @all) {
      this.@myIndex = @myIndex;
      this.@all = @all;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState_ReplicaConstantsState;
      return oth != null && this.@myIndex.Equals(oth.@myIndex) && this.@all.Equals(oth.@all);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@myIndex.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@all.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ReplicaConstantsState__i_Compile.ReplicaConstantsState.ReplicaConstantsState";
      s += "(";
      s += @myIndex.ToString();
      s += ", ";
      s += @all.ToString();
      s += ")";
      return s;
    }
  }
  public struct @ReplicaConstantsState {
    Base_ReplicaConstantsState _d;
    public Base_ReplicaConstantsState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ReplicaConstantsState(Base_ReplicaConstantsState d) { this._d = d; }
    static Base_ReplicaConstantsState theDefault;
    public static Base_ReplicaConstantsState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState_ReplicaConstantsState(0, new @_LiveRSL____ConstantsState__i_Compile.@ConstantsState());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ReplicaConstantsState && _D.Equals(((@ReplicaConstantsState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_ReplicaConstantsState { get { return _D is ReplicaConstantsState_ReplicaConstantsState; } }
    public ulong dtor_myIndex { get { return ((ReplicaConstantsState_ReplicaConstantsState)_D).@myIndex; } }
    public @_LiveRSL____ConstantsState__i_Compile.@ConstantsState dtor_all { get { return ((ReplicaConstantsState_ReplicaConstantsState)_D).@all; } }
  }

  public partial class @__default {
    public static void @InitReplicaConstantsState(@_Native____Io__s_Compile.@EndPoint @endPoint, @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config, out @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @rc)
    {
      @rc = new @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState();
    TAIL_CALL_START: ;
      @_LiveRSL____ParametersState__i_Compile.@ParametersState @_24778_params = new @_LiveRSL____ParametersState__i_Compile.@ParametersState();
      @_24778_params = new _LiveRSL____ParametersState__i_Compile.@ParametersState(new _LiveRSL____ParametersState__i_Compile.@ParametersState_ParametersState(9999UL, 100000UL, 200UL, 18446744073709551615UL, 48UL, 10UL));
      @_LiveRSL____ConstantsState__i_Compile.@ConstantsState @_24779_constants = new @_LiveRSL____ConstantsState__i_Compile.@ConstantsState();
      @_24779_constants = new _LiveRSL____ConstantsState__i_Compile.@ConstantsState(new _LiveRSL____ConstantsState__i_Compile.@ConstantsState_ConstantsState(@config, @_24778_params));
      bool @_24780_found = false;
      ulong @_24781_index = 0;
      bool _out108;
      ulong _out109;
      @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@__default.@CGetReplicaIndex(@endPoint, @config, out _out108, out _out109);
      @_24780_found = _out108;
      @_24781_index = _out109;
      @rc = new _LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState(new _LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState_ReplicaConstantsState(@_24781_index, @_24779_constants));
    }
  }
} // end of namespace _LiveRSL____ReplicaConstantsState__i_Compile
namespace @_LiveRSL____ElectionState__i_Compile {




  public abstract class Base_CElectionState { }
  public partial class CElectionState_CElectionState : Base_CElectionState {
    public readonly @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants;
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @currentView;
    public readonly Dafny.Sequence<ulong> @currentViewSuspectors;
    public readonly ulong @epochEndTime;
    public readonly ulong @epochLength;
    public readonly Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @requestsReceivedThisEpoch;
    public readonly Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @requestsReceivedPrevEpochs;
    public CElectionState_CElectionState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, @_LiveRSL____CTypes__i_Compile.@CBallot @currentView, Dafny.Sequence<ulong> @currentViewSuspectors, ulong @epochEndTime, ulong @epochLength, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @requestsReceivedThisEpoch, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @requestsReceivedPrevEpochs) {
      this.@constants = @constants;
      this.@currentView = @currentView;
      this.@currentViewSuspectors = @currentViewSuspectors;
      this.@epochEndTime = @epochEndTime;
      this.@epochLength = @epochLength;
      this.@requestsReceivedThisEpoch = @requestsReceivedThisEpoch;
      this.@requestsReceivedPrevEpochs = @requestsReceivedPrevEpochs;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@currentView.Equals(oth.@currentView) && this.@currentViewSuspectors.Equals(oth.@currentViewSuspectors) && this.@epochEndTime.Equals(oth.@epochEndTime) && this.@epochLength.Equals(oth.@epochLength) && this.@requestsReceivedThisEpoch.Equals(oth.@requestsReceivedThisEpoch) && this.@requestsReceivedPrevEpochs.Equals(oth.@requestsReceivedPrevEpochs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@currentView.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@currentViewSuspectors.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@epochEndTime.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@epochLength.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@requestsReceivedThisEpoch.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@requestsReceivedPrevEpochs.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ElectionState__i_Compile.CElectionState.CElectionState";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @currentView.ToString();
      s += ", ";
      s += @currentViewSuspectors.ToString();
      s += ", ";
      s += @epochEndTime.ToString();
      s += ", ";
      s += @epochLength.ToString();
      s += ", ";
      s += @requestsReceivedThisEpoch.ToString();
      s += ", ";
      s += @requestsReceivedPrevEpochs.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CElectionState {
    Base_CElectionState _d;
    public Base_CElectionState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CElectionState(Base_CElectionState d) { this._d = d; }
    static Base_CElectionState theDefault;
    public static Base_CElectionState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState(new @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState(), new @_LiveRSL____CTypes__i_Compile.@CBallot(), Dafny.Sequence<ulong>.Empty, 0, 0, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CElectionState && _D.Equals(((@CElectionState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CElectionState { get { return _D is CElectionState_CElectionState; } }
    public @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState dtor_constants { get { return ((CElectionState_CElectionState)_D).@constants; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_currentView { get { return ((CElectionState_CElectionState)_D).@currentView; } }
    public Dafny.Sequence<ulong> dtor_currentViewSuspectors { get { return ((CElectionState_CElectionState)_D).@currentViewSuspectors; } }
    public ulong dtor_epochEndTime { get { return ((CElectionState_CElectionState)_D).@epochEndTime; } }
    public ulong dtor_epochLength { get { return ((CElectionState_CElectionState)_D).@epochLength; } }
    public Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> dtor_requestsReceivedThisEpoch { get { return ((CElectionState_CElectionState)_D).@requestsReceivedThisEpoch; } }
    public Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> dtor_requestsReceivedPrevEpochs { get { return ((CElectionState_CElectionState)_D).@requestsReceivedPrevEpochs; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____ElectionState__i_Compile
namespace @_LiveRSL____ProposerState__i_Compile {




  public abstract class Base_CIncompleteBatchTimer { }
  public partial class CIncompleteBatchTimer_CIncompleteBatchTimerOn : Base_CIncompleteBatchTimer {
    public readonly ulong @when;
    public CIncompleteBatchTimer_CIncompleteBatchTimerOn(ulong @when) {
      this.@when = @when;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer_CIncompleteBatchTimerOn;
      return oth != null && this.@when.Equals(oth.@when);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@when.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ProposerState__i_Compile.CIncompleteBatchTimer.CIncompleteBatchTimerOn";
      s += "(";
      s += @when.ToString();
      s += ")";
      return s;
    }
  }
  public partial class CIncompleteBatchTimer_CIncompleteBatchTimerOff : Base_CIncompleteBatchTimer {
    public CIncompleteBatchTimer_CIncompleteBatchTimerOff() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer_CIncompleteBatchTimerOff;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ProposerState__i_Compile.CIncompleteBatchTimer.CIncompleteBatchTimerOff";
      return s;
    }
  }
  public struct @CIncompleteBatchTimer {
    Base_CIncompleteBatchTimer _d;
    public Base_CIncompleteBatchTimer _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CIncompleteBatchTimer(Base_CIncompleteBatchTimer d) { this._d = d; }
    static Base_CIncompleteBatchTimer theDefault;
    public static Base_CIncompleteBatchTimer Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer_CIncompleteBatchTimerOn(0);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CIncompleteBatchTimer && _D.Equals(((@CIncompleteBatchTimer)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CIncompleteBatchTimerOn { get { return _D is CIncompleteBatchTimer_CIncompleteBatchTimerOn; } }
    public bool is_CIncompleteBatchTimerOff { get { return _D is CIncompleteBatchTimer_CIncompleteBatchTimerOff; } }
    public ulong dtor_when { get { return ((CIncompleteBatchTimer_CIncompleteBatchTimerOn)_D).@when; } }
  }

  public abstract class Base_ProposerState { }
  public partial class ProposerState_ProposerState : Base_ProposerState {
    public readonly @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants;
    public readonly byte @currentState;
    public readonly Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @requestQueue;
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @maxBallotISent1a;
    public readonly ulong @nextOperationNumberToPropose;
    public readonly Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @received1bPackets;
    public readonly Dafny.Map<@_Native____Io__s_Compile.@EndPoint,ulong> @highestSeqnoRequestedByClientThisView;
    public readonly @_LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer @incompleteBatchTimer;
    public readonly @_LiveRSL____ElectionState__i_Compile.@CElectionState @electionState;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @maxOpnWithProposal;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @maxLogTruncationPoint;
    public ProposerState_ProposerState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, byte @currentState, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @requestQueue, @_LiveRSL____CTypes__i_Compile.@CBallot @maxBallotISent1a, ulong @nextOperationNumberToPropose, Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @received1bPackets, Dafny.Map<@_Native____Io__s_Compile.@EndPoint,ulong> @highestSeqnoRequestedByClientThisView, @_LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer @incompleteBatchTimer, @_LiveRSL____ElectionState__i_Compile.@CElectionState @electionState, @_LiveRSL____CTypes__i_Compile.@COperationNumber @maxOpnWithProposal, @_LiveRSL____CTypes__i_Compile.@COperationNumber @maxLogTruncationPoint) {
      this.@constants = @constants;
      this.@currentState = @currentState;
      this.@requestQueue = @requestQueue;
      this.@maxBallotISent1a = @maxBallotISent1a;
      this.@nextOperationNumberToPropose = @nextOperationNumberToPropose;
      this.@received1bPackets = @received1bPackets;
      this.@highestSeqnoRequestedByClientThisView = @highestSeqnoRequestedByClientThisView;
      this.@incompleteBatchTimer = @incompleteBatchTimer;
      this.@electionState = @electionState;
      this.@maxOpnWithProposal = @maxOpnWithProposal;
      this.@maxLogTruncationPoint = @maxLogTruncationPoint;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@currentState.Equals(oth.@currentState) && this.@requestQueue.Equals(oth.@requestQueue) && this.@maxBallotISent1a.Equals(oth.@maxBallotISent1a) && this.@nextOperationNumberToPropose.Equals(oth.@nextOperationNumberToPropose) && this.@received1bPackets.Equals(oth.@received1bPackets) && this.@highestSeqnoRequestedByClientThisView.Equals(oth.@highestSeqnoRequestedByClientThisView) && this.@incompleteBatchTimer.Equals(oth.@incompleteBatchTimer) && this.@electionState.Equals(oth.@electionState) && this.@maxOpnWithProposal.Equals(oth.@maxOpnWithProposal) && this.@maxLogTruncationPoint.Equals(oth.@maxLogTruncationPoint);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@currentState.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@requestQueue.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBallotISent1a.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@nextOperationNumberToPropose.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@received1bPackets.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@highestSeqnoRequestedByClientThisView.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@incompleteBatchTimer.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@electionState.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxOpnWithProposal.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxLogTruncationPoint.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ProposerState__i_Compile.ProposerState.ProposerState";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @currentState.ToString();
      s += ", ";
      s += @requestQueue.ToString();
      s += ", ";
      s += @maxBallotISent1a.ToString();
      s += ", ";
      s += @nextOperationNumberToPropose.ToString();
      s += ", ";
      s += @received1bPackets.ToString();
      s += ", ";
      s += @highestSeqnoRequestedByClientThisView.ToString();
      s += ", ";
      s += @incompleteBatchTimer.ToString();
      s += ", ";
      s += @electionState.ToString();
      s += ", ";
      s += @maxOpnWithProposal.ToString();
      s += ", ";
      s += @maxLogTruncationPoint.ToString();
      s += ")";
      return s;
    }
  }
  public struct @ProposerState {
    Base_ProposerState _d;
    public Base_ProposerState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ProposerState(Base_ProposerState d) { this._d = d; }
    static Base_ProposerState theDefault;
    public static Base_ProposerState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState(new @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState(), 0, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty, new @_LiveRSL____CTypes__i_Compile.@CBallot(), 0, Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.Empty, Dafny.Map<@_Native____Io__s_Compile.@EndPoint,ulong>.Empty, new @_LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer(), new @_LiveRSL____ElectionState__i_Compile.@CElectionState(), new @_LiveRSL____CTypes__i_Compile.@COperationNumber(), new @_LiveRSL____CTypes__i_Compile.@COperationNumber());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ProposerState && _D.Equals(((@ProposerState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_ProposerState { get { return _D is ProposerState_ProposerState; } }
    public @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState dtor_constants { get { return ((ProposerState_ProposerState)_D).@constants; } }
    public byte dtor_currentState { get { return ((ProposerState_ProposerState)_D).@currentState; } }
    public Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> dtor_requestQueue { get { return ((ProposerState_ProposerState)_D).@requestQueue; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_maxBallotISent1a { get { return ((ProposerState_ProposerState)_D).@maxBallotISent1a; } }
    public ulong dtor_nextOperationNumberToPropose { get { return ((ProposerState_ProposerState)_D).@nextOperationNumberToPropose; } }
    public Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> dtor_received1bPackets { get { return ((ProposerState_ProposerState)_D).@received1bPackets; } }
    public Dafny.Map<@_Native____Io__s_Compile.@EndPoint,ulong> dtor_highestSeqnoRequestedByClientThisView { get { return ((ProposerState_ProposerState)_D).@highestSeqnoRequestedByClientThisView; } }
    public @_LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer dtor_incompleteBatchTimer { get { return ((ProposerState_ProposerState)_D).@incompleteBatchTimer; } }
    public @_LiveRSL____ElectionState__i_Compile.@CElectionState dtor_electionState { get { return ((ProposerState_ProposerState)_D).@electionState; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_maxOpnWithProposal { get { return ((ProposerState_ProposerState)_D).@maxOpnWithProposal; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_maxLogTruncationPoint { get { return ((ProposerState_ProposerState)_D).@maxLogTruncationPoint; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____ProposerState__i_Compile
namespace @_LiveRSL____COperationNumberSort__i_Compile {


  public partial class @__default {
    public static void @InsertionSortCOperationNumbers(@_LiveRSL____CTypes__i_Compile.@COperationNumber[] @a)
    {
    TAIL_CALL_START: ;
      if (((ulong)(@a).LongLength).@Equals(0UL))
      {
        return;
      }
      ulong @_24782_i = 0;
      @_24782_i = 1UL;
      while ((@_24782_i) < ((ulong)(@a).LongLength))
      {
        ulong @_24783_j = 0;
        @_24783_j = @_24782_i;
        while (((0UL) < (@_24783_j)) && ((((@a)[(int)((@_24783_j) - (1UL))]).@dtor_n) > (((@a)[(int)(@_24783_j)]).@dtor_n)))
        {
          var _arr0 = @a;
          var _index0 = @_24783_j;
          var _rhs0 = (@a)[(int)((@_24783_j) - (1UL))];
          var _arr1 = @a;
          var _index1 = (@_24783_j) - (1UL);
          var _rhs1 = (@a)[(int)(@_24783_j)];
          _arr0[(int)_index0] = _rhs0;
          _arr1[(int)_index1] = _rhs1;
          @_24783_j = (@_24783_j) - (1UL);
        }
        @_24782_i = (@_24782_i) + (1UL);
      }
      { }
    }
  }
} // end of namespace _LiveRSL____COperationNumberSort__i_Compile
namespace @_LiveRSL____CLastCheckpointedMap__i_Compile {








  public partial class @__default {
    public static void @SeqToArray<@T>(Dafny.Sequence<@T> @s, out @T[] @a)
    {
      @a = (@T[])null;
    TAIL_CALL_START: ;
      @a = Dafny.Helpers.InitNewArray1<@T>((new BigInteger((@s).Length)));
      BigInteger @_24784_i = BigInteger.Zero;
      @_24784_i = new BigInteger(0);
      while ((@_24784_i) < (new BigInteger((@s).Length)))
      {
        (@a)[(int)(@_24784_i)] = (@s).Select(@_24784_i);
        @_24784_i = (@_24784_i) + (new BigInteger(1));
      }
    }
    public static void @ComputeNthHighestValue(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> @cm, ulong @n, out @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn)
    {
      @opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
    TAIL_CALL_START: ;
      @_LiveRSL____CTypes__i_Compile.@COperationNumber[] @_24785_a = (@_LiveRSL____CTypes__i_Compile.@COperationNumber[])null;
      @_LiveRSL____CTypes__i_Compile.@COperationNumber[] _out110;
      @_LiveRSL____CLastCheckpointedMap__i_Compile.@__default.@SeqToArray(@cm, out _out110);
      @_24785_a = _out110;
      { }
      @_LiveRSL____COperationNumberSort__i_Compile.@__default.@InsertionSortCOperationNumbers(@_24785_a);
      { }
      { }
      { }
      @opn = (@_24785_a)[(int)((new BigInteger((@_24785_a).@Length)) - (new BigInteger(@n)))];
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
  }
} // end of namespace _LiveRSL____CLastCheckpointedMap__i_Compile
namespace @_LiveRSL____AcceptorState__i_Compile {





  public abstract class Base_AcceptorState { }
  public partial class AcceptorState_AcceptorState : Base_AcceptorState {
    public readonly @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants;
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @maxBallot;
    public readonly @_LiveRSL____CTypes__i_Compile.@CVotes @votes;
    public readonly Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> @lastCheckpointedOperation;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @minVotedOpn;
    public AcceptorState_AcceptorState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, @_LiveRSL____CTypes__i_Compile.@CBallot @maxBallot, @_LiveRSL____CTypes__i_Compile.@CVotes @votes, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> @lastCheckpointedOperation, @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint, @_LiveRSL____CTypes__i_Compile.@COperationNumber @minVotedOpn) {
      this.@constants = @constants;
      this.@maxBallot = @maxBallot;
      this.@votes = @votes;
      this.@lastCheckpointedOperation = @lastCheckpointedOperation;
      this.@logTruncationPoint = @logTruncationPoint;
      this.@minVotedOpn = @minVotedOpn;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____AcceptorState__i_Compile.@AcceptorState_AcceptorState;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@maxBallot.Equals(oth.@maxBallot) && this.@votes.Equals(oth.@votes) && this.@lastCheckpointedOperation.Equals(oth.@lastCheckpointedOperation) && this.@logTruncationPoint.Equals(oth.@logTruncationPoint) && this.@minVotedOpn.Equals(oth.@minVotedOpn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBallot.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@votes.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@lastCheckpointedOperation.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@logTruncationPoint.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@minVotedOpn.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____AcceptorState__i_Compile.AcceptorState.AcceptorState";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @maxBallot.ToString();
      s += ", ";
      s += @votes.ToString();
      s += ", ";
      s += @lastCheckpointedOperation.ToString();
      s += ", ";
      s += @logTruncationPoint.ToString();
      s += ", ";
      s += @minVotedOpn.ToString();
      s += ")";
      return s;
    }
  }
  public struct @AcceptorState {
    Base_AcceptorState _d;
    public Base_AcceptorState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @AcceptorState(Base_AcceptorState d) { this._d = d; }
    static Base_AcceptorState theDefault;
    public static Base_AcceptorState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____AcceptorState__i_Compile.@AcceptorState_AcceptorState(new @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState(), new @_LiveRSL____CTypes__i_Compile.@CBallot(), new @_LiveRSL____CTypes__i_Compile.@CVotes(), Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber>.Empty, new @_LiveRSL____CTypes__i_Compile.@COperationNumber(), new @_LiveRSL____CTypes__i_Compile.@COperationNumber());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @AcceptorState && _D.Equals(((@AcceptorState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_AcceptorState { get { return _D is AcceptorState_AcceptorState; } }
    public @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState dtor_constants { get { return ((AcceptorState_AcceptorState)_D).@constants; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_maxBallot { get { return ((AcceptorState_AcceptorState)_D).@maxBallot; } }
    public @_LiveRSL____CTypes__i_Compile.@CVotes dtor_votes { get { return ((AcceptorState_AcceptorState)_D).@votes; } }
    public Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> dtor_lastCheckpointedOperation { get { return ((AcceptorState_AcceptorState)_D).@lastCheckpointedOperation; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_logTruncationPoint { get { return ((AcceptorState_AcceptorState)_D).@logTruncationPoint; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_minVotedOpn { get { return ((AcceptorState_AcceptorState)_D).@minVotedOpn; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____AcceptorState__i_Compile
namespace @_LiveRSL____ExecutorState__i_Compile {




  public abstract class Base_COutstandingOperation { }
  public partial class COutstandingOperation_COutstandingOpKnown : Base_COutstandingOperation {
    public readonly Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @v;
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @bal;
    public COutstandingOperation_COutstandingOpKnown(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @v, @_LiveRSL____CTypes__i_Compile.@CBallot @bal) {
      this.@v = @v;
      this.@bal = @bal;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation_COutstandingOpKnown;
      return oth != null && this.@v.Equals(oth.@v) && this.@bal.Equals(oth.@bal);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@v.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@bal.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ExecutorState__i_Compile.COutstandingOperation.COutstandingOpKnown";
      s += "(";
      s += @v.ToString();
      s += ", ";
      s += @bal.ToString();
      s += ")";
      return s;
    }
  }
  public partial class COutstandingOperation_COutstandingOpUnknown : Base_COutstandingOperation {
    public COutstandingOperation_COutstandingOpUnknown() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation_COutstandingOpUnknown;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ExecutorState__i_Compile.COutstandingOperation.COutstandingOpUnknown";
      return s;
    }
  }
  public struct @COutstandingOperation {
    Base_COutstandingOperation _d;
    public Base_COutstandingOperation _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @COutstandingOperation(Base_COutstandingOperation d) { this._d = d; }
    static Base_COutstandingOperation theDefault;
    public static Base_COutstandingOperation Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation_COutstandingOpKnown(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty, new @_LiveRSL____CTypes__i_Compile.@CBallot());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @COutstandingOperation && _D.Equals(((@COutstandingOperation)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_COutstandingOpKnown { get { return _D is COutstandingOperation_COutstandingOpKnown; } }
    public bool is_COutstandingOpUnknown { get { return _D is COutstandingOperation_COutstandingOpUnknown; } }
    public Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> dtor_v { get { return ((COutstandingOperation_COutstandingOpKnown)_D).@v; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_bal { get { return ((COutstandingOperation_COutstandingOpKnown)_D).@bal; } }
  }

  public abstract class Base_ExecutorState { }
  public partial class ExecutorState_ExecutorState : Base_ExecutorState {
    public readonly @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants;
    public readonly ulong @app;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @opsComplete;
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @maxBalReflected;
    public readonly @_LiveRSL____ExecutorState__i_Compile.@COutstandingOperation @nextOpToExecute;
    public readonly Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @replyCache;
    public ExecutorState_ExecutorState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, ulong @app, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opsComplete, @_LiveRSL____CTypes__i_Compile.@CBallot @maxBalReflected, @_LiveRSL____ExecutorState__i_Compile.@COutstandingOperation @nextOpToExecute, Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @replyCache) {
      this.@constants = @constants;
      this.@app = @app;
      this.@opsComplete = @opsComplete;
      this.@maxBalReflected = @maxBalReflected;
      this.@nextOpToExecute = @nextOpToExecute;
      this.@replyCache = @replyCache;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ExecutorState__i_Compile.@ExecutorState_ExecutorState;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@app.Equals(oth.@app) && this.@opsComplete.Equals(oth.@opsComplete) && this.@maxBalReflected.Equals(oth.@maxBalReflected) && this.@nextOpToExecute.Equals(oth.@nextOpToExecute) && this.@replyCache.Equals(oth.@replyCache);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@app.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opsComplete.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBalReflected.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@nextOpToExecute.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@replyCache.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ExecutorState__i_Compile.ExecutorState.ExecutorState";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @app.ToString();
      s += ", ";
      s += @opsComplete.ToString();
      s += ", ";
      s += @maxBalReflected.ToString();
      s += ", ";
      s += @nextOpToExecute.ToString();
      s += ", ";
      s += @replyCache.ToString();
      s += ")";
      return s;
    }
  }
  public struct @ExecutorState {
    Base_ExecutorState _d;
    public Base_ExecutorState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ExecutorState(Base_ExecutorState d) { this._d = d; }
    static Base_ExecutorState theDefault;
    public static Base_ExecutorState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____ExecutorState__i_Compile.@ExecutorState_ExecutorState(new @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState(), 0, new @_LiveRSL____CTypes__i_Compile.@COperationNumber(), new @_LiveRSL____CTypes__i_Compile.@CBallot(), new @_LiveRSL____ExecutorState__i_Compile.@COutstandingOperation(), Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ExecutorState && _D.Equals(((@ExecutorState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_ExecutorState { get { return _D is ExecutorState_ExecutorState; } }
    public @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState dtor_constants { get { return ((ExecutorState_ExecutorState)_D).@constants; } }
    public ulong dtor_app { get { return ((ExecutorState_ExecutorState)_D).@app; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_opsComplete { get { return ((ExecutorState_ExecutorState)_D).@opsComplete; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_maxBalReflected { get { return ((ExecutorState_ExecutorState)_D).@maxBalReflected; } }
    public @_LiveRSL____ExecutorState__i_Compile.@COutstandingOperation dtor_nextOpToExecute { get { return ((ExecutorState_ExecutorState)_D).@nextOpToExecute; } }
    public Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> dtor_replyCache { get { return ((ExecutorState_ExecutorState)_D).@replyCache; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____ExecutorState__i_Compile
namespace @_LiveRSL____LearnerState__i_Compile {




  public abstract class Base_CLearnerTuple { }
  public partial class CLearnerTuple_CLearnerTuple : Base_CLearnerTuple {
    public readonly Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @received2bMessageSenders;
    public readonly Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @candidateLearnedValue;
    public CLearnerTuple_CLearnerTuple(Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @received2bMessageSenders, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @candidateLearnedValue) {
      this.@received2bMessageSenders = @received2bMessageSenders;
      this.@candidateLearnedValue = @candidateLearnedValue;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____LearnerState__i_Compile.@CLearnerTuple_CLearnerTuple;
      return oth != null && this.@received2bMessageSenders.Equals(oth.@received2bMessageSenders) && this.@candidateLearnedValue.Equals(oth.@candidateLearnedValue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@received2bMessageSenders.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@candidateLearnedValue.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____LearnerState__i_Compile.CLearnerTuple.CLearnerTuple";
      s += "(";
      s += @received2bMessageSenders.ToString();
      s += ", ";
      s += @candidateLearnedValue.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CLearnerTuple {
    Base_CLearnerTuple _d;
    public Base_CLearnerTuple _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CLearnerTuple(Base_CLearnerTuple d) { this._d = d; }
    static Base_CLearnerTuple theDefault;
    public static Base_CLearnerTuple Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____LearnerState__i_Compile.@CLearnerTuple_CLearnerTuple(Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.Empty, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CLearnerTuple && _D.Equals(((@CLearnerTuple)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CLearnerTuple { get { return _D is CLearnerTuple_CLearnerTuple; } }
    public Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> dtor_received2bMessageSenders { get { return ((CLearnerTuple_CLearnerTuple)_D).@received2bMessageSenders; } }
    public Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> dtor_candidateLearnedValue { get { return ((CLearnerTuple_CLearnerTuple)_D).@candidateLearnedValue; } }
  }

  public abstract class Base_CLearnerState { }
  public partial class CLearnerState_CLearnerState : Base_CLearnerState {
    public readonly @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @rcs;
    public readonly @_LiveRSL____CTypes__i_Compile.@CBallot @maxBallotSeen;
    public readonly Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple> @unexecutedOps;
    public readonly bool @sendDecision;
    public readonly @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn;
    public readonly bool @recv2b;
    public readonly @_LiveRSL____CMessage__i_Compile.@CPacket @recvCp;
    public CLearnerState_CLearnerState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @rcs, @_LiveRSL____CTypes__i_Compile.@CBallot @maxBallotSeen, Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple> @unexecutedOps, bool @sendDecision, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn, bool @recv2b, @_LiveRSL____CMessage__i_Compile.@CPacket @recvCp) {
      this.@rcs = @rcs;
      this.@maxBallotSeen = @maxBallotSeen;
      this.@unexecutedOps = @unexecutedOps;
      this.@sendDecision = @sendDecision;
      this.@opn = @opn;
      this.@recv2b = @recv2b;
      this.@recvCp = @recvCp;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____LearnerState__i_Compile.@CLearnerState_CLearnerState;
      return oth != null && this.@rcs.Equals(oth.@rcs) && this.@maxBallotSeen.Equals(oth.@maxBallotSeen) && this.@unexecutedOps.Equals(oth.@unexecutedOps) && this.@sendDecision.Equals(oth.@sendDecision) && this.@opn.Equals(oth.@opn) && this.@recv2b.Equals(oth.@recv2b) && this.@recvCp.Equals(oth.@recvCp);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@rcs.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@maxBallotSeen.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@unexecutedOps.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@sendDecision.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@opn.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@recv2b.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@recvCp.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____LearnerState__i_Compile.CLearnerState.CLearnerState";
      s += "(";
      s += @rcs.ToString();
      s += ", ";
      s += @maxBallotSeen.ToString();
      s += ", ";
      s += @unexecutedOps.ToString();
      s += ", ";
      s += @sendDecision.ToString();
      s += ", ";
      s += @opn.ToString();
      s += ", ";
      s += @recv2b.ToString();
      s += ", ";
      s += @recvCp.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CLearnerState {
    Base_CLearnerState _d;
    public Base_CLearnerState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CLearnerState(Base_CLearnerState d) { this._d = d; }
    static Base_CLearnerState theDefault;
    public static Base_CLearnerState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____LearnerState__i_Compile.@CLearnerState_CLearnerState(new @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState(), new @_LiveRSL____CTypes__i_Compile.@CBallot(), Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>.Empty, false, new @_LiveRSL____CTypes__i_Compile.@COperationNumber(), false, new @_LiveRSL____CMessage__i_Compile.@CPacket());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CLearnerState && _D.Equals(((@CLearnerState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CLearnerState { get { return _D is CLearnerState_CLearnerState; } }
    public @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState dtor_rcs { get { return ((CLearnerState_CLearnerState)_D).@rcs; } }
    public @_LiveRSL____CTypes__i_Compile.@CBallot dtor_maxBallotSeen { get { return ((CLearnerState_CLearnerState)_D).@maxBallotSeen; } }
    public Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple> dtor_unexecutedOps { get { return ((CLearnerState_CLearnerState)_D).@unexecutedOps; } }
    public bool dtor_sendDecision { get { return ((CLearnerState_CLearnerState)_D).@sendDecision; } }
    public @_LiveRSL____CTypes__i_Compile.@COperationNumber dtor_opn { get { return ((CLearnerState_CLearnerState)_D).@opn; } }
    public bool dtor_recv2b { get { return ((CLearnerState_CLearnerState)_D).@recv2b; } }
    public @_LiveRSL____CMessage__i_Compile.@CPacket dtor_recvCp { get { return ((CLearnerState_CLearnerState)_D).@recvCp; } }
  }

  public partial class @__default {
    public static void @LearnerState__Init(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @rcs, out @_LiveRSL____LearnerState__i_Compile.@CLearnerState @learner)
    {
      @learner = new @_LiveRSL____LearnerState__i_Compile.@CLearnerState();
    TAIL_CALL_START: ;
      @_Native____Io__s_Compile.@EndPoint @_24786_endPoint = new @_Native____Io__s_Compile.@EndPoint();
      @_24786_endPoint = ((((@rcs).@dtor_all).@dtor_config).@dtor_replicaIds).Select((@rcs).@dtor_myIndex);
      @_LiveRSL____AppInterface__i_Compile.@CAppMessage @_24787_unknown = new @_LiveRSL____AppInterface__i_Compile.@CAppMessage();
      @learner = new _LiveRSL____LearnerState__i_Compile.@CLearnerState(new _LiveRSL____LearnerState__i_Compile.@CLearnerState_CLearnerState(@rcs, new _LiveRSL____CTypes__i_Compile.@CBallot(new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot(0UL, 0UL)), Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>.FromElements(), false, new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL)), false, new _LiveRSL____CMessage__i_Compile.@CPacket(new _LiveRSL____CMessage__i_Compile.@CPacket_CPacket(@_24786_endPoint, @_24786_endPoint, new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__2b(new _LiveRSL____CTypes__i_Compile.@CBallot(new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot(0UL, 0UL)), new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL)), Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements()))))));
      { }
      { }
    }
  }
} // end of namespace _LiveRSL____LearnerState__i_Compile
namespace @_LiveRSL____CBoundedClock__i_Compile {



  public abstract class Base_CBoundedClock { }
  public partial class CBoundedClock_CBoundedClock : Base_CBoundedClock {
    public readonly ulong @min;
    public readonly ulong @max;
    public CBoundedClock_CBoundedClock(ulong @min, ulong @max) {
      this.@min = @min;
      this.@max = @max;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____CBoundedClock__i_Compile.@CBoundedClock_CBoundedClock;
      return oth != null && this.@min.Equals(oth.@min) && this.@max.Equals(oth.@max);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@min.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@max.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____CBoundedClock__i_Compile.CBoundedClock.CBoundedClock";
      s += "(";
      s += @min.ToString();
      s += ", ";
      s += @max.ToString();
      s += ")";
      return s;
    }
  }
  public struct @CBoundedClock {
    Base_CBoundedClock _d;
    public Base_CBoundedClock _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @CBoundedClock(Base_CBoundedClock d) { this._d = d; }
    static Base_CBoundedClock theDefault;
    public static Base_CBoundedClock Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____CBoundedClock__i_Compile.@CBoundedClock_CBoundedClock(0, 0);
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @CBoundedClock && _D.Equals(((@CBoundedClock)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_CBoundedClock { get { return _D is CBoundedClock_CBoundedClock; } }
    public ulong dtor_min { get { return ((CBoundedClock_CBoundedClock)_D).@min; } }
    public ulong dtor_max { get { return ((CBoundedClock_CBoundedClock)_D).@max; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____CBoundedClock__i_Compile
namespace @_LiveRSL____ReplicaState__i_Compile {








  public abstract class Base_ReplicaState { }
  public partial class ReplicaState_ReplicaState : Base_ReplicaState {
    public readonly @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants;
    public readonly ulong @__nextActionIndex;
    public readonly ulong @nextHeartbeatTime;
    public readonly @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer;
    public readonly @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor;
    public readonly @_LiveRSL____LearnerState__i_Compile.@CLearnerState @learner;
    public readonly @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @executor;
    public ReplicaState_ReplicaState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, ulong @__nextActionIndex, ulong @nextHeartbeatTime, @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor, @_LiveRSL____LearnerState__i_Compile.@CLearnerState @learner, @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @executor) {
      this.@constants = @constants;
      this.@__nextActionIndex = @__nextActionIndex;
      this.@nextHeartbeatTime = @nextHeartbeatTime;
      this.@proposer = @proposer;
      this.@acceptor = @acceptor;
      this.@learner = @learner;
      this.@executor = @executor;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState;
      return oth != null && this.@constants.Equals(oth.@constants) && this.@__nextActionIndex.Equals(oth.@__nextActionIndex) && this.@nextHeartbeatTime.Equals(oth.@nextHeartbeatTime) && this.@proposer.Equals(oth.@proposer) && this.@acceptor.Equals(oth.@acceptor) && this.@learner.Equals(oth.@learner) && this.@executor.Equals(oth.@executor);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@constants.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@__nextActionIndex.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@nextHeartbeatTime.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@proposer.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@acceptor.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@learner.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@executor.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____ReplicaState__i_Compile.ReplicaState.ReplicaState";
      s += "(";
      s += @constants.ToString();
      s += ", ";
      s += @__nextActionIndex.ToString();
      s += ", ";
      s += @nextHeartbeatTime.ToString();
      s += ", ";
      s += @proposer.ToString();
      s += ", ";
      s += @acceptor.ToString();
      s += ", ";
      s += @learner.ToString();
      s += ", ";
      s += @executor.ToString();
      s += ")";
      return s;
    }
  }
  public struct @ReplicaState {
    Base_ReplicaState _d;
    public Base_ReplicaState _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ReplicaState(Base_ReplicaState d) { this._d = d; }
    static Base_ReplicaState theDefault;
    public static Base_ReplicaState Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState(new @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState(), 0, 0, new @_LiveRSL____ProposerState__i_Compile.@ProposerState(), new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState(), new @_LiveRSL____LearnerState__i_Compile.@CLearnerState(), new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState());
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ReplicaState && _D.Equals(((@ReplicaState)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_ReplicaState { get { return _D is ReplicaState_ReplicaState; } }
    public @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState dtor_constants { get { return ((ReplicaState_ReplicaState)_D).@constants; } }
    public ulong dtor___nextActionIndex { get { return ((ReplicaState_ReplicaState)_D).@__nextActionIndex; } }
    public ulong dtor_nextHeartbeatTime { get { return ((ReplicaState_ReplicaState)_D).@nextHeartbeatTime; } }
    public @_LiveRSL____ProposerState__i_Compile.@ProposerState dtor_proposer { get { return ((ReplicaState_ReplicaState)_D).@proposer; } }
    public @_LiveRSL____AcceptorState__i_Compile.@AcceptorState dtor_acceptor { get { return ((ReplicaState_ReplicaState)_D).@acceptor; } }
    public @_LiveRSL____LearnerState__i_Compile.@CLearnerState dtor_learner { get { return ((ReplicaState_ReplicaState)_D).@learner; } }
    public @_LiveRSL____ExecutorState__i_Compile.@ExecutorState dtor_executor { get { return ((ReplicaState_ReplicaState)_D).@executor; } }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____ReplicaState__i_Compile
namespace @_LiveRSL____MinCQuorumSize__i_Compile {




  public partial class @__default {
    public static void @MinCQuorumSize(@_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config, out ulong @quorumSize)
    {
      @quorumSize = 0;
    TAIL_CALL_START: ;
      { }
      @quorumSize = (ulong)((Dafny.Helpers.EuclideanDivision((new BigInteger(((@config).@dtor_replicaIds).Length)), new BigInteger(2))) + (new BigInteger(1)));
      { }
      { }
      { }
      { }
      { }
    }
  }
} // end of namespace _LiveRSL____MinCQuorumSize__i_Compile
namespace @_LiveRSL____ElectionModel__i_Compile {




  public partial class @__default {
    public static ulong @ConvertEndPointToUint64Refine(@_Native____Io__s_Compile.@EndPoint @ep) {
      return @_Common____NodeIdentity__i_Compile.@__default.@ConvertEndPointToUint64(@ep);
    }
    public static void @CComputeSuccessorView(@_LiveRSL____CTypes__i_Compile.@CBallot @cb, @_LiveRSL____ConstantsState__i_Compile.@ConstantsState @constants, out @_LiveRSL____CTypes__i_Compile.@CBallot @cb_k)
    {
      @cb_k = new @_LiveRSL____CTypes__i_Compile.@CBallot();
    TAIL_CALL_START: ;
      { }
      if ((((@cb).@dtor_proposerId) + (1UL)) < ((ulong)(((@constants).@dtor_config).@dtor_replicaIds).LongLength))
      {
        @cb_k = new _LiveRSL____CTypes__i_Compile.@CBallot(new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot((@cb).@dtor_seqno, ((@cb).@dtor_proposerId) + (1UL)));
      }
      else
      {
        @cb_k = new _LiveRSL____CTypes__i_Compile.@CBallot(new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot(@_LiveRSL____ParametersState__i_Compile.@__default.@CCappedAddition((@cb).@dtor_seqno, 1UL, (@constants).@dtor_params), 0UL));
      }
    }
    public static Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @BoundCRequestSequence(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @s, @_LiveRSL____ConstantsState__i_Compile.@ConstantsState @c) {
      if (((new BigInteger(0)) <= (new BigInteger(((@c).@dtor_params).@dtor_maxIntegerVal))) && ((new BigInteger(((@c).@dtor_params).@dtor_maxIntegerVal)) < (new BigInteger((@s).Length)))) {
        return (@s).Take(((@c).@dtor_params).@dtor_maxIntegerVal);
      } else {
        return @s;
      }
    }
    public static bool @CRequestsMatch(@_LiveRSL____CTypes__i_Compile.@CRequest @r1, @_LiveRSL____CTypes__i_Compile.@CRequest @r2) {
      return ((((@r1).@is_CRequest) && ((@r2).@is_CRequest)) && (((@r1).@dtor_client).@Equals((@r2).@dtor_client))) && (((@r1).@dtor_seqno).@Equals((@r2).@dtor_seqno));
    }
    public static Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @RemoveFirstMatchingCRequestInSequence(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @s, @_LiveRSL____CTypes__i_Compile.@CRequest @r) {
      if ((new BigInteger((@s).Length)).@Equals(new BigInteger(0))) {
        return Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements();
      } else {
        if (@_LiveRSL____ElectionModel__i_Compile.@__default.@CRequestsMatch((@s).Select(new BigInteger(0)), @r)) {
          return (@s).Drop(new BigInteger(1));
        } else {
          return (Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements((@s).Select(new BigInteger(0)))).@Concat(@_LiveRSL____ElectionModel__i_Compile.@__default.@RemoveFirstMatchingCRequestInSequence((@s).Drop(new BigInteger(1)), @r));
        }
      }
    }
    public static void @InitElectionState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, out @_LiveRSL____ElectionState__i_Compile.@CElectionState @election)
    {
      @election = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
    TAIL_CALL_START: ;
      @election = new _LiveRSL____ElectionState__i_Compile.@CElectionState(new _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState(@constants, new _LiveRSL____CTypes__i_Compile.@CBallot(new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot(1UL, 0UL)), Dafny.Sequence<ulong>.FromElements(), 0UL, (((@constants).@dtor_all).@dtor_params).@dtor_baselineViewTimeoutPeriod, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements(), Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements()));
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @ElectionProcessHeartbeat(@_LiveRSL____ElectionState__i_Compile.@CElectionState @ces, @_LiveRSL____CMessage__i_Compile.@CPacket @cp, ulong @clock__min, ulong @clock__max, out @_LiveRSL____ElectionState__i_Compile.@CElectionState @ces_k)
    {
      @ces_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
    TAIL_CALL_START: ;
      @_Native____Io__s_Compile.@EndPoint @_24788_src__ep = new @_Native____Io__s_Compile.@EndPoint();
      @_24788_src__ep = (@cp).@dtor_src;
      bool @_24789_found = false;
      ulong @_24790_index = 0;
      bool _out111;
      ulong _out112;
      @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@__default.@CGetReplicaIndex(@_24788_src__ep, (((@ces).@dtor_constants).@dtor_all).@dtor_config, out _out111, out _out112);
      @_24789_found = _out111;
      @_24790_index = _out112;
      { }
      { }
      { }
      { }
      if (!(@_24789_found))
      {
        { }
        @ces_k = @ces;
      }
      else
      {
        { }
        { }
        if (((((@cp).@dtor_msg).@dtor_bal__heartbeat).@Equals((@ces).@dtor_currentView)) && (((@cp).@dtor_msg).@dtor_suspicious))
        {
          { }
          @ces_k = Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(@ces, _pat_let1_0 => Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(_pat_let1_0, @_24791_dt__update__tmp_h1 => new _LiveRSL____ElectionState__i_Compile.@CElectionState(new _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState((@_24791_dt__update__tmp_h1).@dtor_constants, (@_24791_dt__update__tmp_h1).@dtor_currentView, @_Common____SeqIsUnique__i_Compile.@__default.@AppendToUniqueSeqMaybe<ulong>((@ces).@dtor_currentViewSuspectors, @_24790_index), (@_24791_dt__update__tmp_h1).@dtor_epochEndTime, (@_24791_dt__update__tmp_h1).@dtor_epochLength, (@_24791_dt__update__tmp_h1).@dtor_requestsReceivedThisEpoch, (@_24791_dt__update__tmp_h1).@dtor_requestsReceivedPrevEpochs))));
          { }
          { }
        }
        else
        {
          bool @_24792_cmp = false;
          bool _out113;
          @_LiveRSL____CTypes__i_Compile.@__default.@CBalLt((@ces).@dtor_currentView, ((@cp).@dtor_msg).@dtor_bal__heartbeat, out _out113);
          @_24792_cmp = _out113;
          if (@_24792_cmp)
          {
            { }
            { }
            ulong @_24793_cnewEpochLength = 0;
            @_24793_cnewEpochLength = @_LiveRSL____ParametersState__i_Compile.@__default.@CCappedAddition((@ces).@dtor_epochLength, (@ces).@dtor_epochLength, (((@ces).@dtor_constants).@dtor_all).@dtor_params);
            @ces_k = Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(@ces, _pat_let2_0 => Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(_pat_let2_0, @_24794_dt__update__tmp_h13 => new _LiveRSL____ElectionState__i_Compile.@CElectionState(new _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState((@_24794_dt__update__tmp_h13).@dtor_constants, ((@cp).@dtor_msg).@dtor_bal__heartbeat, (((@cp).@dtor_msg).@dtor_suspicious) ? (Dafny.Sequence<ulong>.FromElements(@_24790_index)) : (Dafny.Sequence<ulong>.FromElements()), @_LiveRSL____ParametersState__i_Compile.@__default.@CCappedAddition(@clock__max, @_24793_cnewEpochLength, (((@ces).@dtor_constants).@dtor_all).@dtor_params), @_24793_cnewEpochLength, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements(), @_LiveRSL____ElectionModel__i_Compile.@__default.@BoundCRequestSequence(((@ces).@dtor_requestsReceivedPrevEpochs).@Concat((@ces).@dtor_requestsReceivedThisEpoch), ((@ces).@dtor_constants).@dtor_all)))));
            { }
            { }
            { }
            { }
            { }
          }
          else
          {
            { }
            @ces_k = @ces;
          }
        }
        { }
      }
      { }
    }
    public static void @ElectionCheckForViewTimeout(@_LiveRSL____ElectionState__i_Compile.@CElectionState @ces, ulong @clock__min, ulong @clock__max, out @_LiveRSL____ElectionState__i_Compile.@CElectionState @ces_k)
    {
      @ces_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
    TAIL_CALL_START: ;
      ulong @_24795_start__time = 0;
      ulong _out114;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out114);
      @_24795_start__time = _out114;
      { }
      { }
      { }
      if ((@clock__min) < ((@ces).@dtor_epochEndTime))
      {
        { }
        @ces_k = @ces;
        ulong @_24796_end__time = 0;
        ulong _out115;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out115);
        @_24796_end__time = _out115;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ElectionCheckForViewTimeout_nada"), @_24795_start__time, @_24796_end__time);
        { }
      }
      else
      if ((new BigInteger(((@ces).@dtor_requestsReceivedPrevEpochs).Length)).@Equals(new BigInteger(0)))
      {
        { }
        { }
        ulong @_24797_cnewEpochLength = 0;
        @_24797_cnewEpochLength = ((((@ces).@dtor_constants).@dtor_all).@dtor_params).@dtor_baselineViewTimeoutPeriod;
        @ces_k = Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(@ces, _pat_let3_0 => Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(_pat_let3_0, @_24798_dt__update__tmp_h7 => new _LiveRSL____ElectionState__i_Compile.@CElectionState(new _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState((@_24798_dt__update__tmp_h7).@dtor_constants, (@_24798_dt__update__tmp_h7).@dtor_currentView, (@_24798_dt__update__tmp_h7).@dtor_currentViewSuspectors, @_LiveRSL____ParametersState__i_Compile.@__default.@CCappedAddition(@clock__max, @_24797_cnewEpochLength, (((@ces).@dtor_constants).@dtor_all).@dtor_params), @_24797_cnewEpochLength, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements(), (@ces).@dtor_requestsReceivedThisEpoch))));
        { }
        ulong @_24799_end__time = 0;
        ulong _out116;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out116);
        @_24799_end__time = _out116;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ElectionCheckForViewTimeout_noprev"), @_24795_start__time, @_24799_end__time);
      }
      else
      {
        { }
        { }
        ulong @_24800_cnewEpochLength = 0;
        @_24800_cnewEpochLength = @_LiveRSL____ParametersState__i_Compile.@__default.@CCappedAddition((@ces).@dtor_epochLength, (@ces).@dtor_epochLength, (((@ces).@dtor_constants).@dtor_all).@dtor_params);
        @ces_k = Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(@ces, _pat_let4_0 => Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(_pat_let4_0, @_24801_dt__update__tmp_h17 => new _LiveRSL____ElectionState__i_Compile.@CElectionState(new _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState((@_24801_dt__update__tmp_h17).@dtor_constants, (@_24801_dt__update__tmp_h17).@dtor_currentView, @_Common____SeqIsUnique__i_Compile.@__default.@AppendToUniqueSeqMaybe<ulong>((@ces).@dtor_currentViewSuspectors, ((@ces).@dtor_constants).@dtor_myIndex), @_LiveRSL____ParametersState__i_Compile.@__default.@CCappedAddition(@clock__max, @_24800_cnewEpochLength, (((@ces).@dtor_constants).@dtor_all).@dtor_params), @_24800_cnewEpochLength, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements(), @_LiveRSL____ElectionModel__i_Compile.@__default.@BoundCRequestSequence(((@ces).@dtor_requestsReceivedPrevEpochs).@Concat((@ces).@dtor_requestsReceivedThisEpoch), ((@ces).@dtor_constants).@dtor_all)))));
        { }
        { }
        { }
        { }
        ulong @_24802_end__time = 0;
        ulong _out117;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out117);
        @_24802_end__time = _out117;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ElectionCheckForViewTimeout_timeout"), @_24795_start__time, @_24802_end__time);
      }
      { }
    }
    public static void @ElectionCheckForQuorumOfViewSuspicions(@_LiveRSL____ElectionState__i_Compile.@CElectionState @ces, ulong @clock__min, ulong @clock__max, out @_LiveRSL____ElectionState__i_Compile.@CElectionState @ces_k)
    {
      @ces_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
    TAIL_CALL_START: ;
      { }
      { }
      { }
      { }
      { }
      ulong @_24803_minq = 0;
      ulong _out118;
      @_LiveRSL____MinCQuorumSize__i_Compile.@__default.@MinCQuorumSize((((@ces).@dtor_constants).@dtor_all).@dtor_config, out _out118);
      @_24803_minq = _out118;
      if ((new BigInteger(((@ces).@dtor_currentViewSuspectors).Length)) < (new BigInteger(@_24803_minq)))
      {
        { }
        @ces_k = @ces;
      }
      else
      {
        { }
        { }
        @_LiveRSL____CTypes__i_Compile.@CBallot @_24804_cview = new @_LiveRSL____CTypes__i_Compile.@CBallot();
        @_LiveRSL____CTypes__i_Compile.@CBallot _out119;
        @_LiveRSL____ElectionModel__i_Compile.@__default.@CComputeSuccessorView((@ces).@dtor_currentView, ((@ces).@dtor_constants).@dtor_all, out _out119);
        @_24804_cview = _out119;
        ulong @_24805_cnewEpochLength = 0;
        @_24805_cnewEpochLength = @_LiveRSL____ParametersState__i_Compile.@__default.@CCappedAddition((@ces).@dtor_epochLength, (@ces).@dtor_epochLength, (((@ces).@dtor_constants).@dtor_all).@dtor_params);
        @ces_k = Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(@ces, _pat_let5_0 => Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(_pat_let5_0, @_24806_dt__update__tmp_h11 => new _LiveRSL____ElectionState__i_Compile.@CElectionState(new _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState((@_24806_dt__update__tmp_h11).@dtor_constants, @_24804_cview, Dafny.Sequence<ulong>.FromElements(), @_LiveRSL____ParametersState__i_Compile.@__default.@CCappedAddition(@clock__max, @_24805_cnewEpochLength, (((@ces).@dtor_constants).@dtor_all).@dtor_params), @_24805_cnewEpochLength, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements(), @_LiveRSL____ElectionModel__i_Compile.@__default.@BoundCRequestSequence(((@ces).@dtor_requestsReceivedPrevEpochs).@Concat((@ces).@dtor_requestsReceivedThisEpoch), ((@ces).@dtor_constants).@dtor_all)))));
        { }
        { }
      }
      { }
      { }
      { }
    }
    public static void @FindEarlierRequest(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @r1, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @r2, @_LiveRSL____CTypes__i_Compile.@CRequest @target, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      { }
      ulong @_24807_i = 0;
      @_24807_i = 0UL;
      while ((@_24807_i) < ((ulong)(@r1).LongLength))
      {
        if (@_LiveRSL____ElectionModel__i_Compile.@__default.@CRequestsMatch((@r1).Select(@_24807_i), @target))
        {
          @b = true;
          return;
        }
        @_24807_i = (@_24807_i) + (1UL);
      }
      @_24807_i = 0UL;
      while ((@_24807_i) < ((ulong)(@r2).LongLength))
      {
        if (@_LiveRSL____ElectionModel__i_Compile.@__default.@CRequestsMatch((@r2).Select(@_24807_i), @target))
        {
          @b = true;
          return;
        }
        @_24807_i = (@_24807_i) + (1UL);
      }
      @b = false;
    }
    public static void @ElectionReflectReceivedRequest(@_LiveRSL____ElectionState__i_Compile.@CElectionState @ces, @_LiveRSL____CTypes__i_Compile.@CRequest @creq, out @_LiveRSL____ElectionState__i_Compile.@CElectionState @ces_k)
    {
      @ces_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
    TAIL_CALL_START: ;
      { }
      { }
      { }
      bool @_24808_earlier = false;
      bool _out120;
      @_LiveRSL____ElectionModel__i_Compile.@__default.@FindEarlierRequest((@ces).@dtor_requestsReceivedThisEpoch, (@ces).@dtor_requestsReceivedPrevEpochs, @creq, out _out120);
      @_24808_earlier = _out120;
      if (@_24808_earlier)
      {
        { }
        @ces_k = @ces;
      }
      else
      {
        { }
        @ces_k = Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(@ces, _pat_let6_0 => Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(_pat_let6_0, @_24809_dt__update__tmp_h1 => new _LiveRSL____ElectionState__i_Compile.@CElectionState(new _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState((@_24809_dt__update__tmp_h1).@dtor_constants, (@_24809_dt__update__tmp_h1).@dtor_currentView, (@_24809_dt__update__tmp_h1).@dtor_currentViewSuspectors, (@_24809_dt__update__tmp_h1).@dtor_epochEndTime, (@_24809_dt__update__tmp_h1).@dtor_epochLength, @_LiveRSL____ElectionModel__i_Compile.@__default.@BoundCRequestSequence(((@ces).@dtor_requestsReceivedThisEpoch).@Concat(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements(@creq)), ((@ces).@dtor_constants).@dtor_all), (@_24809_dt__update__tmp_h1).@dtor_requestsReceivedPrevEpochs))));
        { }
        { }
        { }
      }
    }
    public static void @ElectionReflectExecutedRequestBatch(@_LiveRSL____ElectionState__i_Compile.@CElectionState @ces, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @creqb, out @_LiveRSL____ElectionState__i_Compile.@CElectionState @ces_k)
    {
      @ces_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
    TAIL_CALL_START: ;
      { }
      BigInteger @_24810_i = BigInteger.Zero;
      @_24810_i = new BigInteger(0);
      { }
      @_LiveRSL____ElectionState__i_Compile.@CElectionState @_24811_tempces_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
      @_24811_tempces_k = @ces;
      while ((@_24810_i) < (new BigInteger((@creqb).Length)))
      {
        @_LiveRSL____CTypes__i_Compile.@CRequest @_24812_creq = new @_LiveRSL____CTypes__i_Compile.@CRequest();
        @_24812_creq = (@creqb).Select(@_24810_i);
        { }
        { }
        { }
        { }
        { }
        { }
        @_24811_tempces_k = Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(@_24811_tempces_k, _pat_let7_0 => Dafny.Helpers.Let<@_LiveRSL____ElectionState__i_Compile.@CElectionState,@_LiveRSL____ElectionState__i_Compile.@CElectionState>(_pat_let7_0, @_24813_dt__update__tmp_h3 => new _LiveRSL____ElectionState__i_Compile.@CElectionState(new _LiveRSL____ElectionState__i_Compile.@CElectionState_CElectionState((@_24813_dt__update__tmp_h3).@dtor_constants, (@_24813_dt__update__tmp_h3).@dtor_currentView, (@_24813_dt__update__tmp_h3).@dtor_currentViewSuspectors, (@_24813_dt__update__tmp_h3).@dtor_epochEndTime, (@_24813_dt__update__tmp_h3).@dtor_epochLength, @_LiveRSL____ElectionModel__i_Compile.@__default.@RemoveFirstMatchingCRequestInSequence((@_24811_tempces_k).@dtor_requestsReceivedThisEpoch, @_24812_creq), @_LiveRSL____ElectionModel__i_Compile.@__default.@RemoveFirstMatchingCRequestInSequence((@_24811_tempces_k).@dtor_requestsReceivedPrevEpochs, @_24812_creq)))));
        { }
        { }
        { }
        { }
        @_24810_i = (@_24810_i) + (new BigInteger(1));
      }
      { }
      @ces_k = @_24811_tempces_k;
    }
  }
} // end of namespace _LiveRSL____ElectionModel__i_Compile
namespace @_Impl____LiveRSL____Broadcast__i_Compile {



  public partial class @__default {
    public static void @BuildBroadcastToEveryone(@_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config, ulong @myIndex, @_LiveRSL____CMessage__i_Compile.@CMessage @msg, out @_LiveRSL____CMessage__i_Compile.@CBroadcast @broadcast)
    {
      @broadcast = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
    TAIL_CALL_START: ;
      @broadcast = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcast(((@config).@dtor_replicaIds).Select(@myIndex), (@config).@dtor_replicaIds, @msg));
    }
  }
} // end of namespace _Impl____LiveRSL____Broadcast__i_Compile
namespace @_LiveRSL____ProposerLemmas__i_Compile {


  public partial class @__default {
  }
} // end of namespace _LiveRSL____ProposerLemmas__i_Compile
namespace @_LiveRSL____ProposerModel__i_Compile {








  public partial class @__default {
    public static void @InitProposerState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer)
    {
      @proposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
    TAIL_CALL_START: ;
      @_LiveRSL____ElectionState__i_Compile.@CElectionState @_24814_election = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
      @_LiveRSL____ElectionState__i_Compile.@CElectionState _out121;
      @_LiveRSL____ElectionModel__i_Compile.@__default.@InitElectionState(@constants, out _out121);
      @_24814_election = _out121;
      @proposer = new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState(@constants, 0, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements(), new _LiveRSL____CTypes__i_Compile.@CBallot(new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot(0UL, (@constants).@dtor_myIndex)), 0UL, Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(), Dafny.Map<@_Native____Io__s_Compile.@EndPoint,ulong>.FromElements(), new _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer(new _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer_CIncompleteBatchTimerOff()), @_24814_election, new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL)), new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL))));
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @ProposerProcessRequest(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, @_LiveRSL____CMessage__i_Compile.@CPacket @packet, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
    TAIL_CALL_START: ;
      ulong @_24815_start__time = 0;
      ulong _out122;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out122);
      @_24815_start__time = _out122;
      { }
      { }
      { }
      @_LiveRSL____CTypes__i_Compile.@CRequest @_24816_val = new @_LiveRSL____CTypes__i_Compile.@CRequest();
      @_24816_val = new _LiveRSL____CTypes__i_Compile.@CRequest(new _LiveRSL____CTypes__i_Compile.@CRequest_CRequest((@packet).@dtor_src, ((@packet).@dtor_msg).@dtor_seqno, ((@packet).@dtor_msg).@dtor_val));
      @_LiveRSL____ElectionState__i_Compile.@CElectionState @_24817_newElectionState = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
      @_LiveRSL____ElectionState__i_Compile.@CElectionState _out123;
      @_LiveRSL____ElectionModel__i_Compile.@__default.@ElectionReflectReceivedRequest((@proposer).@dtor_electionState, @_24816_val, out _out123);
      @_24817_newElectionState = _out123;
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      if ((!((@proposer).@dtor_currentState).@Equals(0)) && ((!((@proposer).@dtor_highestSeqnoRequestedByClientThisView).Contains((@packet).@dtor_src)) || ((((@packet).@dtor_msg).@dtor_seqno) > (((@proposer).@dtor_highestSeqnoRequestedByClientThisView).Select((@packet).@dtor_src)))))
      {
        { }
        Dafny.Map<@_Native____Io__s_Compile.@EndPoint,ulong> @_24818_new__seqno__map = Dafny.Map<@_Native____Io__s_Compile.@EndPoint,ulong>.Empty;
        @_24818_new__seqno__map = ((@proposer).@dtor_highestSeqnoRequestedByClientThisView).Update((@packet).@dtor_src, ((@packet).@dtor_msg).@dtor_seqno);
        @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let8_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let8_0, @_24819_dt__update__tmp_h3 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24819_dt__update__tmp_h3).@dtor_constants, (@_24819_dt__update__tmp_h3).@dtor_currentState, ((@proposer).@dtor_requestQueue).@Concat(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements(@_24816_val)), (@_24819_dt__update__tmp_h3).@dtor_maxBallotISent1a, (@_24819_dt__update__tmp_h3).@dtor_nextOperationNumberToPropose, (@_24819_dt__update__tmp_h3).@dtor_received1bPackets, @_24818_new__seqno__map, (@_24819_dt__update__tmp_h3).@dtor_incompleteBatchTimer, @_24817_newElectionState, (@_24819_dt__update__tmp_h3).@dtor_maxOpnWithProposal, (@_24819_dt__update__tmp_h3).@dtor_maxLogTruncationPoint))));
        { }
        { }
        { }
        { }
        { }
      }
      else
      {
        @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let9_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let9_0, @_24820_dt__update__tmp_h9 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24820_dt__update__tmp_h9).@dtor_constants, (@_24820_dt__update__tmp_h9).@dtor_currentState, (@_24820_dt__update__tmp_h9).@dtor_requestQueue, (@_24820_dt__update__tmp_h9).@dtor_maxBallotISent1a, (@_24820_dt__update__tmp_h9).@dtor_nextOperationNumberToPropose, (@_24820_dt__update__tmp_h9).@dtor_received1bPackets, (@_24820_dt__update__tmp_h9).@dtor_highestSeqnoRequestedByClientThisView, (@_24820_dt__update__tmp_h9).@dtor_incompleteBatchTimer, @_24817_newElectionState, (@_24820_dt__update__tmp_h9).@dtor_maxOpnWithProposal, (@_24820_dt__update__tmp_h9).@dtor_maxLogTruncationPoint))));
        { }
        { }
        { }
        { }
      }
    }
    public static void @ProposerMaybeEnterNewViewAndSend1a(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k, out @_LiveRSL____CMessage__i_Compile.@CBroadcast @sent__packets)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
    TAIL_CALL_START: ;
      ulong @_24821_start__time = 0;
      ulong _out124;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out124);
      @_24821_start__time = _out124;
      { }
      bool @_24822_lt = false;
      bool _out125;
      @_LiveRSL____CTypes__i_Compile.@__default.@CBalLt((@proposer).@dtor_maxBallotISent1a, ((@proposer).@dtor_electionState).@dtor_currentView, out _out125);
      @_24822_lt = _out125;
      if ((((((@proposer).@dtor_electionState).@dtor_currentView).@dtor_proposerId).@Equals(((@proposer).@dtor_constants).@dtor_myIndex)) && (@_24822_lt))
      {
        { }
        { }
        { }
        Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_24823_new__requestQueue = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
        @_24823_new__requestQueue = (((@proposer).@dtor_electionState).@dtor_requestsReceivedPrevEpochs).@Concat(((@proposer).@dtor_electionState).@dtor_requestsReceivedThisEpoch);
        { }
        @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let10_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let10_0, @_24824_dt__update__tmp_h5 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24824_dt__update__tmp_h5).@dtor_constants, 1, @_24823_new__requestQueue, ((@proposer).@dtor_electionState).@dtor_currentView, (@_24824_dt__update__tmp_h5).@dtor_nextOperationNumberToPropose, Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(), Dafny.Map<@_Native____Io__s_Compile.@EndPoint,ulong>.FromElements(), (@_24824_dt__update__tmp_h5).@dtor_incompleteBatchTimer, (@_24824_dt__update__tmp_h5).@dtor_electionState, (@_24824_dt__update__tmp_h5).@dtor_maxOpnWithProposal, (@_24824_dt__update__tmp_h5).@dtor_maxLogTruncationPoint))));
        @_LiveRSL____CMessage__i_Compile.@CMessage @_24825_msg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
        @_24825_msg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__1a(((@proposer).@dtor_electionState).@dtor_currentView));
        { }
        { }
        @_LiveRSL____CMessage__i_Compile.@CBroadcast _out126;
        @_Impl____LiveRSL____Broadcast__i_Compile.@__default.@BuildBroadcastToEveryone((((@proposer).@dtor_constants).@dtor_all).@dtor_config, ((@proposer).@dtor_constants).@dtor_myIndex, @_24825_msg, out _out126);
        @sent__packets = _out126;
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        ulong @_24826_end__time = 0;
        ulong _out127;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out127);
        @_24826_end__time = _out127;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerMaybeEnterNewViewAndSend1a_work"), @_24821_start__time, @_24826_end__time);
      }
      else
      {
        @proposer_k = @proposer;
        @sent__packets = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop());
        ulong @_24827_end__time = 0;
        ulong _out128;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out128);
        @_24827_end__time = _out128;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerMaybeEnterNewViewAndSend1a_nada"), @_24821_start__time, @_24827_end__time);
      }
    }
    public static void @ProposerProcess1b(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, @_LiveRSL____CMessage__i_Compile.@CPacket @packet, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
    TAIL_CALL_START: ;
      @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let11_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let11_0, @_24828_dt__update__tmp_h0 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24828_dt__update__tmp_h0).@dtor_constants, (@_24828_dt__update__tmp_h0).@dtor_currentState, (@_24828_dt__update__tmp_h0).@dtor_requestQueue, (@_24828_dt__update__tmp_h0).@dtor_maxBallotISent1a, (@_24828_dt__update__tmp_h0).@dtor_nextOperationNumberToPropose, ((@proposer).@dtor_received1bPackets).@Union(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(@packet)), (@_24828_dt__update__tmp_h0).@dtor_highestSeqnoRequestedByClientThisView, (@_24828_dt__update__tmp_h0).@dtor_incompleteBatchTimer, (@_24828_dt__update__tmp_h0).@dtor_electionState, (@_24828_dt__update__tmp_h0).@dtor_maxOpnWithProposal, (@_24828_dt__update__tmp_h0).@dtor_maxLogTruncationPoint))));
      { }
      { }
      { }
      { }
      { }
    }
    public static void @getMaxOpnWithProposalFromSingleton(Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> @m, out @_LiveRSL____CTypes__i_Compile.@COperationNumber @maxOpn)
    {
      @maxOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      if ((new BigInteger((@m).Length)).@Equals(new BigInteger(1)))
      {
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24829_opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        foreach (var _assign_such_that_3 in (@m).Domain) { @_24829_opn = _assign_such_that_3;
          if ((@m).Contains(@_24829_opn)) {
            goto _ASSIGN_SUCH_THAT_3;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 16034)");
        _ASSIGN_SUCH_THAT_3: ;
        { }
        { }
        @maxOpn = @_24829_opn;
      }
      else
      {
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24830_opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        foreach (var _assign_such_that_4 in (@m).Domain) { @_24830_opn = _assign_such_that_4;
          if ((@m).Contains(@_24830_opn)) {
            goto _ASSIGN_SUCH_THAT_4;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 16039)");
        _ASSIGN_SUCH_THAT_4: ;
        Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> @_24831_rest = Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.Empty;
        @_24831_rest = @_Collections____Maps__i_Compile.@__default.@RemoveElt<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>(@m, @_24830_opn);
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24832_restMax = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        @_LiveRSL____CTypes__i_Compile.@COperationNumber _out129;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@getMaxOpnWithProposalFromSingleton(@_24831_rest, out _out129);
        @_24832_restMax = _out129;
        if (((@_24832_restMax).@dtor_n) > ((@_24830_opn).@dtor_n))
        {
          @maxOpn = @_24832_restMax;
        }
        else
        {
          @maxOpn = @_24830_opn;
        }
      }
    }
    public static void @getMaxOpnWithProposalFromSet(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @s, out @_LiveRSL____CTypes__i_Compile.@COperationNumber @maxOpn, out bool @foundNonEmpty)
    {
      @maxOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @foundNonEmpty = false;
      if ((new BigInteger((@s).Length)).@Equals(new BigInteger(1)))
      {
        @_LiveRSL____CMessage__i_Compile.@CPacket @_24833_p = new @_LiveRSL____CMessage__i_Compile.@CPacket();
        foreach (var _assign_such_that_5 in (@s).Elements) { @_24833_p = _assign_such_that_5;
          if ((@s).Contains(@_24833_p)) {
            goto _ASSIGN_SUCH_THAT_5;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 16061)");
        _ASSIGN_SUCH_THAT_5: ;
        { }
        if ((new BigInteger(((((@_24833_p).@dtor_msg).@dtor_votes).@dtor_v).Length)) > (new BigInteger(0)))
        {
          @_LiveRSL____CTypes__i_Compile.@COperationNumber _out130;
          @_LiveRSL____ProposerModel__i_Compile.@__default.@getMaxOpnWithProposalFromSingleton((((@_24833_p).@dtor_msg).@dtor_votes).@dtor_v, out _out130);
          @maxOpn = _out130;
          @foundNonEmpty = true;
        }
        else
        {
          @maxOpn = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL));
          @foundNonEmpty = false;
        }
      }
      else
      {
        @_LiveRSL____CMessage__i_Compile.@CPacket @_24834_p = new @_LiveRSL____CMessage__i_Compile.@CPacket();
        foreach (var _assign_such_that_6 in (@s).Elements) { @_24834_p = _assign_such_that_6;
          if ((@s).Contains(@_24834_p)) {
            goto _ASSIGN_SUCH_THAT_6;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 16077)");
        _ASSIGN_SUCH_THAT_6: ;
        Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @_24835_rest = Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.Empty;
        @_24835_rest = (@s).@Difference(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(@_24834_p));
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24836_candidateOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        bool @_24837_foundLocal = false;
        if ((new BigInteger(((((@_24834_p).@dtor_msg).@dtor_votes).@dtor_v).Length)) > (new BigInteger(0)))
        {
          @_LiveRSL____CTypes__i_Compile.@COperationNumber _out131;
          @_LiveRSL____ProposerModel__i_Compile.@__default.@getMaxOpnWithProposalFromSingleton((((@_24834_p).@dtor_msg).@dtor_votes).@dtor_v, out _out131);
          @_24836_candidateOpn = _out131;
          @_24837_foundLocal = true;
          { }
        }
        else
        {
          @_24836_candidateOpn = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL));
          @_24837_foundLocal = false;
        }
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24838_restMaxOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        bool @_24839_foundTemp = false;
        @_LiveRSL____CTypes__i_Compile.@COperationNumber _out132;
        bool _out133;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@getMaxOpnWithProposalFromSet(@_24835_rest, out _out132, out _out133);
        @_24838_restMaxOpn = _out132;
        @_24839_foundTemp = _out133;
        if ((@_24839_foundTemp) || (@_24837_foundLocal))
        {
          @foundNonEmpty = true;
        }
        else
        {
          @foundNonEmpty = false;
        }
        if (((@_24836_candidateOpn).@dtor_n) > ((@_24838_restMaxOpn).@dtor_n))
        {
          @maxOpn = @_24836_candidateOpn;
        }
        else
        {
          @maxOpn = @_24838_restMaxOpn;
        }
      }
    }
    public static void @getMaxLogTruncationPoint(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @s, out @_LiveRSL____CTypes__i_Compile.@COperationNumber @maxLogTruncationPoint)
    {
      @maxLogTruncationPoint = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      if ((new BigInteger((@s).Length)).@Equals(new BigInteger(1)))
      {
        @_LiveRSL____CMessage__i_Compile.@CPacket @_24840_p = new @_LiveRSL____CMessage__i_Compile.@CPacket();
        foreach (var _assign_such_that_7 in (@s).Elements) { @_24840_p = _assign_such_that_7;
          if ((@s).Contains(@_24840_p)) {
            goto _ASSIGN_SUCH_THAT_7;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 16117)");
        _ASSIGN_SUCH_THAT_7: ;
        { }
        @maxLogTruncationPoint = ((@_24840_p).@dtor_msg).@dtor_logTruncationPoint;
      }
      else
      {
        @_LiveRSL____CMessage__i_Compile.@CPacket @_24841_p = new @_LiveRSL____CMessage__i_Compile.@CPacket();
        foreach (var _assign_such_that_8 in (@s).Elements) { @_24841_p = _assign_such_that_8;
          if ((@s).Contains(@_24841_p)) {
            goto _ASSIGN_SUCH_THAT_8;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 16127)");
        _ASSIGN_SUCH_THAT_8: ;
        Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @_24842_rest = Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.Empty;
        @_24842_rest = (@s).@Difference(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(@_24841_p));
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24843_candidateOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        @_24843_candidateOpn = ((@_24841_p).@dtor_msg).@dtor_logTruncationPoint;
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24844_restMaxOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        @_LiveRSL____CTypes__i_Compile.@COperationNumber _out134;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@getMaxLogTruncationPoint(@_24842_rest, out _out134);
        @_24844_restMaxOpn = _out134;
        if (((@_24843_candidateOpn).@dtor_n) > ((@_24844_restMaxOpn).@dtor_n))
        {
          @maxLogTruncationPoint = @_24843_candidateOpn;
        }
        else
        {
          @maxLogTruncationPoint = @_24844_restMaxOpn;
        }
      }
    }
    public static void @ProposerMaybeEnterPhase2(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k, out @_LiveRSL____CMessage__i_Compile.@CBroadcast @sent__packets)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
    TAIL_CALL_START: ;
      ulong @_24845_start__time = 0;
      ulong _out135;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out135);
      @_24845_start__time = _out135;
      { }
      { }
      { }
      { }
      ulong @_24846_quorum__size = 0;
      ulong _out136;
      @_LiveRSL____MinCQuorumSize__i_Compile.@__default.@MinCQuorumSize((((@proposer).@dtor_constants).@dtor_all).@dtor_config, out _out136);
      @_24846_quorum__size = _out136;
      if (((new BigInteger(((@proposer).@dtor_received1bPackets).Length)) >= (new BigInteger(@_24846_quorum__size))) && (((@proposer).@dtor_currentState).@Equals(1)))
      {
        { }
        { }
        { }
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24847_maxOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        bool @_24848_foundNonEmpty = false;
        @_LiveRSL____CTypes__i_Compile.@COperationNumber _out137;
        bool _out138;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@getMaxOpnWithProposalFromSet((@proposer).@dtor_received1bPackets, out _out137, out _out138);
        @_24847_maxOpn = _out137;
        @_24848_foundNonEmpty = _out138;
        if (!(@_24848_foundNonEmpty))
        {
          @_24847_maxOpn = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL));
        }
        else
        if (((@_24847_maxOpn).@dtor_n) < (18446744073709551615UL))
        {
          @_24847_maxOpn = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(((@_24847_maxOpn).@dtor_n) + (1UL)));
        }
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24849_maxLogTP = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        @_LiveRSL____CTypes__i_Compile.@COperationNumber _out139;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@getMaxLogTruncationPoint((@proposer).@dtor_received1bPackets, out _out139);
        @_24849_maxLogTP = _out139;
        @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let12_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let12_0, @_24850_dt__update__tmp_h3 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24850_dt__update__tmp_h3).@dtor_constants, 2, (@_24850_dt__update__tmp_h3).@dtor_requestQueue, (@_24850_dt__update__tmp_h3).@dtor_maxBallotISent1a, (@logTruncationPoint).@dtor_n, (@_24850_dt__update__tmp_h3).@dtor_received1bPackets, (@_24850_dt__update__tmp_h3).@dtor_highestSeqnoRequestedByClientThisView, (@_24850_dt__update__tmp_h3).@dtor_incompleteBatchTimer, (@_24850_dt__update__tmp_h3).@dtor_electionState, @_24847_maxOpn, @_24849_maxLogTP))));
        @_LiveRSL____CMessage__i_Compile.@CMessage @_24851_msg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
        @_24851_msg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__StartingPhase2((@proposer).@dtor_maxBallotISent1a, @logTruncationPoint));
        { }
        @_LiveRSL____CMessage__i_Compile.@CBroadcast _out140;
        @_Impl____LiveRSL____Broadcast__i_Compile.@__default.@BuildBroadcastToEveryone((((@proposer).@dtor_constants).@dtor_all).@dtor_config, ((@proposer).@dtor_constants).@dtor_myIndex, @_24851_msg, out _out140);
        @sent__packets = _out140;
        ulong @_24852_end__time = 0;
        ulong _out141;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out141);
        @_24852_end__time = _out141;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerMaybeEnterPhase2_work"), @_24845_start__time, @_24852_end__time);
      }
      else
      {
        @proposer_k = @proposer;
        @sent__packets = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop());
        { }
        ulong @_24853_end__time = 0;
        ulong _out142;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out142);
        @_24853_end__time = _out142;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerMaybeEnterPhase2_nada"), @_24845_start__time, @_24853_end__time);
      }
      { }
      { }
    }
    public static void @ProposerNominateNewValueAndSend2a(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, ulong @clock__min, ulong @clock__max, @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k, out @_LiveRSL____CMessage__i_Compile.@CBroadcast @sent__packets)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
    TAIL_CALL_START: ;
      BigInteger @_24854_batchSize = BigInteger.Zero;
      @_24854_batchSize = (((new BigInteger(((@proposer).@dtor_requestQueue).Length)) <= (new BigInteger(((((@proposer).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxBatchSize))) || ((((((@proposer).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxBatchSize) < (0UL))) ? (new BigInteger(((@proposer).@dtor_requestQueue).Length)) : (new BigInteger(((((@proposer).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxBatchSize));
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_24855_v = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
      @_24855_v = ((@proposer).@dtor_requestQueue).Take(@_24854_batchSize);
      ulong @_24856_opn = 0;
      @_24856_opn = (@proposer).@dtor_nextOperationNumberToPropose;
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24857_opn__op = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_24857_opn__op = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber((@proposer).@dtor_nextOperationNumberToPropose));
      ulong @_24858_clock__sum = 0;
      ulong _out143;
      @_LiveRSL____ParametersState__i_Compile.@__default.@LCappedAdditionImpl(@clock__min, ((((@proposer).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxBatchDelay, (((@proposer).@dtor_constants).@dtor_all).@dtor_params, out _out143);
      @_24858_clock__sum = _out143;
      @_LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer @_24859_newTimer = new @_LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer();
      @_24859_newTimer = ((new BigInteger(((@proposer).@dtor_requestQueue).Length)) > ((@_24854_batchSize))) ? (new _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer(new _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer_CIncompleteBatchTimerOn(@_24858_clock__sum))) : (new _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer(new _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer_CIncompleteBatchTimerOff()));
      @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let13_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let13_0, @_24860_dt__update__tmp_h3 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24860_dt__update__tmp_h3).@dtor_constants, (@_24860_dt__update__tmp_h3).@dtor_currentState, ((@proposer).@dtor_requestQueue).Drop(@_24854_batchSize), (@_24860_dt__update__tmp_h3).@dtor_maxBallotISent1a, (@_24856_opn) + (1UL), (@_24860_dt__update__tmp_h3).@dtor_received1bPackets, (@_24860_dt__update__tmp_h3).@dtor_highestSeqnoRequestedByClientThisView, @_24859_newTimer, (@_24860_dt__update__tmp_h3).@dtor_electionState, (@_24860_dt__update__tmp_h3).@dtor_maxOpnWithProposal, (@_24860_dt__update__tmp_h3).@dtor_maxLogTruncationPoint))));
      @_LiveRSL____CMessage__i_Compile.@CMessage @_24861_msg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
      @_24861_msg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__2a((@proposer).@dtor_maxBallotISent1a, @_24857_opn__op, @_24855_v));
      { }
      @_LiveRSL____CMessage__i_Compile.@CBroadcast _out144;
      @_Impl____LiveRSL____Broadcast__i_Compile.@__default.@BuildBroadcastToEveryone((((@proposer).@dtor_constants).@dtor_all).@dtor_config, ((@proposer).@dtor_constants).@dtor_myIndex, @_24861_msg, out _out144);
      @sent__packets = _out144;
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @FindValWithHighestNumberedProposal(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @received1bPackets, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn, out Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @v)
    {
      @v = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
    TAIL_CALL_START: ;
      Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @_24862_packets = Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.Empty;
      Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @_24863_processedPackets = Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.Empty;
      @_24862_packets = @received1bPackets;
      @_LiveRSL____CMessage__i_Compile.@CPacket @_24864_pkt = new @_LiveRSL____CMessage__i_Compile.@CPacket();
      foreach (var _assign_such_that_9 in (@_24862_packets).Elements) { @_24864_pkt = _assign_such_that_9;
        if (((@_24862_packets).Contains(@_24864_pkt)) && (((((@_24864_pkt).@dtor_msg).@dtor_votes).@dtor_v).Contains(@opn))) {
          goto _ASSIGN_SUCH_THAT_9;
        }
      }
      throw new System.Exception("assign-such-that search produced no value (line 16468)");
      _ASSIGN_SUCH_THAT_9: ;
      @v = (((((@_24864_pkt).@dtor_msg).@dtor_votes).@dtor_v).Select(@opn)).@dtor_maxVal;
      @_LiveRSL____CTypes__i_Compile.@CBallot @_24865_bal = new @_LiveRSL____CTypes__i_Compile.@CBallot();
      @_24865_bal = (((((@_24864_pkt).@dtor_msg).@dtor_votes).@dtor_v).Select(@opn)).@dtor_maxVBal;
      @_LiveRSL____CMessage__i_Compile.@CPacket @_24866_p__bal = new @_LiveRSL____CMessage__i_Compile.@CPacket();
      @_24866_p__bal = @_24864_pkt;
      @_24862_packets = (@_24862_packets).@Difference(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(@_24864_pkt));
      @_24863_processedPackets = Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(@_24864_pkt);
      { }
      { }
      { }
      { }
      { }
      while (!(@_24862_packets).@Equals(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements()))
      {
        foreach (var _assign_such_that_10 in (@_24862_packets).Elements) { @_24864_pkt = _assign_such_that_10;
          if ((@_24862_packets).Contains(@_24864_pkt)) {
            goto _ASSIGN_SUCH_THAT_10;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 16496)");
        _ASSIGN_SUCH_THAT_10: ;
        if (((((@_24864_pkt).@dtor_msg).@dtor_votes).@dtor_v).Contains(@opn))
        {
          bool @_24867_foundHigherBallot = false;
          bool _out145;
          @_LiveRSL____CTypes__i_Compile.@__default.@CBalLeq(@_24865_bal, (((((@_24864_pkt).@dtor_msg).@dtor_votes).@dtor_v).Select(@opn)).@dtor_maxVBal, out _out145);
          @_24867_foundHigherBallot = _out145;
          if (@_24867_foundHigherBallot)
          {
            @_24866_p__bal = @_24864_pkt;
            @v = (((((@_24864_pkt).@dtor_msg).@dtor_votes).@dtor_v).Select(@opn)).@dtor_maxVal;
            @_24865_bal = (((((@_24864_pkt).@dtor_msg).@dtor_votes).@dtor_v).Select(@opn)).@dtor_maxVBal;
          }
        }
        @_24862_packets = (@_24862_packets).@Difference(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(@_24864_pkt));
        @_24863_processedPackets = (@_24863_processedPackets).@Union(Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(@_24864_pkt));
        { }
      }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @ProposerNominateOldValueAndSend2a(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k, out @_LiveRSL____CMessage__i_Compile.@CBroadcast @sent__packets)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
    TAIL_CALL_START: ;
      { }
      ulong @_24868_opn = 0;
      @_24868_opn = (@proposer).@dtor_nextOperationNumberToPropose;
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24869_opn__op = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_24869_opn__op = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber((@proposer).@dtor_nextOperationNumberToPropose));
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_24870_val = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> _out146;
      @_LiveRSL____ProposerModel__i_Compile.@__default.@FindValWithHighestNumberedProposal((@proposer).@dtor_received1bPackets, @_24869_opn__op, out _out146);
      @_24870_val = _out146;
      { }
      ulong @_24871_sum = 0;
      ulong _out147;
      @_LiveRSL____ParametersState__i_Compile.@__default.@LCappedAdditionImpl(@_24868_opn, 1UL, (((@proposer).@dtor_constants).@dtor_all).@dtor_params, out _out147);
      @_24871_sum = _out147;
      @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let14_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let14_0, @_24872_dt__update__tmp_h1 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24872_dt__update__tmp_h1).@dtor_constants, (@_24872_dt__update__tmp_h1).@dtor_currentState, (@_24872_dt__update__tmp_h1).@dtor_requestQueue, (@_24872_dt__update__tmp_h1).@dtor_maxBallotISent1a, @_24871_sum, (@_24872_dt__update__tmp_h1).@dtor_received1bPackets, (@_24872_dt__update__tmp_h1).@dtor_highestSeqnoRequestedByClientThisView, (@_24872_dt__update__tmp_h1).@dtor_incompleteBatchTimer, (@_24872_dt__update__tmp_h1).@dtor_electionState, (@_24872_dt__update__tmp_h1).@dtor_maxOpnWithProposal, (@_24872_dt__update__tmp_h1).@dtor_maxLogTruncationPoint))));
      { }
      { }
      @_LiveRSL____CMessage__i_Compile.@CMessage @_24873_msg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
      @_24873_msg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__2a((@proposer).@dtor_maxBallotISent1a, @_24869_opn__op, @_24870_val));
      { }
      @_LiveRSL____CMessage__i_Compile.@CBroadcast _out148;
      @_Impl____LiveRSL____Broadcast__i_Compile.@__default.@BuildBroadcastToEveryone((((@proposer).@dtor_constants).@dtor_all).@dtor_config, ((@proposer).@dtor_constants).@dtor_myIndex, @_24873_msg, out _out148);
      @sent__packets = _out148;
      { }
      { }
      { }
      { }
      { }
    }
    public static void @IsAfterLogTruncationPointImpl(@_LiveRSL____CTypes__i_Compile.@COperationNumber @opn, Dafny.Set<@_LiveRSL____CMessage__i_Compile.@CPacket> @received1bPackets, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      { }
      { }
      { }
      @b = Dafny.Helpers.QuantSet(@received1bPackets, true, @_24874_p => !(((@received1bPackets).Contains(@_24874_p)) && (((@_24874_p).@dtor_msg).@is_CMessage__1b)) || (((((@_24874_p).@dtor_msg).@dtor_logTruncationPoint).@dtor_n) <= ((@opn).@dtor_n)));
    }
    public static void @Proposer__CanNominateUsingOperationNumberImpl(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      if (((@proposer).@dtor_currentState).@Equals(2))
      {
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24875_opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        @_24875_opn = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber((@proposer).@dtor_nextOperationNumberToPropose));
        ulong @_24876_quorum__size = 0;
        ulong _out149;
        @_LiveRSL____MinCQuorumSize__i_Compile.@__default.@MinCQuorumSize((((@proposer).@dtor_constants).@dtor_all).@dtor_config, out _out149);
        @_24876_quorum__size = _out149;
        bool @_24877_after__trunk = false;
        if (((@_24875_opn).@dtor_n) >= (((@proposer).@dtor_maxLogTruncationPoint).@dtor_n))
        {
          @_24877_after__trunk = true;
        }
        else
        {
          bool _out150;
          @_LiveRSL____ProposerModel__i_Compile.@__default.@IsAfterLogTruncationPointImpl(@_24875_opn, (@proposer).@dtor_received1bPackets, out _out150);
          @_24877_after__trunk = _out150;
        }
        ulong @_24878_sum = 0;
        ulong _out151;
        @_LiveRSL____ParametersState__i_Compile.@__default.@LCappedAdditionImpl((@logTruncationPoint).@dtor_n, ((((@proposer).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxLogLength, (((@proposer).@dtor_constants).@dtor_all).@dtor_params, out _out151);
        @_24878_sum = _out151;
        { }
        @b = ((((((((@proposer).@dtor_electionState).@dtor_currentView).@Equals((@proposer).@dtor_maxBallotISent1a)) && (((@proposer).@dtor_currentState).@Equals(2))) && ((new BigInteger(((@proposer).@dtor_received1bPackets).Length)) >= (new BigInteger(@_24876_quorum__size)))) && (@_24877_after__trunk)) && (((@_24875_opn).@dtor_n) < (@_24878_sum))) && (((@_24875_opn).@dtor_n) >= (0UL));
        { }
        { }
      }
      else
      {
        @b = false;
      }
    }
    public static void @AllAcceptorsHadNoProposalImpl(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      { }
      { }
      { }
      { }
      { }
      ulong @_24879_start__time = 0;
      ulong _out152;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out152);
      @_24879_start__time = _out152;
      ulong @_24880_end__time = 0;
      if ((((@proposer).@dtor_nextOperationNumberToPropose) < (((@proposer).@dtor_maxOpnWithProposal).@dtor_n)) || ((((@proposer).@dtor_maxOpnWithProposal).@dtor_n).@Equals(18446744073709551615UL)))
      {
        @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24881_opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
        @_24881_opn = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber((@proposer).@dtor_nextOperationNumberToPropose));
        @b = Dafny.Helpers.QuantSet((@proposer).@dtor_received1bPackets, true, @_24882_p => !(((@proposer).@dtor_received1bPackets).Contains(@_24882_p)) || (!(((((@_24882_p).@dtor_msg).@dtor_votes).@dtor_v).Contains(@_24881_opn))));
        ulong _out153;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out153);
        @_24880_end__time = _out153;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("AllAcceptorsHadNoProposalImpl_full"), @_24879_start__time, @_24880_end__time);
      }
      else
      {
        @b = true;
        ulong _out154;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out154);
        @_24880_end__time = _out154;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("AllAcceptorsHadNoProposalImpl_memoized"), @_24879_start__time, @_24880_end__time);
      }
      { }
    }
    public static void @DidSomeAcceptorHaveProposal(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      { }
      { }
      { }
      { }
      { }
      if (((@proposer).@dtor_nextOperationNumberToPropose) >= (((@proposer).@dtor_maxOpnWithProposal).@dtor_n))
      {
        @b = false;
      }
      else
      {
        @b = Dafny.Helpers.QuantSet((@proposer).@dtor_received1bPackets, false, @_24883_p => (((@proposer).@dtor_received1bPackets).Contains(@_24883_p)) && (Dafny.Helpers.QuantMap((((@_24883_p).@dtor_msg).@dtor_votes).@dtor_v, false, @_24884_opn => (((((@_24883_p).@dtor_msg).@dtor_votes).@dtor_v).Contains(@_24884_opn)) && (((@_24884_opn).@dtor_n) > ((@proposer).@dtor_nextOperationNumberToPropose)))));
      }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @ProposerMaybeNominateValueAndSend2a(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, ulong @clock__min, ulong @clock__max, @_LiveRSL____CTypes__i_Compile.@COperationNumber @logTruncationPoint, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k, out @_LiveRSL____CMessage__i_Compile.@CBroadcast @sent__packets)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
    TAIL_CALL_START: ;
      ulong @_24885_start__time = 0;
      ulong _out155;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out155);
      @_24885_start__time = _out155;
      bool @_24886_canNominate = false;
      bool _out156;
      @_LiveRSL____ProposerModel__i_Compile.@__default.@Proposer__CanNominateUsingOperationNumberImpl(@proposer, @logTruncationPoint, out _out156);
      @_24886_canNominate = _out156;
      if (!(@_24886_canNominate))
      {
        @proposer_k = @proposer;
        @sent__packets = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop());
        ulong @_24887_end__timeNotCanNominate = 0;
        ulong _out157;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out157);
        @_24887_end__timeNotCanNominate = _out157;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerMaybeNominateValueAndSend2a_unable"), @_24885_start__time, @_24887_end__timeNotCanNominate);
      }
      else
      {
        if (((((@proposer).@dtor_nextOperationNumberToPropose) >= (((@proposer).@dtor_maxOpnWithProposal).@dtor_n)) && ((new BigInteger(((@proposer).@dtor_requestQueue).Length)).@Equals(new BigInteger(0)))) && ((((@proposer).@dtor_maxOpnWithProposal).@dtor_n) < (18446744073709551615UL)))
        {
          { }
          { }
          @proposer_k = @proposer;
          @sent__packets = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop());
          ulong @_24888_end__time4 = 0;
          ulong _out158;
          @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out158);
          @_24888_end__time4 = _out158;
          @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerMaybeNominateValueAndSend2a_nada"), @_24885_start__time, @_24888_end__time4);
        }
        else
        {
          bool @_24889_noProposal = false;
          bool _out159;
          @_LiveRSL____ProposerModel__i_Compile.@__default.@AllAcceptorsHadNoProposalImpl(@proposer, out _out159);
          @_24889_noProposal = _out159;
          ulong @_24890_end__time2 = 0;
          ulong _out160;
          @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out160);
          @_24890_end__time2 = _out160;
          @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerMaybeNominateValueAndSend2a_AllAcceptorsHadNoProposalImpl"), @_24885_start__time, @_24890_end__time2);
          if (!(@_24889_noProposal))
          {
            @_LiveRSL____ProposerState__i_Compile.@ProposerState _out161;
            @_LiveRSL____CMessage__i_Compile.@CBroadcast _out162;
            @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerNominateOldValueAndSend2a(@proposer, @logTruncationPoint, out _out161, out _out162);
            @proposer_k = _out161;
            @sent__packets = _out162;
            { }
            ulong @_24891_end__timeNotNoProposal = 0;
            ulong _out163;
            @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out163);
            @_24891_end__timeNotNoProposal = _out163;
            @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerMaybeNominateValueAndSend2a_old"), @_24890_end__time2, @_24891_end__timeNotNoProposal);
          }
          else
          {
            BigInteger @_24892_queueSize = BigInteger.Zero;
            @_24892_queueSize = new BigInteger(((@proposer).@dtor_requestQueue).Length);
            bool @_24893_existsOpn = false;
            bool _out164;
            @_LiveRSL____ProposerModel__i_Compile.@__default.@DidSomeAcceptorHaveProposal(@proposer, out _out164);
            @_24893_existsOpn = _out164;
            { }
            { }
            { }
            ulong @_24894_end__time3 = 0;
            ulong _out165;
            @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out165);
            @_24894_end__time3 = _out165;
            { }
            if ((((((@_24892_queueSize) > (new BigInteger(0))) && (((@proposer).@dtor_incompleteBatchTimer).@is_CIncompleteBatchTimerOn)) && ((@clock__max) >= (((@proposer).@dtor_incompleteBatchTimer).@dtor_when))) || ((@_24892_queueSize) >= (new BigInteger(((((@proposer).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxBatchSize)))) || (@_24893_existsOpn))
            {
              { }
              @_LiveRSL____ProposerState__i_Compile.@ProposerState _out166;
              @_LiveRSL____CMessage__i_Compile.@CBroadcast _out167;
              @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerNominateNewValueAndSend2a(@proposer, @clock__min, @clock__max, @logTruncationPoint, out _out166, out _out167);
              @proposer_k = _out166;
              @sent__packets = _out167;
              { }
              ulong @_24895_end__timeNominateNew = 0;
              ulong _out168;
              @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out168);
              @_24895_end__timeNominateNew = _out168;
              @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerMaybeNominateValueAndSend2a_new_or_noop"), @_24890_end__time2, @_24895_end__timeNominateNew);
            }
            else
            {
              if (((@_24892_queueSize) > (new BigInteger(0))) && (((@proposer).@dtor_incompleteBatchTimer).@is_CIncompleteBatchTimerOff))
              {
                ulong @_24896_sum = 0;
                ulong _out169;
                @_LiveRSL____ParametersState__i_Compile.@__default.@LCappedAdditionImpl(@clock__min, ((((@proposer).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxBatchDelay, (((@proposer).@dtor_constants).@dtor_all).@dtor_params, out _out169);
                @_24896_sum = _out169;
                @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let15_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let15_0, @_24897_dt__update__tmp_h0 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24897_dt__update__tmp_h0).@dtor_constants, (@_24897_dt__update__tmp_h0).@dtor_currentState, (@_24897_dt__update__tmp_h0).@dtor_requestQueue, (@_24897_dt__update__tmp_h0).@dtor_maxBallotISent1a, (@_24897_dt__update__tmp_h0).@dtor_nextOperationNumberToPropose, (@_24897_dt__update__tmp_h0).@dtor_received1bPackets, (@_24897_dt__update__tmp_h0).@dtor_highestSeqnoRequestedByClientThisView, new _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer(new _LiveRSL____ProposerState__i_Compile.@CIncompleteBatchTimer_CIncompleteBatchTimerOn(@_24896_sum)), (@_24897_dt__update__tmp_h0).@dtor_electionState, (@_24897_dt__update__tmp_h0).@dtor_maxOpnWithProposal, (@_24897_dt__update__tmp_h0).@dtor_maxLogTruncationPoint))));
                @sent__packets = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop());
              }
              else
              {
                @proposer_k = @proposer;
                @sent__packets = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop());
              }
            }
          }
        }
      }
    }
    public static void @ProposerProcessHeartbeat(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, @_LiveRSL____CMessage__i_Compile.@CPacket @packet, ulong @clock__min, ulong @clock__max, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
    TAIL_CALL_START: ;
      @_LiveRSL____ElectionState__i_Compile.@CElectionState @_24898_electionState_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
      @_LiveRSL____ElectionState__i_Compile.@CElectionState _out170;
      @_LiveRSL____ElectionModel__i_Compile.@__default.@ElectionProcessHeartbeat((@proposer).@dtor_electionState, @packet, @clock__min, @clock__max, out _out170);
      @_24898_electionState_k = _out170;
      byte @_24899_currentState_k = 0;
      @_24899_currentState_k = 0;
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_24900_requestQueue_k = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
      @_24900_requestQueue_k = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements();
      bool @_24901_lt = false;
      bool _out171;
      @_LiveRSL____CTypes__i_Compile.@__default.@CBalLt(((@proposer).@dtor_electionState).@dtor_currentView, (@_24898_electionState_k).@dtor_currentView, out _out171);
      @_24901_lt = _out171;
      if (@_24901_lt)
      {
        @_24899_currentState_k = 0;
        @_24900_requestQueue_k = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements();
      }
      else
      {
        @_24899_currentState_k = (@proposer).@dtor_currentState;
        @_24900_requestQueue_k = (@proposer).@dtor_requestQueue;
      }
      @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let16_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let16_0, @_24902_dt__update__tmp_h2 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24902_dt__update__tmp_h2).@dtor_constants, @_24899_currentState_k, @_24900_requestQueue_k, (@_24902_dt__update__tmp_h2).@dtor_maxBallotISent1a, (@_24902_dt__update__tmp_h2).@dtor_nextOperationNumberToPropose, (@_24902_dt__update__tmp_h2).@dtor_received1bPackets, (@_24902_dt__update__tmp_h2).@dtor_highestSeqnoRequestedByClientThisView, (@_24902_dt__update__tmp_h2).@dtor_incompleteBatchTimer, @_24898_electionState_k, (@_24902_dt__update__tmp_h2).@dtor_maxOpnWithProposal, (@_24902_dt__update__tmp_h2).@dtor_maxLogTruncationPoint))));
    }
    public static void @ProposerCheckForViewTimeout(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, ulong @clock__min, ulong @clock__max, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
    TAIL_CALL_START: ;
      @_LiveRSL____ElectionState__i_Compile.@CElectionState @_24903_electionState_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
      @_LiveRSL____ElectionState__i_Compile.@CElectionState _out172;
      @_LiveRSL____ElectionModel__i_Compile.@__default.@ElectionCheckForViewTimeout((@proposer).@dtor_electionState, @clock__min, @clock__max, out _out172);
      @_24903_electionState_k = _out172;
      @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let17_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let17_0, @_24904_dt__update__tmp_h0 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24904_dt__update__tmp_h0).@dtor_constants, (@_24904_dt__update__tmp_h0).@dtor_currentState, (@_24904_dt__update__tmp_h0).@dtor_requestQueue, (@_24904_dt__update__tmp_h0).@dtor_maxBallotISent1a, (@_24904_dt__update__tmp_h0).@dtor_nextOperationNumberToPropose, (@_24904_dt__update__tmp_h0).@dtor_received1bPackets, (@_24904_dt__update__tmp_h0).@dtor_highestSeqnoRequestedByClientThisView, (@_24904_dt__update__tmp_h0).@dtor_incompleteBatchTimer, @_24903_electionState_k, (@_24904_dt__update__tmp_h0).@dtor_maxOpnWithProposal, (@_24904_dt__update__tmp_h0).@dtor_maxLogTruncationPoint))));
    }
    public static void @ProposerCheckForQuorumOfViewSuspicions(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, ulong @clock__min, ulong @clock__max, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
    TAIL_CALL_START: ;
      ulong @_24905_start__time = 0;
      ulong _out173;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out173);
      @_24905_start__time = _out173;
      @_LiveRSL____ElectionState__i_Compile.@CElectionState @_24906_electionState_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
      @_LiveRSL____ElectionState__i_Compile.@CElectionState _out174;
      @_LiveRSL____ElectionModel__i_Compile.@__default.@ElectionCheckForQuorumOfViewSuspicions((@proposer).@dtor_electionState, @clock__min, @clock__max, out _out174);
      @_24906_electionState_k = _out174;
      byte @_24907_currentState_k = 0;
      @_24907_currentState_k = 0;
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_24908_requestQueue_k = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
      @_24908_requestQueue_k = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements();
      bool @_24909_lt = false;
      bool _out175;
      @_LiveRSL____CTypes__i_Compile.@__default.@CBalLt(((@proposer).@dtor_electionState).@dtor_currentView, (@_24906_electionState_k).@dtor_currentView, out _out175);
      @_24909_lt = _out175;
      if (@_24909_lt)
      {
        @_24907_currentState_k = 0;
        @_24908_requestQueue_k = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.FromElements();
      }
      else
      {
        @_24907_currentState_k = (@proposer).@dtor_currentState;
        @_24908_requestQueue_k = (@proposer).@dtor_requestQueue;
      }
      @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let18_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let18_0, @_24910_dt__update__tmp_h2 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24910_dt__update__tmp_h2).@dtor_constants, @_24907_currentState_k, @_24908_requestQueue_k, (@_24910_dt__update__tmp_h2).@dtor_maxBallotISent1a, (@_24910_dt__update__tmp_h2).@dtor_nextOperationNumberToPropose, (@_24910_dt__update__tmp_h2).@dtor_received1bPackets, (@_24910_dt__update__tmp_h2).@dtor_highestSeqnoRequestedByClientThisView, (@_24910_dt__update__tmp_h2).@dtor_incompleteBatchTimer, @_24906_electionState_k, (@_24910_dt__update__tmp_h2).@dtor_maxOpnWithProposal, (@_24910_dt__update__tmp_h2).@dtor_maxLogTruncationPoint))));
      ulong @_24911_end__time = 0;
      ulong _out176;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out176);
      @_24911_end__time = _out176;
      if (@_24909_lt)
      {
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerCheckForQuorumOfViewSuspicions_changed"), @_24905_start__time, @_24911_end__time);
      }
      else
      {
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ProposerCheckForQuorumOfViewSuspicions_nada"), @_24905_start__time, @_24911_end__time);
      }
    }
    public static void @ProposerResetViewTimerDueToExecution(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @val, out @_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer_k)
    {
      @proposer_k = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
    TAIL_CALL_START: ;
      @_LiveRSL____ElectionState__i_Compile.@CElectionState @_24912_electionState_k = new @_LiveRSL____ElectionState__i_Compile.@CElectionState();
      @_LiveRSL____ElectionState__i_Compile.@CElectionState _out177;
      @_LiveRSL____ElectionModel__i_Compile.@__default.@ElectionReflectExecutedRequestBatch((@proposer).@dtor_electionState, @val, out _out177);
      @_24912_electionState_k = _out177;
      @proposer_k = Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(@proposer, _pat_let19_0 => Dafny.Helpers.Let<@_LiveRSL____ProposerState__i_Compile.@ProposerState,@_LiveRSL____ProposerState__i_Compile.@ProposerState>(_pat_let19_0, @_24913_dt__update__tmp_h0 => new _LiveRSL____ProposerState__i_Compile.@ProposerState(new _LiveRSL____ProposerState__i_Compile.@ProposerState_ProposerState((@_24913_dt__update__tmp_h0).@dtor_constants, (@_24913_dt__update__tmp_h0).@dtor_currentState, (@_24913_dt__update__tmp_h0).@dtor_requestQueue, (@_24913_dt__update__tmp_h0).@dtor_maxBallotISent1a, (@_24913_dt__update__tmp_h0).@dtor_nextOperationNumberToPropose, (@_24913_dt__update__tmp_h0).@dtor_received1bPackets, (@_24913_dt__update__tmp_h0).@dtor_highestSeqnoRequestedByClientThisView, (@_24913_dt__update__tmp_h0).@dtor_incompleteBatchTimer, @_24912_electionState_k, (@_24913_dt__update__tmp_h0).@dtor_maxOpnWithProposal, (@_24913_dt__update__tmp_h0).@dtor_maxLogTruncationPoint))));
    }
  }
} // end of namespace _LiveRSL____ProposerModel__i_Compile
namespace @_LiveRSL____AcceptorModel__i_Compile {



  public partial class @__default {
    public static void @create__seq(BigInteger @len, ulong @init__int, out Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> @s)
    {
      @s = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber>.Empty;
      if ((@len).@Equals(new BigInteger(0)))
      {
        @s = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber>.FromElements();
      }
      else
      {
        Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> @_24914_rest = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber>.Empty;
        Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> _out178;
        @_LiveRSL____AcceptorModel__i_Compile.@__default.@create__seq((@len) - (new BigInteger(1)), @init__int, out _out178);
        @_24914_rest = _out178;
        @s = (Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber>.FromElements(new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(@init__int)))).@Concat(@_24914_rest);
      }
    }
    public static void @DummyInitLastCheckpointedOperation(@_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config, out Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> @ilco)
    {
      @ilco = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber>.Empty;
    TAIL_CALL_START: ;
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> _out179;
      @_LiveRSL____AcceptorModel__i_Compile.@__default.@create__seq(new BigInteger(((@config).@dtor_replicaIds).Length), 0UL, out _out179);
      @ilco = _out179;
      { }
      { }
      { }
    }
    public static void @InitAcceptorState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @rcs, out @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor)
    {
      @acceptor = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
    TAIL_CALL_START: ;
      { }
      @_LiveRSL____CTypes__i_Compile.@CBallot @_24915_maxBallot = new @_LiveRSL____CTypes__i_Compile.@CBallot();
      @_24915_maxBallot = new _LiveRSL____CTypes__i_Compile.@CBallot(new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot(0UL, 0UL));
      @_LiveRSL____CTypes__i_Compile.@CVotes @_24916_votes = new @_LiveRSL____CTypes__i_Compile.@CVotes();
      @_24916_votes = new _LiveRSL____CTypes__i_Compile.@CVotes(new _LiveRSL____CTypes__i_Compile.@CVotes_CVotes(Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.FromElements()));
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> @_24917_lastCheckpointedOperation = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber>.Empty;
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> _out180;
      @_LiveRSL____AcceptorModel__i_Compile.@__default.@DummyInitLastCheckpointedOperation(((@rcs).@dtor_all).@dtor_config, out _out180);
      @_24917_lastCheckpointedOperation = _out180;
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24918_logTruncationPoint = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_24918_logTruncationPoint = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL));
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24919_minVotedOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_24919_minVotedOpn = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL));
      @acceptor = new _LiveRSL____AcceptorState__i_Compile.@AcceptorState(new _LiveRSL____AcceptorState__i_Compile.@AcceptorState_AcceptorState(@rcs, @_24915_maxBallot, @_24916_votes, @_24917_lastCheckpointedOperation, @_24918_logTruncationPoint, @_24919_minVotedOpn));
      { }
    }
    public static void @NextAcceptorState__Phase1(@_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor, @_LiveRSL____CMessage__i_Compile.@CMessage @inMsg, @_Native____Io__s_Compile.@EndPoint @sender, out @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor_k, out @_LiveRSL____CMessage__i_Compile.@CBroadcast @packetsSent)
    {
      @acceptor_k = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
    TAIL_CALL_START: ;
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop());
      @_LiveRSL____CTypes__i_Compile.@CBallot @_24920_ballot = new @_LiveRSL____CTypes__i_Compile.@CBallot();
      @_24920_ballot = (@inMsg).@dtor_bal__1a;
      { }
      if (!(@_LiveRSL____CTypes__i_Compile.@__default.@CBallot__IsLessThan((@acceptor).@dtor_maxBallot, @_24920_ballot)))
      {
        @acceptor_k = @acceptor;
        return;
      }
      if (!(((((@acceptor).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Contains(@sender))
      {
        @acceptor_k = @acceptor;
        return;
      }
      @_LiveRSL____CMessage__i_Compile.@CMessage @_24921_outMsg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
      @_24921_outMsg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__1b(@_24920_ballot, (@acceptor).@dtor_logTruncationPoint, (@acceptor).@dtor_votes));
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcast((((((@acceptor).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Select(((@acceptor).@dtor_constants).@dtor_myIndex), Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.FromElements(@sender), @_24921_outMsg));
      @acceptor_k = Dafny.Helpers.Let<@_LiveRSL____AcceptorState__i_Compile.@AcceptorState,@_LiveRSL____AcceptorState__i_Compile.@AcceptorState>(@acceptor, _pat_let20_0 => Dafny.Helpers.Let<@_LiveRSL____AcceptorState__i_Compile.@AcceptorState,@_LiveRSL____AcceptorState__i_Compile.@AcceptorState>(_pat_let20_0, @_24922_dt__update__tmp_h0 => new _LiveRSL____AcceptorState__i_Compile.@AcceptorState(new _LiveRSL____AcceptorState__i_Compile.@AcceptorState_AcceptorState((@_24922_dt__update__tmp_h0).@dtor_constants, @_24920_ballot, (@_24922_dt__update__tmp_h0).@dtor_votes, (@_24922_dt__update__tmp_h0).@dtor_lastCheckpointedOperation, (@_24922_dt__update__tmp_h0).@dtor_logTruncationPoint, (@_24922_dt__update__tmp_h0).@dtor_minVotedOpn))));
      { }
      { }
      { }
      { }
      { }
    }
    public static void @AddVoteAndRemoveOldOnesImpl(@_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor, @_LiveRSL____CTypes__i_Compile.@CVotes @votes, @_LiveRSL____CTypes__i_Compile.@COperationNumber @newopn, @_LiveRSL____CTypes__i_Compile.@CVote @newvote, @_LiveRSL____CTypes__i_Compile.@COperationNumber @newLogTruncationPoint, @_LiveRSL____CTypes__i_Compile.@COperationNumber @minVotedOpn, out @_LiveRSL____CTypes__i_Compile.@CVotes @votes_k, out @_LiveRSL____CTypes__i_Compile.@COperationNumber @newMinVotedOpn)
    {
      @votes_k = new @_LiveRSL____CTypes__i_Compile.@CVotes();
      @newMinVotedOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      { }
      Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> @_24923_updatedvotes = Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.Empty;
      @_24923_updatedvotes = ((@votes).@dtor_v).Update(@newopn, @newvote);
      Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> @_24924_newvotes = Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.Empty;
      if (((@newLogTruncationPoint).@dtor_n) > ((@minVotedOpn).@dtor_n))
      {
        @_24924_newvotes = ((Dafny.Helpers.MapComprehensionDelegate<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>)delegate() { var _coll = new System.Collections.Generic.List<Dafny.Pair<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>>(); foreach (var @_24925_op in (@_24923_updatedvotes).Domain) { if (((@_24923_updatedvotes).Contains(@_24925_op)) && (((@_24925_op).@dtor_n) >= ((@newLogTruncationPoint).@dtor_n))) { _coll.Add(new Dafny.Pair<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>(@_24925_op,(@_24923_updatedvotes).Select(@_24925_op))); }}return Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.FromCollection(_coll); })();
        @newMinVotedOpn = @newLogTruncationPoint;
      }
      else
      {
        @_24924_newvotes = @_24923_updatedvotes;
        if (((@newopn).@dtor_n) < ((@minVotedOpn).@dtor_n))
        {
          @newMinVotedOpn = @newopn;
        }
        else
        {
          @newMinVotedOpn = @minVotedOpn;
        }
      }
      @votes_k = new _LiveRSL____CTypes__i_Compile.@CVotes(new _LiveRSL____CTypes__i_Compile.@CVotes_CVotes(@_24924_newvotes));
      { }
      { }
      { }
      { }
      { }
    }
    public static void @NextAcceptorState__Phase2(@_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor, @_LiveRSL____CMessage__i_Compile.@CMessage @inMsg, @_Native____Io__s_Compile.@EndPoint @sender, out @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor_k, out @_LiveRSL____CMessage__i_Compile.@CBroadcast @packetsSent)
    {
      @acceptor_k = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
    TAIL_CALL_START: ;
      ulong @_24926_start__time = 0;
      ulong _out181;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out181);
      @_24926_start__time = _out181;
      { }
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop());
      @acceptor_k = @acceptor;
      @_LiveRSL____CTypes__i_Compile.@CBallot @_24927_ballot = new @_LiveRSL____CTypes__i_Compile.@CBallot();
      @_24927_ballot = (@inMsg).@dtor_bal__2a;
      { }
      ulong @_24928_maxLogLengthMinus1 = 0;
      @_24928_maxLogLengthMinus1 = (((((@acceptor).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxLogLength) - (1UL);
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24929_newLogTruncationPoint = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_24929_newLogTruncationPoint = (@acceptor).@dtor_logTruncationPoint;
      if ((((@inMsg).@dtor_opn__2a).@dtor_n) >= (@_24928_maxLogLengthMinus1))
      {
        ulong @_24930_potentialNewTruncationPoint = 0;
        @_24930_potentialNewTruncationPoint = (((@inMsg).@dtor_opn__2a).@dtor_n) - (@_24928_maxLogLengthMinus1);
        if ((@_24930_potentialNewTruncationPoint) > (((@acceptor).@dtor_logTruncationPoint).@dtor_n))
        {
          @_24929_newLogTruncationPoint = new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(@_24930_potentialNewTruncationPoint));
        }
      }
      { }
      ulong @_24931_addition = 0;
      ulong _out182;
      @_LiveRSL____ParametersState__i_Compile.@__default.@LCappedAdditionImpl(((@acceptor).@dtor_logTruncationPoint).@dtor_n, ((((@acceptor).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxLogLength, (((@acceptor).@dtor_constants).@dtor_all).@dtor_params, out _out182);
      @_24931_addition = _out182;
      { }
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24932_opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_24932_opn = (@inMsg).@dtor_opn__2a;
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_24933_value = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
      @_24933_value = (@inMsg).@dtor_val__2a;
      @_LiveRSL____CTypes__i_Compile.@CVote @_24934_newVote = new @_LiveRSL____CTypes__i_Compile.@CVote();
      @_24934_newVote = new _LiveRSL____CTypes__i_Compile.@CVote(new _LiveRSL____CTypes__i_Compile.@CVote_CVote(@_24927_ballot, @_24933_value));
      @_LiveRSL____CTypes__i_Compile.@CVotes @_24935_votes_k = new @_LiveRSL____CTypes__i_Compile.@CVotes();
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24936_newMinVotedOpn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      if ((((@acceptor).@dtor_logTruncationPoint).@dtor_n) <= (((@inMsg).@dtor_opn__2a).@dtor_n))
      {
        @_LiveRSL____CTypes__i_Compile.@CVotes _out183;
        @_LiveRSL____CTypes__i_Compile.@COperationNumber _out184;
        @_LiveRSL____AcceptorModel__i_Compile.@__default.@AddVoteAndRemoveOldOnesImpl(@acceptor, (@acceptor).@dtor_votes, @_24932_opn, @_24934_newVote, @_24929_newLogTruncationPoint, (@acceptor).@dtor_minVotedOpn, out _out183, out _out184);
        @_24935_votes_k = _out183;
        @_24936_newMinVotedOpn = _out184;
      }
      else
      {
        @_24935_votes_k = (@acceptor).@dtor_votes;
        @_24936_newMinVotedOpn = (@acceptor).@dtor_minVotedOpn;
      }
      @_LiveRSL____CMessage__i_Compile.@CMessage @_24937_outMsg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
      @_24937_outMsg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__2b(@_24927_ballot, @_24932_opn, @_24933_value));
      @acceptor_k = Dafny.Helpers.Let<@_LiveRSL____AcceptorState__i_Compile.@AcceptorState,@_LiveRSL____AcceptorState__i_Compile.@AcceptorState>(@acceptor, _pat_let21_0 => Dafny.Helpers.Let<@_LiveRSL____AcceptorState__i_Compile.@AcceptorState,@_LiveRSL____AcceptorState__i_Compile.@AcceptorState>(_pat_let21_0, @_24938_dt__update__tmp_h3 => new _LiveRSL____AcceptorState__i_Compile.@AcceptorState(new _LiveRSL____AcceptorState__i_Compile.@AcceptorState_AcceptorState((@_24938_dt__update__tmp_h3).@dtor_constants, @_24927_ballot, @_24935_votes_k, (@_24938_dt__update__tmp_h3).@dtor_lastCheckpointedOperation, @_24929_newLogTruncationPoint, @_24936_newMinVotedOpn))));
      @_LiveRSL____CMessage__i_Compile.@CBroadcast _out185;
      @_Impl____LiveRSL____Broadcast__i_Compile.@__default.@BuildBroadcastToEveryone((((@acceptor).@dtor_constants).@dtor_all).@dtor_config, ((@acceptor).@dtor_constants).@dtor_myIndex, @_24937_outMsg, out _out185);
      @packetsSent = _out185;
      { }
      ulong @_24939_end__time = 0;
      ulong _out186;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out186);
      @_24939_end__time = _out186;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("NextAcceptorState_Phase2"), @_24926_start__time, @_24939_end__time);
    }
    public static void @NextAcceptorState__ProcessHeartbeat(@_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor, @_LiveRSL____CMessage__i_Compile.@CMessage @inMsg, @_Native____Io__s_Compile.@EndPoint @sender, out @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor_k)
    {
      @acceptor_k = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
    TAIL_CALL_START: ;
      @acceptor_k = @acceptor;
      { }
      { }
      { }
      bool @_24940_found = false;
      ulong @_24941_index = 0;
      bool _out187;
      ulong _out188;
      @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@__default.@CGetReplicaIndex(@sender, (((@acceptor).@dtor_constants).@dtor_all).@dtor_config, out _out187, out _out188);
      @_24940_found = _out187;
      @_24941_index = _out188;
      if (!(@_24940_found))
      {
        return;
      }
      { }
      if ((((@inMsg).@dtor_opn__ckpt).@dtor_n) <= ((((@acceptor).@dtor_lastCheckpointedOperation).Select(@_24941_index)).@dtor_n))
      {
        return;
      }
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> @_24942_LCO = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber>.Empty;
      @_24942_LCO = (@acceptor).@dtor_lastCheckpointedOperation;
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber> @_24943_newLCO = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@COperationNumber>.Empty;
      @_24943_newLCO = ((@acceptor).@dtor_lastCheckpointedOperation).Update(new BigInteger(@_24941_index), (@inMsg).@dtor_opn__ckpt);
      @acceptor_k = Dafny.Helpers.Let<@_LiveRSL____AcceptorState__i_Compile.@AcceptorState,@_LiveRSL____AcceptorState__i_Compile.@AcceptorState>(@acceptor, _pat_let22_0 => Dafny.Helpers.Let<@_LiveRSL____AcceptorState__i_Compile.@AcceptorState,@_LiveRSL____AcceptorState__i_Compile.@AcceptorState>(_pat_let22_0, @_24944_dt__update__tmp_h0 => new _LiveRSL____AcceptorState__i_Compile.@AcceptorState(new _LiveRSL____AcceptorState__i_Compile.@AcceptorState_AcceptorState((@_24944_dt__update__tmp_h0).@dtor_constants, (@_24944_dt__update__tmp_h0).@dtor_maxBallot, (@_24944_dt__update__tmp_h0).@dtor_votes, @_24943_newLCO, (@_24944_dt__update__tmp_h0).@dtor_logTruncationPoint, (@_24944_dt__update__tmp_h0).@dtor_minVotedOpn))));
    }
    public static void @NextAcceptorState__TruncateLog(@_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn, out @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor_k)
    {
      @acceptor_k = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
    TAIL_CALL_START: ;
      if (((@opn).@dtor_n) > (((@acceptor).@dtor_logTruncationPoint).@dtor_n))
      {
        { }
        { }
        Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote> @_24945_truncatedVotes = Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.Empty;
        @_24945_truncatedVotes = ((Dafny.Helpers.MapComprehensionDelegate<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>)delegate() { var _coll = new System.Collections.Generic.List<Dafny.Pair<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>>(); foreach (var @_24946_op in (((@acceptor).@dtor_votes).@dtor_v).Domain) { if (((((@acceptor).@dtor_votes).@dtor_v).Contains(@_24946_op)) && (((@_24946_op).@dtor_n) >= ((@opn).@dtor_n))) { _coll.Add(new Dafny.Pair<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>(@_24946_op,(((@acceptor).@dtor_votes).@dtor_v).Select(@_24946_op))); }}return Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____CTypes__i_Compile.@CVote>.FromCollection(_coll); })();
        @acceptor_k = Dafny.Helpers.Let<@_LiveRSL____AcceptorState__i_Compile.@AcceptorState,@_LiveRSL____AcceptorState__i_Compile.@AcceptorState>(@acceptor, _pat_let23_0 => Dafny.Helpers.Let<@_LiveRSL____AcceptorState__i_Compile.@AcceptorState,@_LiveRSL____AcceptorState__i_Compile.@AcceptorState>(_pat_let23_0, @_24947_dt__update__tmp_h1 => new _LiveRSL____AcceptorState__i_Compile.@AcceptorState(new _LiveRSL____AcceptorState__i_Compile.@AcceptorState_AcceptorState((@_24947_dt__update__tmp_h1).@dtor_constants, (@_24947_dt__update__tmp_h1).@dtor_maxBallot, Dafny.Helpers.Let<@_LiveRSL____CTypes__i_Compile.@CVotes,@_LiveRSL____CTypes__i_Compile.@CVotes>((@acceptor).@dtor_votes, _pat_let24_0 => Dafny.Helpers.Let<@_LiveRSL____CTypes__i_Compile.@CVotes,@_LiveRSL____CTypes__i_Compile.@CVotes>(_pat_let24_0, @_24948_dt__update__tmp_h2 => new _LiveRSL____CTypes__i_Compile.@CVotes(new _LiveRSL____CTypes__i_Compile.@CVotes_CVotes(@_24945_truncatedVotes)))), (@_24947_dt__update__tmp_h1).@dtor_lastCheckpointedOperation, @opn, (@_24947_dt__update__tmp_h1).@dtor_minVotedOpn))));
        { }
        { }
        { }
      }
      else
      {
        @acceptor_k = @acceptor;
      }
    }
    public static void @AcceptorModel__GetNthHighestValueAmongReportedCheckpoints(@_LiveRSL____AcceptorState__i_Compile.@AcceptorState @acceptor, ulong @minQuorumSize, out @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn)
    {
      @opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
    TAIL_CALL_START: ;
      @_LiveRSL____CTypes__i_Compile.@COperationNumber _out189;
      @_LiveRSL____CLastCheckpointedMap__i_Compile.@__default.@ComputeNthHighestValue((@acceptor).@dtor_lastCheckpointedOperation, @minQuorumSize, out _out189);
      @opn = _out189;
    }
  }
} // end of namespace _LiveRSL____AcceptorModel__i_Compile
namespace @_LiveRSL____LearnerModel__i_Compile {



  public partial class @__default {
    public static void @LearnerModel__Process2b(@_LiveRSL____LearnerState__i_Compile.@CLearnerState @learner, @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @executor, @_LiveRSL____CMessage__i_Compile.@CPacket @packet, out @_LiveRSL____LearnerState__i_Compile.@CLearnerState @learner_k)
    {
      @learner_k = new @_LiveRSL____LearnerState__i_Compile.@CLearnerState();
    TAIL_CALL_START: ;
      { }
      { }
      @_LiveRSL____CMessage__i_Compile.@CMessage @_24949_msg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
      @_24949_msg = (@packet).@dtor_msg;
      @_Native____Io__s_Compile.@EndPoint @_24950_src = new @_Native____Io__s_Compile.@EndPoint();
      @_24950_src = (@packet).@dtor_src;
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24951_opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_24951_opn = (@_24949_msg).@dtor_opn__2b;
      bool @_24952_isBalLt1 = false;
      bool _out190;
      @_LiveRSL____CTypes__i_Compile.@__default.@CBalLt((@_24949_msg).@dtor_bal__2b, (@learner).@dtor_maxBallotSeen, out _out190);
      @_24952_isBalLt1 = _out190;
      bool @_24953_isBalLt2 = false;
      bool _out191;
      @_LiveRSL____CTypes__i_Compile.@__default.@CBalLt((@learner).@dtor_maxBallotSeen, (@_24949_msg).@dtor_bal__2b, out _out191);
      @_24953_isBalLt2 = _out191;
      bool @_24954_srcIsReplica = false;
      @_24954_srcIsReplica = (((((@learner).@dtor_rcs).@dtor_all).@dtor_config).@dtor_replicaIds).Contains(@_24950_src);
      { }
      { }
      { }
      { }
      { }
      { }
      if ((!(@_24954_srcIsReplica)) || (@_24952_isBalLt1))
      {
        @learner_k = @learner;
      }
      else
      if (@_24953_isBalLt2)
      {
        @_LiveRSL____LearnerState__i_Compile.@CLearnerTuple @_24955_tup_k = new @_LiveRSL____LearnerState__i_Compile.@CLearnerTuple();
        @_24955_tup_k = new _LiveRSL____LearnerState__i_Compile.@CLearnerTuple(new _LiveRSL____LearnerState__i_Compile.@CLearnerTuple_CLearnerTuple(Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.FromElements((@packet).@dtor_src), (@_24949_msg).@dtor_val__2b));
        @learner_k = Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(@learner, _pat_let25_0 => Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(_pat_let25_0, @_24956_dt__update__tmp_h2 => new _LiveRSL____LearnerState__i_Compile.@CLearnerState(new _LiveRSL____LearnerState__i_Compile.@CLearnerState_CLearnerState((@_24956_dt__update__tmp_h2).@dtor_rcs, (@_24949_msg).@dtor_bal__2b, Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>.FromElements(new Dafny.Pair<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>(@_24951_opn,@_24955_tup_k)), (@_24956_dt__update__tmp_h2).@dtor_sendDecision, (@_24956_dt__update__tmp_h2).@dtor_opn, (@_24956_dt__update__tmp_h2).@dtor_recv2b, (@_24956_dt__update__tmp_h2).@dtor_recvCp))));
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
      }
      else
      if (!((@learner).@dtor_unexecutedOps).Contains(@_24951_opn))
      {
        { }
        @_LiveRSL____LearnerState__i_Compile.@CLearnerTuple @_24957_tup_k = new @_LiveRSL____LearnerState__i_Compile.@CLearnerTuple();
        @_24957_tup_k = new _LiveRSL____LearnerState__i_Compile.@CLearnerTuple(new _LiveRSL____LearnerState__i_Compile.@CLearnerTuple_CLearnerTuple(Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.FromElements((@packet).@dtor_src), (@_24949_msg).@dtor_val__2b));
        @learner_k = Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(@learner, _pat_let26_0 => Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(_pat_let26_0, @_24958_dt__update__tmp_h7 => new _LiveRSL____LearnerState__i_Compile.@CLearnerState(new _LiveRSL____LearnerState__i_Compile.@CLearnerState_CLearnerState((@_24958_dt__update__tmp_h7).@dtor_rcs, (@_24958_dt__update__tmp_h7).@dtor_maxBallotSeen, ((@learner).@dtor_unexecutedOps).Update(@_24951_opn, @_24957_tup_k), (@_24958_dt__update__tmp_h7).@dtor_sendDecision, (@_24958_dt__update__tmp_h7).@dtor_opn, (@_24958_dt__update__tmp_h7).@dtor_recv2b, (@_24958_dt__update__tmp_h7).@dtor_recvCp))));
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
      }
      else
      if (((((@learner).@dtor_unexecutedOps).Select(@_24951_opn)).@dtor_received2bMessageSenders).Contains((@packet).@dtor_src))
      {
        @learner_k = @learner;
      }
      else
      {
        @_LiveRSL____LearnerState__i_Compile.@CLearnerTuple @_24959_tup = new @_LiveRSL____LearnerState__i_Compile.@CLearnerTuple();
        @_24959_tup = ((@learner).@dtor_unexecutedOps).Select(@_24951_opn);
        @_LiveRSL____LearnerState__i_Compile.@CLearnerTuple @_24960_tup_k = new @_LiveRSL____LearnerState__i_Compile.@CLearnerTuple();
        @_24960_tup_k = Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>(@_24959_tup, _pat_let27_0 => Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>(_pat_let27_0, @_24961_dt__update__tmp_h10 => new _LiveRSL____LearnerState__i_Compile.@CLearnerTuple(new _LiveRSL____LearnerState__i_Compile.@CLearnerTuple_CLearnerTuple(((@_24959_tup).@dtor_received2bMessageSenders).@Concat(Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.FromElements((@packet).@dtor_src)), (@_24961_dt__update__tmp_h10).@dtor_candidateLearnedValue))));
        @learner_k = Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(@learner, _pat_let28_0 => Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(_pat_let28_0, @_24962_dt__update__tmp_h12 => new _LiveRSL____LearnerState__i_Compile.@CLearnerState(new _LiveRSL____LearnerState__i_Compile.@CLearnerState_CLearnerState((@_24962_dt__update__tmp_h12).@dtor_rcs, (@_24962_dt__update__tmp_h12).@dtor_maxBallotSeen, ((@learner).@dtor_unexecutedOps).Update(@_24951_opn, @_24960_tup_k), (@_24962_dt__update__tmp_h12).@dtor_sendDecision, (@_24962_dt__update__tmp_h12).@dtor_opn, (@_24962_dt__update__tmp_h12).@dtor_recv2b, (@_24962_dt__update__tmp_h12).@dtor_recvCp))));
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        { }
      }
    }
    public static void @LearnerModel__ForgetDecision(@_LiveRSL____LearnerState__i_Compile.@CLearnerState @learner, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opn, out @_LiveRSL____LearnerState__i_Compile.@CLearnerState @learner_k)
    {
      @learner_k = new @_LiveRSL____LearnerState__i_Compile.@CLearnerState();
    TAIL_CALL_START: ;
      { }
      if (((@learner).@dtor_unexecutedOps).Contains(@opn))
      {
        @learner_k = Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(@learner, _pat_let29_0 => Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(_pat_let29_0, @_24963_dt__update__tmp_h0 => new _LiveRSL____LearnerState__i_Compile.@CLearnerState(new _LiveRSL____LearnerState__i_Compile.@CLearnerState_CLearnerState((@_24963_dt__update__tmp_h0).@dtor_rcs, (@_24963_dt__update__tmp_h0).@dtor_maxBallotSeen, @_Collections____Maps__i_Compile.@__default.@RemoveElt<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>((@learner).@dtor_unexecutedOps, @opn), (@_24963_dt__update__tmp_h0).@dtor_sendDecision, (@_24963_dt__update__tmp_h0).@dtor_opn, (@_24963_dt__update__tmp_h0).@dtor_recv2b, (@_24963_dt__update__tmp_h0).@dtor_recvCp))));
        { }
        { }
      }
      else
      {
        @learner_k = @learner;
      }
    }
    public static void @LearnerModel__ForgetOperationsBefore(@_LiveRSL____LearnerState__i_Compile.@CLearnerState @learner, @_LiveRSL____CTypes__i_Compile.@COperationNumber @opsComplete, out @_LiveRSL____LearnerState__i_Compile.@CLearnerState @learner_k)
    {
      @learner_k = new @_LiveRSL____LearnerState__i_Compile.@CLearnerState();
    TAIL_CALL_START: ;
      Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple> @_24964_unexecutedOps_k = Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>.Empty;
      @_24964_unexecutedOps_k = ((Dafny.Helpers.MapComprehensionDelegate<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>)delegate() { var _coll = new System.Collections.Generic.List<Dafny.Pair<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>>(); foreach (var @_24965_op in ((@learner).@dtor_unexecutedOps).Domain) { if ((((@learner).@dtor_unexecutedOps).Contains(@_24965_op)) && (((@_24965_op).@dtor_n) >= ((@opsComplete).@dtor_n))) { _coll.Add(new Dafny.Pair<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>(@_24965_op,((@learner).@dtor_unexecutedOps).Select(@_24965_op))); }}return Dafny.Map<@_LiveRSL____CTypes__i_Compile.@COperationNumber,@_LiveRSL____LearnerState__i_Compile.@CLearnerTuple>.FromCollection(_coll); })();
      @learner_k = Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(@learner, _pat_let30_0 => Dafny.Helpers.Let<@_LiveRSL____LearnerState__i_Compile.@CLearnerState,@_LiveRSL____LearnerState__i_Compile.@CLearnerState>(_pat_let30_0, @_24966_dt__update__tmp_h0 => new _LiveRSL____LearnerState__i_Compile.@CLearnerState(new _LiveRSL____LearnerState__i_Compile.@CLearnerState_CLearnerState((@_24966_dt__update__tmp_h0).@dtor_rcs, (@_24966_dt__update__tmp_h0).@dtor_maxBallotSeen, @_24964_unexecutedOps_k, (@_24966_dt__update__tmp_h0).@dtor_sendDecision, (@_24966_dt__update__tmp_h0).@dtor_opn, (@_24966_dt__update__tmp_h0).@dtor_recv2b, (@_24966_dt__update__tmp_h0).@dtor_recvCp))));
      { }
    }
  }
} // end of namespace _LiveRSL____LearnerModel__i_Compile
namespace @_LiveRSL____ExecutorModel__i_Compile {




  public partial class @__default {
    public static void @HandleRequestBatchImpl(ulong @state, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @batch, Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @replyCache, out Dafny.Sequence<ulong> @states, out Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply> @replies, out Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @newReplyCache)
    {
      @states = Dafny.Sequence<ulong>.Empty;
      @replies = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply>.Empty;
      @newReplyCache = Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>.Empty;
      { }
      { }
      { }
      BigInteger @_24967_i = BigInteger.Zero;
      @_24967_i = new BigInteger(0);
      @states = Dafny.Sequence<ulong>.FromElements(@state);
      @replies = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply>.FromElements();
      @newReplyCache = @replyCache;
      while ((@_24967_i) < (new BigInteger((@batch).Length)))
      {
        Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply> @_24968_old__replies = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply>.Empty;
        @_24968_old__replies = @replies;
        Dafny.Sequence<ulong> @_24969_old__states = Dafny.Sequence<ulong>.Empty;
        @_24969_old__states = @states;
        Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @_24970_old__newReplyCache = Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>.Empty;
        @_24970_old__newReplyCache = @newReplyCache;
        ulong @_24971_new__state = 0;
        @_LiveRSL____AppInterface__i_Compile.@CAppMessage @_24972_reply = new @_LiveRSL____AppInterface__i_Compile.@CAppMessage();
        ulong _out192;
        @_LiveRSL____AppInterface__i_Compile.@CAppMessage _out193;
        @_LiveRSL____AppInterface__i_Compile.@__default.@HandleAppRequest((@states).Select(@_24967_i), ((@batch).Select(@_24967_i)).@dtor_request, out _out192, out _out193);
        @_24971_new__state = _out192;
        @_24972_reply = _out193;
        @_LiveRSL____CTypes__i_Compile.@CReply @_24973_newReply = new @_LiveRSL____CTypes__i_Compile.@CReply();
        @_24973_newReply = new _LiveRSL____CTypes__i_Compile.@CReply(new _LiveRSL____CTypes__i_Compile.@CReply_CReply(((@batch).Select(@_24967_i)).@dtor_client, ((@batch).Select(@_24967_i)).@dtor_seqno, @_24972_reply));
        @replies = (@replies).@Concat(Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply>.FromElements(@_24973_newReply));
        @states = (@states).@Concat(Dafny.Sequence<ulong>.FromElements(@_24971_new__state));
        Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> _out194;
        @_LiveRSL____ExecutorModel__i_Compile.@__default.@UpdateReplyCache(@newReplyCache, ((@batch).Select(@_24967_i)).@dtor_client, @_24973_newReply, @_24972_reply, @_24967_i, @batch, @replies, @states, out _out194);
        @newReplyCache = _out194;
        @_24967_i = (@_24967_i) + (new BigInteger(1));
        { }
        { }
        { }
      }
      { }
      { }
    }
    public static void @UpdateReplyCache(Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @replyCache, @_Native____Io__s_Compile.@EndPoint @ep, @_LiveRSL____CTypes__i_Compile.@CReply @newReply, @_LiveRSL____AppInterface__i_Compile.@CAppMessage @reply, BigInteger @i, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @batch, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply> @replies, Dafny.Sequence<ulong> @states, out Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @newReplyCache)
    {
      @newReplyCache = Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>.Empty;
      { }
      Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @_24974_slimReplyCache = Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>.Empty;
      @_Native____Io__s_Compile.@EndPoint @_24975_staleEntry = new @_Native____Io__s_Compile.@EndPoint();
      if ((new BigInteger((@replyCache).Length)).@Equals((BigInteger.Parse("4294967296")) - (new BigInteger(1))))
      {
        foreach (var _assign_such_that_11 in (@replyCache).Domain) { @_24975_staleEntry = _assign_such_that_11;
          if ((@replyCache).Contains(@_24975_staleEntry)) {
            goto _ASSIGN_SUCH_THAT_11;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 18202)");
        _ASSIGN_SUCH_THAT_11: ;
        @_24974_slimReplyCache = @_Collections____Maps__i_Compile.@__default.@RemoveElt<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>(@replyCache, @_24975_staleEntry);
      }
      else
      {
        @_24974_slimReplyCache = @replyCache;
      }
      { }
      { }
      @newReplyCache = (@_24974_slimReplyCache).Update(@ep, @newReply);
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @ExecutorInit(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @ccons, out @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs)
    {
      @cs = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
    TAIL_CALL_START: ;
      { }
      { }
      ulong @_24976_app__state = 0;
      ulong _out195;
      @_LiveRSL____AppInterface__i_Compile.@__default.@CAppState__Init(out _out195);
      @_24976_app__state = _out195;
      @cs = new _LiveRSL____ExecutorState__i_Compile.@ExecutorState(new _LiveRSL____ExecutorState__i_Compile.@ExecutorState_ExecutorState(@ccons, @_24976_app__state, new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber(0UL)), new _LiveRSL____CTypes__i_Compile.@CBallot(new _LiveRSL____CTypes__i_Compile.@CBallot_CBallot(0UL, 0UL)), new _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation(new _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation_COutstandingOpUnknown()), Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>.FromElements()));
      { }
      { }
    }
    public static void @ExecutorGetDecision(@_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs, @_LiveRSL____CTypes__i_Compile.@CBallot @cbal, @_LiveRSL____CTypes__i_Compile.@COperationNumber @copn, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @ca, out @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs_k)
    {
      @cs_k = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
    TAIL_CALL_START: ;
      { }
      { }
      { }
      { }
      { }
      @cs_k = Dafny.Helpers.Let<@_LiveRSL____ExecutorState__i_Compile.@ExecutorState,@_LiveRSL____ExecutorState__i_Compile.@ExecutorState>(@cs, _pat_let31_0 => Dafny.Helpers.Let<@_LiveRSL____ExecutorState__i_Compile.@ExecutorState,@_LiveRSL____ExecutorState__i_Compile.@ExecutorState>(_pat_let31_0, @_24977_dt__update__tmp_h3 => new _LiveRSL____ExecutorState__i_Compile.@ExecutorState(new _LiveRSL____ExecutorState__i_Compile.@ExecutorState_ExecutorState((@_24977_dt__update__tmp_h3).@dtor_constants, (@_24977_dt__update__tmp_h3).@dtor_app, (@_24977_dt__update__tmp_h3).@dtor_opsComplete, (@_24977_dt__update__tmp_h3).@dtor_maxBalReflected, new _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation(new _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation_COutstandingOpKnown(@ca, @cbal)), (@_24977_dt__update__tmp_h3).@dtor_replyCache))));
      { }
    }
    public static void @GetPacketsFromRepliesImpl(@_Native____Io__s_Compile.@EndPoint @me, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @requests, Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply> @replies, out Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> @cout)
    {
      @cout = Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket>.Empty;
      if ((new BigInteger((@requests).Length)).@Equals(new BigInteger(0)))
      {
        @cout = Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements();
      }
      else
      {
        { }
        { }
        { }
        Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> @_24978_rest = Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket>.Empty;
        Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> _out196;
        @_LiveRSL____ExecutorModel__i_Compile.@__default.@GetPacketsFromRepliesImpl(@me, (@requests).Drop(new BigInteger(1)), (@replies).Drop(new BigInteger(1)), out _out196);
        @_24978_rest = _out196;
        { }
        @_LiveRSL____CMessage__i_Compile.@CMessage @_24979_cmsg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
        @_24979_cmsg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Reply(((@requests).Select(new BigInteger(0))).@dtor_seqno, ((@replies).Select(new BigInteger(0))).@dtor_reply));
        { }
        @_LiveRSL____CMessage__i_Compile.@CPacket @_24980_cp = new @_LiveRSL____CMessage__i_Compile.@CPacket();
        @_24980_cp = new _LiveRSL____CMessage__i_Compile.@CPacket(new _LiveRSL____CMessage__i_Compile.@CPacket_CPacket(((@requests).Select(new BigInteger(0))).@dtor_client, @me, @_24979_cmsg));
        { }
        { }
        { }
        { }
        { }
        { }
        { }
        @cout = (Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket>.FromElements(@_24980_cp)).@Concat(@_24978_rest);
        { }
        { }
        { }
        { }
        { }
        { }
      }
    }
    public static void @ExecutorExecute(@_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs, out @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @cout)
    {
      @cs_k = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
      @cout = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_24981_cv = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
      @_24981_cv = ((@cs).@dtor_nextOpToExecute).@dtor_v;
      { }
      { }
      { }
      { }
      { }
      { }
      Dafny.Sequence<ulong> @_24982_cstates = Dafny.Sequence<ulong>.Empty;
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply> @_24983_creplies = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply>.Empty;
      Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> @_24984_newReplyCache = Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply>.Empty;
      { }
      ulong @_24985_start__time__request__batch = 0;
      ulong _out197;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out197);
      @_24985_start__time__request__batch = _out197;
      Dafny.Sequence<ulong> _out198;
      Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CReply> _out199;
      Dafny.Map<@_Native____Io__s_Compile.@EndPoint,@_LiveRSL____CTypes__i_Compile.@CReply> _out200;
      @_LiveRSL____ExecutorModel__i_Compile.@__default.@HandleRequestBatchImpl((@cs).@dtor_app, @_24981_cv, (@cs).@dtor_replyCache, out _out198, out _out199, out _out200);
      @_24982_cstates = _out198;
      @_24983_creplies = _out199;
      @_24984_newReplyCache = _out200;
      ulong @_24986_end__time__request__batch = 0;
      ulong _out201;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out201);
      @_24986_end__time__request__batch = _out201;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ExecutorExecute_HandleRequestBatch"), @_24985_start__time__request__batch, @_24986_end__time__request__batch);
      { }
      { }
      { }
      { }
      { }
      @_LiveRSL____CTypes__i_Compile.@CBallot @_24987_newMaxBalReflected = new @_LiveRSL____CTypes__i_Compile.@CBallot();
      @_24987_newMaxBalReflected = (@_LiveRSL____CTypes__i_Compile.@__default.@CBallot__IsNotGreaterThan((@cs).@dtor_maxBalReflected, ((@cs).@dtor_nextOpToExecute).@dtor_bal)) ? (((@cs).@dtor_nextOpToExecute).@dtor_bal) : ((@cs).@dtor_maxBalReflected);
      @cs_k = Dafny.Helpers.Let<@_LiveRSL____ExecutorState__i_Compile.@ExecutorState,@_LiveRSL____ExecutorState__i_Compile.@ExecutorState>(@cs, _pat_let32_0 => Dafny.Helpers.Let<@_LiveRSL____ExecutorState__i_Compile.@ExecutorState,@_LiveRSL____ExecutorState__i_Compile.@ExecutorState>(_pat_let32_0, @_24988_dt__update__tmp_h4 => new _LiveRSL____ExecutorState__i_Compile.@ExecutorState(new _LiveRSL____ExecutorState__i_Compile.@ExecutorState_ExecutorState((@_24988_dt__update__tmp_h4).@dtor_constants, (@_24982_cstates).Select((new BigInteger((@_24982_cstates).Length)) - (new BigInteger(1))), new _LiveRSL____CTypes__i_Compile.@COperationNumber(new _LiveRSL____CTypes__i_Compile.@COperationNumber_COperationNumber((((@cs).@dtor_opsComplete).@dtor_n) + (1UL))), @_24987_newMaxBalReflected, new _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation(new _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation_COutstandingOpUnknown()), @_24984_newReplyCache))));
      { }
      { }
      { }
      { }
      { }
      { }
      BigInteger @_24989_i = BigInteger.Zero;
      @_24989_i = (new BigInteger((@_24981_cv).Length)) - (new BigInteger(1));
      { }
      { }
      { }
      @_Native____Io__s_Compile.@EndPoint @_24990_cme = new @_Native____Io__s_Compile.@EndPoint();
      @_24990_cme = (((((@cs).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Select(((@cs).@dtor_constants).@dtor_myIndex);
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      ulong @_24991_start__time__get__packets = 0;
      ulong _out202;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out202);
      @_24991_start__time__get__packets = _out202;
      Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> @_24992_packets = Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket>.Empty;
      Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> _out203;
      @_LiveRSL____ExecutorModel__i_Compile.@__default.@GetPacketsFromRepliesImpl(@_24990_cme, @_24981_cv, @_24983_creplies, out _out203);
      @_24992_packets = _out203;
      @cout = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_PacketSequence(@_24992_packets));
      ulong @_24993_end__time__get__packets = 0;
      ulong _out204;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out204);
      @_24993_end__time__get__packets = _out204;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ExecutorExecute_GetPackets"), @_24991_start__time__get__packets, @_24993_end__time__get__packets);
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static void @ExecutorProcessAppStateSupply(@_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs, @_LiveRSL____CMessage__i_Compile.@CPacket @cinp, out @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs_k)
    {
      @cs_k = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
    TAIL_CALL_START: ;
      { }
      { }
      { }
      { }
      @_LiveRSL____CMessage__i_Compile.@CMessage @_24994_cm = new @_LiveRSL____CMessage__i_Compile.@CMessage();
      @_24994_cm = (@cinp).@dtor_msg;
      @cs_k = Dafny.Helpers.Let<@_LiveRSL____ExecutorState__i_Compile.@ExecutorState,@_LiveRSL____ExecutorState__i_Compile.@ExecutorState>(@cs, _pat_let33_0 => Dafny.Helpers.Let<@_LiveRSL____ExecutorState__i_Compile.@ExecutorState,@_LiveRSL____ExecutorState__i_Compile.@ExecutorState>(_pat_let33_0, @_24995_dt__update__tmp_h9 => new _LiveRSL____ExecutorState__i_Compile.@ExecutorState(new _LiveRSL____ExecutorState__i_Compile.@ExecutorState_ExecutorState((@_24995_dt__update__tmp_h9).@dtor_constants, (@_24994_cm).@dtor_app__state, (@_24994_cm).@dtor_opn__state__supply, (@_24994_cm).@dtor_bal__state__supply, new _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation(new _LiveRSL____ExecutorState__i_Compile.@COutstandingOperation_COutstandingOpUnknown()), (@_24994_cm).@dtor_reply__cache))));
      { }
    }
    public static void @ExecutorProcessAppStateRequest(@_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs, @_LiveRSL____CMessage__i_Compile.@CPacket @cinp, out @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @cout)
    {
      @cs_k = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
      @cout = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      { }
      { }
      { }
      { }
      { }
      @cs_k = @cs;
      { }
      { }
      { }
      if ((((((((@cs).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Contains((@cinp).@dtor_src)) && (@_LiveRSL____CTypes__i_Compile.@__default.@CBallot__IsNotGreaterThan((@cs).@dtor_maxBalReflected, ((@cinp).@dtor_msg).@dtor_bal__state__req))) && ((((@cs).@dtor_opsComplete).@dtor_n) >= ((((@cinp).@dtor_msg).@dtor_opn__state__req).@dtor_n)))
      {
        { }
        @_Native____Io__s_Compile.@EndPoint @_24996_cme = new @_Native____Io__s_Compile.@EndPoint();
        @_24996_cme = (((((@cs).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Select(((@cs).@dtor_constants).@dtor_myIndex);
        { }
        @cout = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_OutboundPacket(new _Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket>(new _Logic____Option__i_Compile.@Option_Some<@_LiveRSL____CMessage__i_Compile.@CPacket>(new _LiveRSL____CMessage__i_Compile.@CPacket(new _LiveRSL____CMessage__i_Compile.@CPacket_CPacket((@cinp).@dtor_src, @_24996_cme, new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__AppStateSupply((@cs).@dtor_maxBalReflected, (@cs).@dtor_opsComplete, (@cs).@dtor_app, (@cs).@dtor_replyCache))))))));
      }
      else
      {
        { }
        @cout = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_OutboundPacket(new _Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket>(new _Logic____Option__i_Compile.@Option_None<@_LiveRSL____CMessage__i_Compile.@CPacket>())));
      }
      { }
    }
    public static void @ExecutorProcessStartingPhase2(@_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs, @_LiveRSL____CMessage__i_Compile.@CPacket @cinp, out @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs_k, out @_LiveRSL____CMessage__i_Compile.@CBroadcast @cout)
    {
      @cs_k = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
      @cout = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
    TAIL_CALL_START: ;
      ulong @_24997_start__time = 0;
      ulong _out205;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out205);
      @_24997_start__time = _out205;
      { }
      { }
      { }
      { }
      { }
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_24998_copn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_24998_copn = ((@cinp).@dtor_msg).@dtor_logTruncationPoint__2;
      @cs_k = @cs;
      { }
      { }
      { }
      if (((((((@cs).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Contains((@cinp).@dtor_src)) && (((@_24998_copn).@dtor_n) > (((@cs).@dtor_opsComplete).@dtor_n)))
      {
        { }
        @_LiveRSL____CMessage__i_Compile.@CMessage @_24999_cmsg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
        @_24999_cmsg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__AppStateRequest(((@cinp).@dtor_msg).@dtor_bal__2, @_24998_copn));
        { }
        @_LiveRSL____CMessage__i_Compile.@CBroadcast _out206;
        @_Impl____LiveRSL____Broadcast__i_Compile.@__default.@BuildBroadcastToEveryone((((@cs).@dtor_constants).@dtor_all).@dtor_config, ((@cs).@dtor_constants).@dtor_myIndex, @_24999_cmsg, out _out206);
        @cout = _out206;
        ulong @_25000_end__time = 0;
        ulong _out207;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out207);
        @_25000_end__time = _out207;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ExecutorProcessStartingPhase2_request"), @_24997_start__time, @_25000_end__time);
      }
      else
      {
        { }
        @cout = new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop());
        ulong @_25001_end__time = 0;
        ulong _out208;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out208);
        @_25001_end__time = _out208;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("ExecutorProcessStartingPhase2_nada"), @_24997_start__time, @_25001_end__time);
      }
    }
    public static void @ExecutorProcessRequest(@_LiveRSL____ExecutorState__i_Compile.@ExecutorState @cs, @_LiveRSL____CMessage__i_Compile.@CPacket @cinp, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @cout)
    {
      @cout = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      { }
      { }
      { }
      { }
      if ((((@cinp).@dtor_msg).@dtor_seqno).@Equals((((@cs).@dtor_replyCache).Select((@cinp).@dtor_src)).@dtor_seqno))
      {
        @_LiveRSL____CTypes__i_Compile.@CReply @_25002_cr = new @_LiveRSL____CTypes__i_Compile.@CReply();
        @_25002_cr = ((@cs).@dtor_replyCache).Select((@cinp).@dtor_src);
        @_LiveRSL____CMessage__i_Compile.@CMessage @_25003_msg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
        @_25003_msg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Reply((@_25002_cr).@dtor_seqno, (@_25002_cr).@dtor_reply));
        @cout = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_OutboundPacket(new _Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket>(new _Logic____Option__i_Compile.@Option_Some<@_LiveRSL____CMessage__i_Compile.@CPacket>(new _LiveRSL____CMessage__i_Compile.@CPacket(new _LiveRSL____CMessage__i_Compile.@CPacket_CPacket((@_25002_cr).@dtor_client, (((((@cs).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Select(((@cs).@dtor_constants).@dtor_myIndex), @_25003_msg))))));
        { }
      }
      else
      {
        @cout = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_OutboundPacket(new _Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket>(new _Logic____Option__i_Compile.@Option_None<@_LiveRSL____CMessage__i_Compile.@CPacket>())));
      }
    }
  }
} // end of namespace _LiveRSL____ExecutorModel__i_Compile
namespace @_LiveRSL____PaxosAppPacketInv__s_Compile {


  public partial class @__default {
  }
} // end of namespace _LiveRSL____PaxosAppPacketInv__s_Compile
namespace @_LiveRSL____ReplicaModel__i_Compile {








  public partial class @__default {
    public static void @InitReplicaState(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica)
    {
      @replica = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
    TAIL_CALL_START: ;
      @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25004_proposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @_LiveRSL____ProposerState__i_Compile.@ProposerState _out209;
      @_LiveRSL____ProposerModel__i_Compile.@__default.@InitProposerState(@constants, out _out209);
      @_25004_proposer = _out209;
      @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @_25005_acceptor = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
      @_LiveRSL____AcceptorState__i_Compile.@AcceptorState _out210;
      @_LiveRSL____AcceptorModel__i_Compile.@__default.@InitAcceptorState(@constants, out _out210);
      @_25005_acceptor = _out210;
      @_LiveRSL____LearnerState__i_Compile.@CLearnerState @_25006_learner = new @_LiveRSL____LearnerState__i_Compile.@CLearnerState();
      @_LiveRSL____LearnerState__i_Compile.@CLearnerState _out211;
      @_LiveRSL____LearnerState__i_Compile.@__default.@LearnerState__Init(@constants, out _out211);
      @_25006_learner = _out211;
      @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @_25007_executor = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
      @_LiveRSL____ExecutorState__i_Compile.@ExecutorState _out212;
      @_LiveRSL____ExecutorModel__i_Compile.@__default.@ExecutorInit(@constants, out _out212);
      @_25007_executor = _out212;
      @replica = new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState(@constants, 0UL, 0UL, @_25004_proposer, @_25005_acceptor, @_25006_learner, @_25007_executor));
      { }
    }
    public static void @Replica__Next__Process__Request(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @inp, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25008_start__time = 0;
      ulong _out213;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out213);
      @_25008_start__time = _out213;
      { }
      { }
      { }
      { }
      ulong @_25009_afterCheck__time = 0;
      ulong _out214;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out214);
      @_25009_afterCheck__time = _out214;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_Request_checkIsCached"), @_25008_start__time, @_25009_afterCheck__time);
      if (!(((@replica).@dtor_executor).@dtor_replyCache).Contains((@inp).@dtor_src))
      {
        { }
        @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25010_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
        @_LiveRSL____ProposerState__i_Compile.@ProposerState _out215;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerProcessRequest((@replica).@dtor_proposer, @inp, out _out215);
        @_25010_newProposer = _out215;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let34_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let34_0, @_25011_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25011_dt__update__tmp_h0).@dtor_constants, (@_25011_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25011_dt__update__tmp_h0).@dtor_nextHeartbeatTime, @_25010_newProposer, (@_25011_dt__update__tmp_h0).@dtor_acceptor, (@_25011_dt__update__tmp_h0).@dtor_learner, (@_25011_dt__update__tmp_h0).@dtor_executor))));
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        { }
        ulong @_25012_notCachedTime = 0;
        ulong _out216;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out216);
        @_25012_notCachedTime = _out216;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_Request_isNotCached_ProposerProcessRequest"), @_25008_start__time, @_25012_notCachedTime);
        { }
        { }
      }
      else
      if (!(((((@replica).@dtor_executor).@dtor_replyCache).Select((@inp).@dtor_src)).@is_CReply))
      {
        { }
        @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25013_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
        @_LiveRSL____ProposerState__i_Compile.@ProposerState _out217;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerProcessRequest((@replica).@dtor_proposer, @inp, out _out217);
        @_25013_newProposer = _out217;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let35_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let35_0, @_25014_dt__update__tmp_h1 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25014_dt__update__tmp_h1).@dtor_constants, (@_25014_dt__update__tmp_h1).@dtor___nextActionIndex, (@_25014_dt__update__tmp_h1).@dtor_nextHeartbeatTime, @_25013_newProposer, (@_25014_dt__update__tmp_h1).@dtor_acceptor, (@_25014_dt__update__tmp_h1).@dtor_learner, (@_25014_dt__update__tmp_h1).@dtor_executor))));
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        { }
        ulong @_25015_notReplyTime = 0;
        ulong _out218;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out218);
        @_25015_notReplyTime = _out218;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_Request_isNotReply_ProposerProcessRequest"), @_25008_start__time, @_25015_notReplyTime);
        { }
      }
      else
      if ((((@inp).@dtor_msg).@dtor_seqno) > (((((@replica).@dtor_executor).@dtor_replyCache).Select((@inp).@dtor_src)).@dtor_seqno))
      {
        { }
        { }
        @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25016_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
        @_LiveRSL____ProposerState__i_Compile.@ProposerState _out219;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerProcessRequest((@replica).@dtor_proposer, @inp, out _out219);
        @_25016_newProposer = _out219;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let36_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let36_0, @_25017_dt__update__tmp_h2 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25017_dt__update__tmp_h2).@dtor_constants, (@_25017_dt__update__tmp_h2).@dtor___nextActionIndex, (@_25017_dt__update__tmp_h2).@dtor_nextHeartbeatTime, @_25016_newProposer, (@_25017_dt__update__tmp_h2).@dtor_acceptor, (@_25017_dt__update__tmp_h2).@dtor_learner, (@_25017_dt__update__tmp_h2).@dtor_executor))));
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        { }
        ulong @_25018_seqnoIsBeyondTime = 0;
        ulong _out220;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out220);
        @_25018_seqnoIsBeyondTime = _out220;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_Request_seqnoIsBeyond_ProposerProcessRequest"), @_25008_start__time, @_25018_seqnoIsBeyondTime);
        { }
        { }
      }
      else
      {
        { }
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out221;
        @_LiveRSL____ExecutorModel__i_Compile.@__default.@ExecutorProcessRequest((@replica).@dtor_executor, @inp, out _out221);
        @packetsSent = _out221;
        { }
        @replica_k = @replica;
        ulong @_25019_isCachedTime = 0;
        ulong _out222;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out222);
        @_25019_isCachedTime = _out222;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_Request_isCached_ExecutorProcessRequest"), @_25008_start__time, @_25019_isCachedTime);
        { }
      }
      { }
      ulong @_25020_end__time = 0;
      ulong _out223;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out223);
      @_25020_end__time = _out223;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_Request"), @_25008_start__time, @_25020_end__time);
    }
    public static void @Replica__Next__Process__1a(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @inp, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25021_start__time = 0;
      ulong _out224;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out224);
      @_25021_start__time = _out224;
      @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @_25022_newAcceptor = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
      @_LiveRSL____CMessage__i_Compile.@CBroadcast @_25023_packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
      @_LiveRSL____AcceptorState__i_Compile.@AcceptorState _out225;
      @_LiveRSL____CMessage__i_Compile.@CBroadcast _out226;
      @_LiveRSL____AcceptorModel__i_Compile.@__default.@NextAcceptorState__Phase1((@replica).@dtor_acceptor, (@inp).@dtor_msg, (@inp).@dtor_src, out _out225, out _out226);
      @_25022_newAcceptor = _out225;
      @_25023_packets = _out226;
      @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let37_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let37_0, @_25024_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25024_dt__update__tmp_h0).@dtor_constants, (@_25024_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25024_dt__update__tmp_h0).@dtor_nextHeartbeatTime, (@_25024_dt__update__tmp_h0).@dtor_proposer, @_25022_newAcceptor, (@_25024_dt__update__tmp_h0).@dtor_learner, (@_25024_dt__update__tmp_h0).@dtor_executor))));
      { }
      { }
      { }
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(@_25023_packets));
      ulong @_25025_end__time = 0;
      ulong _out227;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out227);
      @_25025_end__time = _out227;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_1a"), @_25021_start__time, @_25025_end__time);
    }
    public static void @ProposerSrcNotPresent(@_LiveRSL____ProposerState__i_Compile.@ProposerState @proposer, @_LiveRSL____CMessage__i_Compile.@CPacket @packet, out bool @b)
    {
      @b = false;
    TAIL_CALL_START: ;
      @b = Dafny.Helpers.QuantSet((@proposer).@dtor_received1bPackets, true, @_25026_other__packet => !(((@proposer).@dtor_received1bPackets).Contains(@_25026_other__packet)) || (!((@_25026_other__packet).@dtor_src).@Equals((@packet).@dtor_src)));
    }
    public static void @Replica__Next__Process__1b(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @inp, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25027_start__time = 0;
      ulong _out228;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out228);
      @_25027_start__time = _out228;
      { }
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
      bool @_25028_srcNotPresent = false;
      bool _out229;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@ProposerSrcNotPresent((@replica).@dtor_proposer, @inp, out _out229);
      @_25028_srcNotPresent = _out229;
      { }
      if ((((((((((@replica).@dtor_proposer).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Contains((@inp).@dtor_src)) && ((((@inp).@dtor_msg).@dtor_bal__1b).@Equals(((@replica).@dtor_proposer).@dtor_maxBallotISent1a))) && ((((@replica).@dtor_proposer).@dtor_currentState).@Equals(1))) && (@_25028_srcNotPresent))
      {
        @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25029_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
        @_LiveRSL____ProposerState__i_Compile.@ProposerState _out230;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerProcess1b((@replica).@dtor_proposer, @inp, out _out230);
        @_25029_newProposer = _out230;
        @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @_25030_newAcceptor = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
        @_LiveRSL____AcceptorState__i_Compile.@AcceptorState _out231;
        @_LiveRSL____AcceptorModel__i_Compile.@__default.@NextAcceptorState__TruncateLog((@replica).@dtor_acceptor, ((@inp).@dtor_msg).@dtor_logTruncationPoint, out _out231);
        @_25030_newAcceptor = _out231;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let38_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let38_0, @_25031_dt__update__tmp_h1 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25031_dt__update__tmp_h1).@dtor_constants, (@_25031_dt__update__tmp_h1).@dtor___nextActionIndex, (@_25031_dt__update__tmp_h1).@dtor_nextHeartbeatTime, @_25029_newProposer, @_25030_newAcceptor, (@_25031_dt__update__tmp_h1).@dtor_learner, (@_25031_dt__update__tmp_h1).@dtor_executor))));
        ulong @_25032_end__time = 0;
        ulong _out232;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out232);
        @_25032_end__time = _out232;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_1b_use"), @_25027_start__time, @_25032_end__time);
        { }
      }
      else
      {
        { }
        @replica_k = @replica;
        ulong @_25033_end__time = 0;
        ulong _out233;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out233);
        @_25033_end__time = _out233;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_1b_discard"), @_25027_start__time, @_25033_end__time);
      }
    }
    public static void @Replica__Next__Process__StartingPhase2(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @inp, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25034_start__time = 0;
      ulong _out234;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out234);
      @_25034_start__time = _out234;
      @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @_25035_newExecutor = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
      @_LiveRSL____CMessage__i_Compile.@CBroadcast @_25036_packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
      @_LiveRSL____ExecutorState__i_Compile.@ExecutorState _out235;
      @_LiveRSL____CMessage__i_Compile.@CBroadcast _out236;
      @_LiveRSL____ExecutorModel__i_Compile.@__default.@ExecutorProcessStartingPhase2((@replica).@dtor_executor, @inp, out _out235, out _out236);
      @_25035_newExecutor = _out235;
      @_25036_packets = _out236;
      @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let39_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let39_0, @_25037_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25037_dt__update__tmp_h0).@dtor_constants, (@_25037_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25037_dt__update__tmp_h0).@dtor_nextHeartbeatTime, (@_25037_dt__update__tmp_h0).@dtor_proposer, (@_25037_dt__update__tmp_h0).@dtor_acceptor, (@_25037_dt__update__tmp_h0).@dtor_learner, @_25035_newExecutor))));
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(@_25036_packets));
      ulong @_25038_end__time = 0;
      ulong _out237;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out237);
      @_25038_end__time = _out237;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_StartingPhase2"), @_25034_start__time, @_25038_end__time);
    }
    public static void @Replica__Next__Process__2a(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @inp, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25039_start__time = 0;
      ulong _out238;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out238);
      @_25039_start__time = _out238;
      { }
      bool @_25040_b1 = false;
      @_25040_b1 = ((((((@replica).@dtor_acceptor).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Contains((@inp).@dtor_src);
      bool @_25041_b2 = false;
      bool _out239;
      @_LiveRSL____CTypes__i_Compile.@__default.@CBalLeq(((@replica).@dtor_acceptor).@dtor_maxBallot, ((@inp).@dtor_msg).@dtor_bal__2a, out _out239);
      @_25041_b2 = _out239;
      if (((@_25040_b1) && (@_25041_b2)) && (((((@inp).@dtor_msg).@dtor_opn__2a).@dtor_n) <= ((((((@replica).@dtor_acceptor).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxIntegerVal)))
      {
        { }
        ulong @_25042_maxLogLengthMinus1 = 0;
        @_25042_maxLogLengthMinus1 = ((((((@replica).@dtor_acceptor).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxLogLength) - (1UL);
        ulong @_25043_newLogTruncationPoint = 0;
        @_25043_newLogTruncationPoint = (((@replica).@dtor_acceptor).@dtor_logTruncationPoint).@dtor_n;
        @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @_25044_newAcceptor = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
        @_LiveRSL____CMessage__i_Compile.@CBroadcast @_25045_packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
        @_LiveRSL____AcceptorState__i_Compile.@AcceptorState _out240;
        @_LiveRSL____CMessage__i_Compile.@CBroadcast _out241;
        @_LiveRSL____AcceptorModel__i_Compile.@__default.@NextAcceptorState__Phase2((@replica).@dtor_acceptor, (@inp).@dtor_msg, (@inp).@dtor_src, out _out240, out _out241);
        @_25044_newAcceptor = _out240;
        @_25045_packets = _out241;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let40_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let40_0, @_25046_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25046_dt__update__tmp_h0).@dtor_constants, (@_25046_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25046_dt__update__tmp_h0).@dtor_nextHeartbeatTime, (@_25046_dt__update__tmp_h0).@dtor_proposer, @_25044_newAcceptor, (@_25046_dt__update__tmp_h0).@dtor_learner, (@_25046_dt__update__tmp_h0).@dtor_executor))));
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(@_25045_packets));
        ulong @_25047_end__time = 0;
        ulong _out242;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out242);
        @_25047_end__time = _out242;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_2a_use"), @_25039_start__time, @_25047_end__time);
      }
      else
      {
        { }
        @replica_k = @replica;
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        ulong @_25048_end__time = 0;
        ulong _out243;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out243);
        @_25048_end__time = _out243;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_2a_discard"), @_25039_start__time, @_25048_end__time);
      }
    }
    public static void @Replica__Next__Process__2b(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @inp, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25049_start__time = 0;
      ulong _out244;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out244);
      @_25049_start__time = _out244;
      { }
      { }
      { }
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_25050_copn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_25050_copn = ((@inp).@dtor_msg).@dtor_opn__2b;
      bool @_25051_cop__learnable = false;
      @_25051_cop__learnable = (((((@replica).@dtor_executor).@dtor_opsComplete).@dtor_n) < ((@_25050_copn).@dtor_n)) || ((((((@replica).@dtor_executor).@dtor_opsComplete).@dtor_n).@Equals((@_25050_copn).@dtor_n)) && ((((@replica).@dtor_executor).@dtor_nextOpToExecute).@is_COutstandingOpUnknown));
      { }
      if (@_25051_cop__learnable)
      {
        @_LiveRSL____LearnerState__i_Compile.@CLearnerState @_25052_newLearner = new @_LiveRSL____LearnerState__i_Compile.@CLearnerState();
        @_LiveRSL____LearnerState__i_Compile.@CLearnerState _out245;
        @_LiveRSL____LearnerModel__i_Compile.@__default.@LearnerModel__Process2b((@replica).@dtor_learner, (@replica).@dtor_executor, @inp, out _out245);
        @_25052_newLearner = _out245;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let41_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let41_0, @_25053_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25053_dt__update__tmp_h0).@dtor_constants, (@_25053_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25053_dt__update__tmp_h0).@dtor_nextHeartbeatTime, (@_25053_dt__update__tmp_h0).@dtor_proposer, (@_25053_dt__update__tmp_h0).@dtor_acceptor, @_25052_newLearner, (@_25053_dt__update__tmp_h0).@dtor_executor))));
      }
      else
      {
        @replica_k = @replica;
      }
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
      ulong @_25054_end__time = 0;
      ulong _out246;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out246);
      @_25054_end__time = _out246;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_2b"), @_25049_start__time, @_25054_end__time);
    }
    public static void @Replica__Next__Spontaneous__MaybeEnterNewViewAndSend1a(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25055_start__time = 0;
      ulong _out247;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out247);
      @_25055_start__time = _out247;
      @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25056_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @_LiveRSL____CMessage__i_Compile.@CBroadcast @_25057_packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
      @_LiveRSL____ProposerState__i_Compile.@ProposerState _out248;
      @_LiveRSL____CMessage__i_Compile.@CBroadcast _out249;
      @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerMaybeEnterNewViewAndSend1a((@replica).@dtor_proposer, out _out248, out _out249);
      @_25056_newProposer = _out248;
      @_25057_packets = _out249;
      @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let42_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let42_0, @_25058_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25058_dt__update__tmp_h0).@dtor_constants, (@_25058_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25058_dt__update__tmp_h0).@dtor_nextHeartbeatTime, @_25056_newProposer, (@_25058_dt__update__tmp_h0).@dtor_acceptor, (@_25058_dt__update__tmp_h0).@dtor_learner, (@_25058_dt__update__tmp_h0).@dtor_executor))));
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(@_25057_packets));
      ulong @_25059_end__time = 0;
      ulong _out250;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out250);
      @_25059_end__time = _out250;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_MaybeEnterNewViewAndSend1a"), @_25055_start__time, @_25059_end__time);
    }
    public static void @Replica__Next__Spontaneous__MaybeEnterPhase2(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25060_start__time = 0;
      ulong _out251;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out251);
      @_25060_start__time = _out251;
      @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25061_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @_LiveRSL____CMessage__i_Compile.@CBroadcast @_25062_packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
      @_LiveRSL____ProposerState__i_Compile.@ProposerState _out252;
      @_LiveRSL____CMessage__i_Compile.@CBroadcast _out253;
      @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerMaybeEnterPhase2((@replica).@dtor_proposer, ((@replica).@dtor_acceptor).@dtor_logTruncationPoint, out _out252, out _out253);
      @_25061_newProposer = _out252;
      @_25062_packets = _out253;
      @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let43_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let43_0, @_25063_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25063_dt__update__tmp_h0).@dtor_constants, (@_25063_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25063_dt__update__tmp_h0).@dtor_nextHeartbeatTime, @_25061_newProposer, (@_25063_dt__update__tmp_h0).@dtor_acceptor, (@_25063_dt__update__tmp_h0).@dtor_learner, (@_25063_dt__update__tmp_h0).@dtor_executor))));
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(@_25062_packets));
      ulong @_25064_end__time = 0;
      ulong _out254;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out254);
      @_25064_end__time = _out254;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_MaybeEnterPhase2"), @_25060_start__time, @_25064_end__time);
    }
    public static void @Replica__Next__Spontaneous__MaybeNominateValueAndSend2a(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25065_start__time = 0;
      ulong _out255;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out255);
      @_25065_start__time = _out255;
      @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25066_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @_LiveRSL____CMessage__i_Compile.@CBroadcast @_25067_packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
      @_LiveRSL____ProposerState__i_Compile.@ProposerState _out256;
      @_LiveRSL____CMessage__i_Compile.@CBroadcast _out257;
      @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerMaybeNominateValueAndSend2a((@replica).@dtor_proposer, (@clock).@dtor_min, (@clock).@dtor_max, ((@replica).@dtor_acceptor).@dtor_logTruncationPoint, out _out256, out _out257);
      @_25066_newProposer = _out256;
      @_25067_packets = _out257;
      @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let44_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let44_0, @_25068_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25068_dt__update__tmp_h0).@dtor_constants, (@_25068_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25068_dt__update__tmp_h0).@dtor_nextHeartbeatTime, @_25066_newProposer, (@_25068_dt__update__tmp_h0).@dtor_acceptor, (@_25068_dt__update__tmp_h0).@dtor_learner, (@_25068_dt__update__tmp_h0).@dtor_executor))));
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(@_25067_packets));
      ulong @_25069_end__time = 0;
      ulong _out258;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out258);
      @_25069_end__time = _out258;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_MaybeNominateValueAndSend2a"), @_25065_start__time, @_25069_end__time);
    }
    public static void @Replica__Next__Process__AppStateRequest(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @inp, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25070_start__time = 0;
      ulong _out259;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out259);
      @_25070_start__time = _out259;
      @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @_25071_newExecutor = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets @_25072_packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
      @_LiveRSL____ExecutorState__i_Compile.@ExecutorState _out260;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out261;
      @_LiveRSL____ExecutorModel__i_Compile.@__default.@ExecutorProcessAppStateRequest((@replica).@dtor_executor, @inp, out _out260, out _out261);
      @_25071_newExecutor = _out260;
      @_25072_packets = _out261;
      @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let45_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let45_0, @_25073_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25073_dt__update__tmp_h0).@dtor_constants, (@_25073_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25073_dt__update__tmp_h0).@dtor_nextHeartbeatTime, (@_25073_dt__update__tmp_h0).@dtor_proposer, (@_25073_dt__update__tmp_h0).@dtor_acceptor, (@_25073_dt__update__tmp_h0).@dtor_learner, @_25071_newExecutor))));
      @packetsSent = @_25072_packets;
      ulong @_25074_end__time = 0;
      ulong _out262;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out262);
      @_25074_end__time = _out262;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_AppStateRequest"), @_25070_start__time, @_25074_end__time);
    }
    public static void @Replica__Next__Process__Heartbeat(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @inp, ulong @clock__min, ulong @clock__max, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25075_start__time = 0;
      ulong _out263;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out263);
      @_25075_start__time = _out263;
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
      { }
      @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25076_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @_LiveRSL____ProposerState__i_Compile.@ProposerState _out264;
      @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerProcessHeartbeat((@replica).@dtor_proposer, @inp, @clock__min, @clock__max, out _out264);
      @_25076_newProposer = _out264;
      @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @_25077_newAcceptor = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
      @_LiveRSL____AcceptorState__i_Compile.@AcceptorState _out265;
      @_LiveRSL____AcceptorModel__i_Compile.@__default.@NextAcceptorState__ProcessHeartbeat((@replica).@dtor_acceptor, (@inp).@dtor_msg, (@inp).@dtor_src, out _out265);
      @_25077_newAcceptor = _out265;
      @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let46_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let46_0, @_25078_dt__update__tmp_h1 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25078_dt__update__tmp_h1).@dtor_constants, (@_25078_dt__update__tmp_h1).@dtor___nextActionIndex, (@_25078_dt__update__tmp_h1).@dtor_nextHeartbeatTime, @_25076_newProposer, @_25077_newAcceptor, (@_25078_dt__update__tmp_h1).@dtor_learner, (@_25078_dt__update__tmp_h1).@dtor_executor))));
      ulong @_25079_end__time = 0;
      ulong _out266;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out266);
      @_25079_end__time = _out266;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_Heartbeat"), @_25075_start__time, @_25079_end__time);
    }
    public static void @Replica__Next__ReadClock__CheckForViewTimeout(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25080_start__time = 0;
      ulong _out267;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out267);
      @_25080_start__time = _out267;
      @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25081_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @_LiveRSL____ProposerState__i_Compile.@ProposerState _out268;
      @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerCheckForViewTimeout((@replica).@dtor_proposer, (@clock).@dtor_min, (@clock).@dtor_max, out _out268);
      @_25081_newProposer = _out268;
      @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let47_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let47_0, @_25082_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25082_dt__update__tmp_h0).@dtor_constants, (@_25082_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25082_dt__update__tmp_h0).@dtor_nextHeartbeatTime, @_25081_newProposer, (@_25082_dt__update__tmp_h0).@dtor_acceptor, (@_25082_dt__update__tmp_h0).@dtor_learner, (@_25082_dt__update__tmp_h0).@dtor_executor))));
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
      { }
      ulong @_25083_end__time = 0;
      ulong _out269;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out269);
      @_25083_end__time = _out269;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_ReadClock_CheckForViewTimeout"), @_25080_start__time, @_25083_end__time);
    }
    public static void @Replica__Next__ReadClock__CheckForQuorumOfViewSuspicions(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25084_start__time = 0;
      ulong _out270;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out270);
      @_25084_start__time = _out270;
      @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25085_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
      @_LiveRSL____ProposerState__i_Compile.@ProposerState _out271;
      @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerCheckForQuorumOfViewSuspicions((@replica).@dtor_proposer, (@clock).@dtor_min, (@clock).@dtor_max, out _out271);
      @_25085_newProposer = _out271;
      @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let48_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let48_0, @_25086_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25086_dt__update__tmp_h0).@dtor_constants, (@_25086_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25086_dt__update__tmp_h0).@dtor_nextHeartbeatTime, @_25085_newProposer, (@_25086_dt__update__tmp_h0).@dtor_acceptor, (@_25086_dt__update__tmp_h0).@dtor_learner, (@_25086_dt__update__tmp_h0).@dtor_executor))));
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
      { }
      ulong @_25087_end__time = 0;
      ulong _out272;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out272);
      @_25087_end__time = _out272;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_ReadClock_CheckForQuorumOfViewSuspicions"), @_25084_start__time, @_25087_end__time);
    }
    public static void @Replica__Next__Process__AppStateSupply(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @inp, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25088_start__time = 0;
      ulong _out273;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out273);
      @_25088_start__time = _out273;
      { }
      if ((((((((@replica).@dtor_executor).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Contains((@inp).@dtor_src)) && (((((@inp).@dtor_msg).@dtor_opn__state__supply).@dtor_n) > ((((@replica).@dtor_executor).@dtor_opsComplete).@dtor_n)))
      {
        @_LiveRSL____LearnerState__i_Compile.@CLearnerState @_25089_newLearner = new @_LiveRSL____LearnerState__i_Compile.@CLearnerState();
        @_LiveRSL____LearnerState__i_Compile.@CLearnerState _out274;
        @_LiveRSL____LearnerModel__i_Compile.@__default.@LearnerModel__ForgetOperationsBefore((@replica).@dtor_learner, ((@inp).@dtor_msg).@dtor_opn__state__supply, out _out274);
        @_25089_newLearner = _out274;
        @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @_25090_newExecutor = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
        @_LiveRSL____ExecutorState__i_Compile.@ExecutorState _out275;
        @_LiveRSL____ExecutorModel__i_Compile.@__default.@ExecutorProcessAppStateSupply((@replica).@dtor_executor, @inp, out _out275);
        @_25090_newExecutor = _out275;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let49_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let49_0, @_25091_dt__update__tmp_h1 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25091_dt__update__tmp_h1).@dtor_constants, (@_25091_dt__update__tmp_h1).@dtor___nextActionIndex, (@_25091_dt__update__tmp_h1).@dtor_nextHeartbeatTime, (@_25091_dt__update__tmp_h1).@dtor_proposer, (@_25091_dt__update__tmp_h1).@dtor_acceptor, @_25089_newLearner, @_25090_newExecutor))));
        ulong @_25092_end__time = 0;
        ulong _out276;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out276);
        @_25092_end__time = _out276;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_AppStateSupply_work"), @_25088_start__time, @_25092_end__time);
      }
      else
      {
        @replica_k = @replica;
        ulong @_25093_end__time = 0;
        ulong _out277;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out277);
        @_25093_end__time = _out277;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Process_AppStateSupply_nada"), @_25088_start__time, @_25093_end__time);
      }
      @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
    }
    public static void @Replica__Next__Spontaneous__MaybeExecute(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25094_start__time = 0;
      ulong _out278;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out278);
      @_25094_start__time = _out278;
      if (((((@replica).@dtor_executor).@dtor_nextOpToExecute).@is_COutstandingOpKnown) && (((((@replica).@dtor_executor).@dtor_opsComplete).@dtor_n) < ((((((@replica).@dtor_executor).@dtor_constants).@dtor_all).@dtor_params).@dtor_maxIntegerVal)))
      {
        Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_25095_val = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
        @_25095_val = (((@replica).@dtor_executor).@dtor_nextOpToExecute).@dtor_v;
        @_LiveRSL____ProposerState__i_Compile.@ProposerState @_25096_newProposer = new @_LiveRSL____ProposerState__i_Compile.@ProposerState();
        @_LiveRSL____ProposerState__i_Compile.@ProposerState _out279;
        @_LiveRSL____ProposerModel__i_Compile.@__default.@ProposerResetViewTimerDueToExecution((@replica).@dtor_proposer, @_25095_val, out _out279);
        @_25096_newProposer = _out279;
        { }
        ulong @_25097_end__time__proposer = 0;
        ulong _out280;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out280);
        @_25097_end__time__proposer = _out280;
        ulong @_25098_start__time__learner = 0;
        ulong _out281;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out281);
        @_25098_start__time__learner = _out281;
        @_LiveRSL____LearnerState__i_Compile.@CLearnerState @_25099_newLearner = new @_LiveRSL____LearnerState__i_Compile.@CLearnerState();
        @_LiveRSL____LearnerState__i_Compile.@CLearnerState _out282;
        @_LiveRSL____LearnerModel__i_Compile.@__default.@LearnerModel__ForgetDecision((@replica).@dtor_learner, ((@replica).@dtor_executor).@dtor_opsComplete, out _out282);
        @_25099_newLearner = _out282;
        { }
        ulong @_25100_end__time__learner = 0;
        ulong _out283;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out283);
        @_25100_end__time__learner = _out283;
        ulong @_25101_start__time__executor = 0;
        ulong _out284;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out284);
        @_25101_start__time__executor = _out284;
        @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @_25102_newExecutor = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets @_25103_packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
        @_LiveRSL____ExecutorState__i_Compile.@ExecutorState _out285;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out286;
        @_LiveRSL____ExecutorModel__i_Compile.@__default.@ExecutorExecute((@replica).@dtor_executor, out _out285, out _out286);
        @_25102_newExecutor = _out285;
        @_25103_packets = _out286;
        { }
        ulong @_25104_end__time__executor = 0;
        ulong _out287;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out287);
        @_25104_end__time__executor = _out287;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let50_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let50_0, @_25105_dt__update__tmp_h2 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25105_dt__update__tmp_h2).@dtor_constants, (@_25105_dt__update__tmp_h2).@dtor___nextActionIndex, (@_25105_dt__update__tmp_h2).@dtor_nextHeartbeatTime, @_25096_newProposer, (@_25105_dt__update__tmp_h2).@dtor_acceptor, @_25099_newLearner, @_25102_newExecutor))));
        @packetsSent = @_25103_packets;
        { }
        ulong @_25106_end__time = 0;
        ulong _out288;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out288);
        @_25106_end__time = _out288;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_MaybeExecute_work"), @_25094_start__time, @_25106_end__time);
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_MaybeExecute_work_proposer"), @_25094_start__time, @_25097_end__time__proposer);
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_MaybeExecute_work_learner"), @_25098_start__time__learner, @_25100_end__time__learner);
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_MaybeExecute_work_execute"), @_25101_start__time__executor, @_25104_end__time__executor);
      }
      else
      {
        @replica_k = @replica;
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_OutboundPacket(new _Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket>(new _Logic____Option__i_Compile.@Option_None<@_LiveRSL____CMessage__i_Compile.@CPacket>())));
        ulong @_25107_end__time = 0;
        ulong _out289;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out289);
        @_25107_end__time = _out289;
        { }
      }
    }
    public static void @Replica__Next__ReadClock__MaybeSendHeartbeat(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25108_start__time = 0;
      ulong _out290;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out290);
      @_25108_start__time = _out290;
      if (((@clock).@dtor_max) >= ((@replica).@dtor_nextHeartbeatTime))
      {
        ulong @_25109_heartbeat = 0;
        ulong _out291;
        @_LiveRSL____ParametersState__i_Compile.@__default.@LCappedAdditionImpl((@clock).@dtor_min, ((((@replica).@dtor_constants).@dtor_all).@dtor_params).@dtor_heartbeatPeriod, (((@replica).@dtor_constants).@dtor_all).@dtor_params, out _out291);
        @_25109_heartbeat = _out291;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let51_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let51_0, @_25110_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25110_dt__update__tmp_h0).@dtor_constants, (@_25110_dt__update__tmp_h0).@dtor___nextActionIndex, @_25109_heartbeat, (@_25110_dt__update__tmp_h0).@dtor_proposer, (@_25110_dt__update__tmp_h0).@dtor_acceptor, (@_25110_dt__update__tmp_h0).@dtor_learner, (@_25110_dt__update__tmp_h0).@dtor_executor))));
        bool @_25111_flag = false;
        @_25111_flag = ((((@replica).@dtor_proposer).@dtor_electionState).@dtor_currentViewSuspectors).Contains(((@replica).@dtor_constants).@dtor_myIndex);
        @_LiveRSL____CMessage__i_Compile.@CMessage @_25112_msg = new @_LiveRSL____CMessage__i_Compile.@CMessage();
        @_25112_msg = new _LiveRSL____CMessage__i_Compile.@CMessage(new _LiveRSL____CMessage__i_Compile.@CMessage_CMessage__Heartbeat((((@replica).@dtor_proposer).@dtor_electionState).@dtor_currentView, @_25111_flag, ((@replica).@dtor_executor).@dtor_opsComplete));
        @_LiveRSL____CMessage__i_Compile.@CBroadcast @_25113_packets = new @_LiveRSL____CMessage__i_Compile.@CBroadcast();
        @_LiveRSL____CMessage__i_Compile.@CBroadcast _out292;
        @_Impl____LiveRSL____Broadcast__i_Compile.@__default.@BuildBroadcastToEveryone((((@replica).@dtor_constants).@dtor_all).@dtor_config, ((@replica).@dtor_constants).@dtor_myIndex, @_25112_msg, out _out292);
        @_25113_packets = _out292;
        { }
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(@_25113_packets));
        ulong @_25114_end__time = 0;
        ulong _out293;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out293);
        @_25114_end__time = _out293;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_ReadClock_MaybeSendHeartbeat_work"), @_25108_start__time, @_25114_end__time);
      }
      else
      {
        @replica_k = @replica;
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        ulong @_25115_end__time = 0;
        ulong _out294;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out294);
        @_25115_end__time = _out294;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_ReadClock_MaybeSendHeartbeat_nada"), @_25108_start__time, @_25115_end__time);
      }
    }
    public static void @Replica__Next__Spontaneous__MaybeMakeDecision(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
      ulong @_25116_start__time = 0;
      ulong _out295;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out295);
      @_25116_start__time = _out295;
      { }
      { }
      { }
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_25117_opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_25117_opn = ((@replica).@dtor_executor).@dtor_opsComplete;
      ulong @_25118_minCQS = 0;
      ulong _out296;
      @_LiveRSL____MinCQuorumSize__i_Compile.@__default.@MinCQuorumSize(((((@replica).@dtor_learner).@dtor_rcs).@dtor_all).@dtor_config, out _out296);
      @_25118_minCQS = _out296;
      { }
      if ((((((@replica).@dtor_executor).@dtor_nextOpToExecute).@is_COutstandingOpUnknown) && ((((@replica).@dtor_learner).@dtor_unexecutedOps).Contains(@_25117_opn))) && ((new BigInteger((((((@replica).@dtor_learner).@dtor_unexecutedOps).Select(@_25117_opn)).@dtor_received2bMessageSenders).Length)) >= (new BigInteger(@_25118_minCQS))))
      {
        Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest> @_25119_candValue = Dafny.Sequence<@_LiveRSL____CTypes__i_Compile.@CRequest>.Empty;
        @_25119_candValue = ((((@replica).@dtor_learner).@dtor_unexecutedOps).Select(@_25117_opn)).@dtor_candidateLearnedValue;
        @_LiveRSL____ExecutorState__i_Compile.@ExecutorState @_25120_newExecutor = new @_LiveRSL____ExecutorState__i_Compile.@ExecutorState();
        @_LiveRSL____ExecutorState__i_Compile.@ExecutorState _out297;
        @_LiveRSL____ExecutorModel__i_Compile.@__default.@ExecutorGetDecision((@replica).@dtor_executor, ((@replica).@dtor_learner).@dtor_maxBallotSeen, @_25117_opn, @_25119_candValue, out _out297);
        @_25120_newExecutor = _out297;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let52_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let52_0, @_25121_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25121_dt__update__tmp_h0).@dtor_constants, (@_25121_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25121_dt__update__tmp_h0).@dtor_nextHeartbeatTime, (@_25121_dt__update__tmp_h0).@dtor_proposer, (@_25121_dt__update__tmp_h0).@dtor_acceptor, (@_25121_dt__update__tmp_h0).@dtor_learner, @_25120_newExecutor))));
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        { }
        { }
        ulong @_25122_end__time = 0;
        ulong _out298;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out298);
        @_25122_end__time = _out298;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_MaybeMakeDecision_work"), @_25116_start__time, @_25122_end__time);
      }
      else
      {
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        @replica_k = @replica;
        ulong @_25123_end__time = 0;
        ulong _out299;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out299);
        @_25123_end__time = _out299;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_MaybeMakeDecision_nada"), @_25116_start__time, @_25123_end__time);
      }
    }
    public static void @Replica__Next__Spontaneous__TruncateLogBasedOnCheckpoints(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packetsSent)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @packetsSent = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      ulong @_25124_start__time = 0;
      ulong _out300;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out300);
      @_25124_start__time = _out300;
      ulong @_25125_minCQS = 0;
      ulong _out301;
      @_LiveRSL____MinCQuorumSize__i_Compile.@__default.@MinCQuorumSize(((((@replica).@dtor_acceptor).@dtor_constants).@dtor_all).@dtor_config, out _out301);
      @_25125_minCQS = _out301;
      @_LiveRSL____CTypes__i_Compile.@COperationNumber @_25126_opn = new @_LiveRSL____CTypes__i_Compile.@COperationNumber();
      @_LiveRSL____CTypes__i_Compile.@COperationNumber _out302;
      @_LiveRSL____AcceptorModel__i_Compile.@__default.@AcceptorModel__GetNthHighestValueAmongReportedCheckpoints((@replica).@dtor_acceptor, @_25125_minCQS, out _out302);
      @_25126_opn = _out302;
      if (((@_25126_opn).@dtor_n) > ((((@replica).@dtor_acceptor).@dtor_logTruncationPoint).@dtor_n))
      {
        { }
        { }
        @_LiveRSL____AcceptorState__i_Compile.@AcceptorState @_25127_newAcceptor = new @_LiveRSL____AcceptorState__i_Compile.@AcceptorState();
        @_LiveRSL____AcceptorState__i_Compile.@AcceptorState _out303;
        @_LiveRSL____AcceptorModel__i_Compile.@__default.@NextAcceptorState__TruncateLog((@replica).@dtor_acceptor, @_25126_opn, out _out303);
        @_25127_newAcceptor = _out303;
        @replica_k = Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(@replica, _pat_let53_0 => Dafny.Helpers.Let<@_LiveRSL____ReplicaState__i_Compile.@ReplicaState,@_LiveRSL____ReplicaState__i_Compile.@ReplicaState>(_pat_let53_0, @_25128_dt__update__tmp_h0 => new _LiveRSL____ReplicaState__i_Compile.@ReplicaState(new _LiveRSL____ReplicaState__i_Compile.@ReplicaState_ReplicaState((@_25128_dt__update__tmp_h0).@dtor_constants, (@_25128_dt__update__tmp_h0).@dtor___nextActionIndex, (@_25128_dt__update__tmp_h0).@dtor_nextHeartbeatTime, (@_25128_dt__update__tmp_h0).@dtor_proposer, @_25127_newAcceptor, (@_25128_dt__update__tmp_h0).@dtor_learner, (@_25128_dt__update__tmp_h0).@dtor_executor))));
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        ulong @_25129_end__time = 0;
        ulong _out304;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out304);
        @_25129_end__time = _out304;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_work"), @_25124_start__time, @_25129_end__time);
      }
      else
      {
        { }
        { }
        @packetsSent = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        @replica_k = @replica;
        { }
        ulong @_25130_end__time = 0;
        ulong _out305;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out305);
        @_25130_end__time = _out305;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_Spontaneous_TruncateLogBasedOnCheckpoints_nada"), @_25124_start__time, @_25130_end__time);
      }
    }
  }
} // end of namespace _LiveRSL____ReplicaModel__i_Compile
namespace @_LiveRSL____UdpRSL__i_Compile {







  public abstract class Base_ReceiveResult { }
  public partial class ReceiveResult_RRFail : Base_ReceiveResult {
    public ReceiveResult_RRFail() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____UdpRSL__i_Compile.@ReceiveResult_RRFail;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____UdpRSL__i_Compile.ReceiveResult.RRFail";
      return s;
    }
  }
  public partial class ReceiveResult_RRTimeout : Base_ReceiveResult {
    public ReceiveResult_RRTimeout() {
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____UdpRSL__i_Compile.@ReceiveResult_RRTimeout;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____UdpRSL__i_Compile.ReceiveResult.RRTimeout";
      return s;
    }
  }
  public partial class ReceiveResult_RRPacket : Base_ReceiveResult {
    public readonly @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket;
    public ReceiveResult_RRPacket(@_LiveRSL____CMessage__i_Compile.@CPacket @cpacket) {
      this.@cpacket = @cpacket;
    }
    public override bool Equals(object other) {
      var oth = other as _LiveRSL____UdpRSL__i_Compile.@ReceiveResult_RRPacket;
      return oth != null && this.@cpacket.Equals(oth.@cpacket);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@cpacket.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "_LiveRSL____UdpRSL__i_Compile.ReceiveResult.RRPacket";
      s += "(";
      s += @cpacket.ToString();
      s += ")";
      return s;
    }
  }
  public struct @ReceiveResult {
    Base_ReceiveResult _d;
    public Base_ReceiveResult _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @ReceiveResult(Base_ReceiveResult d) { this._d = d; }
    static Base_ReceiveResult theDefault;
    public static Base_ReceiveResult Default {
      get {
        if (theDefault == null) {
          theDefault = new _LiveRSL____UdpRSL__i_Compile.@ReceiveResult_RRFail();
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @ReceiveResult && _D.Equals(((@ReceiveResult)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is_RRFail { get { return _D is ReceiveResult_RRFail; } }
    public bool is_RRTimeout { get { return _D is ReceiveResult_RRTimeout; } }
    public bool is_RRPacket { get { return _D is ReceiveResult_RRPacket; } }
    public @_LiveRSL____CMessage__i_Compile.@CPacket dtor_cpacket { get { return ((ReceiveResult_RRPacket)_D).@cpacket; } }
  }

  public partial class @__default {
    public static void @GetEndPoint(@_Native____Io__s_Compile.@IPEndPoint @ipe, out @_Native____Io__s_Compile.@EndPoint @ep)
    {
      @ep = new @_Native____Io__s_Compile.@EndPoint();
    TAIL_CALL_START: ;
      byte[] @_25131_addr = (byte[])null;
      byte[] _out306;
      (@ipe).@GetAddress(out _out306);
      @_25131_addr = _out306;
      ushort @_25132_port = 0;
      @_25132_port = (@ipe).@GetPort();
      @ep = new _Native____Io__s_Compile.@EndPoint(new _Native____Io__s_Compile.@EndPoint_EndPoint(Dafny.Helpers.SeqFromArray(@_25131_addr), @_25132_port));
    }
    public static void @Receive(@_Native____Io__s_Compile.@UdpClient @udpClient, @_Native____Io__s_Compile.@EndPoint @localAddr, @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config, out @_LiveRSL____UdpRSL__i_Compile.@ReceiveResult @rr)
    {
      @rr = new @_LiveRSL____UdpRSL__i_Compile.@ReceiveResult();
      int @_25133_timeout = 0;
      @_25133_timeout = 0;
      bool @_25134_ok = false;
      bool @_25135_timedOut = false;
      @_Native____Io__s_Compile.@IPEndPoint @_25136_remote = (@_Native____Io__s_Compile.@IPEndPoint)null;
      byte[] @_25137_buffer = (byte[])null;
      bool _out307;
      bool _out308;
      @_Native____Io__s_Compile.@IPEndPoint _out309;
      byte[] _out310;
      (@udpClient).@Receive(@_25133_timeout, out _out307, out _out308, out _out309, out _out310);
      @_25134_ok = _out307;
      @_25135_timedOut = _out308;
      @_25136_remote = _out309;
      @_25137_buffer = _out310;
      if (!(@_25134_ok))
      {
        @rr = new _LiveRSL____UdpRSL__i_Compile.@ReceiveResult(new _LiveRSL____UdpRSL__i_Compile.@ReceiveResult_RRFail());
        return;
      }
      if (@_25135_timedOut)
      {
        @rr = new _LiveRSL____UdpRSL__i_Compile.@ReceiveResult(new _LiveRSL____UdpRSL__i_Compile.@ReceiveResult_RRTimeout());
        { }
        return;
      }
      else
      {
        { }
        { }
        { }
        ulong @_25138_start__time = 0;
        ulong _out311;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out311);
        @_25138_start__time = _out311;
        @_LiveRSL____CMessage__i_Compile.@CMessage @_25139_cmessage = new @_LiveRSL____CMessage__i_Compile.@CMessage();
        @_LiveRSL____CMessage__i_Compile.@CMessage _out312;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@PaxosDemarshallDataMethod(@_25137_buffer, out _out312);
        @_25139_cmessage = _out312;
        ulong @_25140_end__time = 0;
        ulong _out313;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out313);
        @_25140_end__time = _out313;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("PaxosDemarshallDataMethod"), @_25138_start__time, @_25140_end__time);
        @_Native____Io__s_Compile.@EndPoint @_25141_srcEp = new @_Native____Io__s_Compile.@EndPoint();
        @_Native____Io__s_Compile.@EndPoint _out314;
        @_LiveRSL____UdpRSL__i_Compile.@__default.@GetEndPoint(@_25136_remote, out _out314);
        @_25141_srcEp = _out314;
        @_LiveRSL____CMessage__i_Compile.@CPacket @_25142_cpacket = new @_LiveRSL____CMessage__i_Compile.@CPacket();
        @_25142_cpacket = new _LiveRSL____CMessage__i_Compile.@CPacket(new _LiveRSL____CMessage__i_Compile.@CPacket_CPacket(@localAddr, @_25141_srcEp, @_25139_cmessage));
        @rr = new _LiveRSL____UdpRSL__i_Compile.@ReceiveResult(new _LiveRSL____UdpRSL__i_Compile.@ReceiveResult_RRPacket(@_25142_cpacket));
        { }
      }
    }
    public static void @ReadClock(@_Native____Io__s_Compile.@UdpClient @udpClient, out @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock)
    {
      @clock = new @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock();
    TAIL_CALL_START: ;
      ulong @_25143_t = 0;
      ulong _out315;
      @_Native____Io__s_Compile.@Time.@GetTime(out _out315);
      @_25143_t = _out315;
      { }
      @clock = new _LiveRSL____CBoundedClock__i_Compile.@CBoundedClock(new _LiveRSL____CBoundedClock__i_Compile.@CBoundedClock_CBoundedClock(@_25143_t, @_25143_t));
    }
    public static void @SendBroadcast(@_Native____Io__s_Compile.@UdpClient @udpClient, @_LiveRSL____CMessage__i_Compile.@CBroadcast @broadcast, out bool @ok)
    {
      @ok = false;
      @ok = true;
      { }
      if ((@broadcast).@is_CBroadcastNop)
      { }
      else
      {
        { }
        { }
        byte[] @_25144_buffer = (byte[])null;
        byte[] _out316;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@PaxosMarshall((@broadcast).@dtor_msg, out _out316);
        @_25144_buffer = _out316;
        { }
        { }
        { }
        ulong @_25145_i = 0;
        @_25145_i = 0UL;
        while ((@_25145_i) < ((ulong)((@broadcast).@dtor_dsts).LongLength))
        {
          { }
          @_Native____Io__s_Compile.@EndPoint @_25146_dstEp = new @_Native____Io__s_Compile.@EndPoint();
          @_25146_dstEp = ((@broadcast).@dtor_dsts).Select(@_25145_i);
          byte[] @_25147_dstAddrAry = (byte[])null;
          byte[] _out317;
          @_Common____Util__i_Compile.@__default.@seqToArrayOpt((@_25146_dstEp).@dtor_addr, out _out317);
          @_25147_dstAddrAry = _out317;
          @_Native____Io__s_Compile.@IPEndPoint @_25148_remote = (@_Native____Io__s_Compile.@IPEndPoint)null;
          bool _out318;
          @_Native____Io__s_Compile.@IPEndPoint _out319;
          @_Native____Io__s_Compile.@IPEndPoint.@Construct(@_25147_dstAddrAry, (@_25146_dstEp).@dtor_port, out _out318, out _out319);
          @ok = _out318;
          @_25148_remote = _out319;
          if (!(@ok))
          {
            return;
          }
          bool _out320;
          (@udpClient).@Send(@_25148_remote, @_25144_buffer, out _out320);
          @ok = _out320;
          if (!(@ok))
          {
            return;
          }
          { }
          { }
          { }
          @_25145_i = (@_25145_i) + (1UL);
        }
      }
    }
    public static void @SendPacket(@_Native____Io__s_Compile.@UdpClient @udpClient, @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packets, out bool @ok)
    {
      @ok = false;
      ulong @_25149_j = 0;
      @_25149_j = 0UL;
      { }
      @ok = true;
      @_Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket> @_25150_opt__packet = new @_Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket>();
      @_25150_opt__packet = (@packets).@dtor_p;
      if ((@_25150_opt__packet).@is_None)
      { }
      else
      {
        @_LiveRSL____CMessage__i_Compile.@CPacket @_25151_cpacket = new @_LiveRSL____CMessage__i_Compile.@CPacket();
        @_25151_cpacket = (@_25150_opt__packet).@dtor_v;
        { }
        @_Native____Io__s_Compile.@EndPoint @_25152_dstEp = new @_Native____Io__s_Compile.@EndPoint();
        @_25152_dstEp = (@_25151_cpacket).@dtor_dst;
        byte[] @_25153_dstAddrAry = (byte[])null;
        byte[] _out321;
        @_Common____Util__i_Compile.@__default.@seqToArrayOpt((@_25152_dstEp).@dtor_addr, out _out321);
        @_25153_dstAddrAry = _out321;
        @_Native____Io__s_Compile.@IPEndPoint @_25154_remote = (@_Native____Io__s_Compile.@IPEndPoint)null;
        bool _out322;
        @_Native____Io__s_Compile.@IPEndPoint _out323;
        @_Native____Io__s_Compile.@IPEndPoint.@Construct(@_25153_dstAddrAry, (@_25152_dstEp).@dtor_port, out _out322, out _out323);
        @ok = _out322;
        @_25154_remote = _out323;
        if (!(@ok))
        {
          return;
        }
        { }
        { }
        byte[] @_25155_buffer = (byte[])null;
        byte[] _out324;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@PaxosMarshall((@_25151_cpacket).@dtor_msg, out _out324);
        @_25155_buffer = _out324;
        { }
        { }
        bool _out325;
        (@udpClient).@Send(@_25154_remote, @_25155_buffer, out _out325);
        @ok = _out325;
        if (!(@ok))
        {
          return;
        }
        { }
        { }
        { }
        { }
        { }
      }
    }
    public static void @SendPacketSequence(@_Native____Io__s_Compile.@UdpClient @udpClient, @_LiveRSL____CMessage__i_Compile.@OutboundPackets @packets, out bool @ok)
    {
      @ok = false;
      Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> @_25156_cpackets = Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket>.Empty;
      @_25156_cpackets = (@packets).@dtor_s;
      ulong @_25157_j = 0;
      @_25157_j = 0UL;
      { }
      @ok = true;
      { }
      { }
      BigInteger @_25158_i = BigInteger.Zero;
      @_25158_i = new BigInteger(0);
      while ((@_25158_i) < (new BigInteger((@_25156_cpackets).Length)))
      {
        @_LiveRSL____CMessage__i_Compile.@CPacket @_25159_cpacket = new @_LiveRSL____CMessage__i_Compile.@CPacket();
        @_25159_cpacket = (@_25156_cpackets).Select(@_25158_i);
        @_Native____Io__s_Compile.@EndPoint @_25160_dstEp = new @_Native____Io__s_Compile.@EndPoint();
        @_25160_dstEp = (@_25159_cpacket).@dtor_dst;
        { }
        { }
        byte[] @_25161_dstAddrAry = (byte[])null;
        byte[] _out326;
        @_Common____Util__i_Compile.@__default.@seqToArrayOpt((@_25160_dstEp).@dtor_addr, out _out326);
        @_25161_dstAddrAry = _out326;
        @_Native____Io__s_Compile.@IPEndPoint @_25162_remote = (@_Native____Io__s_Compile.@IPEndPoint)null;
        bool _out327;
        @_Native____Io__s_Compile.@IPEndPoint _out328;
        @_Native____Io__s_Compile.@IPEndPoint.@Construct(@_25161_dstAddrAry, (@_25160_dstEp).@dtor_port, out _out327, out _out328);
        @ok = _out327;
        @_25162_remote = _out328;
        if (!(@ok))
        {
          return;
        }
        { }
        { }
        byte[] @_25163_buffer = (byte[])null;
        byte[] _out329;
        @_LiveRSL____PacketParsing__i_Compile.@__default.@PaxosMarshall((@_25159_cpacket).@dtor_msg, out _out329);
        @_25163_buffer = _out329;
        { }
        { }
        bool _out330;
        (@udpClient).@Send(@_25162_remote, @_25163_buffer, out _out330);
        @ok = _out330;
        if (!(@ok))
        {
          return;
        }
        { }
        { }
        { }
        { }
        { }
        { }
        @_25158_i = (@_25158_i) + (new BigInteger(1));
      }
    }
  }
} // end of namespace _LiveRSL____UdpRSL__i_Compile
namespace @_LiveRSL____QRelations__i_Compile {


  public partial class @__default {
  }
} // end of namespace _LiveRSL____QRelations__i_Compile
namespace @_LiveRSL____ReplicaImplStubs__i_Compile {






  public partial class @__default {
    public static void @Replica__Next__Process__Heartbeat__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      { }
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out331;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out332;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Process__Heartbeat(@replica, @cpacket, (@clock).@dtor_min, (@clock).@dtor_max, out _out331, out _out332);
      @replica_k = _out331;
      @sent__packets = _out332;
    }
    public static void @Replica__Next__Process__Request__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out333;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out334;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Process__Request(@replica, @cpacket, out _out333, out _out334);
      @replica_k = _out333;
      @sent__packets = _out334;
      { }
    }
    public static void @Replica__Next__Process__1a__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      { }
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out335;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out336;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Process__1a(@replica, @cpacket, out _out335, out _out336);
      @replica_k = _out335;
      @sent__packets = _out336;
      { }
    }
    public static void @Replica__Next__Process__1b__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      { }
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out337;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out338;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Process__1b(@replica, @cpacket, out _out337, out _out338);
      @replica_k = _out337;
      @sent__packets = _out338;
      { }
    }
    public static void @Replica__Next__Process__StartingPhase2__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out339;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out340;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Process__StartingPhase2(@replica, @cpacket, out _out339, out _out340);
      @replica_k = _out339;
      @sent__packets = _out340;
      { }
    }
    public static void @Replica__Next__Process__2a__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      { }
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out341;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out342;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Process__2a(@replica, @cpacket, out _out341, out _out342);
      @replica_k = _out341;
      @sent__packets = _out342;
      { }
    }
    public static void @Replica__Next__Process__2b__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out343;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out344;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Process__2b(@replica, @cpacket, out _out343, out _out344);
      @replica_k = _out343;
      @sent__packets = _out344;
      { }
    }
    public static void @Replica__Next__Process__AppStateRequest__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out345;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out346;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Process__AppStateRequest(@replica, @cpacket, out _out345, out _out346);
      @replica_k = _out345;
      @sent__packets = _out346;
      { }
    }
    public static void @Replica__Next__Process__AppStateSupply__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out347;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out348;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Process__AppStateSupply(@replica, @cpacket, out _out347, out _out348);
      @replica_k = _out347;
      @sent__packets = _out348;
      { }
    }
    public static void @Replica__Next__Spontaneous__MaybeEnterNewViewAndSend1a__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out349;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out350;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Spontaneous__MaybeEnterNewViewAndSend1a(@replica, out _out349, out _out350);
      @replica_k = _out349;
      @sent__packets = _out350;
      { }
    }
    public static void @Replica__Next__Spontaneous__MaybeEnterPhase2__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out351;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out352;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Spontaneous__MaybeEnterPhase2(@replica, out _out351, out _out352);
      @replica_k = _out351;
      @sent__packets = _out352;
      { }
    }
    public static void @Replica__Next__ReadClock__MaybeNominateValueAndSend2a__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out353;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out354;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Spontaneous__MaybeNominateValueAndSend2a(@replica, @clock, out _out353, out _out354);
      @replica_k = _out353;
      @sent__packets = _out354;
      { }
    }
    public static void @Replica__Next__Spontaneous__TruncateLogBasedOnCheckpoints__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out355;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out356;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Spontaneous__TruncateLogBasedOnCheckpoints(@replica, out _out355, out _out356);
      @replica_k = _out355;
      @sent__packets = _out356;
      { }
    }
    public static void @Replica__Next__Spontaneous__MaybeMakeDecision__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out357;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out358;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Spontaneous__MaybeMakeDecision(@replica, out _out357, out _out358);
      @replica_k = _out357;
      @sent__packets = _out358;
      { }
    }
    public static void @Replica__Next__Spontaneous__MaybeExecute__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out359;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out360;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__Spontaneous__MaybeExecute(@replica, out _out359, out _out360);
      @replica_k = _out359;
      @sent__packets = _out360;
      { }
    }
    public static void @Replica__Next__ReadClock__CheckForViewTimeout__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out361;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out362;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__ReadClock__CheckForViewTimeout(@replica, @clock, out _out361, out _out362);
      @replica_k = _out361;
      @sent__packets = _out362;
      { }
    }
    public static void @Replica__Next__ReadClock__CheckForQuorumOfViewSuspicions__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out363;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out364;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__ReadClock__CheckForQuorumOfViewSuspicions(@replica, @clock, out _out363, out _out364);
      @replica_k = _out363;
      @sent__packets = _out364;
      { }
    }
    public static void @Replica__Next__ReadClock__MaybeSendHeartbeat__dummy(@_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica, @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @clock, out @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica_k, out @_LiveRSL____CMessage__i_Compile.@OutboundPackets @sent__packets)
    {
      @replica_k = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
      @sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
    TAIL_CALL_START: ;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out365;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out366;
      @_LiveRSL____ReplicaModel__i_Compile.@__default.@Replica__Next__ReadClock__MaybeSendHeartbeat(@replica, @clock, out _out365, out _out366);
      @replica_k = _out365;
      @sent__packets = _out366;
      { }
    }
  }
} // end of namespace _LiveRSL____ReplicaImplStubs__i_Compile
namespace @_LiveRSL____ReplicaImpl__i_Compile {








  public partial class @ReplicaImpl {
    public @_LiveRSL____ReplicaState__i_Compile.@ReplicaState @replica = new @_LiveRSL____ReplicaState__i_Compile.@ReplicaState();
    public ulong @nextActionIndex = 0;
    public @_Native____Io__s_Compile.@UdpClient @udpClient = (@_Native____Io__s_Compile.@UdpClient)null;
    public @_Native____Io__s_Compile.@EndPoint @localAddr = new @_Native____Io__s_Compile.@EndPoint();
    public void @ConstructUdpClient(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, out bool @ok, out @_Native____Io__s_Compile.@UdpClient @client)
    {
      @ok = false;
      @client = (@_Native____Io__s_Compile.@UdpClient)null;
    TAIL_CALL_START: ;
      var _this = this;
      @_Native____Io__s_Compile.@EndPoint @_25164_my__ep = new @_Native____Io__s_Compile.@EndPoint();
      @_25164_my__ep = ((((@constants).@dtor_all).@dtor_config).@dtor_replicaIds).Select((@constants).@dtor_myIndex);
      byte[] @_25165_ip__byte__array = (byte[])null;
      @_25165_ip__byte__array = new byte[(int)(new BigInteger(((@_25164_my__ep).@dtor_addr).Length))];
      { }
      @_Common____Util__i_Compile.@__default.@seqIntoArrayOpt((@_25164_my__ep).@dtor_addr, @_25165_ip__byte__array);
      @_Native____Io__s_Compile.@IPEndPoint @_25166_ip__endpoint = (@_Native____Io__s_Compile.@IPEndPoint)null;
      bool _out367;
      @_Native____Io__s_Compile.@IPEndPoint _out368;
      @_Native____Io__s_Compile.@IPEndPoint.@Construct(@_25165_ip__byte__array, (@_25164_my__ep).@dtor_port, out _out367, out _out368);
      @ok = _out367;
      @_25166_ip__endpoint = _out368;
      if (!(@ok))
      {
        return;
      }
      bool _out369;
      @_Native____Io__s_Compile.@UdpClient _out370;
      @_Native____Io__s_Compile.@UdpClient.@Construct(@_25166_ip__endpoint, out _out369, out _out370);
      @ok = _out369;
      @client = _out370;
      { }
    }
    public void @Replica__Init(@_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants, out bool @ok)
    {
      @ok = false;
    TAIL_CALL_START: ;
      var _this = this;
      var _obj0 = _this;
      bool _out371;
      @_Native____Io__s_Compile.@UdpClient _out372;
      (_this).@ConstructUdpClient(@constants, out _out371, out _out372);
      @ok = _out371;
      _obj0.@udpClient = _out372;
      if (@ok)
      {
        var _obj1 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out373;
        @_LiveRSL____ReplicaModel__i_Compile.@__default.@InitReplicaState(@constants, out _out373);
        _obj1.@replica = _out373;
        (_this).@nextActionIndex = 0UL;
        (_this).@localAddr = ((((((_this).@replica).@dtor_constants).@dtor_all).@dtor_config).@dtor_replicaIds).Select((((_this).@replica).@dtor_constants).@dtor_myIndex);
        { }
      }
    }
    public static void @rollActionIndex(ulong @a, out ulong @a_k)
    {
      @a_k = 0;
    TAIL_CALL_START: ;
      { }
      if ((@a) >= (9UL))
      {
        @a_k = 0UL;
      }
      else
      {
        @a_k = (@a) + (1UL);
      }
    }
    public void @DeliverPacket(@_LiveRSL____CMessage__i_Compile.@OutboundPackets @packets, out bool @ok)
    {
      @ok = false;
    TAIL_CALL_START: ;
      var _this = this;
      ulong @_25167_start__time = 0;
      ulong _out374;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out374);
      @_25167_start__time = _out374;
      bool _out375;
      @_LiveRSL____UdpRSL__i_Compile.@__default.@SendPacket((_this).@udpClient, @packets, out _out375);
      @ok = _out375;
      if (!(@ok))
      {
        return;
      }
      { }
      { }
      ulong @_25168_end__time = 0;
      ulong _out376;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out376);
      @_25168_end__time = _out376;
      if (((@packets).@dtor_p).@is_None)
      {
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("DeliverPacketEmpty"), @_25167_start__time, @_25168_end__time);
      }
      else
      {
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("DeliverPacketSingleton"), @_25167_start__time, @_25168_end__time);
      }
    }
    public void @DeliverPacketSequence(@_LiveRSL____CMessage__i_Compile.@OutboundPackets @packets, out bool @ok)
    {
      @ok = false;
    TAIL_CALL_START: ;
      var _this = this;
      ulong @_25169_start__time = 0;
      ulong _out377;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out377);
      @_25169_start__time = _out377;
      bool _out378;
      @_LiveRSL____UdpRSL__i_Compile.@__default.@SendPacketSequence((_this).@udpClient, @packets, out _out378);
      @ok = _out378;
      if (!(@ok))
      {
        return;
      }
      { }
      { }
      ulong @_25170_end__time = 0;
      ulong _out379;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out379);
      @_25170_end__time = _out379;
      @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("DeliverPacketSequence"), @_25169_start__time, @_25170_end__time);
    }
    public void @DeliverBroadcast(@_LiveRSL____CMessage__i_Compile.@CBroadcast @broadcast, out bool @ok)
    {
      @ok = false;
    TAIL_CALL_START: ;
      var _this = this;
      ulong @_25171_start__time = 0;
      ulong _out380;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out380);
      @_25171_start__time = _out380;
      bool _out381;
      @_LiveRSL____UdpRSL__i_Compile.@__default.@SendBroadcast((_this).@udpClient, @broadcast, out _out381);
      @ok = _out381;
      if (!(@ok))
      {
        return;
      }
      { }
      { }
      { }
      { }
      { }
      ulong @_25172_end__time = 0;
      ulong _out382;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out382);
      @_25172_end__time = _out382;
      if (((@broadcast).@is_CBroadcastNop) || (((@broadcast).@is_CBroadcast) && (((ulong)((@broadcast).@dtor_dsts).LongLength).@Equals(0UL))))
      {
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("DeliverBroadcastEmpty"), @_25171_start__time, @_25172_end__time);
      }
      else
      if (((@broadcast).@is_CBroadcast) && (((ulong)((@broadcast).@dtor_dsts).LongLength).@Equals(1UL)))
      {
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("DeliverBroadcastSingleton"), @_25171_start__time, @_25172_end__time);
      }
      else
      {
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("DeliverBroadcastMany"), @_25171_start__time, @_25172_end__time);
      }
    }
    public void @DeliverOutboundPackets(@_LiveRSL____CMessage__i_Compile.@OutboundPackets @packets, out bool @ok)
    {
      @ok = false;
    TAIL_CALL_START: ;
      var _this = this;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _source5 = @packets;
      if (_source5.is_Broadcast) {
        @_LiveRSL____CMessage__i_Compile.@CBroadcast @_25173_broadcast = ((_LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast)_source5._D).@broadcast;
        bool _out383;
        (_this).@DeliverBroadcast(@_25173_broadcast, out _out383);
        @ok = _out383;
      } else if (_source5.is_OutboundPacket) {
        @_Logic____Option__i_Compile.@Option<@_LiveRSL____CMessage__i_Compile.@CPacket> @_25174_p = ((_LiveRSL____CMessage__i_Compile.@OutboundPackets_OutboundPacket)_source5._D).@p;
        bool _out384;
        (_this).@DeliverPacket(@packets, out _out384);
        @ok = _out384;
      } else if (true) {
        Dafny.Sequence<@_LiveRSL____CMessage__i_Compile.@CPacket> @_25175_s = ((_LiveRSL____CMessage__i_Compile.@OutboundPackets_PacketSequence)_source5._D).@s;
        bool _out385;
        (_this).@DeliverPacketSequence(@packets, out _out385);
        @ok = _out385;
      }
    }
    public void @Replica__Next__ReadClockAndProcessPacket(@_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out bool @ok)
    {
      @ok = false;
    TAIL_CALL_START: ;
      var _this = this;
      @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @_25176_clock = new @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock();
      @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock _out386;
      @_LiveRSL____UdpRSL__i_Compile.@__default.@ReadClock((_this).@udpClient, out _out386);
      @_25176_clock = _out386;
      { }
      { }
      { }
      { }
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets @_25177_sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
      var _obj2 = _this;
      @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out387;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out388;
      @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Process__Heartbeat__dummy((_this).@replica, @cpacket, @_25176_clock, out _out387, out _out388);
      _obj2.@replica = _out387;
      @_25177_sent__packets = _out388;
      { }
      bool _out389;
      (_this).@DeliverOutboundPackets(@_25177_sent__packets, out _out389);
      @ok = _out389;
      if (!(@ok))
      {
        return;
      }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public void @Replica__Next__ProcessPacketWithoutReadingClock__body(@_LiveRSL____CMessage__i_Compile.@CPacket @cpacket, out bool @ok)
    {
      @ok = false;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets @_25178_sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
      { }
      { }
      { }
      if (((@cpacket).@dtor_msg).@is_CMessage__Request)
      {
        var _obj3 = this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out390;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out391;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Process__Request__dummy((this).@replica, @cpacket, out _out390, out _out391);
        _obj3.@replica = _out390;
        @_25178_sent__packets = _out391;
        { }
      }
      else
      if (((@cpacket).@dtor_msg).@is_CMessage__1a)
      {
        var _obj4 = this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out392;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out393;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Process__1a__dummy((this).@replica, @cpacket, out _out392, out _out393);
        _obj4.@replica = _out392;
        @_25178_sent__packets = _out393;
        { }
      }
      else
      if (((@cpacket).@dtor_msg).@is_CMessage__1b)
      {
        var _obj5 = this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out394;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out395;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Process__1b__dummy((this).@replica, @cpacket, out _out394, out _out395);
        _obj5.@replica = _out394;
        @_25178_sent__packets = _out395;
        { }
      }
      else
      if (((@cpacket).@dtor_msg).@is_CMessage__StartingPhase2)
      {
        var _obj6 = this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out396;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out397;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Process__StartingPhase2__dummy((this).@replica, @cpacket, out _out396, out _out397);
        _obj6.@replica = _out396;
        @_25178_sent__packets = _out397;
        { }
      }
      else
      if (((@cpacket).@dtor_msg).@is_CMessage__2a)
      {
        var _obj7 = this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out398;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out399;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Process__2a__dummy((this).@replica, @cpacket, out _out398, out _out399);
        _obj7.@replica = _out398;
        @_25178_sent__packets = _out399;
        { }
      }
      else
      if (((@cpacket).@dtor_msg).@is_CMessage__2b)
      {
        var _obj8 = this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out400;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out401;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Process__2b__dummy((this).@replica, @cpacket, out _out400, out _out401);
        _obj8.@replica = _out400;
        @_25178_sent__packets = _out401;
        { }
      }
      else
      if (((@cpacket).@dtor_msg).@is_CMessage__Reply)
      {
        @_25178_sent__packets = new _LiveRSL____CMessage__i_Compile.@OutboundPackets(new _LiveRSL____CMessage__i_Compile.@OutboundPackets_Broadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast(new _LiveRSL____CMessage__i_Compile.@CBroadcast_CBroadcastNop())));
        { }
        { }
        { }
      }
      else
      if (((@cpacket).@dtor_msg).@is_CMessage__AppStateRequest)
      {
        var _obj9 = this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out402;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out403;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Process__AppStateRequest__dummy((this).@replica, @cpacket, out _out402, out _out403);
        _obj9.@replica = _out402;
        @_25178_sent__packets = _out403;
        { }
      }
      else
      if (((@cpacket).@dtor_msg).@is_CMessage__AppStateSupply)
      {
        var _obj10 = this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out404;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out405;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Process__AppStateSupply__dummy((this).@replica, @cpacket, out _out404, out _out405);
        _obj10.@replica = _out404;
        @_25178_sent__packets = _out405;
        { }
      }
      else
      { }
      { }
      { }
      { }
      bool _out406;
      (this).@DeliverOutboundPackets(@_25178_sent__packets, out _out406);
      @ok = _out406;
      if (!(@ok))
      {
        return;
      }
      { }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public void @Replica__Next__ProcessPacketX(out bool @ok)
    {
      @ok = false;
    TAIL_CALL_START: ;
      var _this = this;
      ulong @_25179_start__time = 0;
      ulong _out407;
      @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out407);
      @_25179_start__time = _out407;
      @_LiveRSL____UdpRSL__i_Compile.@ReceiveResult @_25180_rr = new @_LiveRSL____UdpRSL__i_Compile.@ReceiveResult();
      { }
      @_LiveRSL____UdpRSL__i_Compile.@ReceiveResult _out408;
      @_LiveRSL____UdpRSL__i_Compile.@__default.@Receive((_this).@udpClient, (_this).@localAddr, ((((_this).@replica).@dtor_constants).@dtor_all).@dtor_config, out _out408);
      @_25180_rr = _out408;
      { }
      { }
      if ((@_25180_rr).@is_RRFail)
      {
        @ok = false;
        ulong @_25181_end__time = 0;
        ulong _out409;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out409);
        @_25181_end__time = _out409;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_ProcessPacket_fail"), @_25179_start__time, @_25181_end__time);
        return;
      }
      else
      if ((@_25180_rr).@is_RRTimeout)
      {
        @ok = true;
        { }
        { }
        { }
        ulong @_25182_end__time = 0;
        ulong _out410;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out410);
        @_25182_end__time = _out410;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_ProcessPacket_timeout"), @_25179_start__time, @_25182_end__time);
      }
      else
      {
        @ok = true;
        { }
        { }
        { }
        if ((((@_25180_rr).@dtor_cpacket).@dtor_msg).@is_CMessage__Heartbeat)
        {
          { }
          { }
          bool _out411;
          (_this).@Replica__Next__ReadClockAndProcessPacket((@_25180_rr).@dtor_cpacket, out _out411);
          @ok = _out411;
          { }
          { }
        }
        else
        {
          bool _out412;
          (_this).@Replica__Next__ProcessPacketWithoutReadingClock__body((@_25180_rr).@dtor_cpacket, out _out412);
          @ok = _out412;
          { }
          { }
        }
        { }
        { }
        ulong @_25183_end__time = 0;
        ulong _out413;
        @_Native____Io__s_Compile.@Time.@GetDebugTimeTicks(out _out413);
        @_25183_end__time = _out413;
        @_Common____Util__i_Compile.@__default.@RecordTimingSeq(Dafny.Sequence<char>.FromString("Replica_Next_ProcessPacket_work"), @_25179_start__time, @_25183_end__time);
        if (!(@ok))
        {
          return;
        }
        { }
        { }
      }
      { }
      { }
    }
    public void @Replica__NoReceive__NoClock__Next(out bool @ok)
    {
      @ok = false;
    TAIL_CALL_START: ;
      var _this = this;
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets @_25184_sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
      if (((_this).@nextActionIndex).@Equals(1UL))
      {
        var _obj11 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out414;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out415;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Spontaneous__MaybeEnterNewViewAndSend1a__dummy((_this).@replica, out _out414, out _out415);
        _obj11.@replica = _out414;
        @_25184_sent__packets = _out415;
      }
      else
      if (((_this).@nextActionIndex).@Equals(2UL))
      {
        var _obj12 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out416;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out417;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Spontaneous__MaybeEnterPhase2__dummy((_this).@replica, out _out416, out _out417);
        _obj12.@replica = _out416;
        @_25184_sent__packets = _out417;
      }
      else
      if (((_this).@nextActionIndex).@Equals(4UL))
      {
        var _obj13 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out418;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out419;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Spontaneous__TruncateLogBasedOnCheckpoints__dummy((_this).@replica, out _out418, out _out419);
        _obj13.@replica = _out418;
        @_25184_sent__packets = _out419;
      }
      else
      if (((_this).@nextActionIndex).@Equals(5UL))
      {
        var _obj14 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out420;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out421;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Spontaneous__MaybeMakeDecision__dummy((_this).@replica, out _out420, out _out421);
        _obj14.@replica = _out420;
        @_25184_sent__packets = _out421;
      }
      else
      if (((_this).@nextActionIndex).@Equals(6UL))
      {
        var _obj15 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out422;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out423;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__Spontaneous__MaybeExecute__dummy((_this).@replica, out _out422, out _out423);
        _obj15.@replica = _out422;
        @_25184_sent__packets = _out423;
      }
      bool _out424;
      (_this).@DeliverOutboundPackets(@_25184_sent__packets, out _out424);
      @ok = _out424;
      if (!(@ok))
      {
        return;
      }
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public void @Replica__NoReceive__ReadClock__Next(out bool @ok)
    {
      @ok = false;
    TAIL_CALL_START: ;
      var _this = this;
      @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock @_25185_clock = new @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock();
      @_LiveRSL____CBoundedClock__i_Compile.@CBoundedClock _out425;
      @_LiveRSL____UdpRSL__i_Compile.@__default.@ReadClock((_this).@udpClient, out _out425);
      @_25185_clock = _out425;
      { }
      { }
      @_LiveRSL____CMessage__i_Compile.@OutboundPackets @_25186_sent__packets = new @_LiveRSL____CMessage__i_Compile.@OutboundPackets();
      if (((_this).@nextActionIndex).@Equals(3UL))
      {
        var _obj16 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out426;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out427;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__ReadClock__MaybeNominateValueAndSend2a__dummy((_this).@replica, @_25185_clock, out _out426, out _out427);
        _obj16.@replica = _out426;
        @_25186_sent__packets = _out427;
      }
      else
      if (((_this).@nextActionIndex).@Equals(7UL))
      {
        var _obj17 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out428;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out429;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__ReadClock__CheckForViewTimeout__dummy((_this).@replica, @_25185_clock, out _out428, out _out429);
        _obj17.@replica = _out428;
        @_25186_sent__packets = _out429;
      }
      else
      if (((_this).@nextActionIndex).@Equals(8UL))
      {
        var _obj18 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out430;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out431;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__ReadClock__CheckForQuorumOfViewSuspicions__dummy((_this).@replica, @_25185_clock, out _out430, out _out431);
        _obj18.@replica = _out430;
        @_25186_sent__packets = _out431;
      }
      else
      if (((_this).@nextActionIndex).@Equals(9UL))
      {
        var _obj19 = _this;
        @_LiveRSL____ReplicaState__i_Compile.@ReplicaState _out432;
        @_LiveRSL____CMessage__i_Compile.@OutboundPackets _out433;
        @_LiveRSL____ReplicaImplStubs__i_Compile.@__default.@Replica__Next__ReadClock__MaybeSendHeartbeat__dummy((_this).@replica, @_25185_clock, out _out432, out _out433);
        _obj19.@replica = _out432;
        @_25186_sent__packets = _out433;
      }
      { }
      { }
      { }
      { }
      { }
      { }
      bool _out434;
      (_this).@DeliverOutboundPackets(@_25186_sent__packets, out _out434);
      @ok = _out434;
      if (!(@ok))
      {
        return;
      }
      { }
      { }
      { }
      { }
    }
    public void @Replica__Next__main(out bool @ok)
    {
      @ok = false;
      ulong @_25187_curActionIndex = 0;
      @_25187_curActionIndex = (this).@nextActionIndex;
      ulong @_25188_nextActionIndex_k = 0;
      ulong _out435;
      @_LiveRSL____ReplicaImpl__i_Compile.@ReplicaImpl.@rollActionIndex((this).@nextActionIndex, out _out435);
      @_25188_nextActionIndex_k = _out435;
      { }
      { }
      { }
      { }
      { }
      if ((@_25187_curActionIndex).@Equals(0UL))
      {
        bool _out436;
        (this).@Replica__Next__ProcessPacketX(out _out436);
        @ok = _out436;
        if (!(@ok))
        {
          return;
        }
      }
      else
      if (((((((this).@nextActionIndex).@Equals(1UL)) || (((this).@nextActionIndex).@Equals(2UL))) || (((this).@nextActionIndex).@Equals(4UL))) || (((this).@nextActionIndex).@Equals(5UL))) || (((this).@nextActionIndex).@Equals(6UL)))
      {
        bool _out437;
        (this).@Replica__NoReceive__NoClock__Next(out _out437);
        @ok = _out437;
        if (!(@ok))
        {
          return;
        }
      }
      else
      if ((((this).@nextActionIndex).@Equals(3UL)) || (((7UL) <= ((this).@nextActionIndex)) && (((this).@nextActionIndex) <= (9UL))))
      {
        bool _out438;
        (this).@Replica__NoReceive__ReadClock__Next(out _out438);
        @ok = _out438;
        if (!(@ok))
        {
          return;
        }
      }
      else
      { }
      { }
      (this).@nextActionIndex = @_25188_nextActionIndex_k;
      { }
      { }
      { }
      { }
    }
  }

  public partial class @__default {
  }
} // end of namespace _LiveRSL____ReplicaImpl__i_Compile
namespace @_CmdLineParser__i_Compile {




  public partial class @__default {
    public static @_System.@__tuple_h2<bool,byte> @ascii__to__int(ushort @short) {
      if (((48) <= (@short)) && ((@short) <= (57))) {
        return new _System.@__tuple_h2<bool,byte>(new _System.@__tuple_h2____hMake<bool,byte>(true, (byte)((ushort)((@short) - (48)))));
      } else {
        return new _System.@__tuple_h2<bool,byte>(new _System.@__tuple_h2____hMake<bool,byte>(false, 0));
      }
    }
    public static void @power10(BigInteger @e, out BigInteger @val)
    {
      @val = BigInteger.Zero;
      { }
      if ((@e).@Equals(new BigInteger(0)))
      {
        @val = new BigInteger(1);
        return;
      }
      else
      {
        BigInteger @_25189_tmp = BigInteger.Zero;
        BigInteger _out439;
        @_CmdLineParser__i_Compile.@__default.@power10((@e) - (new BigInteger(1)), out _out439);
        @_25189_tmp = _out439;
        @val = (new BigInteger(10)) * (@_25189_tmp);
        return;
      }
    }
    public static @_System.@__tuple_h2<bool,Dafny.Sequence<byte>> @shorts__to__bytes(Dafny.Sequence<ushort> @shorts) {
      if ((new BigInteger((@shorts).Length)).@Equals(new BigInteger(0))) {
        return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(true, Dafny.Sequence<byte>.FromElements()));
      } else {
        @_System.@__tuple_h2<bool,Dafny.Sequence<byte>> @_25190_tuple = @_CmdLineParser__i_Compile.@__default.@shorts__to__bytes((@shorts).Drop(new BigInteger(1)));
        bool @_25191_ok = (@_25190_tuple).@dtor__0;
        Dafny.Sequence<byte> @_25192_rest = (@_25190_tuple).@dtor__1;
        @_System.@__tuple_h2<bool,byte> @_25193_tuple_k = @_CmdLineParser__i_Compile.@__default.@ascii__to__int((@shorts).Select(new BigInteger(0)));
        bool @_25194_ok_k = (@_25193_tuple_k).@dtor__0;
        byte @_25195_a__byte = (@_25193_tuple_k).@dtor__1;
        if ((@_25191_ok) && (@_25194_ok_k)) {
          return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(true, (Dafny.Sequence<byte>.FromElements(@_25195_a__byte)).@Concat(@_25192_rest)));
        } else {
          return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(false, Dafny.Sequence<byte>.FromElements()));
        }
      }
    }
    public static BigInteger @bytes__to__decimal(Dafny.Sequence<byte> @bytes) {
      if ((new BigInteger((@bytes).Length)).@Equals(new BigInteger(0))) {
        return new BigInteger(0);
      } else {
        return (new BigInteger((@bytes).Select((new BigInteger((@bytes).Length)) - (new BigInteger(1))))) + ((new BigInteger(10)) * (@_CmdLineParser__i_Compile.@__default.@bytes__to__decimal((@bytes).Take((new BigInteger((@bytes).Length)) - (new BigInteger(1))).Drop(new BigInteger(0)))));
      }
    }
    public static @_System.@__tuple_h2<bool,BigInteger> @shorts__to__nat(Dafny.Sequence<ushort> @shorts) {
      if ((new BigInteger((@shorts).Length)).@Equals(new BigInteger(0))) {
        return new _System.@__tuple_h2<bool,BigInteger>(new _System.@__tuple_h2____hMake<bool,BigInteger>(false, new BigInteger(0)));
      } else {
        @_System.@__tuple_h2<bool,Dafny.Sequence<byte>> @_25196_tuple = @_CmdLineParser__i_Compile.@__default.@shorts__to__bytes(@shorts);
        bool @_25197_ok = (@_25196_tuple).@dtor__0;
        Dafny.Sequence<byte> @_25198_bytes = (@_25196_tuple).@dtor__1;
        if (!(@_25197_ok)) {
          return new _System.@__tuple_h2<bool,BigInteger>(new _System.@__tuple_h2____hMake<bool,BigInteger>(false, new BigInteger(0)));
        } else {
          return new _System.@__tuple_h2<bool,BigInteger>(new _System.@__tuple_h2____hMake<bool,BigInteger>(true, @_CmdLineParser__i_Compile.@__default.@bytes__to__decimal(@_25198_bytes)));
        }
      }
    }
    public static @_System.@__tuple_h2<bool,byte> @shorts__to__byte(Dafny.Sequence<ushort> @shorts) {
      @_System.@__tuple_h2<bool,BigInteger> @_25199_tuple = @_CmdLineParser__i_Compile.@__default.@shorts__to__nat(@shorts);
      bool @_25200_ok = (@_25199_tuple).@dtor__0;
      BigInteger @_25201_val = (@_25199_tuple).@dtor__1;
      if (((new BigInteger(0)) <= (@_25201_val)) && ((@_25201_val) < (new BigInteger(256)))) {
        return new _System.@__tuple_h2<bool,byte>(new _System.@__tuple_h2____hMake<bool,byte>(true, (byte)(@_25201_val)));
      } else {
        return new _System.@__tuple_h2<bool,byte>(new _System.@__tuple_h2____hMake<bool,byte>(false, 0));
      }
    }
    public static @_System.@__tuple_h2<bool,ushort> @shorts__to__uint16(Dafny.Sequence<ushort> @shorts) {
      @_System.@__tuple_h2<bool,BigInteger> @_25202_tuple = @_CmdLineParser__i_Compile.@__default.@shorts__to__nat(@shorts);
      bool @_25203_ok = (@_25202_tuple).@dtor__0;
      BigInteger @_25204_val = (@_25202_tuple).@dtor__1;
      if (((new BigInteger(0)) <= (@_25204_val)) && ((@_25204_val) < (new BigInteger(65536)))) {
        return new _System.@__tuple_h2<bool,ushort>(new _System.@__tuple_h2____hMake<bool,ushort>(true, (ushort)(@_25204_val)));
      } else {
        return new _System.@__tuple_h2<bool,ushort>(new _System.@__tuple_h2____hMake<bool,ushort>(false, 0));
      }
    }
    public static @_System.@__tuple_h2<bool,uint> @shorts__to__uint32(Dafny.Sequence<ushort> @shorts) {
      @_System.@__tuple_h2<bool,BigInteger> @_25205_tuple = @_CmdLineParser__i_Compile.@__default.@shorts__to__nat(@shorts);
      bool @_25206_ok = (@_25205_tuple).@dtor__0;
      BigInteger @_25207_val = (@_25205_tuple).@dtor__1;
      if (((new BigInteger(0)) <= (@_25207_val)) && ((@_25207_val) < (BigInteger.Parse("4294967296")))) {
        return new _System.@__tuple_h2<bool,uint>(new _System.@__tuple_h2____hMake<bool,uint>(true, (uint)(@_25207_val)));
      } else {
        return new _System.@__tuple_h2<bool,uint>(new _System.@__tuple_h2____hMake<bool,uint>(false, 0U));
      }
    }
    public static bool @is__ascii__period(ushort @short) {
      return (@short).@Equals(46);
    }
    public static @_System.@__tuple_h2<bool,Dafny.Sequence<byte>> @parse__ip__addr__helper(Dafny.Sequence<ushort> @ip__shorts, Dafny.Sequence<ushort> @current__octet__shorts) {
      if ((new BigInteger((@ip__shorts).Length)).@Equals(new BigInteger(0))) {
        @_System.@__tuple_h2<bool,byte> @_25208_tuple = @_CmdLineParser__i_Compile.@__default.@shorts__to__byte(@current__octet__shorts);
        bool @_25209_okay = (@_25208_tuple).@dtor__0;
        byte @_25210_b = (@_25208_tuple).@dtor__1;
        if (!(@_25209_okay)) {
          return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(false, Dafny.Sequence<byte>.FromElements()));
        } else {
          return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(true, Dafny.Sequence<byte>.FromElements(@_25210_b)));
        }
      } else {
        if (@_CmdLineParser__i_Compile.@__default.@is__ascii__period((@ip__shorts).Select(new BigInteger(0)))) {
          @_System.@__tuple_h2<bool,byte> @_25211_tuple = @_CmdLineParser__i_Compile.@__default.@shorts__to__byte(@current__octet__shorts);
          bool @_25212_okay = (@_25211_tuple).@dtor__0;
          byte @_25213_b = (@_25211_tuple).@dtor__1;
          if (!(@_25212_okay)) {
            return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(false, Dafny.Sequence<byte>.FromElements()));
          } else {
            @_System.@__tuple_h2<bool,Dafny.Sequence<byte>> @_25214_tuple_k = @_CmdLineParser__i_Compile.@__default.@parse__ip__addr__helper((@ip__shorts).Drop(new BigInteger(1)), Dafny.Sequence<ushort>.FromElements());
            bool @_25215_ok = (@_25214_tuple_k).@dtor__0;
            Dafny.Sequence<byte> @_25216_ip__bytes = (@_25214_tuple_k).@dtor__1;
            if (!(@_25215_ok)) {
              return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(false, Dafny.Sequence<byte>.FromElements()));
            } else {
              return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(true, (Dafny.Sequence<byte>.FromElements(@_25213_b)).@Concat(@_25216_ip__bytes)));
            }
          }
        } else {
          return @_CmdLineParser__i_Compile.@__default.@parse__ip__addr__helper((@ip__shorts).Drop(new BigInteger(1)), (@current__octet__shorts).@Concat(Dafny.Sequence<ushort>.FromElements((@ip__shorts).Select(new BigInteger(0)))));
        }
      }
    }
    public static @_System.@__tuple_h2<bool,Dafny.Sequence<byte>> @parse__ip__addr(Dafny.Sequence<ushort> @ip__shorts) {
      @_System.@__tuple_h2<bool,Dafny.Sequence<byte>> @_25217_tuple = @_CmdLineParser__i_Compile.@__default.@parse__ip__addr__helper(@ip__shorts, Dafny.Sequence<ushort>.FromElements());
      bool @_25218_ok = (@_25217_tuple).@dtor__0;
      Dafny.Sequence<byte> @_25219_ip__bytes = (@_25217_tuple).@dtor__1;
      if ((@_25218_ok) && ((new BigInteger((@_25219_ip__bytes).Length)).@Equals(new BigInteger(4)))) {
        return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(true, @_25219_ip__bytes));
      } else {
        return new _System.@__tuple_h2<bool,Dafny.Sequence<byte>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<byte>>(false, Dafny.Sequence<byte>.FromElements()));
      }
    }
    public static @_System.@__tuple_h2<bool,@_Native____Io__s_Compile.@EndPoint> @parse__end__point(Dafny.Sequence<ushort> @ip__shorts, Dafny.Sequence<ushort> @port__shorts) {
      return @_CmdLineParser__i_Compile.@__default.@_hparse__end__point__FULL(@ip__shorts, @port__shorts);
    }
    public static void @test__unique_k(Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @endpoints, out bool @unique)
    {
      @unique = false;
    TAIL_CALL_START: ;
      @unique = true;
      BigInteger @_25220_i = BigInteger.Zero;
      @_25220_i = new BigInteger(0);
      while ((@_25220_i) < (new BigInteger((@endpoints).Length)))
      {
        BigInteger @_25221_j = BigInteger.Zero;
        @_25221_j = new BigInteger(0);
        while ((@_25221_j) < (new BigInteger((@endpoints).Length)))
        {
          if ((!(@_25220_i).@Equals(@_25221_j)) && (((@endpoints).Select(@_25220_i)).@Equals((@endpoints).Select(@_25221_j))))
          {
            @unique = false;
            { }
            return;
          }
          @_25221_j = (@_25221_j) + (new BigInteger(1));
        }
        @_25220_i = (@_25220_i) + (new BigInteger(1));
      }
      { }
    }
    public static @_System.@__tuple_h2<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>> @parse__end__points(Dafny.Sequence<Dafny.Sequence<ushort>> @args) {
      if ((new BigInteger((@args).Length)).@Equals(new BigInteger(0))) {
        return new _System.@__tuple_h2<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>>(true, Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.FromElements()));
      } else {
        @_System.@__tuple_h2<bool,@_Native____Io__s_Compile.@EndPoint> _let_tmp_rhs10 = @_CmdLineParser__i_Compile.@__default.@parse__end__point((@args).Select(new BigInteger(0)), (@args).Select(new BigInteger(1)));
        bool @_25222_ok1 = ((_System.@__tuple_h2____hMake<bool,@_Native____Io__s_Compile.@EndPoint>)(_let_tmp_rhs10)._D).@_0;
        @_Native____Io__s_Compile.@EndPoint @_25223_ep = ((_System.@__tuple_h2____hMake<bool,@_Native____Io__s_Compile.@EndPoint>)(_let_tmp_rhs10)._D).@_1;
        @_System.@__tuple_h2<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>> _let_tmp_rhs11 = @_CmdLineParser__i_Compile.@__default.@parse__end__points((@args).Drop(new BigInteger(2)));
        bool @_25224_ok2 = ((_System.@__tuple_h2____hMake<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>>)(_let_tmp_rhs11)._D).@_0;
        Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @_25225_rest = ((_System.@__tuple_h2____hMake<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>>)(_let_tmp_rhs11)._D).@_1;
        if (!((@_25222_ok1) && (@_25224_ok2))) {
          return new _System.@__tuple_h2<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>>(false, Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.FromElements()));
        } else {
          return new _System.@__tuple_h2<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>>(new _System.@__tuple_h2____hMake<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>>(true, (Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.FromElements(@_25223_ep)).@Concat(@_25225_rest)));
        }
      }
    }
    public static void @collect__cmd__line__args(out Dafny.Sequence<Dafny.Sequence<ushort>> @args)
    {
      @args = Dafny.Sequence<Dafny.Sequence<ushort>>.Empty;
    TAIL_CALL_START: ;
      uint @_25226_num__args = 0;
      uint _out440;
      @_Native____Io__s_Compile.@HostConstants.@NumCommandLineArgs(out _out440);
      @_25226_num__args = _out440;
      uint @_25227_i = 0;
      @_25227_i = 0U;
      @args = Dafny.Sequence<Dafny.Sequence<ushort>>.FromElements();
      while ((@_25227_i) < (@_25226_num__args))
      {
        ushort[] @_25228_arg = (ushort[])null;
        ushort[] _out441;
        @_Native____Io__s_Compile.@HostConstants.@GetCommandLineArg((ulong)(@_25227_i), out _out441);
        @_25228_arg = _out441;
        @args = (@args).@Concat(Dafny.Sequence<Dafny.Sequence<ushort>>.FromElements(Dafny.Helpers.SeqFromArray(@_25228_arg)));
        @_25227_i = (@_25227_i) + (1U);
      }
    }
    public static void @parse__cmd__line(out bool @ok, out @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @config, out byte @my__index)
    {
      @ok = false;
      @config = new @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration();
      @my__index = 0;
    TAIL_CALL_START: ;
      @ok = false;
      uint @_25229_num__args = 0;
      uint _out442;
      @_Native____Io__s_Compile.@HostConstants.@NumCommandLineArgs(out _out442);
      @_25229_num__args = _out442;
      if (((@_25229_num__args) < (4U)) || (!((@_25229_num__args) % (2U)).@Equals(0U)))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Incorrect number of command line arguments.\n"));
        System.Console.Write(Dafny.Sequence<char>.FromString("Expected: ./Main.exe [IP port]+ MyIndex\n"));
        System.Console.Write(Dafny.Sequence<char>.FromString("  where MyIndex is in the range of the number of IP-port pairs provided \n"));
        return;
      }
      Dafny.Sequence<Dafny.Sequence<ushort>> @_25230_args = Dafny.Sequence<Dafny.Sequence<ushort>>.Empty;
      Dafny.Sequence<Dafny.Sequence<ushort>> _out443;
      @_CmdLineParser__i_Compile.@__default.@collect__cmd__line__args(out _out443);
      @_25230_args = _out443;
      { }
      { }
      @_System.@__tuple_h2<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>> @_25231_tuple1 = new @_System.@__tuple_h2<bool,Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>>();
      @_25231_tuple1 = @_CmdLineParser__i_Compile.@__default.@parse__end__points((@_25230_args).Take((new BigInteger((@_25230_args).Length)) - (new BigInteger(1))).Drop(new BigInteger(1)));
      @ok = (@_25231_tuple1).@dtor__0;
      Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint> @_25232_endpoints = Dafny.Sequence<@_Native____Io__s_Compile.@EndPoint>.Empty;
      @_25232_endpoints = (@_25231_tuple1).@dtor__1;
      if ((!(@ok)) || ((new BigInteger((@_25232_endpoints).Length)) >= (BigInteger.Parse("18446744073709551615"))))
      {
        @ok = false;
        return;
      }
      @_System.@__tuple_h2<bool,byte> @_25233_tuple2 = new @_System.@__tuple_h2<bool,byte>();
      @_25233_tuple2 = @_CmdLineParser__i_Compile.@__default.@shorts__to__byte((@_25230_args).Select((new BigInteger((@_25230_args).Length)) - (new BigInteger(1))));
      @ok = (@_25233_tuple2).@dtor__0;
      @my__index = (@_25233_tuple2).@dtor__1;
      if (!(@ok))
      {
        return;
      }
      if (!(((0UL) <= ((ulong)(@my__index))) && (((ulong)(@my__index)) < ((ulong)(@_25232_endpoints).LongLength))))
      {
        @ok = false;
        return;
      }
      bool @_25234_unique = false;
      bool _out444;
      @_CmdLineParser__i_Compile.@__default.@test__unique_k(@_25232_endpoints, out _out444);
      @_25234_unique = _out444;
      if (!(@_25234_unique))
      {
        @ok = false;
        return;
      }
      @config = new _LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration(new _LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration_PaxosConcreteConfiguration(@_25232_endpoints));
      { }
      { }
      { }
      { }
      { }
      { }
    }
    public static @_System.@__tuple_h2<bool,@_Native____Io__s_Compile.@EndPoint> @_hparse__end__point__FULL(Dafny.Sequence<ushort> @ip__shorts, Dafny.Sequence<ushort> @port__shorts) {
      @_System.@__tuple_h2<bool,Dafny.Sequence<byte>> @_25235_tuple = @_CmdLineParser__i_Compile.@__default.@parse__ip__addr(@ip__shorts);
      bool @_25236_okay = (@_25235_tuple).@dtor__0;
      Dafny.Sequence<byte> @_25237_ip__bytes = (@_25235_tuple).@dtor__1;
      if (!(@_25236_okay)) {
        return new _System.@__tuple_h2<bool,@_Native____Io__s_Compile.@EndPoint>(new _System.@__tuple_h2____hMake<bool,@_Native____Io__s_Compile.@EndPoint>(false, new _Native____Io__s_Compile.@EndPoint(new _Native____Io__s_Compile.@EndPoint_EndPoint(Dafny.Sequence<byte>.FromElements(0, 0, 0, 0), 0))));
      } else {
        @_System.@__tuple_h2<bool,ushort> @_25238_tuple_k = @_CmdLineParser__i_Compile.@__default.@shorts__to__uint16(@port__shorts);
        bool @_25239_okay_k = (@_25238_tuple_k).@dtor__0;
        ushort @_25240_port = (@_25238_tuple_k).@dtor__1;
        if (!(@_25239_okay_k)) {
          return new _System.@__tuple_h2<bool,@_Native____Io__s_Compile.@EndPoint>(new _System.@__tuple_h2____hMake<bool,@_Native____Io__s_Compile.@EndPoint>(false, new _Native____Io__s_Compile.@EndPoint(new _Native____Io__s_Compile.@EndPoint_EndPoint(Dafny.Sequence<byte>.FromElements(0, 0, 0, 0), 0))));
        } else {
          return new _System.@__tuple_h2<bool,@_Native____Io__s_Compile.@EndPoint>(new _System.@__tuple_h2____hMake<bool,@_Native____Io__s_Compile.@EndPoint>(true, new _Native____Io__s_Compile.@EndPoint(new _Native____Io__s_Compile.@EndPoint_EndPoint(@_25237_ip__bytes, @_25240_port))));
        }
      }
    }
  }
} // end of namespace _CmdLineParser__i_Compile
namespace @_LiveRSL____Main__i_Compile {



  public partial class @__default {
    public static void @HostInit(out bool @ok, out @_LiveRSL____ReplicaImpl__i_Compile.@ReplicaImpl @scheduler, out @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @constants)
    {
      @ok = false;
      @scheduler = (@_LiveRSL____ReplicaImpl__i_Compile.@ReplicaImpl)null;
      @constants = new @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState();
    TAIL_CALL_START: ;
      @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration @_25241_config = new @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration();
      byte @_25242_my__index = 0;
      bool _out445;
      @_LiveRSL____PaxosConcreteConfiguration__i_Compile.@PaxosConcreteConfiguration _out446;
      byte _out447;
      @_CmdLineParser__i_Compile.@__default.@parse__cmd__line(out _out445, out _out446, out _out447);
      @ok = _out445;
      @_25241_config = _out446;
      @_25242_my__index = _out447;
      if (!(@ok))
      {
        return;
      }
      @_Native____Io__s_Compile.@EndPoint @_25243_me__ep = new @_Native____Io__s_Compile.@EndPoint();
      @_25243_me__ep = ((@_25241_config).@dtor_replicaIds).Select(@_25242_my__index);
      @scheduler = new @_LiveRSL____ReplicaImpl__i_Compile.@ReplicaImpl();
      @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState _out448;
      @_LiveRSL____ReplicaConstantsState__i_Compile.@__default.@InitReplicaConstantsState(@_25243_me__ep, @_25241_config, out _out448);
      @constants = _out448;
      { }
      { }
      { }
      bool _out449;
      (@scheduler).@Replica__Init(@constants, out _out449);
      @ok = _out449;
    }
    public static void @IronfleetMain(out BigInteger @exitCode)
    {
      @exitCode = BigInteger.Zero;
    TAIL_CALL_START: ;
      bool @_25244_ok = false;
      @_LiveRSL____ReplicaImpl__i_Compile.@ReplicaImpl @_25245_scheduler = (@_LiveRSL____ReplicaImpl__i_Compile.@ReplicaImpl)null;
      @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState @_25246_constants = new @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState();
      bool _out450;
      @_LiveRSL____ReplicaImpl__i_Compile.@ReplicaImpl _out451;
      @_LiveRSL____ReplicaConstantsState__i_Compile.@ReplicaConstantsState _out452;
      @_LiveRSL____Main__i_Compile.@__default.@HostInit(out _out450, out _out451, out _out452);
      @_25244_ok = _out450;
      @_25245_scheduler = _out451;
      @_25246_constants = _out452;
      if (!(@_25244_ok))
      {
        System.Console.Write(Dafny.Sequence<char>.FromString("Main: init failed\n"));
        @exitCode = new BigInteger(1);
        return;
      }
      { }
      @_LiveRSL____Main__i_Compile.@__default.@Loop(@_25245_scheduler);
      @exitCode = new BigInteger(0);
    }
    public static void @Loop(@_LiveRSL____ReplicaImpl__i_Compile.@ReplicaImpl @scheduler)
    {
    TAIL_CALL_START: ;
      bool @_25247_ok = false;
      @_25247_ok = true;
      while (@_25247_ok)
      {
        { }
        { }
        { }
        bool _out453;
        (@scheduler).@Replica__Next__main(out _out453);
        @_25247_ok = _out453;
        if (!(@_25247_ok))
        {
          return;
        }
        { }
        { }
      }
    }
  }
} // end of namespace _LiveRSL____Main__i_Compile











































































































public partial class @__default {
}
