using System;
using System.Numerics;
using System.Diagnostics;
using System.Threading;
using System.Collections.Concurrent;
using System.Collections.Generic;
using FStream = System.IO.FileStream;
using UClient = System.Net.Sockets.UdpClient;
using IEndPoint = System.Net.IPEndPoint;


namespace Native____Io__s_Compile {

public partial class HostConstants
{
    public static uint NumCommandLineArgs()
    {
        return (uint)System.Environment.GetCommandLineArgs().Length;
    }

    public static ushort[] GetCommandLineArg(ulong i)
    {
        return Array.ConvertAll(System.Environment.GetCommandLineArgs()[i].ToCharArray(), c => (ushort)c);
    }
}

public partial class IPEndPoint
{
    internal IEndPoint endpoint;
    internal IPEndPoint(IEndPoint endpoint) { this.endpoint = endpoint; }

    public byte[] GetAddress()
    {
        // no exceptions thrown:
        return (byte[])(endpoint.Address.GetAddressBytes().Clone());
    }

    public ushort GetPort()
    {
        // no exceptions thrown:
        return (ushort)endpoint.Port;
    }

    public static void Construct(byte[] ipAddress, ushort port, out bool ok, out IPEndPoint endpoint)
    {
        try
        {
            ipAddress = (byte[])(ipAddress.Clone());
            endpoint = new IPEndPoint(new IEndPoint(new System.Net.IPAddress(ipAddress), port));
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            endpoint = null;
            ok = false;
        }
    }
}

public struct Packet {
    public IEndPoint ep;
    public byte[] buffer;
}

public partial class UdpClient
{
    internal UClient client;
    internal Thread sender;
    internal Thread receiver;
    internal ConcurrentQueue<Packet> send_queue;
    internal ConcurrentQueue<Packet> receive_queue;

    internal UdpClient(UClient client) { 
      this.client = client;
      this.send_queue = new ConcurrentQueue<Packet>();
      this.receive_queue = new ConcurrentQueue<Packet>();
      this.sender = new Thread(SendLoop);
      this.sender.Start();
      this.receiver = new Thread(ReceiveLoop);
      this.receiver.Start();
    }

    // TODO: remove this
    public static void ConstructDeprecated(bool useIPv6, ushort port, out bool ok, out UdpClient udp)
    {
        try
        {
            var family = useIPv6 ? System.Net.Sockets.AddressFamily.InterNetworkV6 : System.Net.Sockets.AddressFamily.InterNetwork;
            udp = new UdpClient(new UClient(port, family));
            uint SIO_UDP_CONNRESET = 0x9800000C; // suppress UDP "connection" closed exceptions, since UDP is connectionless
            udp.client.Client.IOControl((System.Net.Sockets.IOControlCode)SIO_UDP_CONNRESET, new byte[] { 0 }, new byte[0]);
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            udp = null;
            ok = false;
        }
    }

    public static void Construct(IPEndPoint localEP, out bool ok, out UdpClient udp)
    {
        try
        {
            udp = new UdpClient(new UClient(localEP.endpoint));
            uint SIO_UDP_CONNRESET = 0x9800000C; // suppress UDP "connection" closed exceptions, since UDP is connectionless
            udp.client.Client.IOControl((System.Net.Sockets.IOControlCode)SIO_UDP_CONNRESET, new byte[] { 0 }, new byte[0]);
            udp.client.Client.ReceiveBufferSize = 8192 * 100;
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            udp = null;
            ok = false;
        }
    }

    public void Close(out bool ok)
    {
        try
        {
            client.Close();
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            ok = false;
        }
    }

    public void Receive(int timeLimit, out bool ok, out bool timedOut, out IPEndPoint remote, out byte[] buffer)
    {
        buffer = null;
        remote = null;
        try
        {
            Packet packet;
            bool dequeued = this.receive_queue.TryDequeue(out packet);
            if (!dequeued) {
                if (timeLimit == 0) {
                    ok = true;
                    timedOut = true;
                    return;
                } else {
                    System.Console.Out.WriteLine("Going to sleep unexpectedly!");
                    Thread.Sleep(timeLimit);  // REVIEW: This is very conservative, but shouldn't matter, since we don't use this path
                    Receive(0, out ok, out timedOut, out remote, out buffer);
                }
            } else {
                //System.Console.Out.WriteLine("Dequeued a packet from: " + packet.ep.Address);
                timedOut = false;
                remote = new IPEndPoint(packet.ep);
                buffer = new byte[packet.buffer.Length];
                Array.Copy(packet.buffer, buffer, packet.buffer.Length);
                ok = true;
            }     
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            timedOut = false;
            ok = false;
        }
    }

    public void ReceiveLoop() {
        while (true) {
            try {
                Packet packet = new Packet();
                packet.buffer = client.Receive(ref packet.ep);
                this.receive_queue.Enqueue(packet);
                //System.Console.Out.WriteLine("Enqueued a packet from: " + packet.ep.Address);
            } catch (Exception e) {
                System.Console.Error.WriteLine(e);
            }
        }
    }

    public void SendLoop() {
        while (true) {
            try {
                Packet packet;
                bool dequeued = this.send_queue.TryDequeue(out packet);
                if (dequeued) {                
                      int nSent = client.Send(packet.buffer, packet.buffer.Length, packet.ep);
                      if (nSent != packet.buffer.Length) {
                          //throw new Exception("only sent " + nSent + " of " + packet.buffer.Length + " bytes");
                          System.Console.Error.Write("only sent " + nSent + " of " + packet.buffer.Length + " bytes");
                      }                
                }
            } catch (Exception e) {
              System.Console.Error.WriteLine(e);
            }
        }
    }

    public bool Send(IPEndPoint remote, byte[] buffer)
    {
        Packet p = new Packet();
        p.ep = remote.endpoint;
        p.buffer = new byte[buffer.Length];
        Array.Copy(buffer, p.buffer, buffer.Length);
        this.send_queue.Enqueue(p);
        return true; // ok
    }

}

public partial class FileStream
{
    internal FStream fstream;
    internal FileStream(FStream fstream) { this.fstream = fstream; }

    public static void Open(char[] name, out bool ok, out FileStream f)
    {
        try
        {
            f = new FileStream(new FStream(new string(name), System.IO.FileMode.OpenOrCreate, System.IO.FileAccess.ReadWrite));
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            f = null;
            ok = false;
        }
    }

    public void Close(out bool ok)
    {
        try
        {
            fstream.Close();
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            ok = false;
        }
    }

    public void Read(int fileOffset, byte[] buffer, int start, int end, out bool ok)
    {
        try
        {
            fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
            fstream.Read(buffer, start, end - start);
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            ok = false;
        }
    }

    public void Write(int fileOffset, byte[] buffer, int start, int end, out bool ok)
    {
        try
        {
            fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
            fstream.Write(buffer, start, end - start);
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            ok = false;
        }
    }

    public void Flush(out bool ok)
    {
        try
        {
            fstream.Flush();
            ok = true;
        }
        catch (Exception e)
        {
            System.Console.Error.WriteLine(e);
            ok = false;
        }
    }
}

public partial class Time
{
    static Stopwatch watch;

    public static void Initialize()
    {
        watch = new Stopwatch();
        watch.Start();
    }

    public static ulong GetTime()
    {
        return (ulong) (DateTime.Now.Ticks / 10000);
    }
    
    public static ulong GetDebugTimeTicks()
    {
        return (ulong) watch.ElapsedTicks;
    }
    
    public static void RecordTiming(char[] name, ulong time)
    {
        var str = new string(name);
        Common.Profiler.Record(str, (long)time);
    }
}

public partial class MutableSet<T>
{
    private HashSet<T> setImpl;
    public MutableSet() {
        this.setImpl = new HashSet<T>();
    }

    public static Dafny.Set<T> SetOf(MutableSet<T> s) { return Dafny.Set<T>.FromCollection(s.setImpl); }

    public static MutableSet<T> EmptySet(Dafny.TypeDescriptor<T> typeDescriptor) { return new MutableSet<T>(); }

    public BigInteger Size() { return new BigInteger(this.setImpl.Count); }
    
    public ulong SizeModest() { return (ulong)this.setImpl.Count; }

    public bool Contains(T x) { return this.setImpl.Contains(x); }

    public void Add(T x) { this.setImpl.Add(x); }
           
    public void AddSet(MutableSet<T> s) { this.setImpl.UnionWith(s.setImpl); }

    public void TransferSet(MutableSet<T> s) { this.setImpl = s.setImpl; s.setImpl = new HashSet<T>(); }
           
    public void Remove(T x) { this.setImpl.Remove(x); }

    public void RemoveAll() { this.setImpl.Clear(); }
}

public partial class MutableMap<K,V>
{
    private Dictionary<K,V> mapImpl;

    // TODO: This is pretty inefficient.  Should change Dafny's interface to allow us to 
    // pass in an enumerable or an ImmutableDictionary
    public static Dafny.Map<K,V> MapOf(MutableMap<K,V> s) {
      List<Dafny.Pair<K, V>> pairs = new List<Dafny.Pair<K, V>>();
      foreach (var pair in s.mapImpl) {
        pairs.Add(new Dafny.Pair<K, V>(pair.Key, pair.Value));
      }
      return Dafny.Map<K,V>.FromCollection(pairs); 
    }

    public static MutableMap<K, V> EmptyMap()
    {
      var m = new MutableMap<K,V>();
      m.mapImpl = new Dictionary<K, V>();
      return m;
    }

    public static MutableMap<K, V> FromMap(Dafny.IMap<K, V> m) {
      var new_m = new MutableMap<K,V>();
      new_m.mapImpl = new Dictionary<K, V>();
      foreach (var kv in m.ItemEnumerable) {
        new_m.mapImpl.Add(kv.Car, kv.Cdr);
      }
      return new_m;
    }

    public BigInteger Size() { return new BigInteger(this.mapImpl.Count); }

    public ulong SizeModest() { return (ulong)this.mapImpl.Count; }

    public bool Contains(K key) { return this.mapImpl.ContainsKey(key); }

    public void TryGetValue(K key, out bool contains, out V val)
    {
      contains = this.mapImpl.TryGetValue(key, out val);
    }

    public void Set(K key, V val) { this.mapImpl[key] = val; }
           
    //public void AddMap(MutableMap<K,V> s) { this.mapImpl.}

    public void Remove(K key) { this.mapImpl.Remove(key); }
}

public partial class @Arrays
{
    public static void @CopySeqIntoArray<A>(Dafny.ISequence<A> src, ulong srcIndex, A[] dst, ulong dstIndex, ulong len) {
        System.Array.Copy(src.Elements, (long)srcIndex, dst, (long)dstIndex, (long)len);
    }

}


}

