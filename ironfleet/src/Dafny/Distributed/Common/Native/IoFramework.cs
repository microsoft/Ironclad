using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Threading;
using System.Threading.Tasks.Dataflow;

namespace IronfleetIoFramework
{
  public class CryptographicIdentity
  {
  }

  public class IoEncoder
  {
    private static int MAX_IO_SIZE = 0x80_0000 /* 8 MB */;

    public static bool ReadBytes(Stream stream, byte[] buf, int offset, UInt64 byteCount)
    {
      UInt64 bytesRead = 0;
      while (bytesRead < byteCount)
      {
        int bytesToRead = (byteCount - bytesRead > (UInt64)(MAX_IO_SIZE)) ? MAX_IO_SIZE : (int)(byteCount - bytesRead);
        int additionalBytesRead = stream.Read(buf, offset + (int)bytesRead, bytesToRead);
        if (additionalBytesRead == 0) {
          return false;
        }
        bytesRead += (UInt64)additionalBytesRead;
      }
      return true;
    }

    public static void WriteBytes(Stream stream, byte[] buf, int offset, UInt64 byteCount)
    {
      UInt64 bytesWritten = 0;
      while (bytesWritten < byteCount)
      {
        int bytesToWrite = (byteCount - bytesWritten > (UInt64)(MAX_IO_SIZE)) ? MAX_IO_SIZE : (int)(byteCount - bytesWritten);
        stream.Write(buf, offset + (int)bytesWritten, bytesToWrite);
        bytesWritten += (UInt64)(bytesToWrite);
      }
    }

    public static UInt64 ExtractUInt64(byte[] bytes, int offset)
    {
      byte[] extractedBytes = bytes.Skip(offset).Take(8).ToArray();
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(extractedBytes);
      }
      return BitConverter.ToUInt64(extractedBytes, 0);
    }

    public static UInt32 ExtractUInt32(byte[] bytes, int offset)
    {
      byte[] extractedBytes = bytes.Skip(offset).Take(4).ToArray();
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(extractedBytes);
      }
      return BitConverter.ToUInt32(extractedBytes, 0);
    }

    public static Int32 ExtractInt32(byte[] bytes, int offset)
    {
      byte[] extractedBytes = bytes.Skip(offset).Take(4).ToArray();
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(extractedBytes);
      }
      return BitConverter.ToInt32(extractedBytes, 0);
    }

    public static void WriteUInt64(Stream stream, UInt64 value)
    {
      var bytes = BitConverter.GetBytes(value);
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(bytes);
      }
      WriteBytes(stream, bytes, 0, 8);
    }

    public static void WriteUInt32(Stream stream, UInt32 value)
    {
      var bytes = BitConverter.GetBytes(value);
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(bytes);
      }
      WriteBytes(stream, bytes, 0, 4);
    }

    public static void WriteInt32(Stream stream, Int32 value)
    {
      var bytes = BitConverter.GetBytes(value);
      if (BitConverter.IsLittleEndian) {
        Array.Reverse(bytes);
      }
      WriteBytes(stream, bytes, 0, 4);
    }

    public static bool ReadUInt64(Stream stream, out UInt64 value)
    {
      byte[] buf8 = new byte[8];
      bool success = ReadBytes(stream, buf8, 0, 8);
      if (success) {
        if (BitConverter.IsLittleEndian) {
          Array.Reverse(buf8);
        }
        value = BitConverter.ToUInt64(buf8);
      }
      else {
        value = 0;
      }
      return success;
    }

    public static bool ReadUInt32(Stream stream, out UInt32 value)
    {
      byte[] buf4 = new byte[4];
      bool success = ReadBytes(stream, buf4, 0, 4);
      if (success) {
        if (BitConverter.IsLittleEndian) {
          Array.Reverse(buf4);
        }
        value = BitConverter.ToUInt32(buf4);
      }
      else {
        value = 0;
      }
      return success;
    }

    public static bool ReadInt32(Stream stream, out Int32 value)
    {
      byte[] buf4 = new byte[4];
      bool success = ReadBytes(stream, buf4, 0, 4);
      if (success) {
        if (BitConverter.IsLittleEndian) {
          Array.Reverse(buf4);
        }
        value = BitConverter.ToInt32(buf4);
      }
      else {
        value = 0;
      }
      return success;
    }
  }

  public class Packet
  {
    public IPEndPoint ep;
    public byte[] message;

    public Packet(IPEndPoint i_ep, byte[] i_message)
    {
      ep = i_ep;
      message = i_message;
    }
  }

  public class SendTask
  {
    public IPEndPoint ep;
    public byte[] message;
    public int numTriesSoFar;

    public SendTask(IPEndPoint i_ep, byte[] i_message, int i_numTriesSoFar)
    {
      ep = i_ep;
      message = i_message;
      numTriesSoFar = i_numTriesSoFar;
    }
  }

  public class ReceiverThread
  {
    private IoScheduler scheduler;
    private TcpClient conn;
    private IPEndPoint otherEndpoint;
    private bool asServer;
    private NetworkStream stream;

    private ReceiverThread(IoScheduler i_scheduler, TcpClient i_conn, IPEndPoint i_otherEndpoint, bool i_asServer)
    {
      scheduler = i_scheduler;
      conn = i_conn;
      otherEndpoint = i_otherEndpoint;
      asServer = i_asServer;
      stream = conn.GetStream();
    }

    public void Run()
    {
      try
      {
        ReceiveLoop();
      }
      catch (Exception e)
      {
        scheduler.ReportException(e, "receiving from", otherEndpoint);
      }
    }

    public static ReceiverThread Create(IoScheduler scheduler, TcpClient conn, IPEndPoint otherEndpoint, bool asServer)
    {
      ReceiverThread receiverThread = new ReceiverThread(scheduler, conn, otherEndpoint, asServer);
      Thread t = new Thread(receiverThread.Run);
      t.Start();
      return receiverThread;
    }

    private void ReceiveLoop()
    {
      bool success;

      if (scheduler.Verbose) {
        Console.WriteLine("Starting receive loop with other endpoint {0}", IoScheduler.EndpointToString(otherEndpoint));
      }

      // The first thing sent by the client is its effective port
      // number.

      if (asServer) {
        Int32 portNumber;
        success = IoEncoder.ReadInt32(stream, out portNumber);
        if (!success)
        {
          Console.Error.WriteLine("Failed to receive port number from {0}", IoScheduler.EndpointToString(otherEndpoint));
          return;
        }
        if (scheduler.Verbose) {
          Console.WriteLine("Received effective port number {0} from {1}", portNumber, IoScheduler.EndpointToString(otherEndpoint));
        }
        otherEndpoint.Port = portNumber;

        // Now that we know who we're talking to, we can create the
        // sender thread.

        SenderThread senderThread = SenderThread.Create(scheduler, conn, otherEndpoint, asServer);
      }

      while (true)
      {
        // Read the next message's size.

        UInt64 messageSize;
        success = IoEncoder.ReadUInt64(stream, out messageSize);
        if (!success) {
          Console.Error.WriteLine("Failed to receive message size from {0}", IoScheduler.EndpointToString(otherEndpoint));
          return;
        }
        if (scheduler.Verbose) {
          Console.WriteLine("Received message size {0} from {1}", messageSize, IoScheduler.EndpointToString(otherEndpoint));
        }

        byte[] messageBuf = new byte[messageSize];
        success = IoEncoder.ReadBytes(stream, messageBuf, 0, messageSize);
        if (!success) {
          Console.Error.WriteLine("Failed to receive message of size {0} from {1}",
                                  messageSize, IoScheduler.EndpointToString(otherEndpoint));
          return;
        }
        if (scheduler.Verbose) {
          Console.WriteLine("Received message of size {0} from {1}", messageSize, IoScheduler.EndpointToString(otherEndpoint));
        }

        Packet packet = new Packet(otherEndpoint, messageBuf);
        scheduler.NoteReceivedPacket(packet);
      }
    }
  }

  public class SenderThread
  {
    private IoScheduler scheduler;
    private TcpClient conn;
    private IPEndPoint otherEndpoint;
    private bool asServer;
    private NetworkStream stream;
    private BufferBlock<SendTask> sendQueue;
    private SendTask currentSendTask;

    private SenderThread(IoScheduler i_scheduler, TcpClient i_conn, IPEndPoint i_otherEndpoint, bool i_asServer)
    {
      scheduler = i_scheduler;
      conn = i_conn;
      otherEndpoint = i_otherEndpoint;
      asServer = i_asServer;
      sendQueue = new BufferBlock<SendTask>();
      currentSendTask = null;
    }

    public void Run()
    {
      try
      {
        SendLoop();
      }
      catch (Exception e)
      {
        scheduler.ReportException(e, "sending to", otherEndpoint);
      }

      scheduler.UnregisterSender(otherEndpoint, this);

      // If we crashed in the middle of sending a packet, re-queue it
      // for sending by another sender thread.
      
      if (currentSendTask != null) {
        scheduler.ResendPacket(currentSendTask);
        currentSendTask = null;
      }

      // If there are packets queued for us to send, re-queue them
      // for sending by another sender thread.

      while (sendQueue.TryReceive(out currentSendTask)) {
        scheduler.ResendPacket(currentSendTask);
        currentSendTask = null;
      }
    }

    public static SenderThread Create(IoScheduler scheduler, TcpClient conn, IPEndPoint otherEndpoint, bool asServer)
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Creating sender thread for endpoint {0}", IoScheduler.EndpointToString(otherEndpoint));
      }
      
      SenderThread senderThread = new SenderThread(scheduler, conn, otherEndpoint, asServer);
      scheduler.RegisterSender(otherEndpoint, senderThread);
      Thread t = new Thread(senderThread.Run);
      t.Start();
      return senderThread;
    }

    private void SendLoop()
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Starting send loop with other endpoint {0}", IoScheduler.EndpointToString(otherEndpoint));
      }

      // If we're not the server, we need to initiate the connection.

      if (!asServer) {
        var zeroEndpoint = new IPEndPoint(scheduler.MyEndpoint.Address, 0);

        try {
          conn = new TcpClient(zeroEndpoint);
        }
        catch (Exception e)
        {
          Console.Error.WriteLine("Could not bind to address {0} to send to {1}, causing exception:\n{2}",
                                  zeroEndpoint.Address, IoScheduler.EndpointToString(otherEndpoint), e);
          throw;
        }

        if (scheduler.Verbose) {
          Console.WriteLine("Starting connection to {0}", IoScheduler.EndpointToString(otherEndpoint));
        }
        conn.Connect(otherEndpoint);

        // Now that the connection is successful, create a thread to
        // receive packets on it.

        ReceiverThread receiverThread = ReceiverThread.Create(scheduler, conn, otherEndpoint, asServer);
      }
      
      stream = conn.GetStream();

      // The first thing sent by the client is its effective port
      // number.

      if (!asServer) {
        Int32 myPortNumber = scheduler.MyEndpoint.Port;
        if (scheduler.Verbose) {
          Console.WriteLine("Sending my effective port number {0} to {1}", myPortNumber, IoScheduler.EndpointToString(otherEndpoint));
        }
        IoEncoder.WriteInt32(stream, myPortNumber);
      }

      while (true)
      {
        // Wait for there to be a packet to send.

        currentSendTask = sendQueue.Receive();

        // Send its length as an 8-byte value.

        UInt64 messageSize = (UInt64)currentSendTask.message.Length;
        IoEncoder.WriteUInt64(stream, messageSize);
        if (scheduler.Verbose) {
          Console.WriteLine("Sent message size {0} to {1}", messageSize, IoScheduler.EndpointToString(otherEndpoint));
        }

        // Send its contents.

        IoEncoder.WriteBytes(stream, currentSendTask.message, 0, messageSize);
        if (scheduler.Verbose) {
          Console.WriteLine("Sent message of size {0} to {1}", messageSize, IoScheduler.EndpointToString(otherEndpoint));
        }

        // Set the currentSendTask to null so we know we don't have to
        // resend it if the connection fails.

        currentSendTask = null;
      }
    }

    public void EnqueueSendTask(SendTask sendTask)
    {
      sendQueue.Post(sendTask);
    }
  }

  public class ListenerThread
  {
    private IoScheduler scheduler;
    private TcpListener listener;

    public ListenerThread(IoScheduler i_scheduler)
    {
      scheduler = i_scheduler;
    }

    public void Run()
    {
      while (true)
      {
        try
        {
          ListenLoop();
        }
        catch (Exception e)
        {
          Console.Error.WriteLine("Listener thread caught the following exception, so restarting:\n{0}", e);
        }
      }
    }

    private void ListenLoop()
    {
      listener = new TcpListener(scheduler.MyEndpoint);
      listener.Start();
      while (true)
      {
        if (scheduler.Verbose) {
          Console.WriteLine("Waiting for the next incoming connection.");
        }
        TcpClient client = listener.AcceptTcpClient();
        if (client.Client.RemoteEndPoint.AddressFamily != AddressFamily.InterNetwork)
        {
          Console.Error.WriteLine("Ignoring incoming connection from non-IPv4 source");
          continue;
        }
        IPEndPoint clientEndpoint = (IPEndPoint)client.Client.RemoteEndPoint;
        if (scheduler.Verbose) {
          Console.WriteLine("Received an incoming connection from {0}", IoScheduler.EndpointToString(clientEndpoint));
        }

        ReceiverThread receiverThread = ReceiverThread.Create(scheduler, client, clientEndpoint, true /* as server */);
      }
    }
  }

  public class SendDispatchThread
  {
    private IoScheduler scheduler;
    private BufferBlock<SendTask> sendQueue;

    public SendDispatchThread(IoScheduler i_scheduler)
    {
      scheduler = i_scheduler;
      sendQueue = new BufferBlock<SendTask>();
    }

    public void Run()
    {
      while (true)
      {
        try
        {
          SendDispatchLoop();
        }
        catch (Exception e)
        {
          Console.Error.WriteLine("Send dispatch thread caught the following exception, so restarting:\n{0}", e);
        }
      }
    }

    private void SendDispatchLoop()
    {
      while (true)
      {
        if (scheduler.Verbose) {
          Console.WriteLine("Waiting for the next send to dispatch.");
        }

        SendTask sendTask = sendQueue.Receive();

        if (scheduler.Verbose) {
          Console.WriteLine("Dispatching send of message of size {0} to {1}",
                            sendTask.message.Length, IoScheduler.EndpointToString(sendTask.ep));
        }

        SenderThread senderThread = scheduler.FindSenderForEndpoint(sendTask.ep);

        if (senderThread == null) {
          senderThread = SenderThread.Create(scheduler, null, sendTask.ep, false);
        }

        senderThread.EnqueueSendTask(sendTask);
      }
    }

    public void EnqueueSendTask(SendTask sendTask)
    {
      sendQueue.Post(sendTask);
    }
  }

  public class IoScheduler
  {
    private IPEndPoint myEndpoint;
    private bool onlyClient;
    private bool verbose;
    private int maxSendTries;
    private BufferBlock<Packet> receiveQueue;
    private Dictionary<IPEndPoint, List<SenderThread>> endpointToSenderMap;
    private ListenerThread listenerThread;
    private SendDispatchThread sendDispatchThread;

    public IoScheduler(IPEndPoint i_myEndpoint, bool i_onlyClient = false, bool i_verbose = false, int i_maxSendTries = 3)
    {
      myEndpoint = i_myEndpoint;
      onlyClient = i_onlyClient;
      verbose = i_verbose;
      maxSendTries = i_maxSendTries;
      if (verbose) {
        Console.WriteLine("Starting I/O scheduler with endpoint {0}, onlyClient = {1}, maxSendTries = {2}",
                          EndpointToString(i_myEndpoint), onlyClient, maxSendTries);
      }
      receiveQueue = new BufferBlock<Packet>();
      endpointToSenderMap = new Dictionary<IPEndPoint, List<SenderThread>>();
      Start();
    }

    private void Start()
    {
      sendDispatchThread = new SendDispatchThread(this);
      Thread st = new Thread(sendDispatchThread.Run);
      st.Start();

      // Start a thread to listen on a port bound to MyEndpoint.  But,
      // if we're only supposed to connect as a client, don't do this.

      if (!onlyClient) {
        listenerThread = new ListenerThread(this);
        Thread lt = new Thread(listenerThread.Run);
        lt.Start();
      }
    }

    public IPEndPoint MyEndpoint { get { return myEndpoint; } }
    public bool Verbose { get { return verbose; } }
    public bool OnlyClient { get { return onlyClient; } }

    /////////////////////////////////////
    // SENDING
    /////////////////////////////////////

    public void RegisterSender(IPEndPoint ep, SenderThread senderThread)
    {
      lock (endpointToSenderMap)
      {
        if (endpointToSenderMap.ContainsKey(ep)) {
          endpointToSenderMap[ep].Insert(0, senderThread);
        }
        else {
          endpointToSenderMap[ep] = new List<SenderThread> { senderThread };
        }
      }
    }

    public void UnregisterSender(IPEndPoint ep, SenderThread senderThread)
    {
      lock (endpointToSenderMap)
      {
        endpointToSenderMap[ep].Remove(senderThread);
      }
    }

    public SenderThread FindSenderForEndpoint(IPEndPoint ep)
    {
      lock (endpointToSenderMap)
      {
        if (endpointToSenderMap.ContainsKey(ep) && endpointToSenderMap[ep].Count > 0) {
          return endpointToSenderMap[ep][0];
        }
      }

      return null;
    }

    /////////////////////////////////////
    // RECEIVING
    /////////////////////////////////////

    public void NoteReceivedPacket(Packet packet)
    {
      receiveQueue.Post(packet);
    }

    /////////////////////////////////////
    // UTILITY METHODS
    /////////////////////////////////////

    public static string EndpointToString(IPEndPoint ep)
    {
      return string.Format("{0}:{1}", ep.Address, ep.Port);
    }

    public void ReportException(Exception e, string activity, IPEndPoint otherEndpoint)
    {
      if (e is IOException ioe) {
        e = ioe.InnerException;
      }
      if (e is SocketException se) {
        if (se.SocketErrorCode == SocketError.ConnectionReset) {
          Console.WriteLine("Stopped {0} {1} because of a connection reset. Will try again later if necessary.",
                            activity, otherEndpoint);
          return;
        }
        if (se.SocketErrorCode == SocketError.ConnectionRefused) {
          Console.WriteLine("Stopped {0} {1} because the connection was refused. Will try again later if necessary.",
                            activity, otherEndpoint);
          return;
        }
      }
      Console.WriteLine("Stopped {0} {1} because of the following exception, but will try again later if necessary:\n{2}",
                        activity, otherEndpoint, e);
    }

    ///////////////////////////////////
    // API for IoNative.cs
    ///////////////////////////////////

    public void ReceivePacket(Int32 timeLimit, out bool ok, out bool timedOut, out IPEndPoint remote, out byte[] message)
    {
      Packet packet;

      try {
        if (timeLimit == 0) {
          timedOut = !receiveQueue.TryReceive(out packet);
        }
        else {
          TimeSpan timeSpan = TimeSpan.FromMilliseconds(timeLimit);
          packet = receiveQueue.Receive(timeSpan);
          timedOut = false;
        }

        ok = true;
        if (timedOut) {
          remote = null;
          message = null;
        }
        else {
          remote = new IPEndPoint(packet.ep.Address, packet.ep.Port);
          message = packet.message;
          if (verbose) {
            Console.WriteLine("Dequeueing a packet of size {0} from {1}", packet.message.Length, EndpointToString(packet.ep));
          }
        }
      }
      catch (TimeoutException) {
        remote = null;
        message = null;
        ok = true;
        timedOut = true;
      }
      catch (Exception e) {
        Console.Error.WriteLine("Unexpected error trying to read packet from packet queue. Exception:\n{0}", e);
        remote = null;
        message = null;
        ok = false;
        timedOut = false;
      }
    }

    public bool SendPacket(IPEndPoint remote, byte[] message)
    {
      try {
        byte[] messageCopy = new byte[message.Length];
        Array.Copy(message, messageCopy, message.Length);
        SendTask sendTask = new SendTask(remote, messageCopy, 0);
        if (verbose) {
          Console.WriteLine("Enqueueing send of a message of size {0} to {1}", message.Length, EndpointToString(remote));
        }
        sendDispatchThread.EnqueueSendTask(sendTask);
        return true;
      }
      catch (Exception e) {
        Console.Error.WriteLine("Unexpected error when trying to send a message.  Exception:\n{0}", e);
        return false;
      }
    }

    public void ResendPacket(SendTask sendTask)
    {
      sendTask.numTriesSoFar++;
      if (sendTask.numTriesSoFar < maxSendTries) {
        sendDispatchThread.EnqueueSendTask(sendTask);
      }
    }

    ///////////////////////////////////
    // Extra API calls for client
    ///////////////////////////////////

    public void Connect(IPEndPoint otherEndpoint)
    {
      SenderThread senderThread = FindSenderForEndpoint(otherEndpoint);
      if (senderThread == null) {
        senderThread = SenderThread.Create(this, null, otherEndpoint, false);
      }
    }
  }
}
