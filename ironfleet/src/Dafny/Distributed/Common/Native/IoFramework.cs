using System;
using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Security;
using System.Net.Sockets;
using System.Threading;
using System.Threading.Tasks.Dataflow;
using System.Security.Cryptography;
using System.Security.Cryptography.X509Certificates;

namespace IronfleetIoFramework
{
  public class PrivateIdentity
  {
    public string FriendlyName { get; set; }
    public byte[] Pkcs12 { get; set; }
    public string HostNameOrAddress { get; set; }
    public int Port { get; set; }
  }

  public class PublicIdentity
  {
    public string FriendlyName { get; set; }
    public byte[] PublicKey { get; set; }
    public string HostNameOrAddress { get; set; }
    public int Port { get; set; }
  }

  public class ServiceIdentity
  {
    public string FriendlyName { get; set; }
    public string ServiceType { get; set; }
    public List<PublicIdentity> Servers { get; set; }
  }

  public class EndpointInfo
  {
    private string friendlyName;
    private string hostNameOrAddress;
    private IPEndPoint ep;

    public EndpointInfo(string i_friendlyName, string i_hostNameOrAddress, IPEndPoint i_ep)
    {
      friendlyName = i_friendlyName;
      hostNameOrAddress = i_hostNameOrAddress;
      ep = i_ep;
    }

    public string FriendlyName { get { return friendlyName; } }
    public string HostNameOrAddress { get { return hostNameOrAddress; } }
    public IPEndPoint Endpoint { get { return ep; } }
  }

  public class ByteArrayComparer : IEqualityComparer<byte[]>
  {
    private static ByteArrayComparer staticDefault;

    public static ByteArrayComparer Default()
    {
      if (staticDefault == null) {
         staticDefault = new ByteArrayComparer();
      }
      return staticDefault;
    }

    public bool Equals (byte[] a1, byte[] a2)
    {
      return StructuralComparisons.StructuralEqualityComparer.Equals(a1, a2);
    }

    public int GetHashCode(byte[] a)
    {
      return StructuralComparisons.StructuralEqualityComparer.GetHashCode(a);
    }
  }

  public class IronfleetCrypto
  {
    public static bool CreateIdentity(string friendlyName, string publicHostNameOrAddress, int publicPort,
                                      string localHostNameOrAddress, int localPort,
                                      out PublicIdentity publicIdentity, out PrivateIdentity privateIdentity)
    {
      var key = RSA.Create(4096);
      var subject = string.Format("CN = {0}", friendlyName);
      var req = new CertificateRequest(subject, key, HashAlgorithmName.SHA256, RSASignaturePadding.Pss);
      var now = DateTime.Now;
      var expiry = now.AddYears(10);
      var cert = req.CreateSelfSigned(now, expiry);
      var pkcs12 = cert.Export(X509ContentType.Pkcs12, "" /* empty password */);

      publicIdentity = new PublicIdentity {
        FriendlyName = friendlyName,
        PublicKey = IoScheduler.GetCertificatePublicKey(cert),
        HostNameOrAddress = publicHostNameOrAddress,
        Port = publicPort
      };
      privateIdentity = new PrivateIdentity {
        FriendlyName = friendlyName,
        Pkcs12 = pkcs12,
        HostNameOrAddress = localHostNameOrAddress,
        Port = localPort
      };
      return true;
    }

    public static X509Certificate2 CreateTransientClientIdentity ()
    {
      var key = RSA.Create(2048);
      var req = new CertificateRequest("client", key, HashAlgorithmName.SHA256, RSASignaturePadding.Pss);
      var now = DateTime.Now;
      var expiry = now.AddYears(1);
      return req.CreateSelfSigned(now, expiry);
    }
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

  public class ReceivedPacket
  {
    private X509Certificate2 senderCert;
    private byte[] message;

    public ReceivedPacket(X509Certificate2 i_senderCert, byte[] i_message)
    {
      senderCert = i_senderCert;
      message = i_message;
    }

    public X509Certificate2 SenderCert { get { return senderCert; } }
    public byte[] Message { get { return message; } }
  }

  public class SendTask
  {
    private byte[] destinationPublicKey;
    private byte[] message;
    private int numTriesSoFar;

    public SendTask(byte[] i_destinationPublicKey, byte[] i_message)
    {
      destinationPublicKey = i_destinationPublicKey;
      message = i_message;
      numTriesSoFar = 0;
    }

    public byte[] DestinationPublicKey { get { return destinationPublicKey; } }
    public byte[] Message { get { return message; } }

    public int IncrementNumTriesSoFar()
    {
      numTriesSoFar++;
      return numTriesSoFar;
    }
  }

  public class ReceiverThread
  {
    private IoScheduler scheduler;
    private SslStream stream;
    private X509Certificate2 remoteCert;
    private bool asServer;

    private ReceiverThread(IoScheduler i_scheduler, SslStream i_stream, bool i_asServer)
    {
      scheduler = i_scheduler;
      stream = i_stream;
      remoteCert = stream.RemoteCertificate as X509Certificate2;
      asServer = i_asServer;
    }

    public void Run()
    {
      try
      {
        ReceiveLoop();
      }
      catch (Exception e)
      {
        scheduler.ReportException(e, "receiving from", IoScheduler.GetCertificatePublicKey(remoteCert));
      }
    }

    public static ReceiverThread Create(IoScheduler scheduler, SslStream stream, bool asServer)
    {
      ReceiverThread receiverThread = new ReceiverThread(scheduler, stream, asServer);
      Thread t = new Thread(receiverThread.Run);
      t.Start();
      return receiverThread;
    }

    private void ReceiveLoop()
    {
      bool success;

      if (scheduler.Verbose) {
        Console.WriteLine("Starting receive loop with other endpoint {0}", IoScheduler.CertificateToString(remoteCert));
      }

      while (true)
      {
        // Read the next message's size.

        UInt64 messageSize;
        success = IoEncoder.ReadUInt64(stream, out messageSize);
        if (!success) {
          Console.Error.WriteLine("Failed to receive message size from {0}", IoScheduler.CertificateToString(remoteCert));
          return;
        }
        if (scheduler.Verbose) {
          Console.WriteLine("Received message size {0} from {1}", messageSize, IoScheduler.CertificateToString(remoteCert));
        }

        byte[] messageBuf = new byte[messageSize];
        success = IoEncoder.ReadBytes(stream, messageBuf, 0, messageSize);
        if (!success) {
          Console.Error.WriteLine("Failed to receive message of size {0} from {1}",
                                  messageSize, IoScheduler.CertificateToString(remoteCert));
          return;
        }
        if (scheduler.Verbose) {
          Console.WriteLine("Received message of size {0} from {1}", messageSize, IoScheduler.CertificateToString(remoteCert));
        }

        ReceivedPacket packet = new ReceivedPacket(remoteCert, messageBuf);
        scheduler.NoteReceivedPacket(packet);
      }
    }
  }

  public class SenderThread
  {
    private IoScheduler scheduler;
    private X509Certificate2 remoteCert;
    private bool asServer;
    private SslStream stream;
    private byte[] destinationPublicKey;
    private BufferBlock<SendTask> sendQueue;
    private SendTask currentSendTask;

    private SenderThread(IoScheduler i_scheduler, SslStream i_stream, byte[] i_destinationPublicKey, bool i_asServer)
    {
      scheduler = i_scheduler;
      stream = i_stream;
      if (stream != null) {
        remoteCert = stream.RemoteCertificate as X509Certificate2;
        destinationPublicKey = IoScheduler.GetCertificatePublicKey(remoteCert);
      }
      else {
        destinationPublicKey = i_destinationPublicKey;
      }
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
        scheduler.ReportException(e, "sending to", destinationPublicKey);
      }

      scheduler.UnregisterSender(destinationPublicKey, this);

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

    public static SenderThread CreateAsServer(IoScheduler scheduler, SslStream stream)
    {
      var remoteCert = stream.RemoteCertificate as X509Certificate2;
      var destinationPublicKey = IoScheduler.GetCertificatePublicKey(remoteCert);

      if (scheduler.Verbose) {
        Console.WriteLine("Creating sender thread for endpoint {0}", IoScheduler.CertificateToString(remoteCert));
      }

      SenderThread senderThread = new SenderThread(scheduler, stream, null, true);
      scheduler.RegisterSender(destinationPublicKey, senderThread);
      Thread t = new Thread(senderThread.Run);
      t.Start();
      return senderThread;
    }

    public static SenderThread CreateAsClient(IoScheduler scheduler, byte[] destinationPublicKey)
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Creating sender thread for public key {0}", scheduler.PublicKeyToString(destinationPublicKey));
      }

      SenderThread senderThread = new SenderThread(scheduler, null, destinationPublicKey, false);
      scheduler.RegisterSender(destinationPublicKey, senderThread);
      Thread t = new Thread(senderThread.Run);
      t.Start();
      return senderThread;
    }

    private void SendLoop()
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Starting send loop with other endpoint {0}", scheduler.PublicKeyToString(destinationPublicKey));
      }

      // If we're not the server, we need to initiate the connection.

      if (!asServer) {
        if (!ConnectAsClient()) {
          return;
        }
      }

      while (true)
      {
        // Wait for there to be a packet to send.

        currentSendTask = sendQueue.Receive();

        // Send its length as an 8-byte value.

        UInt64 messageSize = (UInt64)currentSendTask.Message.Length;
        IoEncoder.WriteUInt64(stream, messageSize);
        if (scheduler.Verbose) {
          Console.WriteLine("Sent message size {0} to {1}", messageSize, IoScheduler.CertificateToString(remoteCert));
        }

        // Send its contents.

        IoEncoder.WriteBytes(stream, currentSendTask.Message, 0, messageSize);
        if (scheduler.Verbose) {
          Console.WriteLine("Sent message of size {0} to {1}", messageSize, IoScheduler.CertificateToString(remoteCert));
        }

        // Set the currentSendTask to null so we know we don't have to
        // resend it if the connection fails.

        currentSendTask = null;
      }
    }

    private bool ConnectAsClient()
    {
      var otherEndpoint = scheduler.FindEndpointInfoForPublicKey(destinationPublicKey);
      if (otherEndpoint == null) {
        Console.Error.WriteLine("Could not connect to destination public key {0} because we don't know its address.",
                                destinationPublicKey);
        return false;
      }

      TcpClient client;
      try
      {
        client = new TcpClient();
      }
      catch (Exception e)
      {
        Console.Error.WriteLine("Could not create TCP client, causing exception:\n{0}", e);
        return false;
      }

      if (scheduler.Verbose) {
        Console.WriteLine("Starting connection to {0}", IoScheduler.CertificateToString(remoteCert));
      }

      try {
        client.Connect(otherEndpoint.Endpoint);
      }
      catch (Exception e)
      {
        Console.Error.WriteLine("Could not connect to {0}, causing exception:\n{1}",
                                IoScheduler.EndpointInfoToString(otherEndpoint), e);
        return false;
      }

      var myCertificateCollection = new X509CertificateCollection();
      myCertificateCollection.Add(scheduler.MyCert);

      try {
        stream = new SslStream(client.GetStream(), leaveInnerStreamOpen: false, IoScheduler.ValidateSSLCertificate);
        stream.AuthenticateAsClient(otherEndpoint.FriendlyName, myCertificateCollection, checkCertificateRevocation: false);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not authenticate connection to {0} as client, so disconnecting. Exception:\n{1}",
                                IoScheduler.EndpointInfoToString(otherEndpoint), e);
        return false;
      }

      remoteCert = stream.RemoteCertificate as X509Certificate2;

      if (!ByteArrayComparer.Default().Equals(IoScheduler.GetCertificatePublicKey(remoteCert), destinationPublicKey)) {
        Console.Error.WriteLine("Connected to {0} expecting public key {1} but found public key {2}, so disconnecting.",
                                IoScheduler.EndpointInfoToString(otherEndpoint),
                                scheduler.PublicKeyToString(destinationPublicKey),
                                scheduler.PublicKeyToString(IoScheduler.GetCertificatePublicKey(remoteCert)));
        return false;
      }

      // Now that the connection is successful, create a thread to
      // receive packets on it.

      ReceiverThread receiverThread = ReceiverThread.Create(scheduler, stream, asServer: false);
      return true;
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
    private IPEndPoint myEndpoint;

    public ListenerThread(IoScheduler i_scheduler, IPEndPoint i_myEndpoint)
    {
      scheduler = i_scheduler;
      myEndpoint = i_myEndpoint;
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
      listener = new TcpListener(myEndpoint);
      listener.Start();
      while (true)
      {
        if (scheduler.Verbose) {
          Console.WriteLine("Waiting for the next incoming connection.");
        }
        TcpClient client = listener.AcceptTcpClient();

        SslStream sslStream = new SslStream(client.GetStream(), leaveInnerStreamOpen: false, IoScheduler.ValidateSSLCertificate);

        sslStream.AuthenticateAsServer(scheduler.MyCert, clientCertificateRequired: true, checkCertificateRevocation: false);

        var remoteCert = sslStream.RemoteCertificate as X509Certificate2;

        if (scheduler.Verbose) {
          Console.WriteLine("Received an incoming connection from {0} with public key {1}",
                            remoteCert.FriendlyName, IoScheduler.GetCertificatePublicKey(remoteCert));
        }

        ReceiverThread receiverThread = ReceiverThread.Create(scheduler, sslStream, asServer: true);
        SenderThread senderThread = SenderThread.CreateAsServer(scheduler, sslStream);
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
                            sendTask.Message.Length, scheduler.PublicKeyToString(sendTask.DestinationPublicKey));
        }

        SenderThread senderThread = scheduler.FindSenderForDestinationPublicKey(sendTask.DestinationPublicKey);

        if (senderThread == null) {
          senderThread = SenderThread.CreateAsClient(scheduler, sendTask.DestinationPublicKey);
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
    private X509Certificate2 myCert;
    private bool onlyClient;
    private bool verbose;
    private int maxSendTries;
    private BufferBlock<ReceivedPacket> receiveQueue;
    private Dictionary<byte[], List<SenderThread>> destinationPublicKeyToSenderThreadMap;
    private Dictionary<byte[], EndpointInfo> publicKeyToEndpointInfoMap;
    private ListenerThread listenerThread;
    private SendDispatchThread sendDispatchThread;

    public IoScheduler(PrivateIdentity myIdentity, List<PublicIdentity> knownIdentities,
                       bool i_verbose = false, int i_maxSendTries = 3)
    {
      verbose = i_verbose;
      maxSendTries = i_maxSendTries;
      receiveQueue = new BufferBlock<ReceivedPacket>();
      destinationPublicKeyToSenderThreadMap = new Dictionary<byte[], List<SenderThread>>(ByteArrayComparer.Default());
      publicKeyToEndpointInfoMap = new Dictionary<byte[], EndpointInfo>(ByteArrayComparer.Default());

      foreach (var knownIdentity in knownIdentities) {
        try {
          var publicKey = knownIdentity.PublicKey;
          var addresses = Dns.GetHostAddresses(knownIdentity.HostNameOrAddress);
          if (addresses.Length < 1) {
            Console.WriteLine("WARNING:  Could not find any addresses when resolving {0} for identity {1} with public key {2}",
                              knownIdentity.HostNameOrAddress, knownIdentity.FriendlyName, publicKey);
            continue;
          }
          var address = addresses[0];
          var ep = new IPEndPoint(address, knownIdentity.Port);
          var info = new EndpointInfo(knownIdentity.FriendlyName, knownIdentity.HostNameOrAddress, ep);
          publicKeyToEndpointInfoMap[publicKey] = info;
          if (verbose) {
            Console.WriteLine("Discovered that {0} is the address/port for key {1}", ep, publicKey);
          }
        }
        catch (Exception e) {
          Console.WriteLine("WARNING:  Caught exception when resolving {0}, the host name given for identity {1}:\n{2}",
                            knownIdentity.HostNameOrAddress, knownIdentity.FriendlyName, e);
        }
      }

      if (myIdentity == null) {
        StartClient();
      }
      else {
        StartServer(myIdentity);
      }
    }

    private void StartServer(PrivateIdentity myIdentity)
    {
      onlyClient = false;

      try {
        myCert = new X509Certificate2(myIdentity.Pkcs12, "" /* empty password */, X509KeyStorageFlags.Exportable);
      }
      catch (Exception e) {
        Console.WriteLine("Could not import private key. Exception:{0}", e);
        throw new Exception("Can't start server because private key file not readable");
      }

      var addresses = Dns.GetHostAddresses(myIdentity.HostNameOrAddress);
      if (addresses.Length < 1) {
        Console.Error.WriteLine("ERROR:  Could not find any addresses when resolving {0}, which I'm supposed to bind to.");
        throw new Exception("Can't resolve binding address");
      }
      var address = addresses[0];
      var myEndpoint = new IPEndPoint(address, myIdentity.Port);

      if (verbose) {
        Console.WriteLine("Starting I/O scheduler as server listening to {0} with friendly name {1} and public key {2}",
                          myEndpoint, myCert.FriendlyName, IoScheduler.GetCertificatePublicKey(myCert));
      }

      sendDispatchThread = new SendDispatchThread(this);
      Thread st = new Thread(sendDispatchThread.Run);
      st.Start();

      // Start a thread to listen on my binding endpoint.

      listenerThread = new ListenerThread(this, myEndpoint);
      Thread lt = new Thread(listenerThread.Run);
      lt.Start();
    }

    private void StartClient()
    {
      onlyClient = true;

      myCert = IronfleetCrypto.CreateTransientClientIdentity();

      if (verbose) {
        Console.WriteLine("Starting I/O scheduler as client with public key {0}",
                          myCert.PublicKey.Key);
      }

      sendDispatchThread = new SendDispatchThread(this);
      Thread st = new Thread(sendDispatchThread.Run);
      st.Start();
    }

    public bool Verbose { get { return verbose; } }
    public bool OnlyClient { get { return onlyClient; } }
    public X509Certificate2 MyCert { get { return myCert; } }

    /////////////////////////////////////
    // SENDING
    /////////////////////////////////////

    public void RegisterSender(byte[] destinationPublicKey, SenderThread senderThread)
    {
      lock (destinationPublicKeyToSenderThreadMap)
      {
        if (destinationPublicKeyToSenderThreadMap.ContainsKey(destinationPublicKey)) {
          destinationPublicKeyToSenderThreadMap[destinationPublicKey].Insert(0, senderThread);
        }
        else {
          destinationPublicKeyToSenderThreadMap[destinationPublicKey] = new List<SenderThread> { senderThread };
        }
      }
    }

    public void UnregisterSender(byte[] destinationPublicKey, SenderThread senderThread)
    {
      lock (destinationPublicKeyToSenderThreadMap)
      {
        destinationPublicKeyToSenderThreadMap[destinationPublicKey].Remove(senderThread);
      }
    }

    public SenderThread FindSenderForDestinationPublicKey(byte[] destinationPublicKey)
    {
      lock (destinationPublicKeyToSenderThreadMap)
      {
        if (destinationPublicKeyToSenderThreadMap.ContainsKey(destinationPublicKey) &&
            destinationPublicKeyToSenderThreadMap[destinationPublicKey].Count > 0) {
          return destinationPublicKeyToSenderThreadMap[destinationPublicKey][0];
        }
      }

      return null;
    }

    public EndpointInfo FindEndpointInfoForPublicKey(byte[] publicKey)
    {
      EndpointInfo endpointInfo;
      if (!publicKeyToEndpointInfoMap.TryGetValue(publicKey, out endpointInfo)) {
        return null;
      }
      else {
        return endpointInfo;
      }
    }

    /////////////////////////////////////
    // RECEIVING
    /////////////////////////////////////

    public void NoteReceivedPacket(ReceivedPacket packet)
    {
      receiveQueue.Post(packet);
    }

    /////////////////////////////////////
    // UTILITY METHODS
    /////////////////////////////////////

    public static string EndpointInfoToString(EndpointInfo info)
    {
      return string.Format("{0} ({1}:{2} @ {3})", info.FriendlyName, info.HostNameOrAddress, info.Endpoint.Port,
                           info.Endpoint.Address);
    }

    public static string CertificateToString(X509Certificate2 cert)
    {
      return string.Format("{0} (public key {1}", cert.FriendlyName, IoScheduler.GetCertificatePublicKey(cert));
    }

    public string PublicKeyToString(byte[] destinationPublicKey)
    {
      EndpointInfo info;
      if (publicKeyToEndpointInfoMap.TryGetValue(destinationPublicKey, out info)) {
        return EndpointInfoToString(info);
      }
      else {
        return string.Format("public key {0}", destinationPublicKey);
      }
    }

    public static byte[] GetCertificatePublicKey(X509Certificate2 cert)
    {
      return cert.PublicKey.EncodedKeyValue.RawData;
    }

    public void ReportException(Exception e, string activity, byte[] publicKey)
    {
      if (e is IOException ioe) {
        e = ioe.InnerException;
      }
      if (e is SocketException se) {
        if (se.SocketErrorCode == SocketError.ConnectionReset) {
          Console.WriteLine("Stopped {0} {1} because of a connection reset. Will try again later if necessary.",
                            activity, PublicKeyToString(publicKey));
          return;
        }
        if (se.SocketErrorCode == SocketError.ConnectionRefused) {
          Console.WriteLine("Stopped {0} {1} because the connection was refused. Will try again later if necessary.",
                            activity, PublicKeyToString(publicKey));
          return;
        }
      }
      Console.WriteLine("Stopped {0} {1} because of the following exception, but will try again later if necessary:\n{2}",
                        activity, PublicKeyToString(publicKey), e);
    }

    public static bool ValidateSSLCertificate(object sender, X509Certificate certificate, X509Chain chain, SslPolicyErrors sslPolicyErrors)
    {
      const SslPolicyErrors ignoredErrors =
          SslPolicyErrors.RemoteCertificateChainErrors |  // self-signed
          SslPolicyErrors.RemoteCertificateNameMismatch;  // name mismatch

      return ((sslPolicyErrors & ~ignoredErrors) == SslPolicyErrors.None);
    }

    ///////////////////////////////////
    // API for IoNative.cs
    ///////////////////////////////////

    public void ReceivePacket(Int32 timeLimit, out bool ok, out bool timedOut, out byte[] remotePublicKey, out byte[] message)
    {
      ReceivedPacket packet;

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
          remotePublicKey = null;
          message = null;
        }
        else {
          remotePublicKey = IoScheduler.GetCertificatePublicKey(packet.SenderCert);
          message = packet.Message;
          if (verbose) {
            Console.WriteLine("Dequeueing a packet of size {0} from {1}", message.Length, CertificateToString(packet.SenderCert));
          }
        }
      }
      catch (TimeoutException) {
        remotePublicKey = null;
        message = null;
        ok = true;
        timedOut = true;
      }
      catch (Exception e) {
        Console.Error.WriteLine("Unexpected error trying to read packet from packet queue. Exception:\n{0}", e);
        remotePublicKey = null;
        message = null;
        ok = false;
        timedOut = false;
      }
    }

    public bool SendPacket(byte[] remotePublicKey, byte[] message)
    {
      try {
        byte[] messageCopy = new byte[message.Length];
        Array.Copy(message, messageCopy, message.Length);
        byte[] remotePublicKeyCopy = new byte[remotePublicKey.Length];
        Array.Copy(remotePublicKey, remotePublicKeyCopy, remotePublicKey.Length);
        SendTask sendTask = new SendTask(remotePublicKeyCopy, messageCopy);
        if (verbose) {
          Console.WriteLine("Enqueueing send of a message of size {0} to {1}", message.Length,
                            PublicKeyToString(remotePublicKey));
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
      if (sendTask.IncrementNumTriesSoFar() < maxSendTries) {
        sendDispatchThread.EnqueueSendTask(sendTask);
      }
    }

    ///////////////////////////////////
    // Extra API calls for client
    ///////////////////////////////////

    public void Connect(byte[] destinationPublicKey)
    {
      SenderThread senderThread = FindSenderForDestinationPublicKey(destinationPublicKey);
      if (senderThread == null) {
        senderThread = SenderThread.CreateAsClient(this, destinationPublicKey);
      }
    }
  }
}
