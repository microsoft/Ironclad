using System;
using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Security;
using System.Net.Sockets;
using System.Text;
using System.Text.Json;
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

    public bool WriteToFile (string fileName)
    {
      string json;

      try {
        json = JsonSerializer.Serialize<PrivateIdentity>(this);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not serialize private key data for {0}. Exception:\n{1}", FriendlyName, e);
        return false;
      }

      try {
        File.WriteAllText(fileName, json);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not create file {0}. Exception:\n{1}", fileName, e);
        return false;
      }

      return true;
    }

    public static PrivateIdentity ReadFromFile(string fileName)
    {
      string json;

      try {
        json = File.ReadAllText(fileName);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not read contents of private key file {0}. Exception:\n{1}", fileName, e);
        return null;
      }

      PrivateIdentity privateIdentity;
      try {
        privateIdentity = JsonSerializer.Deserialize<PrivateIdentity>(json);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not deserialize contents of private key file {0}. Exception:\n{1}", fileName, e);
        return null;
      }

      return privateIdentity;
    }
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

    public bool WriteToFile(string fileName)
    {
      string json;

      try {
        json = JsonSerializer.Serialize<ServiceIdentity>(this);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not serialize service identity. Exception:\n{0}", e);
        return false;
      }

      try {
        File.WriteAllText(fileName, json);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not write service identity to file {0}. Exception:\n{1}", fileName, e);
        return false;
      }

      return true;
    }

    public static ServiceIdentity ReadFromFile(string fileName)
    {
      string json;

      try {
        json = File.ReadAllText(fileName);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not read contents of service file {0}. Exception:\n{1}", fileName, e);
        return null;
      }

      ServiceIdentity serviceIdentity;
      try {
        serviceIdentity = JsonSerializer.Deserialize<ServiceIdentity>(json);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not deserialize contents of service file {0}. Exception:\n{1}", fileName, e);
        return null;
      }

      return serviceIdentity;
    }
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
    public static void CreateNewIdentity(string friendlyName, string hostNameOrAddress, int port,
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
        HostNameOrAddress = hostNameOrAddress,
        Port = port
      };
      privateIdentity = new PrivateIdentity {
        FriendlyName = friendlyName,
        Pkcs12 = pkcs12,
        HostNameOrAddress = hostNameOrAddress,
        Port = port
      };
    }

    public static X509Certificate2 CreateTransientClientIdentity ()
    {
      var key = RSA.Create(2048);
      var req = new CertificateRequest("CN = client", key, HashAlgorithmName.SHA256, RSASignaturePadding.Pss);
      var now = DateTime.Now;
      var expiry = now.AddYears(1);
      var cert = req.CreateSelfSigned(now, expiry);
      // On Linux, it's OK to just return cert. But on Windows, we need the following
      // code to allow it to be used to authenticate a client.
      return new X509Certificate2(cert.Export(X509ContentType.Pkcs12));
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

  public class CertificateValidator
  {
    private IoScheduler scheduler;
    private PublicIdentity expectedPublicIdentity;

    public CertificateValidator(IoScheduler i_scheduler, PublicIdentity i_expectedPublicIdentity = null)
    {
      scheduler = i_scheduler;
      expectedPublicIdentity = i_expectedPublicIdentity;
    }

    public bool ValidateSSLCertificate(object sender, X509Certificate certificate, X509Chain chain,
                                       SslPolicyErrors sslPolicyErrors)
    {
      const SslPolicyErrors ignoredErrors = SslPolicyErrors.RemoteCertificateChainErrors;

      if ((sslPolicyErrors & ~ignoredErrors) != SslPolicyErrors.None) {
        Console.Error.WriteLine("Could not validate SSL certificate for {0} due to errors {1}",
                                IoScheduler.GetCertificatePublicKey(certificate as X509Certificate2),
                                sslPolicyErrors & ~ignoredErrors);
        return false;
      }

      var cert2 = certificate as X509Certificate2;

      // If we were expecting a specific public identity, check that
      // the key in the certificate matches what we were expecting.

      if (expectedPublicIdentity != null) {
        if (!ByteArrayComparer.Default().Equals(IoScheduler.GetCertificatePublicKey(cert2), expectedPublicIdentity.PublicKey)) {
          Console.Error.WriteLine("Connected to {0} expecting public key {1} but found public key {2}, so disconnecting.",
                                  IoScheduler.PublicIdentityToString(expectedPublicIdentity),
                                  IoScheduler.PublicKeyToString(expectedPublicIdentity.PublicKey),
                                  IoScheduler.PublicKeyToString(IoScheduler.GetCertificatePublicKey(cert2)));
          return false;
        }

        if (cert2.SubjectName.Name != "CN=" + expectedPublicIdentity.FriendlyName) {
          Console.Error.WriteLine("Connected to {0} expecting subject CN={1} but found {2}, so disconnecting.",
                                  IoScheduler.PublicIdentityToString(expectedPublicIdentity),
                                  expectedPublicIdentity.FriendlyName,
                                  cert2.SubjectName.Name);
          return false;
        }
      }
      else {
        // If we weren't expecting any particular public identity,
        // consider the expected public identity to be the known one
        // matching the public key in the certificate we got.  If
        // there is no known one, then this is just an anonymous
        // client, which is fine.  Otherwise, check that the subject
        // matches what we expect.  This is just a paranoid check; it
        // should never fail.

        expectedPublicIdentity = scheduler.LookupPublicKey(IoScheduler.GetCertificatePublicKey(cert2));
        if (expectedPublicIdentity != null) {
          if (cert2.SubjectName.Name != "CN=" + expectedPublicIdentity.FriendlyName) {
            Console.Error.WriteLine("Received a certificate we expected to have subject CN={1} but found {2}, so disconnecting.",
                                    IoScheduler.PublicIdentityToString(expectedPublicIdentity),
                                    expectedPublicIdentity.FriendlyName,
                                    cert2.SubjectName.Name);
            return false;
          }
        }
      }

      return true;
    }
  }

  public class ReceiverThread
  {
    private IoScheduler scheduler;
    private SslStream stream;
    private X509Certificate2 remoteCert;

    private ReceiverThread(IoScheduler i_scheduler, SslStream i_stream)
    {
      scheduler = i_scheduler;
      stream = i_stream;
      remoteCert = stream.RemoteCertificate as X509Certificate2;
    }

    public void Run()
    {
      try
      {
        ReceiveLoop();
      }
      catch (Exception e)
      {
        scheduler.ReportException(e, "receiving from " + IoScheduler.GetCertificatePublicKey(remoteCert));
      }
    }

    public static ReceiverThread Create(IoScheduler scheduler, SslStream stream)
    {
      ReceiverThread receiverThread = new ReceiverThread(scheduler, stream);
      Thread t = new Thread(receiverThread.Run);
      t.Start();
      return receiverThread;
    }

    private void ReceiveLoop()
    {
      bool success;

      if (scheduler.Verbose) {
        Console.WriteLine("Starting receive loop with remote identified as {0}", IoScheduler.CertificateToString(remoteCert));
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

  public abstract class SenderThread
  {
    protected IoScheduler scheduler;
    protected byte[] destinationPublicKey;
    protected SslStream stream;
    protected X509Certificate2 remoteCert;
    private BufferBlock<SendTask> sendQueue;
    private SendTask currentSendTask;

    protected SenderThread(IoScheduler i_scheduler, byte[] i_destinationPublicKey, SslStream i_stream,
                           X509Certificate2 i_remoteCert)
    {
      scheduler = i_scheduler;
      destinationPublicKey = i_destinationPublicKey;
      stream = i_stream;
      remoteCert = i_remoteCert;
      sendQueue = new BufferBlock<SendTask>();
      currentSendTask = null;
    }

    protected abstract string EndpointDescription();
    protected abstract bool Connect();

    public void Start()
    {
      scheduler.RegisterSender(destinationPublicKey, this);
      Thread t = new Thread(this.Run);
      t.Start();
    }

    private void Run()
    {
      try
      {
        if (Connect()) {
          SendLoop();
        }
      }
      catch (Exception e)
      {
        scheduler.ReportException(e, "sending to " + EndpointDescription());
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

    private void SendLoop()
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Starting send loop with {0}", EndpointDescription());
      }

      while (true)
      {
        // Wait for there to be a packet to send.

        currentSendTask = sendQueue.Receive();

        // Send its length as an 8-byte value.

        UInt64 messageSize = (UInt64)currentSendTask.Message.Length;
        IoEncoder.WriteUInt64(stream, messageSize);
        if (scheduler.Verbose) {
          Console.WriteLine("Sent message size {0} to {1}", messageSize, EndpointDescription());
        }

        // Send its contents.

        IoEncoder.WriteBytes(stream, currentSendTask.Message, 0, messageSize);
        if (scheduler.Verbose) {
          Console.WriteLine("Sent message of size {0} to {1}", messageSize, EndpointDescription());
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

  public class ServerSenderThread : SenderThread
  {
    private ServerSenderThread(IoScheduler i_scheduler, byte[] i_destinationPublicKey, SslStream i_stream,
                               X509Certificate2 i_remoteCert) :
      base(i_scheduler, i_destinationPublicKey, i_stream, i_remoteCert)
    {
    }

    public static ServerSenderThread Create(IoScheduler scheduler, SslStream stream)
    {
      var remoteCert = stream.RemoteCertificate as X509Certificate2;
      var destinationPublicKey = IoScheduler.GetCertificatePublicKey(remoteCert);

      if (scheduler.Verbose) {
        Console.WriteLine("Creating sender thread to send to remote certified as {0}",
                          IoScheduler.CertificateToString(remoteCert));
      }

      ServerSenderThread senderThread = new ServerSenderThread(scheduler, destinationPublicKey, stream, remoteCert);
      senderThread.Start();
      return senderThread;
    }

    protected override bool Connect()
    {
      // There's nothing to do since server sender threads start out connected.
      return true;
    }

    protected override string EndpointDescription()
    {
      return IoScheduler.CertificateToString(remoteCert);
    }
  }

  public class ClientSenderThread : SenderThread
  {
    private ClientSenderThread(IoScheduler i_scheduler, byte[] i_destinationPublicKey) :
      base(i_scheduler, i_destinationPublicKey, null, null)
    {
    }

    public static ClientSenderThread Create(IoScheduler scheduler, byte[] destinationPublicKey)
    {
      if (scheduler.Verbose) {
        Console.WriteLine("Creating sender thread to send to remote public key {0}",
                          scheduler.LookupPublicKeyAsString(destinationPublicKey));
      }

      ClientSenderThread senderThread = new ClientSenderThread(scheduler, destinationPublicKey);
      senderThread.Start();
      return senderThread;
    }

    protected override string EndpointDescription()
    {
      return scheduler.LookupPublicKeyAsString(destinationPublicKey);
    }

    protected override bool Connect()
    {
      var destinationPublicIdentity = scheduler.LookupPublicKey(destinationPublicKey);
      if (destinationPublicIdentity == null) {
        Console.Error.WriteLine("Could not connect to destination public key {0} because we don't know its address.",
                                IoScheduler.PublicKeyToString(destinationPublicKey));
        return false;
      }

      if (scheduler.Verbose) {
        Console.WriteLine("Starting connection to {0}", IoScheduler.PublicIdentityToString(destinationPublicIdentity));
      }

      TcpClient client;
      try
      {
        client = new TcpClient(destinationPublicIdentity.HostNameOrAddress, destinationPublicIdentity.Port);
      }
      catch (Exception e)
      {
        scheduler.ReportException(e, "connecting to " + IoScheduler.PublicIdentityToString(destinationPublicIdentity));
        return false;
      }

      var myCertificateCollection = new X509CertificateCollection();
      myCertificateCollection.Add(scheduler.MyCert);
      var myValidator = new CertificateValidator(scheduler, destinationPublicIdentity);

      try {
        stream = new SslStream(client.GetStream(), leaveInnerStreamOpen: false, myValidator.ValidateSSLCertificate);
        stream.AuthenticateAsClient(destinationPublicIdentity.FriendlyName, myCertificateCollection,
                                    checkCertificateRevocation: false);
      }
      catch (Exception e) {
        scheduler.ReportException(e, "authenticating connection to " + IoScheduler.PublicIdentityToString(destinationPublicIdentity));
        return false;
      }

      remoteCert = stream.RemoteCertificate as X509Certificate2;

      if (!ByteArrayComparer.Default().Equals(IoScheduler.GetCertificatePublicKey(remoteCert), destinationPublicKey)) {
        Console.Error.WriteLine("Connected to {0} expecting public key {1} but found public key {2}, so disconnecting.",
                                IoScheduler.PublicIdentityToString(destinationPublicIdentity),
                                IoScheduler.PublicKeyToString(destinationPublicKey),
                                IoScheduler.PublicKeyToString(IoScheduler.GetCertificatePublicKey(remoteCert)));
        return false;
      }

      if (scheduler.Verbose) {
        Console.WriteLine("Successfully connected to {0} and got certificate identifying it as {1}",
                          IoScheduler.PublicIdentityToString(destinationPublicIdentity),
                          IoScheduler.CertificateToString(remoteCert));
      }

      // Now that the connection is successful, create a thread to
      // receive packets on it.

      ReceiverThread receiverThread = ReceiverThread.Create(scheduler, stream);
      return true;
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
      if (scheduler.Verbose) {
        Console.WriteLine("Starting to listen on {0}", myEndpoint);
      }

      listener = new TcpListener(myEndpoint);
      listener.ExclusiveAddressUse = true;
      listener.Start();
      while (true)
      {
        if (scheduler.Verbose) {
          Console.WriteLine("Waiting for the next incoming connection");
        }

        TcpClient client = listener.AcceptTcpClient();

        CertificateValidator myValidator = new CertificateValidator(scheduler);
        SslStream sslStream = new SslStream(client.GetStream(), leaveInnerStreamOpen: false, myValidator.ValidateSSLCertificate);
        sslStream.AuthenticateAsServer(scheduler.MyCert, clientCertificateRequired: true, checkCertificateRevocation: false);

        var remoteCert = sslStream.RemoteCertificate as X509Certificate2;

        if (scheduler.Verbose) {
          Console.WriteLine("Received an incoming connection from remote certified as {0}",
                            IoScheduler.CertificateToString(remoteCert));
        }

        ReceiverThread.Create(scheduler, sslStream);
        ServerSenderThread.Create(scheduler, sslStream);
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
          Console.WriteLine("Waiting for the next send to dispatch");
        }

        SendTask sendTask = sendQueue.Receive();

        if (scheduler.Verbose) {
          Console.WriteLine("Dispatching send of message of size {0} to {1}",
                            sendTask.Message.Length, IoScheduler.PublicKeyToString(sendTask.DestinationPublicKey));
        }

        SenderThread senderThread = scheduler.FindSenderForDestinationPublicKey(sendTask.DestinationPublicKey);

        if (senderThread == null) {
          senderThread = ClientSenderThread.Create(scheduler, sendTask.DestinationPublicKey);
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
    private Dictionary<byte[], PublicIdentity> publicKeyToPublicIdentityMap;
    private ListenerThread listenerThread;
    private SendDispatchThread sendDispatchThread;

    private IoScheduler(PrivateIdentity myIdentity, string localHostNameOrAddress, int localPort,
                        List<PublicIdentity> knownIdentities, bool i_verbose = false, int i_maxSendTries = 3)
    {
      verbose = i_verbose;
      maxSendTries = i_maxSendTries;
      receiveQueue = new BufferBlock<ReceivedPacket>();
      destinationPublicKeyToSenderThreadMap = new Dictionary<byte[], List<SenderThread>>(ByteArrayComparer.Default());
      publicKeyToPublicIdentityMap = new Dictionary<byte[], PublicIdentity>(ByteArrayComparer.Default());

      foreach (var knownIdentity in knownIdentities) {
        publicKeyToPublicIdentityMap[knownIdentity.PublicKey] = knownIdentity;
      }

      if (myIdentity == null) {
        StartClient();
      }
      else {
        StartServer(myIdentity, localHostNameOrAddress, localPort);
      }
    }

    public static IoScheduler CreateServer(PrivateIdentity myIdentity, string localHostNameOrAddress, int localPort,
                                           List<PublicIdentity> knownIdentities, bool verbose = false,
                                           int maxSendTries = 3)
    {
      return new IoScheduler(myIdentity, localHostNameOrAddress, localPort, knownIdentities, verbose, maxSendTries);
    }

    public static IoScheduler CreateClient(List<PublicIdentity> serverIdentities, bool verbose = false,
                                           bool connectToAllServers = true, int maxSendTries = 3)
    {
      var scheduler = new IoScheduler(null, null, 0, serverIdentities, verbose, maxSendTries);
      if (connectToAllServers) {
        foreach (var serverIdentity in serverIdentities) {
          scheduler.Connect(serverIdentity.PublicKey);
        }
      }
      return scheduler;
    }

    private void StartServer(PrivateIdentity myIdentity, string localHostNameOrAddress, int localPort)
    {
      onlyClient = false;

      try {
        myCert = new X509Certificate2(myIdentity.Pkcs12, "" /* empty password */, X509KeyStorageFlags.Exportable);
      }
      catch (Exception e) {
        Console.Error.WriteLine("Could not import private key. Exception:{0}", e);
        throw new Exception("Can't start server because private key not decryptable");
      }

      // The `local` parameters override the parameters in
      // `myIdentity`, unless they're empty or zero.

      if (localHostNameOrAddress == null || localHostNameOrAddress.Length == 0) {
        localHostNameOrAddress = myIdentity.HostNameOrAddress;
      }
      if (localPort == 0) {
        localPort = myIdentity.Port;
      }

      var address = LookupHostNameOrAddress(localHostNameOrAddress);
      if (address == null) {
        Console.Error.WriteLine("ERROR:  Could not find any addresses when resolving {0}, which I'm supposed to bind to.");
        throw new Exception("Can't resolve binding address");
      }
      var myEndpoint = new IPEndPoint(address, localPort);

      if (verbose) {
        Console.WriteLine("Starting I/O scheduler as server listening to {0} certified as {1}",
                          myEndpoint, IoScheduler.CertificateToString(myCert));
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
        Console.WriteLine("Starting I/O scheduler as client with certificate {0}",
                          IoScheduler.CertificateToString(myCert));
      }

      sendDispatchThread = new SendDispatchThread(this);
      Thread st = new Thread(sendDispatchThread.Run);
      st.Start();
    }

    private static IPAddress LookupHostNameOrAddress(string hostNameOrAddress)
    {
      var addresses = Dns.GetHostAddresses(hostNameOrAddress);
      if (addresses.Length < 1) {
        return null;
      }

      // Return the first IPv4 address in the list.

      foreach (var address in addresses) {
        if (address.AddressFamily == AddressFamily.InterNetwork) {
          return address;
        }
      }

      // If there was no IPv4 address, return the first address in the
      // list.

      return addresses[0];
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

    public static byte[] GetCertificatePublicKey(X509Certificate2 cert)
    {
      return cert.PublicKey.EncodedKeyValue.RawData;
    }

    public static string PublicKeyToString(byte[] destinationPublicKey)
    {
      return System.Convert.ToBase64String(destinationPublicKey).Substring(12, 8);
    }

    public static string PublicIdentityToString(PublicIdentity id)
    {
      return string.Format("{0} (key {1}) @ {2}:{3}", id.FriendlyName, PublicKeyToString(id.PublicKey),
                           id.HostNameOrAddress, id.Port);
    }

    public static string CertificateToString(X509Certificate2 cert)
    {
      return string.Format("{0} (key {1})",
                           cert.SubjectName.Name, PublicKeyToString(IoScheduler.GetCertificatePublicKey(cert)));
    }

    public PublicIdentity LookupPublicKey(byte[] publicKey)
    {
      PublicIdentity publicIdentity;
      if (!publicKeyToPublicIdentityMap.TryGetValue(publicKey, out publicIdentity)) {
        return null;
      }
      else {
        return publicIdentity;
      }
    }

    public string LookupPublicKeyAsString(byte[] destinationPublicKey)
    {
      var publicIdentity = LookupPublicKey(destinationPublicKey);
      if (publicIdentity == null) {
        return PublicKeyToString(destinationPublicKey);
      }
      else {
        return PublicIdentityToString(publicIdentity);
      }
    }

    public void ReportException(Exception e, string activity)
    {
      if (e is IOException ioe) {
        e = ioe.InnerException;
      }
      if (e is SocketException se) {
        if (se.SocketErrorCode == SocketError.ConnectionReset) {
          Console.WriteLine("Stopped {0} because of a connection reset. Will try again later if necessary.", activity);
          return;
        }
        if (se.SocketErrorCode == SocketError.ConnectionRefused) {
          Console.WriteLine("Stopped {0} because the connection was refused. Will try again later if necessary.", activity);
          return;
        }
        if (se.SocketErrorCode == SocketError.Shutdown) {
          Console.WriteLine("Stopped {0} because the connection was shut down. Will try again later if necessary.", activity);
          return;
        }
      }
      Console.WriteLine("Stopped {0} because of the following exception, but will try again later if necessary:\n{1}",
                        activity, e);
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
            Console.WriteLine("Dequeueing a packet of size {0} from {1}",
                              message.Length, CertificateToString(packet.SenderCert));
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
        senderThread = ClientSenderThread.Create(this, destinationPublicKey);
      }
    }
  }
}
