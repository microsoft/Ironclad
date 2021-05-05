using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;

namespace IronfleetCommon
{
  class RSLClient
  {
    IPEndPoint[] serverEps;
    IPEndPoint myEp;
    IoScheduler scheduler;
    SeqNumManager seqNumManager;
    int primaryServerIndex;

    public RSLClient(IEnumerable<IPEndPoint> i_serverEps, IPEndPoint i_myEp, int seqNumReservationSize = 1000)
    {
      serverEps = Enumerable.ToArray(i_serverEps);
      myEp = i_myEp;
      scheduler = new IoScheduler(myEp, true, false); // onlyClient = true, verbose = false
      seqNumManager = new SeqNumManager(myEp.Port, seqNumReservationSize);
      primaryServerIndex = 0;
      Start();
    }

    private void Start()
    {
      // Create connections to all endpoints, so that if any of them
      // sends a reply we can receive it.  Since we're in "only
      // client" mode, we aren't listening on any port so we have to
      // rely on outgoing connections for all communication.

      foreach (var serverEp in serverEps)
      {
        scheduler.Connect(serverEp);
      }
    }

    public byte[] SubmitRequest (byte[] request, bool verbose = false, int timeBeforeServerSwitchMs = 1000)
    {
      UInt64 seqNum = seqNumManager.Next;
      byte[] requestMessage;
      using (var memStream = new MemoryStream())
      {
        IoEncoder.WriteUInt64(memStream, 0);                                 // 0 means "this is a CMessage_Request"
        IoEncoder.WriteUInt64(memStream, seqNum);                            // sequence number
        IoEncoder.WriteUInt64(memStream, (UInt64)request.Length);            // size of CAppRequest
        IoEncoder.WriteBytes(memStream, request, 0, (UInt64)request.Length); // CAppRequest
        requestMessage = memStream.ToArray();
      }

      while (true)
      {
        scheduler.SendPacket(serverEps[primaryServerIndex], requestMessage);
        if (verbose) {
          Console.WriteLine("Sending a request with sequence number {0} to {1}", seqNum, serverEps[primaryServerIndex]);
        }

        bool ok, timedOut;
        IPEndPoint remote;
        byte[] replyBytes;
        scheduler.ReceivePacket(timeBeforeServerSwitchMs, out ok, out timedOut, out remote, out replyBytes);

        if (!ok) {
          throw new Exception("Unrecoverable networking failure");
        }

        if (timedOut) {
          primaryServerIndex = (primaryServerIndex + 1) % serverEps.Count();
          if (verbose) {
            Console.WriteLine("#timeout; rotating to server {0}", primaryServerIndex);
          }
          continue;
        }

        if (replyBytes.Length < 24) {
          throw new Exception(String.Format("Got RSL reply with invalid length {0}", replyBytes.Length));
        }

        UInt64 messageType = IoEncoder.ExtractUInt64(replyBytes, 0);
        if (messageType != 6) {
          throw new Exception("Got RSL message that wasn't a reply");
        }

        UInt64 replySeqNum = IoEncoder.ExtractUInt64(replyBytes, 8);
        if (replySeqNum != seqNum) {
          continue;
        }
        
        UInt64 replyLength = IoEncoder.ExtractUInt64(replyBytes, 16);
        if (replyLength + 24 != (UInt64)replyBytes.Length) {
          throw new Exception(String.Format("Got RSL reply with invalid encoded length ({0} instead of {1})",
                                            replyLength, replyBytes.Length - 24));
        }

        return replyBytes.Skip(24).ToArray();
      }
    }
  }
}
