using System;
using System.IO;

namespace IronfleetCommon
{
  class SeqNumManager
  {
    private readonly int port;
    private readonly int reservationSize;
    private string fileName;
    private ulong nextSeqNum;
    private ulong minUnreservedSeqNum;

    public SeqNumManager(int i_port, int i_reservationSize)
    {
      port = i_port;
      reservationSize = i_reservationSize;
      nextSeqNum = 0;
      minUnreservedSeqNum = 0;
      fileName = String.Format("port{0}", port);
      Initialize();
    }

    private void Initialize()
    {
      try
      {
        foreach (var line in File.ReadLines(fileName))
        {
          if (line.Length > 4 && line.Substring(0, 4) == "seq:")
          {
            nextSeqNum = UInt64.Parse(line.Substring(4));
            break;
          }
        }
      }
      catch (Exception)
      {
        nextSeqNum = 0;
      }
    }

    private void ReserveSequenceNumbers()
    {
      ulong reservationRequest = nextSeqNum + (UInt64)reservationSize;
      string[] contents = new string[1] { String.Format("seq:{0}", reservationRequest) };
      try
      {
        File.WriteAllLines(fileName, contents);
      }
      catch (Exception e)
      {
        Console.Error.WriteLine("Could not reserve sequence numbers for port {0}.  Exception info:\n{1}", port, e);
        throw;
      }
      minUnreservedSeqNum = reservationRequest;
    }

    public UInt64 Next
    {
      get
      {
        while (nextSeqNum >= minUnreservedSeqNum)
        {
          ReserveSequenceNumbers();
        }
        ulong retVal = nextSeqNum;
        nextSeqNum++;
        return retVal;
      }
    }
  }
}
