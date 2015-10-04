using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace IronfleetShtClient
{
    using System.Net;
    using System.Runtime.Remoting.Messaging;

    public abstract class KeyValueStoreClient
    {
        public IPEndPoint ServerEndPoint { get; private set; }

        public KeyValueStoreClient(IPEndPoint endPoint)
        {
            this.ServerEndPoint = endPoint;
        }

        public abstract byte[] GetValue(byte[] key);

        public abstract void SetValue(byte[] key, byte[] value);
    }
}
