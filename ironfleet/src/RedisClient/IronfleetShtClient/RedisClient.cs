using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace IronfleetShtClient
{
    using System.Diagnostics;
    using System.Net;

    using StackExchange.Redis;

    class RedisClient : KeyValueStoreClient
    {
        private ConnectionMultiplexer redis;

        private IDatabase db;

        private RedisClient(IPEndPoint endPoint, ConnectionMultiplexer redis)
            : base(endPoint)
        {
            if (null == redis)
            {
                throw new ArgumentNullException("redis");
            }

            this.redis = redis;
            this.db = redis.GetDatabase();
        }

        static public RedisClient Connect(IPEndPoint endPoint)
        {
            var config = new ConfigurationOptions { EndPoints = { endPoint }, WriteBuffer = 0, Ssl = false, ResolveDns = false };
            var redis = ConnectionMultiplexer.Connect(config/*, Console.Error*/);
            return new RedisClient(endPoint, redis);
        }

        public override byte[] GetValue(byte[] key)
        {
            Debug.Assert(this.db != null, "the database reference cannot be null.");
            return this.db.StringGet(key);
        }

        public override void SetValue(byte[] key, byte[] value)
        {
            Debug.Assert(this.db != null, "the database reference cannot be null.");
            this.db.StringSet(key, value);
        }
    }
}
