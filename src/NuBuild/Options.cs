namespace NuBuild
{
    using System;
    using System.Collections.Generic;

    using Microsoft.WindowsAzure.Storage;

    using Newtonsoft.Json;
    using Newtonsoft.Json.Linq;

    public class Options
    {
        private const int DefaultParallelJobs = 1;
        private const bool DefaultUseCloudExecution = false;
        private const string DefaultCloudServiceName = "NuBuildExecutionService";

        private readonly JObject root;
        private bool? useCloudCache;
        private bool? useCloudExecution;
        private string cloudServiceName;
        private bool? enforceWhitespace;
        private int? parallelJobs;

        private Options(JObject root)
        {
            if (root == null)
            {
                throw new ArgumentNullException("root");
            }
            this.root = root;
        }
        public static Options FromString(string s)
        {
            return new Options((JObject)JsonConvert.DeserializeObject(s));
        }

        public static Options Empty
        {
            get
            {
                return new Options(new JObject());
            }
        }

        public CloudStorageAccount CloudStorageAccount
        {
            get
            {
                string connectionString;
                try
                {
                    connectionString = (string)this.root["credentials"]["storage"];
                }
                catch (ArgumentNullException)
                {
                    throw new InvalidOperationException("Unable to find storage credentials. Please check your config.json file.");
                }
                catch (NullReferenceException)
                {
                    throw new InvalidOperationException("Unable to find storage credentials. Please check your config.json file.");
                }
                return CloudStorageAccount.Parse(connectionString);
            }
        }

        public bool UseCloudCache
        {
            // todo: port to use this.GetValue()
            get
            {
                const bool defaultValue = false;
                if (this.useCloudCache.HasValue)
                {
                    return this.useCloudCache.Value;
                }

                bool result;
                try
                {
                    result = (bool)this.root["use_cloud_cache"];

                }
                catch (ArgumentNullException)
                {
                    return defaultValue;
                }
                catch (NullReferenceException)
                {
                    return defaultValue;
                }

                this.useCloudCache = result;
                return this.useCloudCache.Value;
            }

            set
            {
                this.useCloudCache = value;
            }
        }

        public bool UseCloudExecution
        {
            get
            {
                if (!this.useCloudExecution.HasValue)
                {
                    this.useCloudExecution = this.GetValue(d => (bool)d["use_cloud_execution"], DefaultUseCloudExecution);
                }

                return this.useCloudExecution.Value;
            }

            set
            {
                this.useCloudExecution = value;
            }
        }

        public string LookupPath(string name, string defaultValue = null)
        {
            try
            {
                return (string)this.root["paths"][name];

            }
            catch (ArgumentNullException)
            {
                return defaultValue;
            }
            catch (NullReferenceException)
            {
                return defaultValue;
            }
        }

        public string CloudServiceName
        {
            get    
            {
                if (this.cloudServiceName == null)
                {
                    this.cloudServiceName = this.GetValue(d => (string)d["cloud_service_name"], DefaultCloudServiceName);
                }

                return this.cloudServiceName;
            }

            set
            {
                this.cloudServiceName = value;
            }
        }

        public string SubscriptionId
        {
            get
            {
                try
                {
                    return (string)this.root["credentials"]["subscription_id"];
                }
                catch (ArgumentNullException)
                {
                    throw new InvalidOperationException("Unable to find subscription id. Please check your config.json file.");
                }
                catch (NullReferenceException)
                {
                    throw new InvalidOperationException("Unable to find subscription id. Please check your config.json file.");
                }
            }
        }

        public string Certificate
        {
            get
            {
                try
                {
                    return (string)this.root["credentials"]["certificate"];
                }
                catch (ArgumentNullException)
                {
                    throw new InvalidOperationException("Unable to find certificate. Please check your config.json file.");
                }
                catch (NullReferenceException)
                {
                    throw new InvalidOperationException("Unable to find certificate. Please check your config.json file.");
                }
            }
        }

        public bool EnforceWhitespace
        {
            // todo: port to use this.GetValue()
            get
            {
                const bool defaultValue = false;
                if (this.enforceWhitespace.HasValue)
                {
                    return this.enforceWhitespace.Value;
                }

                bool result;
                try
                {
                    result = (bool)this.root["enforce_whitespace"];

                }
                catch (ArgumentNullException)
                {
                    return defaultValue;
                }
                catch (NullReferenceException)
                {
                    return defaultValue;
                }

                this.enforceWhitespace = result;
                return this.enforceWhitespace.Value;
            }

            set
            {
                this.enforceWhitespace = value;
            }
        }

        public int ParallelJobs
        {
            get
            {
                if (!this.parallelJobs.HasValue)
                {
                    this.parallelJobs = this.GetValue(d => (int)d["parallel_jobs"], DefaultParallelJobs);
                }

                return this.parallelJobs.Value;
            }

            set
            {
                if (value < 1)
                {
                    throw new ArgumentOutOfRangeException("Simultaneous job limit must be greater than 0.");
                }

                this.parallelJobs = value;
            }
        }


        private T GetValue<T>(Func<JObject, T> access, T defaultValue = default(T))
        {
            T result;
            try
            {
                result = (T)access(this.root);
            }
            catch (ArgumentNullException)
            {
                return defaultValue;
            }
            catch (NullReferenceException)
            {
                return defaultValue;
            }

            return result;
        }
    }
}