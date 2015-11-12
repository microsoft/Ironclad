//--
// <copyright file="Program.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace CloudQueueTool
{
    using System;
    using System.Collections.Generic;
    using System.Configuration;
    using System.IO;
    using Microsoft.WindowsAzure.Storage;
    using Microsoft.WindowsAzure.Storage.Queue;

    /// <summary>
    /// Cloud queue management program.
    /// </summary>
    internal class Program
    {
        /// <summary>
        /// Acts upon command line arguments.
        /// </summary>
        /// <param name="args">Command line arguments.</param>
        private static void Main(string[] args)
        {
            // Create our CloudQueueClient object.
            // REVIEW: Hard-coded connection string index "Ironclad".
            string connectionString = null;
            ConnectionStringSettings settings = ConfigurationManager.ConnectionStrings["Ironclad"];
            if (settings != null)
            {
                connectionString = settings.ConnectionString;
            }

            if (string.IsNullOrEmpty(connectionString))
            {
                throw new ConfigurationException("Azure connection string missing from your .exe.config file!");
            }

            CloudStorageAccount storageAccount = CloudStorageAccount.Parse(connectionString);

            CloudQueueClient queueClient = storageAccount.CreateCloudQueueClient();

            switch (args.Length)
            {
                case 0:
                    Status(queueClient.ListQueues());
                    break;
                    
                case 2:
                    {
                        CloudQueue queue = queueClient.GetQueueReference(args[1]);
                        if (!queue.Exists())
                        {
                            Console.WriteLine("No such queue '{0}'", args[1]);
                            return;
                        }

                        queue.FetchAttributes();

                        switch (args[0])
                        {
                            case "clear":
                            case "Clear":
                                queue.Clear();
                                Console.WriteLine("Queue '{0}' cleared.", queue.Name);
                                break;

                            case "peek":
                            case "Peek":
                                int numberToPeekAt = (queue.ApproximateMessageCount != null) ? (int)queue.ApproximateMessageCount : 0;
                                Console.WriteLine("Queue '{0}' contains {1} messages:", queue.Name, numberToPeekAt);
                                if (numberToPeekAt != 0)
                                {
                                    // Peek API only allows a maximum of 32 messages to be peeked at.
                                    numberToPeekAt = Math.Min(numberToPeekAt, 32);

                                    foreach (CloudQueueMessage message in queue.PeekMessages(numberToPeekAt))
                                    {
                                        Console.WriteLine(
                                            "\t{0} {1} {2}",
                                            message.Id,
                                            message.InsertionTime,
                                            message.ExpirationTime);
                                    }
                                }

                                break;

                            case "status":
                            case "Status":
                                Status(new CloudQueue[]{queue});
                                break;

                            default:
                                Usage();
                                break;
                        }
                    }
                    break;

                default:
                    Usage();
                    break;
            }
        }

        private static void Status(IEnumerable<CloudQueue> queues)
        {
            foreach (CloudQueue queue in queues)
            {
                queue.FetchAttributes();
                Console.WriteLine("Queue '{0}' contains about {1} messages.", queue.Name, queue.ApproximateMessageCount);
            }
        }

        private static void Usage()
        {
            Console.WriteLine("Usage: CloudQueueTool [<command> <queue>]");
            Console.WriteLine("\t <command> = Clear | Peek | Status");
            Console.WriteLine("\t <queue> = reports | requests");
            Console.WriteLine();
            Console.WriteLine("If given no arguments, CloudQueueTool returns the status of all queues.");
        }
    }
}
