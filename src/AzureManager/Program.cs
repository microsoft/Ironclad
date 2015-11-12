//--
// <copyright file="Program.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace AzureManager
{
    using System;
    using System.Collections.Specialized;
    using System.Configuration;
    using System.IO;
    using System.Security.Cryptography.X509Certificates;
    using Microsoft.WindowsAzure.Management.Compute.Models;
    using Microsoft.WindowsAzure.Storage;
    using Microsoft.WindowsAzure.Storage.Blob;

    /// <summary>
    /// Program to manage Azure cloud resources used by NuBuild.
    /// </summary>
    public class Program
    {
        /// <summary>
        /// Name of our service (hard-wired).
        /// </summary>
        private const string NuBuildServiceName = "NuBuildExecutionService";

        /// <summary>
        /// Name of the deployment package blob we use for the "start" and
        /// "upload" commands (hard-wired).
        /// </summary>
        private const string NuBuildServicePackageName = "NuBuildExecutionEngine";

        /// <summary>
        /// Default package file name used by "deploy" and "upload" commands.
        /// Can be overridden by command line argument.
        /// </summary>
        private const string DefaultPackageFilename = "NuBuildExecutionService.cspkg";

        /// <summary>
        /// Default configuration file name used by the "deploy" command
        /// Can be overridden by command line argument.
        /// </summary>
        private const string DefaultConfigurationFilename = "ServiceConfiguration.Cloud.cscfg";

        /// <summary>
        /// Default number of service instances to "start".
        /// Can be overridden by command line argument.
        /// </summary>
        private const int DefaultInstanceCount = 10;

        /// <summary>
        /// Main program entry point.
        /// </summary>
        /// <param name="args">The parameter is unused.</param>
        private static void Main(string[] args)
        {
            Console.WriteLine();

            // Set some defaults.
            string packageFilename = DefaultPackageFilename;
            string configurationFilename = DefaultConfigurationFilename;
            int instanceCount = DefaultInstanceCount;
            string command = "status";

            // Parse command line arguments.
            if (args.Length > 0)
            {
                command = args[0].ToLower();

                if (args.Length > 1)
                {
                    if (command == "start")
                    {
                        if (!int.TryParse(args[1], out instanceCount))
                        {
                            Usage(-1);
                        }
                    }
                    else
                    {
                        packageFilename = args[1];
                    }

                    if (args.Length > 2)
                    {
                        configurationFilename = args[2];
                    }
                }
            }

            // Get our Azure account information.
            AzureAccount azureAccount = GetOurAzureAccount();

            // Perform user requested action.
            CloudBlockBlob packageBlob;
            switch (command)
            {
                case "create":
                    azureAccount.CreateServiceSpecification(NuBuildServiceName, "West US");
                    break;

                case "deploy":
                    // Upload our package (.cspkg file) to a blob.
                    // We name the blob after the package filename.
                    string blobName = Path.GetFileNameWithoutExtension(packageFilename);
                    packageBlob = GetPackageBlob(azureAccount, blobName);
                    packageBlob.UploadFromFile(packageFilename, System.IO.FileMode.Open);

                    // Create a new deployment using the desired package blob.
                    // TODO: Provide an unique name for each deployment?
                    // REVIEW: Upload to "Staging" slot instead?
                    string configuration = File.ReadAllText(configurationFilename);
                    azureAccount.DeployService(NuBuildServiceName, "Production", DeploymentSlot.Production, configuration, packageBlob.Uri, startImmediately: true);

                    Console.WriteLine("Issued deployment request");
                    break;

                case "start":
                    // Create a new deployment using a hard-coded configuration and a previously uploaded blob.
                    ServiceConfiguration config = new ServiceConfiguration(
                        NuBuildServiceName,
                        "4",
                        "*",
                        "2014-06.2.4",
                        "CloudExecutionWorker",
                        instanceCount);
                    packageBlob = GetPackageBlob(azureAccount, NuBuildServicePackageName);
                    azureAccount.DeployService(NuBuildServiceName, "Production", DeploymentSlot.Production, config.ToXml(), packageBlob.Uri, startImmediately: true);

                    Console.WriteLine("Issued deployment request");
                    break;

                case "status":
                    HostedServiceGetDetailedResponse serviceInfo = azureAccount.GetServiceInformation(NuBuildServiceName);
                    DisplayServiceInformation(serviceInfo);
                    break;

                case "stop":
                    // Delete the Azure deployment.
                    // This stops the currently running service, but leaves the
                    // configuration for this service in the Azure database.
                    azureAccount.DeleteDeployment(NuBuildServiceName, DeploymentSlot.Production);
                    break;

                case "test":
                    ////azureAccount.TestSomething();

                    ServiceConfiguration testConfig = new ServiceConfiguration(NuBuildServiceName, "4", "*", "2014-06.2.4", "CloudExecutionWorker", 42);
                    Console.WriteLine(testConfig.ToXml());
                    break;

                case "upload":
                    // Upload our package (.cspkg file) to a blob.
                    packageBlob = GetPackageBlob(azureAccount, NuBuildServicePackageName);
                    packageBlob.UploadFromFile(packageFilename, System.IO.FileMode.Open);
                    Console.WriteLine("Uploaded package");
                    break;

                case "/?":
                case "help":
                    Usage(0);
                    break;

                default:
                    Usage(-1);
                    break;
            }
        }

        /// <summary>
        /// Display a (hopefully) helpful usage message to the user,
        /// and exit the process.
        /// </summary>
        /// <param name="exitcode">Process exit code to use.</param>
        private static void Usage(int exitcode)
        {
            Console.WriteLine("Usage: AzureManager [create | deploy [package file [config file]] |");
            Console.WriteLine("                     start [instances] | status | stop |");
            Console.WriteLine("                     upload [package file]]");
            Console.WriteLine();
            Console.WriteLine("    where");
            Console.WriteLine("        instances       Number of service instances to start.");
            Console.WriteLine("                         (default: {0})", DefaultInstanceCount);
            Console.WriteLine("        package file    Package file to deploy.");
            Console.WriteLine("                         (default: .\\{0})", DefaultPackageFilename);
            Console.WriteLine("        config file     Configuration file for deployment.");
            Console.WriteLine("                         (default: .\\{0})", DefaultConfigurationFilename);
            Console.WriteLine();
            Console.WriteLine("    Commands:");
            Console.WriteLine("        create    Create a new service configuration (using hard-wired info).");
            Console.WriteLine("        deploy    Deploy using the given package and configuration");
            Console.WriteLine("                   (overwrites existing hard-wired package blob).");
            Console.WriteLine("        start     Start the given number of instances of an existing package");
            Console.WriteLine("                   named '{0}'.", NuBuildServicePackageName);
            Console.WriteLine("        status    Display the current service and deployment status.");
            Console.WriteLine("        stop      Stop the current deployment of the service.");
            Console.WriteLine("        upload    Upload the given package file to hard-wired package blob");
            Console.WriteLine("                   named '{0}'.", NuBuildServicePackageName);
            Environment.Exit(exitcode);
        }

        /// <summary>
        /// Gets our Azure account.
        /// </summary>
        /// <returns>An Azure account.</returns>
        private static AzureAccount GetOurAzureAccount()
        {
            string subscriptionId = null;
            string certBase64Encoded = null;

            NameValueCollection appSettings = ConfigurationManager.AppSettings;
            if (appSettings != null)
            {
                subscriptionId = appSettings["Subscription Id"];
                certBase64Encoded = appSettings["Certificate (Base 64 Encoded)"];
            }

            if (string.IsNullOrEmpty(subscriptionId))
            {
                throw new ConfigurationException("Subscription Id setting missing from your AzureManager.exe.config file!");
            }

            if (string.IsNullOrEmpty(certBase64Encoded))
            {
                throw new ConfigurationException("Certificate setting missing from your AzureManager.exe.config file!");
            }

            byte[] cert = Convert.FromBase64String(certBase64Encoded);
            X509Certificate2 x509Cert = new X509Certificate2(cert);
            AzureAccount azureAccount = new AzureAccount(subscriptionId, x509Cert);

            return azureAccount;
        }

        /// <summary>
        /// Writes selected fields of the give HostedServiceGetDetailedResponse
        /// object out to the console.
        /// </summary>
        /// <param name="service">
        /// The HostedServiceGetDetailedResponse object to display.
        /// </param>
        private static void DisplayServiceInformation(HostedServiceGetDetailedResponse service)
        {
            Console.WriteLine("Service Name {0}:", service.ServiceName);

            Console.WriteLine("  Date Created = {0}", service.Properties.DateCreated);
            Console.WriteLine("  Date Last Modified = {0}", service.Properties.DateLastModified);
            Console.WriteLine("  Description = {0}", service.Properties.Description);
            Console.WriteLine("  Label = {0}", service.Properties.Label);
            Console.WriteLine("  Location = {0}", service.Properties.Location);
            Console.WriteLine("  Status = {0}", service.Properties.Status);

#if false
            foreach(string size in service.ComputeCapabilities.VirtualMachinesRoleSizes)
            {
                Console.WriteLine("VM Role Size = {0}", size);
            }

            Console.WriteLine("URI = {0}", service.Uri);
#endif

            if (service.Deployments.Count == 0)
            {
                Console.WriteLine("  No current deployments!");
            }

            foreach (HostedServiceGetDetailedResponse.Deployment deployment in service.Deployments)
            {
                    Console.WriteLine();
                    Console.WriteLine("  Deployment Name {0}:", deployment.Name);
                    Console.WriteLine("    Created = {0}", deployment.CreatedTime);
                    Console.WriteLine("    Label = {0}", deployment.Label);
                    Console.WriteLine("    Slot = {0}", deployment.DeploymentSlot);
                    Console.WriteLine("    Status = {0}", deployment.Status);
                    Console.WriteLine("    Instances = {0}", deployment.RoleInstances.Count);
                    ////Console.WriteLine(deployment.Configuration);
            }
        }

        /// <summary>
        /// Uploads the given file to the specified Azure blob.
        /// </summary>
        /// <param name="azureAccount">Azure account to use.</param>
        /// <param name="blobName">Name of the blob to upload to.</param>
        /// <returns>A reference to the CloudBlockBlob.</returns>
        private static CloudBlockBlob GetPackageBlob(AzureAccount azureAccount, string blobName)
        {
            // Get connection string for our storage account.
            // TODO: Remove hard-coded storage account name.
            const string StorageAccountName = "ironcladstoretest";
            string connectionString = azureAccount.GetConnectionStringForStorageAccount(StorageAccountName);

            ////Console.WriteLine("Using connection string " + connectionString);

            // Use our storage account connection string to get our CloudStorageAccount.
            CloudStorageAccount storageAccount = CloudStorageAccount.Parse(connectionString);

            ////Console.WriteLine("Storage account URI = {0}", storageAccount.BlobEndpoint.AbsoluteUri);

            // Use our CloudStorageAccount to create a CloudBlobClient.
            CloudBlobClient blobClient = storageAccount.CreateCloudBlobClient();

            ////Console.WriteLine("Blob base URI = {0}", blobClient.BaseUri);

            // Find or create our "packages" blob storage container.
            CloudBlobContainer container = blobClient.GetContainerReference("packages");
            container.CreateIfNotExists(BlobContainerPublicAccessType.Container);

            // Get the package blob we want to deploy.
            // This is a 'cspkg' file stored as a blob.
            CloudBlockBlob packageBlob = container.GetBlockBlobReference(blobName);
            return packageBlob;
        }
    }
}
