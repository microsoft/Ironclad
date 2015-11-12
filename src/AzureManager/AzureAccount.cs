//--
// <copyright file="AzureAccount.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace AzureManager
{
    using System;
    using System.Globalization;
    using System.Security.Cryptography.X509Certificates;
    using Microsoft.WindowsAzure;
    using Microsoft.WindowsAzure.Management.Compute;
    using Microsoft.WindowsAzure.Management.Compute.Models;
    using Microsoft.WindowsAzure.Management.Storage;
    using Microsoft.WindowsAzure.Management.Storage.Models;

    /// <summary>
    /// Representation of an Azure Account Subscription.
    /// </summary>
    public class AzureAccount
    {
        /// <summary>
        /// Credentials associated with this Azure account.
        /// </summary>
        private SubscriptionCloudCredentials credentials;

        /// <summary>
        /// ComputeManagementClient for managing Azure compute resources.
        /// </summary>
        private ComputeManagementClient computeManager;

        /// <summary>
        /// StorageManagementClient for managing Azure storage resources.
        /// </summary>
        private StorageManagementClient storageManager;

        /// <summary>
        /// Initializes a new instance of the AzureAccount class.
        /// </summary>
        /// <param name="subscriptionId">Subscription ID of the Azure account.</param>
        /// <param name="cert">X509 certificate used for authentication.</param>
        public AzureAccount(string subscriptionId, X509Certificate2 cert)
        {
            this.credentials = new CertificateCloudCredentials(subscriptionId, cert);

            this.computeManager = CloudContext.Clients.CreateComputeManagementClient(this.credentials);
            this.storageManager = CloudContext.Clients.CreateStorageManagementClient(this.credentials);
        }

        /// <summary>
        /// Gets the service information for the specified service.
        /// </summary>
        /// <param name="serviceName">Name of the service to query.</param>
        /// <returns>A HostedServiceGetDetailedResponse object containing the information.</returns>
        public HostedServiceGetDetailedResponse GetServiceInformation(string serviceName)
        {
            HostedServiceGetDetailedResponse service;
            service = this.computeManager.HostedServices.GetDetailed(serviceName);

            return service;
        }

        /// <summary>
        /// Creates a service specification (configuration?) entry in Azure's database.
        /// This reserves the (Azure-unique) DNS prefix name used to access the service.
        /// </summary>
        /// <remarks>
        /// Note that this does not deploy and start the service.
        /// </remarks>
        /// <param name="serviceName">Name of the cloud service.</param>
        /// <param name="location">Geographical region where the service should be hosted.</param>
        public void CreateServiceSpecification(string serviceName, string location)
        {
            // Required: Label, ServiceName.
            // One Required (but not both): AffinityGroup, Location.
            // Optional: Description, ExtendedProperties,
            HostedServiceCreateParameters parameters = new HostedServiceCreateParameters();
            parameters.Label = serviceName;
            parameters.ServiceName = serviceName;
            parameters.Location = location;

            this.computeManager.HostedServices.Create(parameters);
        }

        /// <summary>
        /// Deletes the specified service deployment.
        /// </summary>
        /// <param name="serviceName">Name of the service</param>
        /// <param name="deploymentSlot">Environment for this deployment (e.g. Production or Staging).</param>
        public void DeleteDeployment(string serviceName, DeploymentSlot deploymentSlot)
        {
            this.computeManager.Deployments.DeleteBySlot(serviceName, deploymentSlot);
        }

        /// <summary>
        /// Deploys a service.
        /// </summary>
        /// <remarks>
        /// Note that the service specification must already have been created.
        /// </remarks>
        /// <param name="serviceName">Name of the service.</param>
        /// <param name="deploymentName">Name of this deployment.</param>
        /// <param name="deploymentSlot">Environment for this deployment (e.g. Production or Staging).</param>
        /// <param name="configuration">Deployment configuration information (i.e. .cscfg file contents).</param>
        /// <param name="packageBlob">URI for blob containing package (i.e. .cspkg) file contents.</param>
        /// <param name="startImmediately">Whether to start the deployment immediately after it is created.</param>
        public void DeployService(
            string serviceName,
            string deploymentName,
            DeploymentSlot deploymentSlot,
            string configuration,
            Uri packageBlob,
            bool startImmediately = true)
        {
            // Required: Configuration, Label, Name, PackageUri.
            // Optional: ExtendedProperties, ExtensionConfiguration, StartDeployment, TreatWarningsAsError.
            DeploymentCreateParameters parameters = new DeploymentCreateParameters();
            parameters.Configuration = configuration;  // Contents of .cscfg file.
            parameters.Label = serviceName;  // Name for hosted service.  Does not need to match serviceName.
            parameters.Name = deploymentName;  // Unique name for this particular deployment.
            parameters.PackageUri = packageBlob;  // URI for blob containing .cspkg file.
            parameters.StartDeployment = startImmediately;  // Whether to start the deployment immediately after it is created.

            this.computeManager.Deployments.Create(serviceName, deploymentSlot, parameters);
        }

        /// <summary>
        /// Gets the connection string for the given storage account.
        /// </summary>
        /// <param name="storageAccountName">A storage account name.</param>
        /// <returns>The connection string for the given storage account.</returns>
        public string GetConnectionStringForStorageAccount(string storageAccountName)
        {
            // This makes a call to the Azure infrastructure to get the keys.
            // REVIEW: Check status code of the response?
            StorageAccountGetKeysResponse keys = this.storageManager.StorageAccounts.GetKeys(storageAccountName);

            string connectionString = string.Format(
                CultureInfo.InvariantCulture,
                "DefaultEndpointsProtocol=https;AccountName={0};AccountKey={1}",
                storageAccountName,
                keys.PrimaryKey);

            return connectionString;
        }

        /// <summary>
        /// Procedure for testing random things.
        /// </summary>
        public void TestSomething()
        {
            HostedServiceListResponse response;
            response = this.computeManager.HostedServices.List();
            Console.WriteLine("List of hosted services:");
            foreach (HostedServiceListResponse.HostedService service in response.HostedServices)
            {
                Console.WriteLine("\n{0}\n", service.ServiceName);

                // Note: The HostedServiceListResponse.HostedService class
                // contains many of the same properties as the
                // HostedServiceGetDetailedResponse class.
            }
        }

        /// <summary>
        /// Displays all the deployments in a given service.
        /// </summary>
        /// <remarks>
        /// This is an alternative way to access the deployments.
        /// HostedServiceGetDetailedResponse.Deployment is another.
        /// </remarks>
        /// <param name="serviceName">The service to query.</param>
        public void ShowDeployments(string serviceName)
        {
            DeploymentGetResponse response;

            try
            {
                response = this.computeManager.Deployments.GetBySlot(serviceName, DeploymentSlot.Production);
                Console.WriteLine("Production Deployment");
                Console.WriteLine("Label = {0}", response.Label);
            }
            catch (Microsoft.WindowsAzure.CloudException except)
            {
                Console.WriteLine("Show Deployment Exception: {0}", except.ErrorMessage);
            }
        }
    }
}
