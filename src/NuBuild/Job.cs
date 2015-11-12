//--
// <copyright file="Job.cs" company="Microsoft Corporation">
//     Copyright (c) Microsoft Corporation.  All rights reserved.
// </copyright>
//--

namespace NuBuild
{
    using System;
    using System.ComponentModel;
    using System.Diagnostics;
    using System.Diagnostics.CodeAnalysis;
    using System.Globalization;
    using System.Runtime.InteropServices;
    using Microsoft.Win32.SafeHandles;

    /// <summary>
    /// Represents a Windows Job Object.
    /// </summary>
    /// <remarks>
    /// This class is only used by ProcessInvoker, so it could be private to that class.
    /// </remarks>
    [SuppressMessage("StyleCop.CSharp.ReadabilityRules", "SA1121:UseBuiltInTypeAlias", Justification = "UInt* is more appropriate for system programming")]
    internal class Job : IDisposable
    {
        /// <summary>
        /// Handle to the native Windows job object.
        /// </summary>
        private SafeFileHandle jobObjectHandle;

        /// <summary>
        /// Flag indicating whether or not Dispose has already been called.
        /// </summary>
        private bool disposed;

        /// <summary>
        /// Initializes a new instance of the Job class.
        /// </summary>
        public Job()
        {
            this.jobObjectHandle = NativeMethods.CreateJobObject(IntPtr.Zero, null);
            if (this.jobObjectHandle.IsInvalid)
            {
                // Note that the parameterless Win32Exception constructor calls Marshal.GetLastWin32Error internally.
                throw new Win32Exception();
            }

            // -
            // Set up this job object so that any processes assigned to it will
            // be terminated when it is closed (since this job object will be
            // closed automatically when the owning process exits, all assigned
            // processes will also be closed when the owning process exists).
            // -
            // Note that to set the JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE flag,
            // the call to SetInformationJobObject must be of JobObjectInfoClass
            // ExtendedLimitInformation, even though the flag is in the simpler
            // BasicLimitInformation structure contained in the former.
            // -
            NativeMethods.JOBOBJECT_EXTENDED_LIMIT_INFORMATION info = new NativeMethods.JOBOBJECT_EXTENDED_LIMIT_INFORMATION();
            int infoSize = Marshal.SizeOf(typeof(NativeMethods.JOBOBJECT_EXTENDED_LIMIT_INFORMATION));

            info.BasicLimitInformation.LimitFlags =
                NativeMethods.JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;

            IntPtr infoPtr = Marshal.AllocHGlobal(infoSize);

            try
            {
                Marshal.StructureToPtr(info, infoPtr, false);

                if (!NativeMethods.SetInformationJobObject(
                         this.jobObjectHandle,
                         NativeMethods.JOBOBJECTINFOCLASS.ExtendedLimitInformation,
                         infoPtr,
                         (UInt32)infoSize))
                {
                    // Note that the parameterless Win32Exception constructor calls Marshal.GetLastWin32Error internally.
                    throw new Win32Exception();
                }
            }
            finally
            {
                Marshal.FreeHGlobal(infoPtr);
            }
        }

        /// <summary>
        /// Adds the given process to the job object.
        /// </summary>
        /// <param name="process">Process to add.</param>
        /// <returns>True if successful, false otherwise.</returns>
        public bool AddProcess(Process process)
        {
            return NativeMethods.AssignProcessToJobObject(this.jobObjectHandle, process.Handle);
        }

        /// <summary>
        /// Gets the total CPU consumed by all processes associated with this job object.
        /// </summary>
        /// <returns>Total CPU time.</returns>
        public TimeSpan GetCpuTime()
        {
            UInt64 totalCpuTime = 0;
            NativeMethods.JOBOBJECT_BASIC_ACCOUNTING_INFORMATION basicAccountingInfo;

            basicAccountingInfo = this.GetBasicAccountingInformation();
            totalCpuTime = basicAccountingInfo.TotalKernelTime + basicAccountingInfo.TotalUserTime;

            return new TimeSpan((long)totalCpuTime);
        }

        /// <summary>
        /// Terminates all processes currently associated with this job object.
        /// </summary>
        /// <param name="exitCode">Exit code to be used by all processes and threads.</param>
        /// <returns>True if successful, false otherwise.</returns>
        public bool Terminate(UInt32 exitCode)
        {
            return NativeMethods.TerminateJobObject(this.jobObjectHandle, exitCode);
        }

        /// <summary>
        /// Closes this Job object.
        /// </summary>
        public void Close()
        {
            this.jobObjectHandle.Close();
        }

        /// <summary>
        /// Releases resources.
        /// </summary>
        public void Dispose()
        {
            this.Dispose(true);
            GC.SuppressFinalize(this);
        }

        /// <summary>
        /// Releases unmanaged and (optionally) managed resources.
        /// </summary>
        /// <param name="disposing">Whether or not to release managed resources.</param>
        private void Dispose(bool disposing)
        {
            if (this.disposed)
            {
                return;
            }

            if (disposing)
            {
                this.jobObjectHandle.Dispose();
            }

            this.disposed = true;
        }

        /// <summary>
        /// Gets a struct containing the basic accounting information for the job object.
        /// </summary>
        /// <returns>A JOBOBJECT_BASIC_ACCOUNTING_INFORMATION structure.</returns>
        private NativeMethods.JOBOBJECT_BASIC_ACCOUNTING_INFORMATION GetBasicAccountingInformation()
        {
            NativeMethods.JOBOBJECT_BASIC_ACCOUNTING_INFORMATION info;
            int infoSize = Marshal.SizeOf(typeof(NativeMethods.JOBOBJECT_BASIC_ACCOUNTING_INFORMATION));
            IntPtr infoPtr = Marshal.AllocHGlobal(infoSize);

            try
            {
                if (!NativeMethods.QueryInformationJobObject(
                         this.jobObjectHandle,
                         NativeMethods.JOBOBJECTINFOCLASS.BasicAccountingInformation,
                         infoPtr,
                         (UInt32)infoSize,
                         IntPtr.Zero))
                {
                    // Note that the parameterless Win32Exception constructor calls Marshal.GetLastWin32Error internally.
                    throw new Win32Exception();
                }

                info = (NativeMethods.JOBOBJECT_BASIC_ACCOUNTING_INFORMATION)Marshal.PtrToStructure(infoPtr, typeof(NativeMethods.JOBOBJECT_BASIC_ACCOUNTING_INFORMATION));
            }
            finally
            {
                Marshal.FreeHGlobal(infoPtr);
            }

            return info;
        }

        /// <summary>
        /// Represents the native Windows API for accessing job objects.
        /// </summary>
        [SuppressMessage("StyleCop.CSharp.NamingRules", "SA1310:FieldNamesMustNotContainUnderscore", Justification = "Part of Windows API")]
        [SuppressMessage("StyleCop.CSharp.DocumentationRules", "SA1600:ElementsMustBeDocumented", Justification = "Part of Windows API")]
        [SuppressMessage("StyleCop.CSharp.DocumentationRules", "SA1602:EnumerationItemsMustBeDocumented", Justification = "Part of Windows API")]
        private static class NativeMethods
        {
            public const UInt32 JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x2000;

            public enum JOBOBJECTINFOCLASS
            {
                BasicAccountingInformation = 1,
                BasicLimitInformation = 2,
                ExtendedLimitInformation = 9
            }

            [DllImport("kernel32.dll", CharSet = CharSet.Unicode)]
            public static extern SafeFileHandle CreateJobObject(IntPtr jobAttributes, string name);

            [DllImport("kernel32.dll")]
            [return: MarshalAs(UnmanagedType.Bool)]
            public static extern bool AssignProcessToJobObject(SafeHandle jobHandle, IntPtr processHandle);

            [DllImport("kernel32.dll")]
            [return: MarshalAs(UnmanagedType.Bool)]
            public static extern bool SetInformationJobObject(SafeHandle jobHandle, JOBOBJECTINFOCLASS infoClass, IntPtr info, UInt32 infoLength);

            [DllImport("kernel32.dll")]
            [return: MarshalAs(UnmanagedType.Bool)]
            public static extern bool QueryInformationJobObject(SafeHandle jobHandle, JOBOBJECTINFOCLASS infoClass, IntPtr info, UInt32 infoLength, IntPtr returnLength);

            [DllImport("kernel32.dll")]
            [return: MarshalAs(UnmanagedType.Bool)]
            public static extern bool TerminateJobObject(SafeHandle job, UInt32 exitCode);

            [StructLayout(LayoutKind.Sequential, Pack = 8)]
            public struct JOBOBJECT_BASIC_LIMIT_INFORMATION
            {
                public UInt64 PerProcessUserTimeLimit;
                public UInt64 PerJobUserTimeLimit;
                public UInt32 LimitFlags;
                public UIntPtr MinimumWorkingSetSize;
                public UIntPtr MaximumWorkingSetSize;
                public UInt32 ActiveProcessLimit;
                public UIntPtr Affinity;
                public UInt32 PriorityClass;
                public UInt32 SchedulingClass;
            }

            [StructLayout(LayoutKind.Sequential)]
            public struct IO_COUNTERS
            {
                public UInt64 ReadOperationCount;
                public UInt64 WriteOperationCount;
                public UInt64 OtherOperationCount;
                public UInt64 ReadTransferCount;
                public UInt64 WriteTransferCount;
                public UInt64 OtherTransferCount;
            }

            [StructLayout(LayoutKind.Sequential)]
            public struct JOBOBJECT_EXTENDED_LIMIT_INFORMATION
            {
                public JOBOBJECT_BASIC_LIMIT_INFORMATION BasicLimitInformation;
                public IO_COUNTERS IoInfo;
                public UIntPtr ProcessMemoryLimit;
                public UIntPtr JobMemoryLimit;
                public UIntPtr PeakProcessMemoryLimit;
                public UIntPtr PeakJobMemoryUsed;
            }

            [StructLayout(LayoutKind.Sequential)]
            public struct JOBOBJECT_BASIC_ACCOUNTING_INFORMATION
            {
                public UInt64 TotalUserTime;
                public UInt64 TotalKernelTime;
                public UInt64 ThisPeriodTotalUserTime;
                public UInt64 ThisPeriodTotalKernelTime;
                public UInt32 TotalPageFaultCount;
                public UInt32 TotalProcesses;
                public UInt32 ActiveProcesses;
                public UInt32 TotalTerminatedProcesses;
            }
        }
    }
}