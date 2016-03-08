// Copyright (c) Microsoft. All rights reserved.

using System.Collections.Generic;
using System.Diagnostics;
using System.Text;

namespace NuBuild
{
    using System.IO;

    public class SimpleProcessInvoker : IProcessInvoker
    {
        public readonly AbsoluteFileSystemPath ExePath;
        private readonly Process process;

        private string stdout;
        private string stderr;

        private SimpleProcessInvoker(AbsoluteFileSystemPath exePath, string args, IDictionary<string, string> env = null)
        {
            this.ExePath = exePath;

            var info = new ProcessStartInfo
            {
                FileName = exePath.ToString(),
                Arguments = args,
                UseShellExecute = false,
                RedirectStandardInput = true,
                RedirectStandardError = true,
                RedirectStandardOutput = true
            };

            if (env != null)
            {
                foreach (var key in env.Keys)
                {
                    info.EnvironmentVariables[key] = env[key];
                }
            }

            this.process = Process.Start(info);
        }
    
        public int ExitCode { get; private set; }

        public double CpuTime { get; private set; }

        public string GetStdout()
        {
            return this.stdout;
        }

        public string GetStderr()
        {
            return this.stderr;
        }

        public static SimpleProcessInvoker Exec(AbsoluteFileSystemPath exePath, string args, IDictionary<string, string> env = null)
        {
            var invoker = new SimpleProcessInvoker(exePath, args, env);
            var msg = string.Format("Waiting for invocation of `{0} {1}` to complete...", invoker.ExePath.FileName, args);
            Logger.WriteLine(msg, "info");
            invoker.process.WaitForExit();

            invoker.ExitCode = invoker.process.ExitCode;
            invoker.stdout = invoker.process.StandardOutput.ReadToEnd();
            invoker.stderr = invoker.process.StandardError.ReadToEnd();
            invoker.CpuTime = invoker.process.TotalProcessorTime.TotalSeconds;

            return invoker;
        }
    }
}
