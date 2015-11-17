@rem //////////////////////////////////////////////////////////////////////
@rem 
@rem   Microsoft Research Singularity
@rem 
@rem   Copyright (c) Microsoft Corporation.  All rights reserved.
@rem 
@rem This script launches bootd with paths set up for the current build
@rem environment.  It replies to hosts specified in the file
@rem %SINGULARITY_ROOT%\boothosts.txt.  MAC addresses should appear one per
@rem line.
@rem
@echo off

setlocal enabledelayedexpansion enableextensions

:parse

if /I .%1==./1394 (
    set ConnectArgs=/dhcp /c:DBG=1
    shift
    goto :parse
)

if not defined BOOT_HOSTS (
    set BOOT_HOSTS=%~dp0\boothosts.txt
)

if not exist "%BOOT_HOSTS%" (
    echo.Could not find boot hosts file:
    echo.
    echo.  %BOOT_HOSTS%
    echo.
    echo.The boot hosts file should specify a list of MAC addresses one per
    echo.line for bootd to respond to.  If IP addresses are to be associated
    echo.with a MAC address then they should be comma-separated from their MAC
    echo.addresses, e.g. 00-01-02-03-04-05,10.0.0.1
    exit /b 1
)

@rem NB using type here because of need to quote protect path to support
@rem paths with spaces in.
set MacArgs=
for /F %%m in ('type "%BOOT_HOSTS%"') do (
    set MacArgs=!MacArgs! /m:%%m
)

start %~dp0\bootd.exe /dhcp %ConnectArgs% /b:pxe-loader !MacArgs! /tftp /v ..\nuobj\src\Dafny\Apps\BenchmarkService\bootable-NoVerify %*
