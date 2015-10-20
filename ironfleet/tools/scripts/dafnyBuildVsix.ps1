# Run this file from the ironfleet directory 
# (not from ironfleet\tools or ironfleet\tools\scripts or ironfleet\tools\Dafny)
# This script assumes existence of:
#   .\tools\Dafny\DafnyLanguageService.vsix
#   .\tools\Dafny\DafnyOptions.txt
#   .\tools\Dafny\z3.exe
# It copies .\tools\Dafny\DafnyLanguageService.vsix into:
#   .\tools\Dafny\DafnyIroncladVsPlugin.vsix
# It then adds DafnyOptions.txt and z3.exe to .\tools\Dafny\DafnyIroncladVsPlugin.vsix
# It also fixes up the Boogie stack size

"running in $pwd"
$null = [System.Reflection.Assembly]::LoadWithPartialName("System.IO.Compression")
$null = [System.Reflection.Assembly]::LoadWithPartialName("System.IO.Compression.FileSystem")
cp .\tools\Dafny\DafnyLanguageService.vsix .\tools\Dafny\DafnyIroncladVsPlugin.vsix
$zipArchive = [System.IO.Compression.ZipFile]::Open("$pwd\tools\Dafny\DafnyIroncladVsPlugin.vsix", [System.IO.Compression.ZipArchiveMode]::Update)
$zipArchive.GetEntry("DafnyOptions.txt").Delete()
$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\tools\Dafny\DafnyOptions.txt", "DafnyOptions.txt")
#$null = [System.IO.Compression.ZipFileExtensions]::CreateEntryFromFile($zipArchive, "$pwd\tools\Dafny\z3.exe", "z3.exe")
$zipArchive.Dispose();
"done"

$vis = (ls "C:\Program Files (x86)\Microsoft Visual Studio *")[0].FullName
$p = $env:PATH
$env:PATH = $p + ";$vis\VC\bin\;$vis\Common7\IDE"
& editbin.exe /stack:268435456 .\tools\Dafny\Boogie.exe
& editbin.exe /stack:268435456 .\tools\Dafny\Dafny.exe
$env:PATH = $p
