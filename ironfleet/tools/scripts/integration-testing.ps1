#param (
#  [string]$path
#)

#C:\cygwin\bin\bash.exe --login -c "cd '$path' ; make "
#C:\cygwin\bin\bash.exe --login -c "cd research/ironclad/code/iron/src/Dafny; make flib"

# If this script is not running on a build server, remind user to 
# set environment variables so that this script can be debugged
if(-not $Env:TF_BUILD -and -not ($Env:TF_BUILD_SOURCESDIRECTORY -and ($Env:TF_BUILD_BUILDNUMBER -and ($Env:TF_BUILD_SOURCEGETVERSION -and $Env:TF_BUILD_BINARIESDIRECTORY))))
{
	Write-Error "You must set the following environment variables"
	Write-Error "to test this script interactively."
	Write-Host '$Env:TF_BUILD_SOURCESDIRECTORY - For example, enter something like:'
	Write-Host '    $Env:TF_BUILD_SOURCESDIRECTORY = "C:\Builds\1\IroncladApps\DistributedVerify\src\"'
	Write-Host '$Env:TF_BUILD_BINARIESDIRECTORY - For example, enter something like:'
	Write-Host '    $Env:TF_BUILD_BINARIESDIRECTORY = "C:\Builds\1\IroncladApps\DistributedVerify\bin\"'
	Write-Host '$Env:TF_BUILD_BUILDNUMBER - For example, enter something like:'
	Write-Host '    $Env:TF_BUILD_BUILDNUMBER = "build123"'
	Write-Host '$Env:TF_BUILD_SOURCEGETVERSION - Expects three colon-delimited fields.  For example, enter something like:'
	Write-Host '    $Env:TF_BUILD_SOURCEGETVERSION = "git:master:4abcd7adf9098012355"'
	exit 1
}

$sha = $Env:TF_BUILD_SOURCEGETVERSION.split(":")[2]

#cd $Env:TF_BUILD_SOURCESDIRECTORY\iron
#. .\build-tools.ps1

# Run the cygwin make file to run Dafny on all the files
C:\cygwin\bin\bash.exe --login -c "cd '$Env:TF_BUILD_SOURCESDIRECTORY'; cd ironfleet/; ./bin_tools/NuBuild/NuBuild.exe -j 4 BatchDafny src/Dafny/Distributed/apps.dfy.batch --html summary.html; git log -1 > gitlog.txt; sed -i -b -e '/_VERIFICATION_RESULT_PLACEHOLDER/r gitlog.txt' -e 's/_VERIFICATION_RESULT_PLACEHOLDER//' summary.html"
$cygwin_make_exit_code = $LASTEXITCODE   # Save the error code, so we can report it appropriately

# Run the email generator
C:\cygwin\bin\bash.exe --login -c "cd '$Env:TF_BUILD_SOURCESDIRECTORY'; cd ironfleet/; email -html -f ironclad@microsoft.com -n Ironclad -subject 'Ironclad build summary $Env:TF_BUILD_BUILDNUMBER-$sha' ironclad@microsoft.com  < summary.html "

## Attempt to collect any output that may have been produced
#$target_dir_name = "C:\BuildLogs\$Env:TF_BUILD_BUILDNUMBER-$sha"
##echo "$target_dir_name" >> C:\BuildLogs\dir_name.txt
#mkdir $target_dir_name
#
#$src_dir_name = "$Env:TF_BUILD_SOURCESDIRECTORY\iron\nuobj\"
##copy "$src_dir_name\summary.xml"    $target_dir_name
#copy "$src_dir_name\test.tgz"       $target_dir_name
##copy "$src_dir_name\iso.sha1"       $target_dir_name
##copy "$src_dir_name\build-out.txt"  $target_dir_name
##copy "$src_dir_name\summary.html"   $target_dir_name
#
## Place a copy of all the files above in the bin directory, so TFS will also bundle them up for us
#$target_dir_name = $Env:TF_BUILD_BINARIESDIRECTORY 
##copy "$src_dir_name\summary.xml"    $target_dir_name
#copy "$src_dir_name\test.tgz"       $target_dir_name
##copy "$src_dir_name\iso.sha1"       $target_dir_name
##copy "$src_dir_name\build-out.txt"  $target_dir_name
##copy "$src_dir_name\summary.html"   $target_dir_name

if ($cygwin_make_exit_code -gt 0)
{
  # Cause the build to fail
  echo make failed
  exit 5
}
