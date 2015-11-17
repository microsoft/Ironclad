$build_args = $args[0]
$BUILD_SUFFIX = "$($build_args | %{"-$_"})".Replace(" ", "")
$BUILD_DEFS = $($build_args | %{"-def"; $_})

$BUILD = "$ROOT\tools\build"
$OBJROOT = "$ROOT\obj$BUILD_SUFFIX"
$BINROOT = "$ROOT\bin$BUILD_SUFFIX"
$BINTOOLS = "$ROOT\bin_tools"
$SPEC = "$ROOT\src\Trusted\Spec"

# By default, all the following should be true:
$SYMDIFF_ENABLED = $false
$BOOGIE_ENABLED = $true
$DAFNYCC_INCREMENTAL_BUILD = $true

# The AppLoader doesn't know any secrets, so we don't need to run SymDiff on it.
if ($build_args -contains "AppLoader")
{
    $SYMDIFF_ENABLED = $false
}

function list
{
    @($args)
}

$boogieasm_x64_flag = ""
if ($build_args.Contains("x64"))
{
    $boogieasm_x64_flag = "-x64"
}

# recursively flatten all arrays into a single array
function flatten($arr)
{
    do
    {
        $c = $arr.count
        $arr = @($arr | %{$_})
    } while ($c -ne $arr.count)
    ,($arr)
}

function run([Parameter(Mandatory=$true)]$cmd, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    & $cmd $(flatten $arr)
    if($LastExitCode)
    {
        throw "error running $cmd $(flatten $arr)"
    }
}

function runShell
{
    powershell -command "$(flatten $args)"
    if($LastExitCode)
    {
        throw "error running $(flatten $args)"
    }
}

function needToBuild($out, $ins)
{
    #Write-Host "Do I need to build $out ?"
    if (-not (test-path $out)) { return $true }
    $t = (get-item $out).LastWriteTimeUtc
    foreach ($f in $ins)
    {
        if (-not (test-path $f)) { throw "cannot find input file $f" }
        if ($t -lt (get-item $f).LastWriteTimeUtc) { return $true }
        #Write-Host "Checking need to build based on: $f"
    }
    return $false
}

function ensureDir($dir)
{
    if (-not (test-path $dir)) { mkdir $dir }
}

function ensureDirForFile($path)
{
    $dir = [System.IO.Path]::GetDirectoryName($path)
    if (-not (test-path $dir)) { mkdir $dir }
}

function _boogie_dbg([Parameter(Mandatory=$true)]$out, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    $arr = flatten $arr
    $boogieasm = "$BINTOOLS\boogieasm\boogieasm.exe"
    $ins = @($arr | ?{-not $_.StartsWith("/")}) + @($boogieasm)
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out)
        "boogie $arr"
        $bpls = $arr | ?{$_.EndsWith(".bpl")}
        $flags = $arr | ?{-not $_.EndsWith(".bpl")}
        run $boogieasm $BUILD_DEFS $boogieasm_x64_flag "-verify" "-out" "$out.bpl" $bpls
        $time1 = Get-Date
        & "$ROOT\..\iron\build\boogie-new\boogie.exe" /printModel:4 /noinfer /typeEncoding:m $flags "$out.bpl" | out-file -encoding ascii "$out.err"
        #& "$ROOT\..\iron\build\boogie-new\boogie.exe" /mv:model.bvd /noinfer /typeEncoding:m $flags "$out.bpl" | out-file -encoding ascii "$out.err"
        $time2 = Get-Date
        cat "$out.err"
        if(-not (findstr /c:"verified, 0 errors" "$out.err")) {throw "error building $out"}
        if(     (findstr /c:"inconclusive" "$out.err")) {throw "error building $out"}
        if(     (findstr /c:"time out" "$out.err")) {throw "error building $out"}
        mv -force "$out.err" $out
        "Time: $($time2 - $time1)"
        ""
    }
}

function __boogie_exe($out, $flags, $arr)
{
    $time1 = Get-Date
    "$ROOT\tools\Dafny\boogie.exe    /noinfer /typeEncoding:m /z3opt:ARITH_RANDOM_SEED=1 $flags  $out.bpl"
    & "$ROOT\tools\Dafny\boogie.exe" /noinfer /typeEncoding:m /z3opt:ARITH_RANDOM_SEED=1 $flags "$out.bpl" | out-file -encoding ascii "$out.err"
    $time2 = Get-Date
    cat "$out.err"
    if(-not (findstr /c:"verified, 0 errors" "$out.err")) {throw "error building $out"}
    if(     (findstr /c:"inconclusive" "$out.err")) {throw "error building $out"}
    if(     (findstr /c:"time out" "$out.err")) {throw "error building $out"}
    mv -force "$out.err" $out
    "Time: $(($time2 - $time1).TotalSeconds) $out"
    ""
}

function __boogie_sd_optional($out, $sdiff, $arr)
{
    $arr = flatten $arr
    $boogieasm = "$BINTOOLS\boogieasm\boogieasm.exe"
    $ins = @($arr | ?{-not $_.StartsWith("/")}) + @($boogieasm)
    $outname = $out


    # Assume the file to be verified is the last in line
    $src = $arr[-1]
    $src_i = $src.replace(".bpl", "_i.bpl")  # Create the potential interface file name 

    # Check whether the Boogie files use relational logic
    $rel_i = $false
    $pub_i = $false
    if (Test-Path ($src_i)) {  # If this is the module implementation, check the interface too
      $rel_i = (Select-String -CaseSensitive "[^a-zA-Z0-9_]relation\(.*\)" $src_i).Count -gt 0
      $pub_i = (Select-String -CaseSensitive "[^a-zA-Z0-9_]public\(.*\)"   $src_i).Count -gt 0
    }
    $rel   = (Select-String -CaseSensitive "[^a-zA-Z0-9_]relation\(.*\)" $src).Count   -gt 0 
    $pub   = (Select-String -CaseSensitive "[^a-zA-Z0-9_]public\(.*\)"   $src).Count   -gt 0 

    if ($src.EndsWith("EntryCP.bpl")) { # Special-case entry, since its interface lives in spec land
      $rel_i = $true
    }

    # Apply SymDiff if we find relation or public in the implementation or the interface
    $deduced_symdiff = $rel -or $pub -or $rel_i -or $pub_i

    #echo "For $src, sdiff is $sdiff and I deduced $deduced_symdiff" | out-file -append -encoding ascii sdiff.txt
    $sdiff = $deduced_symdiff

    if ($sdiff -and $SYMDIFF_ENABLED)
    {
        $outname = "$out.merged"
    }
    if (((needToBuild $outname $ins) -and $BOOGIE_ENABLED) -or ((-not $BOOGIE_ENABLED) -and (needToBuild "$outname.assume" $ins)))
    {
        ensureDirForFile($out)
        "boogie $arr"
        $bpls = $arr | ?{$_.EndsWith(".bpl")}
        $ba_flagnames = @("")
        $ba_flags = $arr | ?{$ba_flagnames -contains $_} | %{$_.Replace("/", "-")}
        $flags = $arr | ?{-not $_.EndsWith(".bpl")} | ?{-not ($ba_flagnames -contains $_)}
        $fulltime1 = Get-Date
        if ($sdiff)
        {
            run $boogieasm $BUILD_DEFS $boogieasm_x64_flag $ba_flags "-verify" "-symdiffok" "-out" "$out.bpl" $bpls
            run $boogieasm $BUILD_DEFS $boogieasm_x64_flag $ba_flags "-verify" "-symdiffms" "$out.ms.bpl" "-out" "$out.symdiff.bpl" $bpls
        }
        else
        {
            run $boogieasm $BUILD_DEFS $boogieasm_x64_flag $ba_flags "-verify" "-out" "$out.bpl" $bpls
        }
        $fulltime2 = Get-Date
        if ($BOOGIE_ENABLED) {
          __boogie_exe $out $flags $arr
        } else {
          echo $null > "$out.assume"
        }
        $fulltime3 = Get-Date
        if ($sdiff -and $SYMDIFF_ENABLED)
        {
            $save_dir = pwd
            try
            {
                $outfile = [System.IO.Path]::GetFileName($out)
                cd $([System.IO.Path]::GetDirectoryName($out))
                cp $($outfile + ".symdiff.bpl") v1.bpl
                cp $($outfile + ".symdiff.bpl") v2.bpl
                echo "" | out-file -encoding ascii ms_symdiff_file.bpl
                echo "LOOPS"
                run "$SYMDIFF\symdiff.exe" -extractLoops v1.bpl v1_u.bpl
                run "$SYMDIFF\symdiff.exe" -extractLoops v2.bpl v2_u.bpl
                echo "INFER"
                run "$SYMDIFF\symdiff.exe" -inferConfig v1_u.bpl v2_u.bpl | out-file -encoding ascii v1_uv2_u.config
                echo "CONFIGURE"
                run $BINTOOLS\boogieasm\symdiffmerge.exe -config "$outfile.ms.bpl" v1_uv2_u.config | out-file -encoding ascii "$outfile.config"
                echo "RUN SYMDIFF"
                run "$SYMDIFF\symdiff.exe" -allInOne  v1_u.bpl v2_u.bpl "$outfile.config" -asserts -freeContracts -usemutual -sound -dontUseHoudiniForMS -checkMutualPrecondNonTerminating
                echo "MERGE"
                run $BINTOOLS\boogieasm\symdiffmerge.exe -merge "$outfile.ms.bpl" mergedProgSingle.bpl | out-file -encoding ascii "$outfile.merged.bpl"
                cd $save_dir
                echo "RUN BOOGIE"
                __boogie_exe $outname $flags $arr
            }
            finally
            {
                cd $save_dir
            }
        }
        $fulltime4 = Get-Date
        $t = $(($fulltime2 - $fulltime1).TotalSeconds); $t | out-file -encoding ascii "$out.____$($t)____.time_bgasm"
        $t = $(($fulltime3 - $fulltime2).TotalSeconds); $t | out-file -encoding ascii "$out.____$($t)____.time_boogie"
        $t = $(($fulltime4 - $fulltime3).TotalSeconds); $t | out-file -encoding ascii "$out.____$($t)____.time_symdiff"
    }
}

function _boogie_sd_optional([Parameter(Mandatory=$true)]$out, [Parameter(Mandatory=$true)]$relational, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    __boogie_sd_optional $out $relational $arr
}

function _boogie([Parameter(Mandatory=$true)]$out, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    __boogie_sd_optional $out $false $arr
}

function _boogie_symdiff([Parameter(Mandatory=$true)]$out, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    __boogie_sd_optional $out $true $arr
}

function _copy([Parameter(Mandatory=$true)]$out, [Parameter(Mandatory=$true)]$in)
{
    $ins = list $in
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out);
        "copy -out $out -in $in"
        cat $in | out-file -encoding ascii $out
    }
}

function _copy_if_different([Parameter(Mandatory=$true)]$out, [Parameter(Mandatory=$true)]$in)
{
    if (-not $DAFNYCC_INCREMENTAL_BUILD)
    {
        cp $in $out
    }
    elseif (-not (test-path $out))
    {
        cp $in $out
    }
    else
    {
        $bytes_out = [System.IO.File]::ReadAllBytes((ls $out).FullName)
        $bytes_in = [System.IO.File]::ReadAllBytes((ls $in).FullName)
        if (-not ([System.Collections.StructuralComparisons]::StructuralEqualityComparer.Equals($bytes_out, $bytes_in)))
        {
            cp $in $out
        }
    }
}

function _cat([Parameter(Mandatory=$true)]$out, [Parameter(Mandatory=$true)][string[]]$in)
{
    $ins = $in
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out);
        "cat -out $out -in $in"
        cat $in | out-file -encoding ascii $out
    }
}

function _beat([Parameter(Mandatory=$true)]$out, [Parameter(Mandatory=$true)]$in, [string[]]$includes)
{
    if ($includes -eq $null) { $includes = @() }
    $beat = "$BINTOOLS\beat\beat.exe"
    $ins = flatten (list $in $beat $includes)
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out)
        $incls = @($includes | %{"-i"; $_})
        "beat $BUILD_DEFS -out $out.tmp -in $in $incls"
        # & $beat -printAndExit $BUILD_DEFS -in $in $incls | out-file -encoding ascii "$out.ppall"
        # if($LastExitCode) { cat "$out.ppall"; throw "error building $out" }
        # & $beat -printNonghostAndExit $BUILD_DEFS -in $in $incls | out-file -encoding ascii "$out.ppwog"
        # if($LastExitCode) { cat "$out.ppwog"; throw "error building $out" }
        & $beat $BUILD_DEFS -in $in $incls | out-file -encoding ascii "$out.tmp"
        if($LastExitCode)
        {
            cat "$out.tmp"
            throw "error building $out"
        }
        mv -force "$out.tmp" $out
        ""
    }
}

function _dafnyspec([Parameter(Mandatory=$true)]$outdir, [Parameter(Mandatory=$true)]$outlist, [Parameter(Mandatory=$true)]$deps, [Parameter(Mandatory=$true)]$in)
{
    $dafnyspec = "$BINTOOLS\dafnyspec\dafnyspec.exe"
    $ins = flatten ((list $in $dafnyspec) + @($deps))
    if (needToBuild $outlist $ins)
    {
        ensureDirForFile("$outdir\dummy")
        "dafnyspec $in /outdir:$outdir /outlist:$outlist"
        & $dafnyspec $in /outdir:$outdir /outlist:$outlist
        if($LastExitCode)
        {
            throw "error building $out"
        }
        ""
    }
}

function _dafnycc([Parameter(Mandatory=$true)]$outdir, [Parameter(Mandatory=$true)]$outlist, [Parameter(Mandatory=$true)]$heap, [Parameter(Mandatory=$true)]$heapi, [Parameter(Mandatory=$true)]$deps, [Parameter(Mandatory=$true)]$in)
{
    $dafnycc = "$BINTOOLS\dafnycc\dafnycc.exe"
    $ins = flatten ((list $in $dafnycc) + @($deps))
    if ($build_args.Contains("x64"))
    {
        $x64_flag = "/x64"
    }
    if (needToBuild $heap $ins)
    {
        ensureDirForFile($heap)
        ensureDirForFile($heapi)
        ensureDirForFile("$outdir\dummy")
        "dafnycc $in /useFramePointer /heapfile:$heap /heapifile:$heapi /outdir:$outdir /relational /outlist:$outlist $x64_flag"
        & $dafnycc $in /useFramePointer /heapfile:$heap /heapifile:$heapi /outdir:$outdir /relational /outlist:$outlist $x64_flag
        if($LastExitCode)
        {
            throw "error building $out"
        }
        ""
    }
}

function _boogieasm([Parameter(Mandatory=$true)]$out, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    $boogieasm = "$BINTOOLS\boogieasm\boogieasm.exe"
    $arr = flatten $arr
    $ins = @($arr | %{"$_.bpl"}) + @($arr | %{"$($_)_i.bpl"}) + @($boogieasm)
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out)
        "$boogieasm $BUILD_DEFS $boogieasm_x64_flag -link $arr | out-file -encoding ascii $out.tmp "
        & $boogieasm $BUILD_DEFS $boogieasm_x64_flag -link $arr | out-file -encoding ascii "$out.tmp"
        if($LastExitCode)
        {
            #cat "$out.tmp" | out-file -encoding ascii "$OBJROOT\$out.tmp"
            throw "error building $out.  Check the end of $out.tmp for more details."
        }
        mv -force "$out.tmp" $out
        ""
    }
}

function _cdimage([Parameter(Mandatory=$true)]$inDir, [Parameter(Mandatory=$true)]$bootSector, [Parameter(Mandatory=$true)]$out, [Parameter(ValueFromRemainingArguments=$true)]$arr)
{
    $arr = flatten $arr
    $ins = @(ls -r $inDir | %{$_.FullName}) + @($bootsector)
    if (needToBuild $out $ins)
    {
        ensureDirForFile($out)
        "cdimage $arr -b$bootSector $inDir $out"
        run $BUILD\cdimage.exe $arr "-b$bootSector" $inDir $out
        ""
    }
}
