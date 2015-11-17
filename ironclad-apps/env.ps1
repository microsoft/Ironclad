if ($env:SAFEOS_ROOT -eq $null)
{
    $env:SAFEOS_ROOT = $PWD
    $env:PATH = $env:PATH + ";$env:SAFEOS_ROOT\tools\build"
}
