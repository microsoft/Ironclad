include "../../Drivers/TPM/tpm-wrapper.i.dfy"
include "../../Drivers/IO/pci.i.dfy"
include "../../Libraries/Util/repeat_digit.i.dfy"


method test_get_pcr()
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures TPM_satisfies_integrity_policy(TPM);
{
    var success, pcr17 := get_pcr(17);
    if !success {
        debug_print(0x30, 0xB000);
    }
    else {
        debug_print(0x30, 0x3333);
        debug_print(0x31, pcr17[0]);
        debug_print(0x32, pcr17[1]);
        debug_print(0x33, pcr17[2]);
        debug_print(0x34, pcr17[3]);
        debug_print(0x35, pcr17[4]);
    }

    var success2, pcr18 := get_pcr(18);
    if !success2 {
        debug_print(0x40, 0xB000);
    }
    else {
        debug_print(0x40, 0x4444);
        debug_print(0x41, pcr18[0]);
        debug_print(0x42, pcr18[1]);
        debug_print(0x43, pcr18[2]);
        debug_print(0x44, pcr18[3]);
        debug_print(0x45, pcr18[4]);
    }
}

method test_random()
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures TPM_satisfies_integrity_policy(TPM);
{
    lemma_2toX();
    var rand_bytes := get_random(100);
    debug_print(0x50, rand_bytes[0]);
    debug_print(0x51, rand_bytes[1]);
    debug_print(0x52, rand_bytes[2]);
    debug_print(0x53, rand_bytes[3]);
    debug_print(0x54, rand_bytes[4]);

    rand_bytes := get_random(100);
    debug_print(0x60, rand_bytes[0]);
    debug_print(0x61, rand_bytes[1]);
    debug_print(0x62, rand_bytes[2]);
    debug_print(0x63, rand_bytes[3]);
    debug_print(0x64, rand_bytes[4]);
}

method test_quote()
    requires Locality3_obtained();
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
    ensures TPM_valid(TPM);
    ensures IoMemPerm.Null?;
    ensures TPM_satisfies_integrity_policy(TPM);
{
    var success:bool;
    var pcr_info_bytes:seq<int>;
    var sig_bytes:seq<int>;
    var nonce_external := RepeatDigit_impl(0, 20);
    success, pcr_info_bytes, sig_bytes := quote(nonce_external);

    if !success {
        debug_print(0x80, 0xB00B00);
    }
    else {
        debug_print(0x80, 0x4444);
        debug_print(0x81, |pcr_info_bytes|);
        debug_print(0x82, |sig_bytes|);
        if |sig_bytes| >= 2 {
            debug_print(0x83, sig_bytes[0]);
            debug_print(0x84, sig_bytes[1]);
        }
    }
}

method Main () returns (result:int)
    requires TPM_valid(TPM);
    requires IoMemPerm.Null?;
    requires TPM_satisfies_integrity_policy(TPM);
    modifies this`TPM;
    modifies this`IoMemPerm;
{
    debug_print(0x10, 0x1111);

    establish_locality();

    debug_print(0x20, 0x2222);

    test_get_pcr();
    test_random();
    test_quote();

    return 0;
}
