include "sha256.i.dfy"
include "sha1.i.dfy"

static method PrintHash(hash:seq<int>)
{
    var i := 0;
    while (i < |hash|)
        invariant 0 <= i <= |hash|;
    {
        print hash[i];
        i := i + 1;
    }
}

//- FIPS says:
//- SHA1("abc") = A9993E36 4706816A BA3E2571 7850C26C 9CD0D89D
//- http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA1.pdf
//- SHA256("abc") = BA7816BF 8F01CFEA 414140DE 5DAE2223 B00361A3 96177A9C B410FF61 F20015AD
//- http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA256.pdf
method Test1()
{
    var data := [0x61, 0x62, 0x63];

    lemma_2toX();

    var hash_sha1 := SHA1_impl_Bytes(data);
    PrintHash(hash_sha1);
    var hash_sha256 := SHA256_impl_Bytes(data);
    PrintHash(hash_sha256);
}

//- FIPS says:
//- SHA1("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
//- 84983E44 1C3BD26E BAAE4AA1 F95129E5 E54670F1
//- http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA1.pdf
//- SHA256("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
//- 248D6A61 D20638B8 E5C02693 0C3E6039 A33CE459 64FF2167 F6ECEDD4 19DB06C1
//- http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA256.pdf
method Test2()
{
    var data := [
        0x61, 0x62, 0x63, 0x64,
        0x62, 0x63, 0x64, 0x65,
        0x63, 0x64, 0x65, 0x66,
        0x64, 0x65, 0x66, 0x67,
        0x65, 0x66, 0x67, 0x68,
        0x66, 0x67, 0x68, 0x69,
        0x67, 0x68, 0x69, 0x6A,
        0x68, 0x69, 0x6A, 0x6B,
        0x69, 0x6A, 0x6B, 0x6C,
        0x6A, 0x6B, 0x6C, 0x6D,
        0x6B, 0x6C, 0x6D, 0x6E,
        0x6C, 0x6D, 0x6E, 0x6F,
        0x6D, 0x6E, 0x6F, 0x70,
        0x6E, 0x6F, 0x70, 0x71
    ];

    lemma_2toX();

    var hash_sha1 := SHA1_impl_Bytes(data);
    PrintHash(hash_sha1);
    var hash_sha256 := SHA256_impl_Bytes(data);
    PrintHash(hash_sha256);
}

method Main() {
    Test1();
    Test2();
}
