include "power2.i.dfy"

method MakePower2(e:nat) returns (x:nat)
    requires e < 32;
    ensures x==power2(e);
{
    lemma_2toX32();
    if (e<16) {
      if (e<8) {
        if (e<4) {
          if (e<2) {
            if (e<1) {
              x := 1;
            } else {
              x := 2;
            }
          } else {
            if (e<3) {
              x := 4;
            } else {
              x := 8;
            }
          }
        } else {
          if (e<6) {
            if (e<5) {
              x := 16;
            } else {
              x := 32;
            }
          } else {
            if (e<7) {
              x := 64;
            } else {
              x := 128;
            }
          }
        }
      } else {
        if (e<12) {
          if (e<10) {
            if (e<9) {
              x := 256;
            } else {
              x := 512;
            }
          } else {
            if (e<11) {
              x := 1024;
            } else {
              x := 2048;
            }
          }
        } else {
          if (e<14) {
            if (e<13) {
              x := 4096;
            } else {
              x := 8192;
            }
          } else {
            if (e<15) {
              x := 16384;
            } else {
              x := 32768;
            }
          }
        }
      }
    } else {
      if (e<24) {
        if (e<20) {
          if (e<18) {
            if (e<17) {
              x := 65536;
            } else {
              x := 131072;
            }
          } else {
            if (e<19) {
              x := 262144;
            } else {
              x := 524288;
            }
          }
        } else {
          if (e<22) {
            if (e<21) {
              x := 1048576;
            } else {
              x := 2097152;
            }
          } else {
            if (e<23) {
              x := 4194304;
            } else {
              x := 8388608;
            }
          }
        }
      } else {
        if (e<28) {
          if (e<26) {
            if (e<25) {
              x := 16777216;
            } else {
              x := 33554432;
            }
          } else {
            if (e<27) {
              x := 67108864;
            } else {
              x := 134217728;
            }
          }
        } else {
          if (e<30) {
            if (e<29) {
              x := 268435456;
            } else {
              x := 536870912;
            }
          } else {
            if (e<31) {
              x := 1073741824;
            } else {
              x := 2147483648;
            }
          }
        }
      }
    }
}
method CountBits(x:nat) returns (e:nat)
    requires x<power2(32);
    ensures x>0 ==> 0<e && power2(e-1) <= x;
    ensures x < power2(e);
{
    lemma_2toX32();
    if (x==0) { e:=0; return; }
    if (x<65536) {
      if (x<256) {
        if (x<16) {
          if (x<4) {
            if (x<2) {
              e := 1;
            } else {
              e := 2;
            }
          } else {
            if (x<8) {
              e := 3;
            } else {
              e := 4;
            }
          }
        } else {
          if (x<64) {
            if (x<32) {
              e := 5;
            } else {
              e := 6;
            }
          } else {
            if (x<128) {
              e := 7;
            } else {
              e := 8;
            }
          }
        }
      } else {
        if (x<4096) {
          if (x<1024) {
            if (x<512) {
              e := 9;
            } else {
              e := 10;
            }
          } else {
            if (x<2048) {
              e := 11;
            } else {
              e := 12;
            }
          }
        } else {
          if (x<16384) {
            if (x<8192) {
              e := 13;
            } else {
              e := 14;
            }
          } else {
            if (x<32768) {
              e := 15;
            } else {
              e := 16;
            }
          }
        }
      }
    } else {
      if (x<16777216) {
        if (x<1048576) {
          if (x<262144) {
            if (x<131072) {
              e := 17;
            } else {
              e := 18;
            }
          } else {
            if (x<524288) {
              e := 19;
            } else {
              e := 20;
            }
          }
        } else {
          if (x<4194304) {
            if (x<2097152) {
              e := 21;
            } else {
              e := 22;
            }
          } else {
            if (x<8388608) {
              e := 23;
            } else {
              e := 24;
            }
          }
        }
      } else {
        if (x<268435456) {
          if (x<67108864) {
            if (x<33554432) {
              e := 25;
            } else {
              e := 26;
            }
          } else {
            if (x<134217728) {
              e := 27;
            } else {
              e := 28;
            }
          }
        } else {
          if (x<1073741824) {
            if (x<536870912) {
              e := 29;
            } else {
              e := 30;
            }
          } else {
            if (x<2147483648) {
              e := 31;
            } else {
              e := 32;
            }
          }
        }
      }
    }
}
