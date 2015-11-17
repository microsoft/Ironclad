//-<NuBuild BasmEnableSymdiff true />
include "../../Libraries/Util/relational.s.dfy"
include "../../Libraries/Util/bytes_and_words.s.dfy"

function {:opaque} mod4(n:int):int { n % 4 }
function {:opaque} mod16(n:int):int { n % 16 }
function {:opaque} mod128(n:int):int { n % 128 }
function {:opaque} div16(n:int):int { n / 16 }

/**************************************************
 * Spec for interacting with the network card
 **************************************************/

//-function intel_NIC_device_vendor_id() : int { 0x107c8086 }

//- Track whether we've initialized the network card
//- TODO: dafnycc support for: var net_init:bool;

function IsValidPciId(id:int):bool
function PciMemAddr(id:int):int     //- Region where the device's PCI config registers are mapped into memory
function PciMemSize(id:int):int
function DeviceMemAddr() : int      //- Region where devices are allowed to read/write
function DeviceMemSize() : int

/****************************************
   Connections to Verve's PCI interface
 ****************************************/
method {:decl} NetworkPciMemSetup() returns (id:int, size:int, addr:int, device_mem_addr:int)
    ensures Word32(size) && Word32(addr) && Word32(device_mem_addr);
    ensures IsValidPciId(id);
    ensures size == PciMemSize(id);
    ensures addr == PciMemAddr(id);
    ensures Word32(addr + size);
    ensures Word32(DeviceMemAddr() + DeviceMemSize());
    ensures DeviceMemAddr() == device_mem_addr;
    ensures mod16(device_mem_addr) == 0;
    ensures DeviceMemSize() > 0x204004;
    ensures public(id);
    ensures public(size);
    ensures public(addr);
    ensures public(device_mem_addr);

method {:decl} PciMemStore(id:int, dst:int, val:int)
    requires IsValidPciId(id);
    requires PciMemAddr(id) <= dst && dst + 4 <= PciMemAddr(id) + PciMemSize(id);
    requires Word32(val);
    requires public(id);
    requires public(dst);
    requires public(val);

method {:decl} PciMemLoad(id:int, src:int) returns (val:int)
    requires IsValidPciId(id);
    requires PciMemAddr(id) <= src && src + 4 <= PciMemAddr(id) + PciMemSize(id);
    ensures Word32(val);
    requires public(id);
    requires public(src);
    ensures  public(val);

method {:decl} {:instruction "mem", "in"} {:modifies_io} DeviceMemStore(dst:int, val:int)
    requires DeviceMemAddr() <= dst && dst + 4 <= DeviceMemAddr() + DeviceMemSize();
    requires Word32(dst);
    requires Word32(val);
    requires public(dst);
    requires public(val);

method {:decl} {:instruction "mem", "out"} {:modifies_io} DeviceMemLoad(src:int) returns (val:int)
    requires DeviceMemAddr() <= src && src + 4 <= DeviceMemAddr() + DeviceMemSize();
    requires Word32(src);
    requires public(src);
    ensures  Word32(val);
    ensures  public(val);

static method {:decl} debug_print(loc:int, val:int)
    requires 0 <= loc <= 160 - 16;
