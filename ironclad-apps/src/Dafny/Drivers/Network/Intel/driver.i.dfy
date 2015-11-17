//-<NuBuild BasmEnableSymdiff true />
include "../../../Libraries/base.s.dfy"
include "../../../Libraries/Util/relational.s.dfy"
include "../../CPU/assembly_premium.i.dfy"
include "../../../Libraries/Math/bit_vector_lemmas_premium.i.dfy"
include "../../../Libraries/Util/repeat_digit.i.dfy"
include "../../../Libraries/Util/integer_sequences.i.dfy"
include "../../../Libraries/Math/div.i.dfy"
include "../../../Libraries/Util/word_bits.i.dfy"
include "../../IO/pci.i.dfy"

//-
//- Driver for Intel Network Card 82541PI.
//- Sofware Developer's Manual labelled 317453006EN.PDF, Revision 4.0.
//-
//- Implementation Notes:
//-
//- - We don't support VLAN mode.
//- - We don't prefetch or write-back transmit descriptors.
//- - We leave the transmit absolute delay function (see 13.4.44) disabled.
//- - We don't support large segment offload.
//- - We use the "legacy" format of transmit/receive descriptors.
//-

//-
//- Register addresses relative to the card's base address.
//- See Table 13-2 on pages 219-222.
//-
//- Note: all registers should be accessed as 32-bit words.
//-

//- General Registers:
function method{:dafnycc_inline} register_ctrl(addr:int):int                { addr + 0x0000 }
function method{:dafnycc_inline} register_status(addr:int):int              { addr + 0x0008 }
function method{:dafnycc_inline} register_ctrl_ext(addr:int):int            { addr + 0x0018 }
function method{:dafnycc_inline} register_fcal(addr:int):int                { addr + 0x0028 }
function method{:dafnycc_inline} register_fcah(addr:int):int                { addr + 0x002c }
function method{:dafnycc_inline} register_fct(addr:int):int                 { addr + 0x0030 }
function method{:dafnycc_inline} register_fcttv(addr:int):int               { addr + 0x0170 }

//- Receive Registers:
function method{:dafnycc_inline} register_rx_ctrl(addr:int):int             { addr + 0x0100 }
function method{:dafnycc_inline} register_rx_desc_base_lo(addr:int):int     { addr + 0x2800 }
function method{:dafnycc_inline} register_rx_desc_base_hi(addr:int):int     { addr + 0x2804 }
function method{:dafnycc_inline} register_rx_desc_length(addr:int):int      { addr + 0x2808 }
function method{:dafnycc_inline} register_rx_desc_head(addr:int):int        { addr + 0x2810 }
function method{:dafnycc_inline} register_rx_desc_tail(addr:int):int        { addr + 0x2818 }
function method{:dafnycc_inline} register_rx_delay_timer(addr:int):int      { addr + 0x2820 }
function method{:dafnycc_inline} register_rx_int_abs_timer(addr:int):int    { addr + 0x282c }
function method{:dafnycc_inline} register_rx_cksum_ctrl(addr:int):int       { addr + 0x5000 }
function method{:dafnycc_inline} register_rx_mcast_table(addr:int):int      { addr + 0x5200 }
function method{:dafnycc_inline} register_rx_addrN_lo(addr:int):int         { addr + 0x5400 }
function method{:dafnycc_inline} register_rx_addrN_hi(addr:int):int         { addr + 0x5404 }

//- Transmit Registers:
function method{:dafnycc_inline} register_tx_ctrl(addr:int):int             { addr + 0x0400 }
function method{:dafnycc_inline} register_tx_ipg(addr:int):int              { addr + 0x0410 }
function method{:dafnycc_inline} register_tx_desc_base_lo(addr:int):int     { addr + 0x3800 }
function method{:dafnycc_inline} register_tx_desc_base_hi(addr:int):int     { addr + 0x3804 }
function method{:dafnycc_inline} register_tx_desc_length(addr:int):int      { addr + 0x3808 }
function method{:dafnycc_inline} register_tx_desc_head(addr:int):int        { addr + 0x3810 }
function method{:dafnycc_inline} register_tx_desc_tail(addr:int):int        { addr + 0x3818 }

//-
//- Register-related Constants:

//-

//- Device Control Register (register_ctrl).  See Section 13.4.1.
//- Device Reset Bit:
function method{:dafnycc_inline} ctrl_reset():int { 0x04000000 } //- i.e. Bit 26.
//- PHY Reset Bit:
function method{:dafnycc_inline} ctrl_phy_reset():int { 0x80000000 } //- i.e. Bit 31.

//- Receive Control Register (register_rx_ctrl).  See Section 13.4.22.
//- Receiver Enable Bit:
function method{:dafnycc_inline} ctrl_rx_enable():int { 2 } //- i.e. Bit 1.


//- Transmit Control Register (register_tx_ctrl).  See Section 13.4.33.
//- Transmit Enable Bit:
function method{:dafnycc_inline} ctrl_tx_enable():int { 2 } //- i.e. Bit 1.
//- Pad Short Packets Bit:
function method{:dafnycc_inline} tx_pad_short_packets():int { 8 } //- i.e. Bit 3.

//- Transmit Inter-Packet Gap Register (register_tx_ipg).  See Section 13.4.34.
//- Default Value:
function method{:dafnycc_inline} tx_ipg_default():int { 10 }

//- Receive Delay Timer (register_rx_delay_timer).  See Section 13.4.30.

//- Default Value:
function method{:dafnycc_inline} rxdelaytimers_rx_delay_timer():int { 100 }  //- ~100us.

//- Receive Interrupt Absolute Delay Timer(register_rx_int_abs_timer).  See Section 13.4.31.
//- Default Value:

function method{:dafnycc_inline} rxdelaytimers_rx_absolute_timer():int { 1000 } //- ~1000us.

//-
//- Ring Buffer Configuration Values.
//-
function method{:dafnycc_inline} bytes_per_descriptor():int { 16 }
function method{:dafnycc_inline} num_descriptors():int { 512 }
//-function method{:dafnycc_inline} total_desc_bytes():int { num_descriptors() * bytes_per_descriptor() }
function method{:dafnycc_inline} total_desc_bytes():int { 512 * bytes_per_descriptor() }
function method{:dafnycc_inline} bytes_per_buffer():int { 2 * 1024 }
//-function method{:dafnycc_inline} total_buffer_bytes():int { num_descriptors() * bytes_per_buffer() }
function method{:dafnycc_inline} total_buffer_bytes():int { 512 * bytes_per_buffer() }

//-
//- Hard code the MAC address to 90:e2:ba:4f:0c:5b.
//- Hard code the MAC address to 00:1b:21:31:8e:d9.


//-
function method my_ethernet_addr() : ethernet_addr
{
    ethernet_addr_builder( [ 0x90, 0xe2, 0xba, 0x4f, 0x0c, 0x5b] )  
//-    ethernet_addr_builder( [ 0x00, 0x1b, 0x21, 0x31, 0x8e, 0xd9] )
                                                                      
}

//-
//- Define what an "ethernet_addr" is.
//-
datatype ethernet_addr = ethernet_addr_builder(bytes:seq<int>);
function valid_ethernet_addr(addr:ethernet_addr) : bool
{
    IsByteSeqOfLen(addr.bytes, 6)
}

/****************************************
      Ring buffers used for tx/rx
 ****************************************/
datatype network_state = network_state_build(rx_rb:rx_ring_buffer, tx_rb:tx_ring_buffer);
datatype rx_ring_buffer = rx_ring_buffer_build(rb:ring_buffer);
datatype tx_ring_buffer = tx_ring_buffer_build(rb:ring_buffer);
datatype ring_buffer = ring_buffer_build(base:int, size:int, head:int, tail:int, id:int, reg_addr:int);

function valid_ring_buffer(rb:ring_buffer):bool
    requires num_descriptors() == 512;
{
    mod16(rb.base) == 0 && rb.base >= 0 &&
    Word32(rb.base + total_desc_bytes() + total_buffer_bytes()) && //- Include space for descriptors and the buffers they point at
    DeviceMemAddr() <= rb.base && rb.base + total_desc_bytes() + total_buffer_bytes() + 4 <= DeviceMemAddr() + DeviceMemSize() &&
    DeviceMemSize() >= 0x204000 &&
    mod128(rb.size) == 0 && 128 <= rb.size < power2(19) &&
    div16(rb.size) == 512 &&
    Word32(rb.base + rb.size) &&
    0 <= rb.head < power2(16) && rb.base + 16 * rb.head <= rb.base + rb.size - 16 && //- Assuming head and tail are measured in descriptors (16B each)
    0 <= rb.tail < power2(16) && rb.base + 16 * rb.tail <= rb.base + rb.size - 16 && //- Assuming head and tail are measured in descriptors (16B each)
    rb.reg_addr == PciMemAddr(rb.id) && rb.reg_addr >= 0 && Word32(rb.reg_addr + 128 * 1024) &&
    IsValidPciId(rb.id) && PciMemSize(rb.id) >= 128 * 1024 
}

function valid_network_state(state:network_state):bool
{
    valid_ring_buffer(state.rx_rb.rb) && valid_ring_buffer(state.tx_rb.rb) 
}


/*
 * Device Memory layout plan:
 * Verve gives us, via NetworkPciMemSetup, an address in device memory.
 * That memory is untrusted, but accessible to devices.  We will lay it out as follows:
 *  +1M
 *              Rx Buffers x 512 (2K each)
 *  +8K
 *              Rx Ring Descriptors x 512 (16B each)
 *  +1M
 *              Tx Buffers x 512 (2K each)
 *  +8K
 *              Tx Ring Descriptors x 512 (16B each)
 *  dev_addr->
 *
 * Thus, we need 2M + 16K bytes = 0x204000.
 */


//-lemma init_network_card_lemma1(addr:int)
//-    //-requires mod4(addr) == 0;
//-    //-ensures mod4(register_fcal(addr)) == 0;
//-    //-ensures mod4(register_fcah(addr)) == 0;
//-    //-ensures mod4(register_fct(addr)) == 0;
//-    //-ensures mod4(register_fcttv(addr)) == 0;
//-    //-ensures mod4(register_rx_addrN_lo(addr)) == 0;
//-    //-ensures mod4(register_rx_addrN_hi(addr)) == 0;
//-    //-ensures mod4(register_rx_desc_base_lo(addr)) == 0;
//-    //-ensures mod4(register_rx_desc_base_hi(addr)) == 0;
//-    //-ensures mod4(register_rx_desc_length(addr)) == 0;
//-    //-ensures mod4(register_rx_desc_head(addr)) == 0;
//-    //-ensures mod4(register_rx_desc_tail(addr)) == 0;
//-    //-ensures mod4(register_rx_ctrl(addr)) == 0;
//-    //-ensures mod4(register_rx_delay_timer(addr)) == 0;
//-    //-ensures mod4(register_rx_int_abs_timer(addr)) == 0;
//-    //-ensures mod4(register_rx_cksum_ctrl(addr)) == 0;
//-    //-ensures mod4(register_tx_desc_base_lo(addr)) == 0;
//-    //-ensures mod4(register_tx_desc_base_hi(addr)) == 0;
//-    //-ensures mod4(register_tx_desc_length(addr)) == 0;
//-    //-ensures mod4(register_tx_desc_head(addr)) == 0;
//-    //-ensures mod4(register_tx_desc_tail(addr)) == 0;
//-    //-ensures mod4(register_tx_ctrl(addr)) == 0;
//-    //-ensures mod4(register_tx_ipg(addr)) == 0;
//-{
//-    reveal_mod4();
//-    reveal_mod16();
//-    reveal_mod128();
//-    reveal_div16();
//-}

lemma init_network_card_lemma2a(dev_addr:int)
    requires mod16(dev_addr) == 0;
    requires Word32(dev_addr); //- HACK to avoid timeout
    ensures mod4(dev_addr) == 0;
{
    reveal_mod4();
    reveal_mod16();
}

lemma init_network_card_lemma2b(dev_addr:int)
    requires mod4(dev_addr) == 0;
    ensures mod4(dev_addr + 512 * 16 + 512 * 2 * 1024) == 0;
{
    reveal_mod4();
}

lemma init_network_card_lemma2c(dev_addr:int)
    requires mod16(dev_addr) == 0;
    ensures mod16(dev_addr + 512 * 16 + 512 * 2 * 1024) == 0;
{
    reveal_mod16();
}

lemma init_network_card_lemma3()
    ensures mod128(total_desc_bytes()) == 0;
    ensures div16(total_desc_bytes()) == 512;
{
    reveal_mod4();
    reveal_mod16();
    reveal_mod128();
    reveal_div16();
}

//-lemma init_network_card_lemma4(addr:int, mta_register:int)
//-    //-requires mod4(addr) == 0;
//-    //-ensures mod4(register_rx_mcast_table(addr) + mta_register * 4) == 0;
//-{
//-    reveal_mod4();
//-    reveal_mod16();
//-    reveal_mod128();
//-    reveal_div16();
//-}

//-
//- Debug print a register value.
//-
//-method debug_print_register(loc:int, id:int, reg:int)
//-    requires IsValidPciId(id);
//-    requires PciMemAddr(id) <= reg && reg + 4 <= PciMemAddr(id) + PciMemSize(id);
//-    requires 0 <= loc <= 160 - 16;
//-    requires public(id);
//-    requires public(reg);
//-{
//-    var reg_dbg := PciMemLoad(id, reg);
//-    debug_print(loc, reg_dbg);
//-}

//-
//- Busy-wait something in the neighborhood of the requested amount of time.
//-
method delay(microseconds:int)
    requires 0 <= microseconds < 0xEFFFFFFF;
{
    var ms := microseconds;
    while (ms > 0) 
        decreases ms;
    {
        var count := 3 * 1000;  //- 3K ops on a 3 GHz machine should be ~1 us.
        while (count > 0)
            decreases count;
        {
            count := count - 1;
        }
        ms := ms - 1;
    }
}


//-
//- Card Initialization Routines.
//-
method init_network_card() returns (success:bool, state:network_state)
    ensures success ==> valid_network_state(state);
    ensures public(success);
    ensures public(state);
{
    var id, size, addr, dev_addr := NetworkPciMemSetup();

//-    debug_print(0x00, 0xbeefcafe);
//-    debug_print(0x00, addr);
//-    debug_print(0x12, size);
//-    debug_print(0x24, dev_addr);

    var rx_ring_buff:rx_ring_buffer;
    var tx_ring_buff:tx_ring_buffer;

    if (size < 128 * 1024) {
        //-
        //- We expect the Intel NIC to get 128K worth of PCI config space mapped into memory.
        //- So this is bad.
        //-
        success := false;
        var buff := ring_buffer_build(0, 0, 0, 0, 0, 0);  //- TODO: dafnycc: had to add this line because dafnycc doesn't handle returning uninitialized variables.
        rx_ring_buff := rx_ring_buffer_build(buff); 
        tx_ring_buff := tx_ring_buffer_build(buff);
    } else {
        assert 512 == num_descriptors();  
        lemma_2toX();

        //
        
        //

        init_network_card_step1(id, addr);
        init_network_card_step2(id, addr);
        rx_ring_buff := init_network_card_step2rx(id, addr, size, dev_addr);

        init_network_card_step3(id, addr, size);
        tx_ring_buff := init_network_card_step3tx(id, addr, size, dev_addr);

        init_network_card_step4(id, addr, size);
        
        success := true;
    }

    state := network_state_build(rx_ring_buff, tx_ring_buff);
}

method init_network_card_step1a_stop_everything(id:int, addr:int)
    requires Word32(addr);
    requires IsValidPciId(id);
    requires addr == PciMemAddr(id);
    requires PciMemSize(id) >= 128 * 1024;
    requires public(id);
    requires public(addr);
{
    init_network_card_lemma3();
    lemma_2toX();

    //-
    //- Stop everything.
    
    //-
    PciMemStore(id, register_rx_ctrl(addr), 0);
    PciMemStore(id, register_tx_ctrl(addr), tx_pad_short_packets());

    //- Allow pending PCI transactions to complete.
    delay(10 * 1000);
}


method init_network_card_step1b_reset(id:int, addr:int)
    requires Word32(addr);
    requires IsValidPciId(id);
    requires addr == PciMemAddr(id);
    requires PciMemSize(id) >= 128 * 1024;
    requires public(id);
    requires public(addr);
{
    lemma_2toX();
    //-
    //- Reset the card.
    
    //-
    var ctrl_reg := PciMemLoad(id, register_ctrl(addr));
    //-debug_print(0x48, ctrl_reg);  
    var temp_reg := ctrl_reg;  
    temp_reg := Asm_BitwiseOr(temp_reg, ctrl_phy_reset());
    //-debug_print(0x48, temp_reg);
    PciMemStore(id, register_ctrl(addr), temp_reg);
    delay(5 * 1000);

    temp_reg := Asm_BitwiseOr(ctrl_reg, ctrl_reset());
    PciMemStore(id, register_ctrl(addr), temp_reg);
    //-debug_print(0x48, temp_reg);

    //- Wait 3us (or more) for the board to quiesce.
    delay(20 * 1000);
    
    
    delay(1 * 1000 * 1000);
}


method init_network_card_step1c_set_ctrl(id:int, addr:int)
    requires Word32(addr);
    requires IsValidPciId(id);
    requires addr == PciMemAddr(id);
    requires PciMemSize(id) >= 128 * 1024;
    requires public(id);
    requires public(addr);
{
    lemma_2toX();
    //- Set the device control register to values we want:
    //- (See Table 13-3 in section 13.4.1)
    //- Bit 0: Full-Duplex (Must also set the Force-Duplex Bit (Bit 12)).
    //- Bit 5: Auto-Speed Detection Enable (ASDE).
    //- Bit 6: Set Link Up (SLU).
    //- Bit 12: Force-Duplex Bit.
    PciMemStore(id, register_ctrl(addr), 0x1061);  

    //- Wait for the autonegotiation to complete.
    
    
    var negotiated := false;
    var ctrl:int := 0;
    var count := 0;
    while (!negotiated)
        decreases *;
        invariant public(id);
        invariant public(addr);
        invariant public(negotiated);
    {
        //-debug_print(0x90, count);
        ctrl := PciMemLoad(id, register_ctrl(addr));
        var done := Asm_BitwiseAnd(ctrl, ctrl_reset());
        if (done == 0) {
            negotiated := true;
        }
        count := count + 1;
    }
}

method init_network_card_step1d_disable_flow_ctrl(id:int, addr:int)
    requires Word32(addr);
    requires IsValidPciId(id);
    requires addr == PciMemAddr(id);
    requires PciMemSize(id) >= 128 * 1024;
    requires public(id);
    requires public(addr);
{
    //-
    //- Turn off flow control.
    //- See Section 14.3, General Configuration.
    //-
    PciMemStore(id, register_fcal(addr), 0);
    PciMemStore(id, register_fcah(addr), 0);
    PciMemStore(id, register_fct(addr), 0);
    PciMemStore(id, register_fcttv(addr), 0);
}


method init_network_card_step1(id:int, addr:int)
    requires Word32(addr);
    requires IsValidPciId(id);
    requires addr == PciMemAddr(id);
    requires PciMemSize(id) >= 128 * 1024;
    requires public(id);
    requires public(addr);
{
    init_network_card_step1a_stop_everything(id, addr);
    init_network_card_step1b_reset(id, addr);
    init_network_card_step1c_set_ctrl(id, addr);
    init_network_card_step1d_disable_flow_ctrl(id, addr);
}



//-
//- Clear the multicast table.
//-
method clear_multicast(id:int, addr:int)
    requires Word32(addr);
    requires IsValidPciId(id);
    requires addr == PciMemAddr(id);
    requires PciMemSize(id) >= 128 * 1024;
    requires public(id);
    requires public(addr);
{
    var mta_entry := 0;
    while (mta_entry < 128)
        invariant mta_entry >= 0;
        invariant public(id);
        invariant public(addr);
        invariant public(mta_entry);
    {
        PciMemStore(id, register_rx_mcast_table(addr) + mta_entry * 4, 0);
        mta_entry := mta_entry + 1;
    }
}

method init_network_card_step2(id:int, addr:int)
    requires Word32(addr);
    requires IsValidPciId(id);
    requires addr == PciMemAddr(id);
    requires PciMemSize(id) >= 128 * 1024;
    requires public(id);
    requires public(addr);
{
    //-init_network_card_lemma1(addr);
    init_network_card_lemma3();
    lemma_2toX();

    //-
    //- Setup the MAC address.
    
    //-
    var mac_addr := my_ethernet_addr();
    var addr_lo := mac_addr.bytes[0] + 256 * mac_addr.bytes[1] + 256 * 256 * mac_addr.bytes[2] + 256 * 256 * 256 * mac_addr.bytes[3]; //-little_endian_bytes_to_word(mac_addr.bytes[0..4]);
    var addr_hi := mac_addr.bytes[4] + 256 * mac_addr.bytes[5]; //-little_endian_bytes_to_word(mac_addr.bytes[4..6]);
    PciMemStore(id, register_rx_addrN_lo(addr), addr_lo);
    var temp_reg := addr_hi;
    temp_reg := Asm_BitwiseOr(temp_reg, 0x80000000); //- Set the Address Valid bit
    PciMemStore(id, register_rx_addrN_hi(addr), temp_reg);

    clear_multicast(id, addr);
}

method init_network_card_step2rx(id:int, addr:int, size:int, dev_addr:int)
    returns (rx_ring_buff:rx_ring_buffer)
    requires Word32(size) && Word32(addr) && Word32(dev_addr);
    requires IsValidPciId(id);
    requires size == PciMemSize(id);
    requires addr == PciMemAddr(id);
    requires Word32(addr + size);
    requires Word32(DeviceMemAddr() + DeviceMemSize());
    requires size >= 128 * 1024;
    requires DeviceMemAddr() == dev_addr;
    requires mod16(dev_addr) == 0;
    requires DeviceMemSize() > 0x204004;
    requires public(id);
    requires public(addr);
    requires public(dev_addr);
    ensures valid_ring_buffer(rx_ring_buff.rb);
    ensures public(rx_ring_buff);
{
    //-init_network_card_lemma1(addr);
    init_network_card_lemma2a(dev_addr);
    init_network_card_lemma2b(dev_addr);
    init_network_card_lemma2c(dev_addr);
    init_network_card_lemma3();
    lemma_2toX();

    //-
    //- Setup Receive Descriptor Queue.
    //- See Section 3.2.6.
    //-

    var rx_desc_base_lo := dev_addr + total_desc_bytes() + total_buffer_bytes();
    var rx_desc_len := total_desc_bytes();    

    assert(rx_desc_base_lo == dev_addr + 512 * 16 + 512 * 2 * 1024);

    //-    assert rx_desc_base_lo % 16 == 0;
    //-    assert rx_desc_len % 128 == 0 && 128 <= rx_desc_len < power2(19);
    //-    assert (512 * 16 + 512 * 2 * 1024) % 4 == 0;
    //-    assert rx_desc_base_lo % 4 == dev_addr % 4;

    //-
    //- The head pointer references the next empty descriptor to be filled with an incoming packet.
    //- Once the hardware has written a packet to that descriptor, it advances the head pointer.
    //- The tail pointer references one descriptor past the last one the hardware is allowed to write to.
    //- Once the driver has processed the packet in the (tail + 1) descriptor, it advances the tail pointer.
    //-
    //- When the head pointer is advanced to equal the tail pointer, there are no free (empty) descriptors available
    //- for the hardware to fill, and the hardware will stop adding packets to the circular queue until the driver
    //- processes some packets and advances the tail pointer.
    //-
    //- When the tail pointer is advanced to the point where it is one less than the head pointer, then all the
    //- receive descriptors are empty and are waiting for the hardware to fill them with packets.
    //- This is the initial state we establish below.
    //-
    var rx_desc_head := 1;
    var rx_desc_tail := 0;

    assert rx_desc_head < power2(16);
    assert rx_desc_tail < power2(16);

    PciMemStore(id, register_rx_desc_base_lo(addr), rx_desc_base_lo);
    PciMemStore(id, register_rx_desc_base_hi(addr), 0);
    PciMemStore(id, register_rx_desc_length(addr), rx_desc_len);
    PciMemStore(id, register_rx_desc_head(addr), rx_desc_head);    
    PciMemStore(id, register_rx_desc_tail(addr), rx_desc_tail);

    //-
    //- Create a full set of empty descriptors and buffers.
    //-
    BuildDescriptors(rx_desc_base_lo, false);

    rx_ring_buff := rx_ring_buffer_build(ring_buffer_build(rx_desc_base_lo, rx_desc_len, rx_desc_head, rx_desc_tail, id, addr));
}

method init_network_card_step3(id:int, addr:int, size:int)
    requires Word32(size) && Word32(addr);
    requires IsValidPciId(id);
    requires size == PciMemSize(id);
    requires addr == PciMemAddr(id);
    requires Word32(addr + size);
    requires Word32(DeviceMemAddr() + DeviceMemSize());
    requires size >= 128 * 1024;
    requires public(id);
    requires public(addr);
{
    //-init_network_card_lemma1(addr);
    init_network_card_lemma3();
    lemma_2toX();

    //-
    //- Set Receiever Control flags (See Table 13-67 in Section 13.4.22):
    //- Bits 8-9: Receive Descriptor Minimum Threshold Size set to 1/4 of RDLEN (01).
    //- Bit 26: Strip Ethernet CRC from incoming packet.
    //-
    //- Note: We leave all other bits at their initial zero value. This means:
    //- - Receiver Enable is not set (we enable this in final step).
    //- - We do not store bad packets.
    //- - Unicast Promiscuous is disabled.
    //- - Multicast Promiscuous is disabled.
    //- - We discard packets longer than 1522 bytes.
    //- - Loopback is off.
    //- - Multicast Offset - bits 47:36 are used in the lookup.
    //- - We ignore broadcast packets.
    //- - Receive Buffer Size is set to 2048 bytes.
    //- - Various VLAN things (Filter, Canonical Form Indicator) are disabled.
    //- - We don't Discard Pause Frames (used by flow control, if it's enabled).
    //-
    assert bytes_per_buffer() == 2 * 1024;  //- Ensure we match the Receive Buffer Size flag.
    PciMemStore(id, register_rx_ctrl(addr), 0x04000100);
//-    PciMemStore(id, register_rx_ctrl(addr), 0x04008118);  //- Promiscuous everything.

    //-
    //- Setup the rx interrupt delay.
    //- TODO: Don't we have interrupts off?  Why do this?
    //- TODO: Manual *strongly recommends* against using these fields.
    //-
//-    PciMemStore(id, register_rx_delay_timer(addr), rxdelaytimers_rx_delay_timer());
//-    PciMemStore(id, register_rx_int_abs_timer(addr), rxdelaytimers_rx_absolute_timer());

    //-
    //- Enable IP and TCP receive checksum calculation offloading.
    
//-    PciMemStore(id, register_rx_cksum_ctrl(addr), 0x00000700);
    //-                 Flags value above corresponds to:
    //-                rxchecksum_ip_checksum_enable()  |    //- 1u <<  8
    //-                rxchecksum_tcp_checksum_enable() |    //- 1u <<  9
    //-                rxchecksum_ip6_checksum_enable() ));  //- 1u << 10
}

method init_network_card_step3tx(id:int, addr:int, size:int, dev_addr:int)
    returns (tx_ring_buff:tx_ring_buffer)
    requires Word32(size) && Word32(addr) && Word32(dev_addr);
    requires IsValidPciId(id);
    requires size == PciMemSize(id);
    requires addr == PciMemAddr(id);
    requires Word32(addr + size);
    requires Word32(DeviceMemAddr() + DeviceMemSize());
    requires size >= 128 * 1024;
    requires DeviceMemAddr() == dev_addr;
    requires mod16(dev_addr) == 0;
    requires DeviceMemSize() > 0x204000;
    requires public(id);
    requires public(addr);
    requires public(dev_addr);
    ensures valid_ring_buffer(tx_ring_buff.rb);
    ensures public(tx_ring_buff);
{
    //-init_network_card_lemma1(addr);
    init_network_card_lemma2a(dev_addr);
    init_network_card_lemma2b(dev_addr);
    init_network_card_lemma2c(dev_addr);
    init_network_card_lemma3();
    lemma_2toX();

    //-debug_print(0x24, dev_addr);

    var tx_desc_base_lo := dev_addr;
    var tx_desc_len := total_desc_bytes();
    var tx_desc_head := 0;
    var tx_desc_tail := 0;  //- tail == head ==> queue is empty (Sec. 3.4) ==> no packets to transmit.

    assert tx_desc_head < power2(16);
    assert tx_desc_tail < power2(16);

    PciMemStore(id, register_tx_desc_base_lo(addr), tx_desc_base_lo);
    PciMemStore(id, register_tx_desc_base_hi(addr), 0);
    PciMemStore(id, register_tx_desc_length(addr), tx_desc_len);
    PciMemStore(id, register_tx_desc_head(addr), tx_desc_head);
    PciMemStore(id, register_tx_desc_tail(addr), tx_desc_tail);
    
    //-
    //- Create a full set of empty descriptors and buffers.
    //-
    BuildDescriptors(tx_desc_base_lo, true);

    tx_ring_buff := tx_ring_buffer_build(ring_buffer_build(tx_desc_base_lo, tx_desc_len, tx_desc_head, tx_desc_tail, id, addr));
}

method init_network_card_step4(id:int, addr:int, size:int)
    requires Word32(size) && Word32(addr);
    requires IsValidPciId(id);
    requires size == PciMemSize(id);
    requires addr == PciMemAddr(id);
    requires Word32(addr + size);
    requires Word32(DeviceMemAddr() + DeviceMemSize());
    requires size >= 128 * 1024;
    requires public(id);
    requires public(addr);
{
    //-init_network_card_lemma1(addr);
    init_network_card_lemma3();
    lemma_2toX();

    //-
    //- Set Transmit Control flags:
    //- Bit 3: Pad Short Packets to 64 bytes (including CRC).
    //- Bits 4-11: Collision Threshold set to 0xf.  TODO: Only for half-duplex?
    //- Bits 12-21: Collision Distance set to 0x40.
    //-
    //- Note: We leave all other bits at their initial zero value. This means:
    //- - Transmit Enable is not zet (we enable this in final step).
    //- - Software XOFF Transmission is disabled.
    //- - Re-transmit on Late Collision is disabled (ignored for full-duplex).
    //-
    PciMemStore(id, register_tx_ctrl(addr), 0x000400F8);

    //- Setup Transmit Inter Frame Gap.
    PciMemStore(id, register_tx_ipg(addr), tx_ipg_default());

    //-
    //- Start receiving.
    //-
    var temp_reg := PciMemLoad(id, register_rx_ctrl(addr));
    temp_reg := Asm_BitwiseOr(temp_reg, ctrl_rx_enable());
    PciMemStore(id, register_rx_ctrl(addr), temp_reg);

    //-
    //- Start transmitting.
    //-
    temp_reg := PciMemLoad(id, register_tx_ctrl(addr));
    temp_reg := Asm_BitwiseOr(temp_reg, ctrl_tx_enable());
    PciMemStore(id, register_tx_ctrl(addr), temp_reg);

    //-debug_print_register(0x36, id, register_status(addr));
}

//-
//- Setup a static set of descriptors pointing at a static set of buffers.
//-
method BuildDescriptors(BaseAddress:int, Transmit:bool)
    requires mod4(BaseAddress) == 0;
    requires num_descriptors() == 512;
    requires bytes_per_descriptor() == 16;
    requires bytes_per_buffer() == 2 * 1024;
    requires Word32(BaseAddress);
    requires Word32(BaseAddress + total_desc_bytes() + total_buffer_bytes());
    requires DeviceMemAddr() <= BaseAddress && BaseAddress + total_desc_bytes() + total_buffer_bytes() <= DeviceMemAddr() + DeviceMemSize();
    requires public(BaseAddress);
    requires public(Transmit);
{
    var Index := 0;
    var StartingStatus := 0;

    //-
    //- For transmit descriptors, we initialize the DD bit in the Status field to 1.
    //- This mimics the "transmission complete" state (i.e. our code is free to use them).
    //- For receive descriptors, we initialize the DD bit in the Status field to 0.
    //- This is the state that the hardware expects to find them prior to using them.
    //-
    if (Transmit)
    {
        StartingStatus := 1;  //- Set the DD bit.
    }
    
    while (Index < 512)
        invariant Index >= 0;
        invariant public(BaseAddress);        
        invariant public(Index);
        invariant public(StartingStatus);
    {
        var Descriptor := BaseAddress + Index * 16;
        var Buffer := BaseAddress + total_desc_bytes() + Index * 2 * 1024;
        DeviceMemStore(Descriptor + 0, Buffer);
        DeviceMemStore(Descriptor + 4, 0);
        DeviceMemStore(Descriptor + 8, 0);
        DeviceMemStore(Descriptor + 12, StartingStatus);

        Index := Index + 1;
    }
}

//- Write out the packet to device memory.
method write_out_packet(addr:int, ghost data_buffer:int, packet:seq<int>)
    returns (final_addr:int)
    requires IsWordSeq(packet);
    requires addr == data_buffer;
    requires Word32(addr);
    requires Word32(addr + 4 * |packet|);
    requires DeviceMemAddr() <= addr && data_buffer + 4 * |packet| <= DeviceMemAddr() + DeviceMemSize();
    requires public(addr);
    requires public(packet);
    ensures  final_addr == data_buffer + 4 * |packet|;
{
    var i := 0;
    var local_addr := addr;
    if (|packet| > 0) {
        ghost var complete := false;
        while (i < |packet|)
            invariant i < |packet| ==> !complete;
            invariant !complete ==> 0 <= i < |packet|;
            invariant IsWordSeq(packet);
            invariant Word32(local_addr);
            invariant local_addr == data_buffer + 4 * i;
            //-invariant valid_ring_buffer(tx_buff);
            invariant !complete ==> DeviceMemAddr() <= local_addr && local_addr + 4 <= DeviceMemAddr() + DeviceMemSize();
            invariant complete ==> i == |packet|;
            invariant public(local_addr);
            invariant public(i);
            invariant public(packet);
        {
            DeviceMemStore(local_addr, packet[i]);
            local_addr := local_addr + 4;
            i := i + 1;
            complete := complete || (i == |packet|);
        }
    }

    final_addr := local_addr;
}

//-
//- Reverse the byte-order in the given 32-bit word.
//-
method ByteSwapWord32(InWord:int)
    returns (OutWord:int)
    requires Word32(InWord);
    ensures Word32(OutWord);
    ensures relation(left(InWord) == right(InWord) ==> left(OutWord) == right(OutWord));
{
    lemma_2toX();

    var ByteA := Asm_RightShift(Asm_BitwiseAnd(InWord, 0xff000000), 24);
    var ByteB := Asm_RightShift(Asm_BitwiseAnd(InWord, 0x00ff0000), 8);
    var ByteC := Asm_LeftShift(Asm_BitwiseAnd(InWord, 0x0000ff00), 8);
    var ByteD := Asm_LeftShift(Asm_BitwiseAnd(InWord, 0x000000ff), 24);

    OutWord := Asm_BitwiseOr(Asm_BitwiseOr(ByteA, ByteB), Asm_BitwiseOr(ByteC, ByteD));
}

//-
//- Copy packet data to buffer.
//-
method CopyPacketToBuffer(BufferAddr:int, PacketData:seq<int>)
    requires Word32(BufferAddr);
    requires IsByteSeq(PacketData);
    requires Word32(BufferAddr + |PacketData| + 4);
    requires DeviceMemAddr() <= BufferAddr;
    requires BufferAddr + |PacketData| + 4 <= DeviceMemAddr() + DeviceMemSize();
    requires public(BufferAddr);
    requires public(PacketData);
{
    lemma_2toX();

    //-
    //- Convert the packet data byte sequence to a sequence of 32-bit words.
    //-
    var Words := BEByteSeqToWordSeqTailPadding(PacketData);

    var Index := 0;
    var WordAddr := BufferAddr;

    if (|Words| > 0) {
        ghost var Complete := false;

        //-
        //- Write the 32-bit words that comprise the packet data out to the buffer.
        //- We byte-swap the words in the process as BEByteSeqToWordSeqTailPadding gave
        //- us the opposite of what we need.     
        //-                      
        while (Index < |Words|)
            invariant Index < |Words| ==> !Complete;
            invariant !Complete ==> 0 <= Index < |Words|;
            invariant IsWordSeq(Words);
            invariant Word32(WordAddr);
            invariant WordAddr == BufferAddr + 4 * Index;
            invariant !Complete ==> DeviceMemAddr() <= WordAddr && WordAddr + 4 <= DeviceMemAddr() + DeviceMemSize();
            invariant Complete ==> Index == |Words|;
            invariant public(Words);
            invariant public(Index);
            invariant public(WordAddr);
        {
            var Word := ByteSwapWord32(Words[Index]);
            DeviceMemStore(WordAddr, Word);
            WordAddr := WordAddr + 4;
            Index := Index + 1;
            Complete := Complete || (Index == |Words|);
        }
    }
}

//-
//- Copy buffer contents to packet representation.
//-
method CopyBufferToPacket(BufferAddr:int, Length:int)
    returns (Success:bool, PacketData:seq<int>)
    requires Word32(BufferAddr);
    requires DeviceMemAddr() <= BufferAddr;
    requires Word16(Length);
    requires Word32(BufferAddr + 2048 + 4);
    requires BufferAddr + 2048 + 4 <= DeviceMemAddr() + DeviceMemSize();
    requires public(BufferAddr);
    requires public(Length);
    ensures Success ==> IsByteSeq(PacketData);
    ensures Success ==> |PacketData| == Length;
    ensures public(PacketData);
    ensures public(Success);
{
    reveal_mod4();
    reveal_mod16();
    reveal_mod128();
    reveal_div16();

    lemma_2toX();

    PacketData := [];

    //-
    //- Sanity-check the amount of data this is supposedly in this buffer.
    //- We use 2K buffers, so anything more than that doesn't make sense.
    //- We also protect ourselves against the hardware indicating it received a zero byte packet.
    //-
    if ((Length <= 0) || (Length > 2048))
    {
        Success := false;
    }
    else
    {
        //-
        //- Calculate the number of 32-bit words (containing valid data) in the buffer.
        //- Note that only some of the bytes in the last word of this count may contain valid data.
        //-
        var NumWords := ((Length - 1) / 4) + 1;
        assert 0 <= NumWords <= 512;

        //-
        //- Read in the packet data from the buffer.
        //-
        var Words := [];
        var Index := 0;
        var WordAddr := BufferAddr;

        ghost var Complete := false;
        while (Index < NumWords)
            invariant Index < NumWords ==> !Complete;
            invariant !Complete ==> 0 <= Index < NumWords;
            invariant IsWordSeq(Words);
            invariant Word32(WordAddr);
//-            invariant Word32(WordAddr) && WordAddr % 4 == 0;
            invariant WordAddr == BufferAddr + 4 * Index;
            invariant !Complete ==> DeviceMemAddr() <= WordAddr && WordAddr + 4 <= DeviceMemAddr() + DeviceMemSize();
            invariant Complete ==> Index == NumWords;
            invariant |Words| == Index;
            invariant 0 <= Index <= 512;
            invariant public(WordAddr);
            invariant public(Words);
            invariant public(Index);
            invariant public(NumWords);
            invariant public(Length);
            invariant public(Complete);
        {
            var Word := DeviceMemLoad(WordAddr);
            Word := ByteSwapWord32(Word);
            Words := Words + [Word];

            WordAddr := WordAddr + 4;
            Index := Index + 1;

            Complete := Complete || (Index == NumWords);
        }

        PacketData := BEWordSeqToByteSeq_impl(Words);
        PacketData := PacketData[0..Length];
        Success := true;
    }
}


method update_tx_descriptor(tx_rb:tx_ring_buffer, packet_size:int)
    requires valid_ring_buffer(tx_rb.rb);
    requires Word32(packet_size);
    requires public(tx_rb);
    requires public(packet_size);
{
    lemma_2toX();
    //-
    //- Update the corresponding (legacy format) transmit descriptor.
    //- See Table 3-8 and 3-9 in Section 3.3.3.
    //-
    //- Bytes 0 to 7 of the transmit descriptor contain the address of its
    //- corresponding buffer, which we never change after initialization.
    //-
    //- Bytes 8 and 9 contain the length of the data to be sent.
    //- Byte 10 is the Checksum Offset, which we currently do not use.
    //- Byte 11 is the Command Field (See Section 3.3.3.1):
    //-     Bit 0: Indicates this descriptor is the End Of Packet (EOP).
    //-     Bit 1: Insert FCS/CRC field (IFCS).  Valid only if EOP is set.
    //-     Bit 2: Insert Checksum (IC).  We currently do not set.
    //-     Bit 3: Report Status (RS).  Hardware sets Status DD bit when done.
    //-     Bit 4: Only for 82544GC/CI, reserved bit for the 82541.
    //-     Bit 5: Extention (DEXT).  We write as 0 for legacy mode.
    //-     Bit 6: VLAN Packet Enable (VLE).  We currently do not set.
    //-     Bit 7: Interrupt Delay Enable.  We currently do not set.
    //- Byte 12 is the Status Field (bits 0-2, bits 3-7 are Reserved).
    //- Byte 13 is the Checksum Start Field, which we currently do not use.
    //- Bytes 14 and 15 is the Special Field (VLAN related, we do not use).
    //-
    //- We write 32 bits at a time, so we write bytes 8-11 in one operation,
    //- and 12-14 in another.
    //-
    var TailDesc := tx_rb.rb.base + 16 * tx_rb.rb.tail;
//-    debug_print(0x90, TailDesc); //- Debug.
    //-
    //- We set RS, IFCS, and EOP bits (i.e. 0xb) in the Command Field.
    //-
    var Temp := Asm_BitwiseOr(0x0b000000, packet_size);
    DeviceMemStore(TailDesc + 8, Temp);  //- Bytes 8-11.
    DeviceMemStore(TailDesc + 12, 0);  //- Bytes 12-15.
}

//-
//- Before advancing the tail descriptor, make sure the hardware is done
//- with the next entry.
//-
method wait_for_available_tx_buffer(tx_rb:tx_ring_buffer, NextIndex:int)
    requires valid_ring_buffer(tx_rb.rb);
    requires 0 <= NextIndex < 512;
    requires public(tx_rb);
    requires public(NextIndex);
{
    lemma_2toX();
    var done := 0;
    while (done != 1)
        invariant valid_ring_buffer(tx_rb.rb);
        invariant public(tx_rb);
        invariant public(done);
        invariant public(NextIndex);
        decreases *;
    {
        var NextDescStatus := DeviceMemLoad(tx_rb.rb.base + 16 * NextIndex + 12);
        done := Asm_BitwiseAnd(NextDescStatus, 1); //- Check DD bit.
    }
}

method tx_cleanup(tx_rb:tx_ring_buffer, NextIndex:int)
    requires valid_ring_buffer(tx_rb.rb);
    requires 0 <= NextIndex < 512;
    requires public(tx_rb);
    requires public(NextIndex);
{
    lemma_2toX();
    //- Clear out the status register.  TODO: Why?
    DeviceMemStore(tx_rb.rb.base + 16 * NextIndex + 12, 0);

    //-
    //- Advance the tail pointer.  This submits the descriptor pointed to by
    //- the current tail pointer to the hardware for processing.
    //-
    PciMemStore(tx_rb.rb.id, register_tx_desc_tail(tx_rb.rb.reg_addr), NextIndex);
}

//-
//- Send an Ethernet packet on our interface.
//-
method NetIfSend(state:network_state, Headers:seq<int>, Data:seq<int>)
    returns (new_state:network_state)
    requires valid_network_state(state);
    requires public(state);
    requires |Headers| >= 14;  //- Must contain at least an Ethernet header.
    requires |Headers| + |Data| <= 1514;  //- Cannot exceed maximum Ethernet packet size.
    requires IsByteSeq(Headers);
    requires IsByteSeq(Data);
    requires public(Headers);
    requires public(Data);
    ensures  valid_network_state(new_state);
    ensures  new_state == state[tx_rb := tx_ring_buffer_build(ring_buffer_build(state.tx_rb.rb.base, state.tx_rb.rb.size, state.tx_rb.rb.head, (state.tx_rb.rb.tail + 1) % 512, state.tx_rb.rb.id, state.tx_rb.rb.reg_addr))];
    ensures  public(new_state);
{
    reveal_mod4();
    reveal_mod16();
    reveal_mod128();
    reveal_div16();

    lemma_2toX();

    var Ring:ring_buffer := state.tx_rb.rb;

    //-debug_print(0x60, Ring.base);
//-    debug_print(0x84, Ring.tail);

    //-
    //- Determine how much padding we need to add to meet minimal Ethernet packet size (if any).
    //-
    var Padding := [];
    if (|Headers| + |Data| < 60)
    {
        Padding := SequenceOfZerosIterative(60 - |Headers| - |Data|);
    }

    //-
    //- Write the packet data to the buffer indicated by the tail pointer.
    //- The tail pointer is the index of the next descriptor in the circular
    //- queue beyond that which has already been submitted to the hardware.
    //-
    //- The data buffers start at total_desc_bytes above the base address.
    //- Ring.tail is an index into the array, and each buffer is 2KB in size.
    //-
    var PacketBuffer := Ring.base + total_desc_bytes() + Ring.tail * 2048;
    CopyPacketToBuffer(PacketBuffer, Headers + Data + Padding);

    update_tx_descriptor(state.tx_rb, |Headers| + |Data| + |Padding|);

    //-
    //- Find the next entry in the descriptor ring.
    //-
    var NextIndex := (Ring.tail + 1) % 512;  //- ModInstruction(Ring.tail + 1, 512);
    //-lemma_mod_512(Ring.tail + 1);
    assert NextIndex == (Ring.tail + 1) % 512;
    assert 0 <= NextIndex < 512;

    //-
    //- Before advancing the tail descriptor, make sure the hardware is done
    //- with the next entry.
    //-
    wait_for_available_tx_buffer(state.tx_rb, NextIndex);

    tx_cleanup(state.tx_rb, NextIndex);

    //-
    //- Update the ring buffer state that we pass around.
    //-
    var NewRing := tx_ring_buffer_build(ring_buffer_build(Ring.base, Ring.size, Ring.head, NextIndex, Ring.id, Ring.reg_addr));
    new_state := state[tx_rb := NewRing];
}

//-
//- Advance a descriptor pointer to the next descriptor in the ring.
//-
method AdvanceDescriptorIndex(Index:int) returns (NewIndex:int)
    requires num_descriptors() == 512;
    requires 0 <= Index < 512;
    requires public(Index);
    ensures 0 <= NewIndex < 512;
    ensures public(NewIndex);
{
    ghost var OldIndex := Index;
    NewIndex := (Index + 1) % 512;
    //-lemma_mod_512(OldIndex + 1);
    assert NewIndex == (OldIndex + 1) % 512;
}

//-method check_for_eop(TailDesc:int,TailIndex:int,rx_rb:rx_ring_buffer) returns (NewTailIndex:int, EndOfPacket:bool, Success:bool, NewData:seq<int>)
//-    requires 0 <= TailIndex < 512 && rx_rb.rb.base + 16 * TailIndex < rx_rb.rb.base + rx_rb.rb.size;
//-    requires valid_ring_buffer(rx_rb.rb);
//-    requires public(TailDesc);
//-    requires public(rx_rb);
//-    ensures 0 <= NewTailIndex < 512; //- && rx_rb.rb.base + 16 * NewTailIndex < rx_rb.rb.base + rx_rb.rb.size;
//-    ensures Success ==> IsByteSeq(NewData);
//-    ensures public(NewTailIndex);
//-    ensures public(EndOfPacket);
//-    ensures public(Success);
//-    ensures public(NewData);
//-{
//-    //-
//-    //- Receive descriptor format.
//-    //- See Table 3-1 and 3-2 in Section 3.2.3.
//-    //-
//-    //- Bytes 0 to 7 of the receive descriptor contain the address of its
//-    //- corresponding buffer, which we never change after initialization.
//-    //-
//-    //- Bytes 8 and 9 contain the length of the data received into this descriptor's buffer.
//-    //- Bytes 10 and 11 contain the Packet Checksum, which we currently do not use.
//-    //- Byte 12 is the Status field (See Section 3.2.3.1):
//-    //-     Bit 0: Indicates whether the hardware is Done with this Descriptor (DD).
//-    //-     Bit 1: Indicates whether this descriptor is the End Of Packet (EOP).
//-    //-     Bit 2: Ignore Checksum Indication (IXSM), which we currently do not use.
//-    //-     Bit 3: VLAN related.  We do not use.
//-    //-     Bit 4: Reserved bit.  We ignore it.
//-    //-     Bit 5: Indicates whether the TCP CheckSum (TCPCS) was calculated on the packet.
//-    //-     Bit 6: Indicates whether the IP CheckSum (IPCS) was calculated on the packet.
//-    //-     Bit 7: Indicates whether the packet Passed an In-exact Filter (PIF).
//-    //- Byte 13 is the Errors field, which we currently do not use (note we do not store bad packets).
//-    //- Bytes 14 and 15 is the Special field (VLAN related, we do not use).
//-    //-
//-    //- We read 32 bits at a time, so we read bytes 8-11 in one operation, and 12-14 in another.
//-    //-
//-
//-    //-
//-    //- Check the Descriptor Done (DD) bit in the Status field.
//-    //-
//-    var WordContainingStatus := DeviceMemLoad(TailDesc + 12);  //- Bytes 12-14.
//-    var DDBit := Asm_BitwiseAnd(WordContainingStatus, 1);  //- Bit 0.
//-    NewData := [];
//-    if (DDBit == 1) {
//-        var WordContainingLength := DeviceMemLoad(TailDesc + 8);  //- Bytes 8-11.
//-        var Length := TruncateToWord16(WordContainingLength);  //- Bytes 8-9.
//-
//-        var PacketBuffer := rx_rb.rb.base + total_desc_bytes() + TailIndex * 2048;
//-        var ReadOkay, NewData := CopyBufferToPacket(PacketBuffer, Length);
//-
//-        if (!ReadOkay || (|NewData| >= 0x10000)) {
//-            Success := false;
//-            NewData := [];
//-        }
//-
//-        //-
//-        //- Clear out the status field before giving this descriptor back to the hardware.
//-        //- Note we still have a copy of the status value in WordContainingStatus.
//-        //-
//-        DeviceMemStore(TailDesc + 12, 0);
//-
//-        //-
//-        //- Tell the hardware that we are done with all descriptors preceeding this one in the ring.
//-        //- TODO: Only do this after we reach end of packet?  Optimization trade-off, not a correctness issue.
//-        //-
//-        PciMemStore(rx_rb.rb.id, register_rx_desc_tail(rx_rb.rb.reg_addr), TailIndex);
//-
//-        //-
//-        //- Was this descriptor the end of the current packet?
//-        //- If not, proceed to the next descriptor in the ring.
//-        //-
//-        var Eop := Asm_BitwiseAnd(WordContainingStatus, 2);  //- Bit 1.
//-        if (Eop > 0) {
//-            EndOfPacket := true;
//-        }
//-        else
//-        {
//-            NewTailIndex := AdvanceDescriptorIndex(TailIndex);
//-        }
//-    }
//-
//-}
//-
//-
//-method NetIfReceive(state:network_state)
//-    returns (Success:bool, new_state:network_state, Data:seq<int>)
//-    requires valid_network_state(state);
//-    requires public(state);
//-    requires num_descriptors() == 512;
//-    requires bytes_per_buffer() == 2048;
//-    ensures valid_network_state(new_state);
//-    ensures public(new_state);
//-    ensures Success ==> IsByteSeq(Data);
//-    ensures public(Success);
//-    ensures public(Data);
//-{
//-    reveal_mod4();
//-    reveal_mod16();
//-    reveal_mod128();
//-    reveal_div16();
//-
//-    lemma_2toX();
//-
//-    Success := true;
//-    Data := [];
//-
//-    var Ring := state.rx_rb.rb;
//-
//-    //-debug_print(0x72, Ring.base);
//-
//-    //-
//-    //- The next descriptor we should read is *the one after* the current tail pointer.
//-    //-
//-    var TailIndex:int := AdvanceDescriptorIndex(Ring.tail);
//-
//-    //-
//-    //- Wait for the hardware to be done with this descriptor.
//-    //- Note that receipt of a single packet can result in the use of multiple descriptors,
//-    //- so we loop until we find a descriptor with the End-Of-Packet bit set.
//-    //-
//-    var EndOfPacket:bool := false;
//-    while (!EndOfPacket)
//-        decreases *;
//-        invariant IsByteSeq(Data);
//-        invariant valid_ring_buffer(Ring);
//-        invariant public(Ring);
//-        invariant 0 <= TailIndex < 512 && Ring.base + 16 * TailIndex < Ring.base + Ring.size;
//-        invariant |Data| < power2(16);
//-        invariant public(Data);
//-        invariant public(TailIndex);
//-        invariant public(Success);
//-        invariant public(EndOfPacket);
//-    {
//-        lemma_2toX();
//-
//-        //-
//-        //- Convert tail index to descriptor address.
//-        //-
//-        var TailDesc := Ring.base + 16 * TailIndex;
//-        var NewData:seq<int>;
//-        TailDesc, EndOfPacket, Success, NewData := check_for_eop(TailDesc, TailIndex, state.rx_rb);
//-        Data := Data + NewData;
//-    }
//-
//-    var NewRing := rx_ring_buffer_build(ring_buffer_build(Ring.base, Ring.size, Ring.head, TailIndex, Ring.id, Ring.reg_addr));
//-    new_state := state[rx_rb := NewRing];
//-}



//-
//- Check the Descriptor Done (DD) bit in the Status field.
//-
method check_desc_dd(src:int) returns (DD:bool, Length:int, Eop:bool)
    requires DeviceMemAddr() <= src + 4 <= DeviceMemAddr() + DeviceMemSize();
    requires DeviceMemAddr() <= src + 8 + 4 <= DeviceMemAddr() + DeviceMemSize();
    requires DeviceMemAddr() <= src + 12 + 4 <= DeviceMemAddr() + DeviceMemSize();
    requires Word32(src + 8);
    requires Word32(src + 12);
    requires public(src);
    ensures Word16(Length);
    ensures public (DD);
    ensures public(Length);
    ensures public(Eop);
{
    DD := false;
    Length := 0;
    var WordContainingStatus := DeviceMemLoad(src + 12);  //- Bytes 12-14.
    var DDBit := Asm_BitwiseAnd(WordContainingStatus, 1);  //- Bit 0.
    if (DDBit == 1) {
        DD := true;
        var WordContainingLength := DeviceMemLoad(src + 8);  //- Bytes 8-11.
        Length := TruncateToWord16(WordContainingLength);  //- Bytes 8-9.
    } 
        
    //- Was this descriptor the end of the current packet?
    var EopBit := Asm_BitwiseAnd(WordContainingStatus, 2);  //- Bit 1.
    if EopBit > 0 {
        Eop := true;
    } else {
        Eop := false;
    }

}

method reset_descriptor(desc:int,rx_rb:rx_ring_buffer, TailIndex:int)
    requires DeviceMemAddr() <= desc + 12 && desc + 12 + 4 <= DeviceMemAddr() + DeviceMemSize();
    requires Word32(desc + 12);
    requires valid_ring_buffer(rx_rb.rb);
    requires Word32(TailIndex);
    requires public(desc);
    requires public(rx_rb);
    requires public(TailIndex);
{
    //-
    //- Clear out the status field before giving this descriptor back to the hardware.
    //- Note we still have a copy of the status value in WordContainingStatus.
    //-
    DeviceMemStore(desc + 12, 0);

    //-
    //- Tell the hardware that we are done with all descriptors preceeding this one in the ring.
    
    //-
    PciMemStore(rx_rb.rb.id, register_rx_desc_tail(rx_rb.rb.reg_addr), TailIndex);
}

method receive_loop_body(rx_rb:rx_ring_buffer, TailIndex:int) returns (NewTailIndex:int, EndOfPacket:bool, NewData:seq<int>, Success:bool)
    requires valid_ring_buffer(rx_rb.rb);
    requires 0 <= TailIndex < 512;
    requires rx_rb.rb.base + 16 * TailIndex < rx_rb.rb.base + rx_rb.rb.size;
    requires public(rx_rb);
    requires public(TailIndex);
    ensures  0 <= NewTailIndex < 512;
    ensures IsByteSeq(NewData);
    ensures public(NewTailIndex);
    ensures public(EndOfPacket);
    ensures public(NewData);
    ensures public(Success);

{
    lemma_2toX();
    reveal_mod16();

    NewTailIndex := TailIndex;
    NewData := [];
    EndOfPacket := false;
    Success := true;
    //-
    //- Convert tail index to descriptor address.
    //-
    var TailDesc := rx_rb.rb.base + 16 * TailIndex;

    //-
    //- Receive descriptor format.
    //- See Table 3-1 and 3-2 in Section 3.2.3.
    //-
    //- Bytes 0 to 7 of the receive descriptor contain the address of its
    //- corresponding buffer, which we never change after initialization.
    //-
    //- Bytes 8 and 9 contain the length of the data received into this descriptor's buffer.
    //- Bytes 10 and 11 contain the Packet Checksum, which we currently do not use.
    //- Byte 12 is the Status field (See Section 3.2.3.1):
    //-     Bit 0: Indicates whether the hardware is Done with this Descriptor (DD).
    //-     Bit 1: Indicates whether this descriptor is the End Of Packet (EOP).
    //-     Bit 2: Ignore Checksum Indication (IXSM), which we currently do not use.
    //-     Bit 3: VLAN related.  We do not use.
    //-     Bit 4: Reserved bit.  We ignore it.
    //-     Bit 5: Indicates whether the TCP CheckSum (TCPCS) was calculated on the packet.
    //-     Bit 6: Indicates whether the IP CheckSum (IPCS) was calculated on the packet.
    //-     Bit 7: Indicates whether the packet Passed an In-exact Filter (PIF).
    //- Byte 13 is the Errors field, which we currently do not use (note we do not store bad packets).
    //- Bytes 14 and 15 is the Special field (VLAN related, we do not use).
    //-
    //- We read 32 bits at a time, so we read bytes 8-11 in one operation, and 12-14 in another.
    //-

    //-
    //- Check the Descriptor Done (DD) bit in the Status field.
    //-
    var DD, Length, Eop := check_desc_dd(TailDesc);

    if (DD) {
        var PacketBuffer := rx_rb.rb.base + total_desc_bytes() + TailIndex * 2048;
        var ReadOkay:bool;
        ReadOkay, NewData := CopyBufferToPacket(PacketBuffer, Length);

        if (!ReadOkay || (|NewData| >= 0x10000)) {
            Success := false;
            NewData := [];
        }

        reset_descriptor(TailDesc, rx_rb, TailIndex);

        //-
        //- Was this descriptor the end of the current packet?
        //- If not, proceed to the next descriptor in the ring.
        //-
        if (Eop) {
            EndOfPacket := true;
        }
        else
        {
            NewTailIndex := AdvanceDescriptorIndex(TailIndex);
        }
    }
}

method NetIfReceive(state:network_state)
    returns (Success:bool, new_state:network_state, Data:seq<int>)
    requires valid_network_state(state);
    requires public(state);
    requires num_descriptors() == 512;
    requires bytes_per_buffer() == 2048;
    ensures valid_network_state(new_state);
    ensures Success ==> IsByteSeq(Data);
    ensures public(Success);
    ensures public(new_state);
    ensures public(Data);
{
//-    reveal_mod4();
//-    reveal_mod16();
//-    reveal_mod128();
    reveal_div16();

    lemma_2toX();

    Success := true;
    Data := [];

    //-debug_print(0x72, state.rx_rb.rb.base);

    //-
    //- The next descriptor we should read is *the one after* the current tail pointer.
    //-
    var TailIndex:int := AdvanceDescriptorIndex(state.rx_rb.rb.tail);

    //-
    //- Wait for the hardware to be done with this descriptor.
    //- Note that receipt of a single packet can result in the use of multiple descriptors,
    //- so we loop until we find a descriptor with the End-Of-Packet bit set.
    //-
    var EndOfPacket:bool := false;
    while (!EndOfPacket)
        decreases *;
        invariant IsByteSeq(Data);
        invariant valid_ring_buffer(state.rx_rb.rb);
        invariant 0 <= TailIndex < 512 && state.rx_rb.rb.base + 16 * TailIndex < state.rx_rb.rb.base + state.rx_rb.rb.size;
        invariant |Data| < power2(16);
        invariant public(state);
        invariant public(Data);
        invariant public(TailIndex);
        invariant public(Success);
        invariant public(EndOfPacket);
    {
        var NewData:seq<int>;
        TailIndex, EndOfPacket, NewData, Success := receive_loop_body(state.rx_rb, TailIndex);
        Data := Data + NewData;
        if !Success || |Data| >= 0x10000 {
            Success := false;
            Data := [];
        }
    }

    var NewRing := rx_ring_buffer_build(ring_buffer_build(state.rx_rb.rb.base, state.rx_rb.rb.size, state.rx_rb.rb.head, TailIndex, state.rx_rb.rb.id, state.rx_rb.rb.reg_addr));
    new_state := state[rx_rb := NewRing];
}


