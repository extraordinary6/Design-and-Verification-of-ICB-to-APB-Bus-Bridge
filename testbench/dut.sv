//=====================================================================
// Description:
// This file wraps the dut_top
// Designer : lynnxie@sjtu.edu.cn
// Revision History
// V0 date:2024/11/13 Initial version, lynnxie@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps
`include "cfig.svh"

module dut (
    icb_bus     icb,
    apb_bus     apb0,
    apb_bus     apb1,
    apb_bus     apb2,
    apb_bus     apb3
);
// dut top
    dut_top i_dut(
        // input bus
        .icb_bus(       icb.slave       ),

        // output bus
        .apb_bus_0(     apb0.master     ),
        .apb_bus_1(     apb1.master     ),
        .apb_bus_2(     apb2.master     ),
        .apb_bus_3(     apb3.master     )
    );

// other testbench modules if needed
    
// assertion bind
`ifdef CHECK
    bind dut_top icb_assertion 
    icb_assertion_bind_dut_top (
        .icb(           icb.others      )
    );

    bind dut_top apb_assertion #(.ID(0))
    apb_assertion_bind_dut_top0 (
        .apb(           apb0.others      )
    );

    bind dut_top apb_assertion #(.ID(1))
    apb_assertion_bind_dut_top1 (
        .apb(           apb1.others      )
    );

    bind dut_top apb_assertion #(.ID(2))
    apb_assertion_bind_dut_top2 (
        .apb(           apb2.others      )
    );

    bind dut_top apb_assertion #(.ID(3))
    apb_assertion_bind_dut_top3 (
        .apb(           apb3.others      )
    );
`endif
endmodule