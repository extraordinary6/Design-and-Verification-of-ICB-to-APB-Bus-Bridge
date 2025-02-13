//=====================================================================
// Description:
// This file realize assertion of apb ports
// Designer : extraordinary.h@sjtu.edu.cn
// Revision History
// V0 date:2024/12/14 Initial version, extraordinary.h@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

module apb_assertion #(
    parameter ID = 0
)
(
    apb_bus.others   apb
);

// Signal X Assertion
    property psel_no_x_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        not ($isunknown(apb.psel));
    endproperty

    property pwrite_no_x_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        apb.psel |-> (not ($isunknown(apb.pwrite)));
    endproperty

    property paddr_no_x_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        apb.psel |-> (not ($isunknown(apb.paddr)));
    endproperty

    property pwdata_no_x_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        (apb.psel && apb.pwrite) |-> (not ($isunknown(apb.pwdata)));
    endproperty

    property penable_no_x_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        not ($isunknown(apb.penable));
    endproperty

    property prdata_no_x_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        (apb.penable && !apb.pwrite) |-> (not ($isunknown(apb.prdata)));
    endproperty

    property pready_no_x_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        apb.penable |-> (not ($isunknown(apb.pready)));
    endproperty
    
    check_psel_no_x: assert property (psel_no_x_check) else $error($stime, "\t\t FATAL: psel %0d exists X!\n", ID);
    check_pwrite_no_x: assert property (pwrite_no_x_check) else $error($stime, "\t\t FATAL: pwrite %0d exists X!\n", ID);
    check_paddr_no_x: assert property (paddr_no_x_check) else $error($stime, "\t\t FATAL: paddr %0d exists X!\n", ID);
    check_pwdata_no_x: assert property (pwdata_no_x_check) else $error($stime, "\t\t FATAL: pwdata %0d exists X!\n", ID);
    check_penable_no_x: assert property (penable_no_x_check) else $error($stime, "\t\t FATAL: penable %0d exists X!\n", ID);
    check_prdata_no_x: assert property (prdata_no_x_check) else $error($stime, "\t\t FATAL: prdata %0d exists X!\n", ID);
    check_pready_no_x: assert property (pready_no_x_check) else $error($stime, "\t\t FATAL: pready %0d exists X!\n", ID);

// Signals Keep Assertion
    property paddr_keep_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        (apb.psel && !apb.pready) |=> $stable(apb.paddr);
    endproperty

    property pwrite_keep_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        (apb.psel && !apb.pready) |=> $stable(apb.pwrite);
    endproperty

    property pwdata_keep_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        (apb.pready && apb.pwrite) |-> (apb.pwdata == $past(apb.pwdata));
    endproperty

    check_paddr_keep: assert property (paddr_keep_check) else $error($stime, "\t\t FATAL: paddr %0d does not keep!\n", ID);
    check_pwrite_keep: assert property (pwrite_keep_check) else $error($stime, "\t\t FATAL: pwrite %0d does not keep!\n", ID);
    check_pwdata_keep: assert property (pwdata_keep_check) else $error($stime, "\t\t FATAL: pwdata %0d does not keep!\n", ID);

// APB Handshake Assertion
    property apb_handshake_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        $rose(apb.psel) |-> ##[1:$] (apb.penable && apb.pready);
        // $rose(apb.psel) |=> ##[0:$] (apb.penable && apb.pready);
    endproperty

    check_apb_handshake: assert property (apb_handshake_check) else $error($stime, "\t\t FATAL: apb %0d does not handshake!\n", ID);

// penable and pready must be low after handshaking
    property penable_handshake_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        apb.penable |-> ##[1:$] (!apb.penable);
    endproperty

    property pready_handshake_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        apb.pready |=> (!apb.pready);
    endproperty

    check_penable_handshake: assert property (penable_handshake_check) 
    else $error($stime, "\t\t FATAL: penable %0d is not low after handshaking!\n", ID);

    check_pready_handshake: assert property (pready_handshake_check) 
    else $error($stime, "\t\t FATAL: pready %0d is not low after handshaking!\n", ID);

// psel must be high before penable is high
    property penable_psel_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        apb.penable |-> $past(apb.psel);
    endproperty

    check_penable_psel: assert property (penable_psel_check) 
    else $error($stime, "\t\t FATAL: psel %0d is not high before penable is high!\n", ID);

// penable must be high after psel is high
    property psel_penable_check;
        @(posedge apb.clk) disable iff(!apb.rst_n)
        apb.psel |-> ##[1:$] apb.penable;
    endproperty

    check_psel_penable: assert property (psel_penable_check) 
    else $error($stime, "\t\t FATAL: penable %0d is not high after psel is high!\n", ID);

endmodule