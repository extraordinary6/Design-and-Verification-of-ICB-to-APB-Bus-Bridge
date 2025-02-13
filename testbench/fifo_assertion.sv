//=====================================================================
// Description:
// This file realize assertion of fifo ports
// Designer : extraordinary.h@sjtu.edu.cn
// Revision History
// V0 date:2024/12/15 Initial version, extraordinary.h@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

module fifo_assertion #(
    parameter ID = 0,           // if ID = 0, fifo is wfifo
                                // if ID = 1, fifo is rfifo 
    parameter BUF_SIZE = 16,
    parameter ADDR_SIZE = 4,    // ADDR_SIZE = log2(BUF_SIZE)
    parameter DATA_WIDTH = 64
)
(
    input logic                  wclk,
    input logic                  wrst_n,
    input logic                  wen,
    input logic [DATA_WIDTH-1:0] data_w,
    input logic                  full,
    input logic [ADDR_SIZE:0]    wr_ptr,      // for assertion
    input logic [ADDR_SIZE:0]    wr_ptr_g,    // for assertion
    input logic [ADDR_SIZE:0]    wr_ptr_gd2,  // for assertion

    input logic                  rclk,
    input logic                  rrst_n,
    input logic                  ren,
    input logic [DATA_WIDTH-1:0] data_r,
    input logic                  empty,
    input logic [ADDR_SIZE:0]    rd_ptr,     // for assertion
    input logic [ADDR_SIZE:0]    rd_ptr_g,   // for assertion
    input logic [ADDR_SIZE:0]    rd_ptr_gd2  // for assertion
);

// Signal Empty & Full Assertion
    property fifo_empty_check;
        @(posedge rclk) disable iff(!rrst_n)
        (rd_ptr_g == wr_ptr_gd2) |-> empty;
    endproperty

    property fifo_full_check;
        @(posedge wclk) disable iff(!wrst_n)
        (wr_ptr_g == {~rd_ptr_gd2[ADDR_SIZE:ADDR_SIZE-1], rd_ptr_gd2[ADDR_SIZE-2:0]}) |-> full;
    endproperty

    check_fifo_empty: assert property (fifo_empty_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d empty but empty signal is not high!\n", ID);

    check_fifo_full: assert property (fifo_full_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d full but full signal is not high!\n", ID);

// FIFO Write & Read Function Assertion
    
    property fifo_write_check;
        @(posedge wclk) disable iff(!wrst_n)
        (wen && !full) |-> (not ($isunknown(data_w))); 
    endproperty

    property fifo_read_check;
        @(posedge rclk) disable iff(!rrst_n)
        (ren && !empty) |=> (not ($isunknown(data_r))); 
    endproperty

    property write_full_check;
        @(posedge wclk) disable iff(!wrst_n)
        full |-> (!wen);
    endproperty

    property read_empty_check;
        @(posedge rclk) disable iff(!rrst_n)
        empty |-> (!ren);
    endproperty

    check_fifo_write: assert property (fifo_write_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d data_w exists X when writing!\n", ID);

    check_fifo_read: assert property (fifo_read_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d data_r exists X when reading!\n", ID);

    check_write_full: assert property (write_full_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d write attempted when FIFO is full!\n", ID);

    check_read_empty: assert property (read_empty_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d read attempted when FIFO is empty!\n", ID);

// FIFO Pointer Assertion

    property wptr_keep_check;
        @(posedge wclk) disable iff(!wrst_n)
        !wen |=> $stable(wr_ptr);
    endproperty

    property rptr_keep_check;
        @(posedge rclk) disable iff(!rrst_n)
        !ren |=> $stable(rd_ptr);
    endproperty

    property wptr_incr_check;
        @(posedge wclk) disable iff(!wrst_n)
        (wen && !full) |=> (wr_ptr == ($past(wr_ptr) + 1) % (2 * BUF_SIZE));
    endproperty

    property rptr_incr_check;
        @(posedge rclk) disable iff(!rrst_n)
        (ren && !empty) |=> (rd_ptr == ($past(rd_ptr) + 1) % (2 * BUF_SIZE));
    endproperty

    check_wptr_keep: assert property (wptr_keep_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d write pointer changed when wen is 0!\n", ID);

    check_rptr_keep: assert property (rptr_keep_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d read pointer changed when ren is 0!\n", ID);

    check_wptr_incr: assert property (wptr_incr_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d write pointer did not increase correctly!\n", ID);

    check_rptr_incr: assert property (rptr_incr_check) 
    else $error($stime, "\t\t FATAL: FIFO %0d read pointer did not increase correctly!\n", ID);

endmodule