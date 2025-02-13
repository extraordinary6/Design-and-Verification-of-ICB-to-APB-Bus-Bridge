`timescale 1ns/1ps
//=====================================================================
// Description:
// ICB Slave Module
// Designer : Huang Chaofan, extraordinary.h@sjtu.edu.cn
// Revision History:
// V0 date: 10.31 Initial version, Huang Chaofan
// V1 date: 12.13 Second  version, Huang Chaofan, add the " `ifdef " for des
// ====================================================================
`define CONTROL_ADDR 32'h20000000
`define STATE_ADDR   32'h20000008
`define WDATA_ADDR   32'h20000010
`define RDATA_ADDR   32'h20000018
`define KEY_ADDR     32'h20000020

`include "cfig.svh"

module icb_slave(

    //left ports
    icb_bus.slave       icb_bus,

    //right ports
    input logic         wfifo_full,  
    input logic         rfifo_empty,
    input logic [1:0]   apb_state,  //0 is reset, 1 is free, 2 is read, 3 is write  
    input logic [63:0]  rfifo_rdata,

    output logic        wfifo_wen,
    output logic        rfifo_ren,        

    output logic [63:0] control,   //write or read, APB enable signal
    output logic [63:0] wdata,     //write or read, OUTPUT for decrypt
    output logic [63:0] key,       //write or read, OUTPUT for decrypt and encrypt

    output logic        wdata_vld
);

// register file 
logic [63:0] state;     //read only for icb, state = {60'b0, wfifo_full, rfifo_empty, apb_state}

logic [63:0] rdata;     //read only for icb, INPUT from RFIFO 

logic valid_r;         // valid input for rfifo

logic [63:0] masked_wdata;
/* 
Interactive signal with icb master 
*/
always_ff@(posedge icb_bus.clk or negedge icb_bus.rst_n)
begin
    if(!icb_bus.rst_n)
        valid_r <= 0;
    else if(rfifo_ren && !rfifo_empty)
        valid_r <= 1;
    else
        valid_r <= 0;
end

always_comb 
begin
    if( icb_bus.icb_cmd_read && valid_r)
        icb_bus.icb_cmd_ready = valid_r;
    else if(icb_bus.icb_cmd_valid && icb_bus.icb_cmd_read && icb_bus.icb_cmd_addr != `RDATA_ADDR)
        icb_bus.icb_cmd_ready = 1;
    else if(icb_bus.icb_cmd_valid && ~icb_bus.icb_cmd_read && icb_bus.icb_cmd_addr == `WDATA_ADDR && ~wfifo_full)
        icb_bus.icb_cmd_ready = 1;
    else if(icb_bus.icb_cmd_valid && ~icb_bus.icb_cmd_read && icb_bus.icb_cmd_addr != `WDATA_ADDR )
        icb_bus.icb_cmd_ready = 1;
    else
        icb_bus.icb_cmd_ready = 0;
end

//icb_rsp_valid need control signal of fifo

always_ff@(posedge icb_bus.clk or negedge icb_bus.rst_n)
begin
    if(!icb_bus.rst_n)
        icb_bus.icb_rsp_valid <= 0;
    else if(icb_bus.icb_cmd_read &&  icb_bus.icb_cmd_ready)
        icb_bus.icb_rsp_valid <= 1;
    else if(~icb_bus.icb_cmd_read && icb_bus.icb_cmd_valid && icb_bus.icb_cmd_ready)
        icb_bus.icb_rsp_valid <= 1;
    else
        icb_bus.icb_rsp_valid <= 0;
end

//try to visit registers which are read only, icb_rsp_err = 1, else 0
always_comb 
begin 
    if(icb_bus.icb_cmd_addr == `STATE_ADDR && ~icb_bus.icb_cmd_read)
        icb_bus.icb_rsp_err = 1'b1;
    else if(icb_bus.icb_cmd_addr == `RDATA_ADDR && ~icb_bus.icb_cmd_read)
        icb_bus.icb_rsp_err = 1'b1;
    else
        icb_bus.icb_rsp_err = 0;
end

//read data
always_ff@(posedge icb_bus.clk or negedge icb_bus.rst_n)
begin
    if(!icb_bus.rst_n)
        icb_bus.icb_rsp_rdata <= 0;
    else if(valid_r)
        icb_bus.icb_rsp_rdata <= rdata;
    else if(icb_bus.icb_cmd_ready && icb_bus.icb_cmd_read)
    begin
        case(icb_bus.icb_cmd_addr)
            `CONTROL_ADDR: icb_bus.icb_rsp_rdata <= control;
		    `STATE_ADDR:   icb_bus.icb_rsp_rdata <= state;
		    `WDATA_ADDR:   icb_bus.icb_rsp_rdata <= wdata;
		    `RDATA_ADDR:   icb_bus.icb_rsp_rdata <= rdata;
            `KEY_ADDR:     icb_bus.icb_rsp_rdata <= key;
            default:       icb_bus.icb_rsp_rdata <= 0;
        endcase
    end
end

//write data

//mask
always_comb 
begin
    for(int i = 0; i < 8; i ++)
    begin
        masked_wdata[i*8 +: 8] = icb_bus.icb_cmd_wdata[i*8 +: 8] & {8{~icb_bus.icb_cmd_wmask[i]}};
    end
end

//control
always_ff@(posedge icb_bus.clk or negedge icb_bus.rst_n)
begin
    if(!icb_bus.rst_n)
        control <= 0;
    else if(icb_bus.icb_cmd_valid && icb_bus.icb_cmd_ready && icb_bus.icb_cmd_addr == `CONTROL_ADDR && ~icb_bus.icb_cmd_read)
		control <= masked_wdata;
end

//wdata
always_ff@(posedge icb_bus.clk or negedge icb_bus.rst_n)
begin
    if(!icb_bus.rst_n)
        wdata <= 0;
    else if(icb_bus.icb_cmd_valid && icb_bus.icb_cmd_ready && icb_bus.icb_cmd_addr == `WDATA_ADDR && ~icb_bus.icb_cmd_read && ~wfifo_full)
		wdata <= masked_wdata;
end

// add the wdata_vld, 12.13
always_ff@(posedge icb_bus.clk or negedge icb_bus.rst_n)
begin
    if(!icb_bus.rst_n)
        wdata_vld <= 0;
    else if(icb_bus.icb_cmd_valid && icb_bus.icb_cmd_ready && icb_bus.icb_cmd_addr == `WDATA_ADDR && ~icb_bus.icb_cmd_read && ~wfifo_full)
		wdata_vld <= 1;
    else
        wdata_vld <= 0;
end

//key
always_ff@(posedge icb_bus.clk or negedge icb_bus.rst_n)
begin
    if(!icb_bus.rst_n)
        key <= 0;
    else if(icb_bus.icb_cmd_valid && icb_bus.icb_cmd_ready && icb_bus.icb_cmd_addr == `KEY_ADDR && ~icb_bus.icb_cmd_read)
		key <= masked_wdata;
end


/* 
Interactive signal with FIFO and codec
*/

//wfifo_wen
`ifdef DES
    logic [3:0] cnt;
    logic start;

    always_ff @(posedge icb_bus.clk or negedge icb_bus.rst_n) 
    begin
        if(!icb_bus.rst_n)
            start <= 0;
        else if(wdata_vld)
            start <= 1;
        else if(cnt == 15)
            start <= 0;
    end

    always_ff @(posedge icb_bus.clk or negedge icb_bus.rst_n) 
    begin
        if(!icb_bus.rst_n)
            cnt <= 0;
        else if(start)
            cnt <= cnt + 1;
    end

    always_ff @(posedge icb_bus.clk or negedge icb_bus.rst_n) 
    begin
        if(!icb_bus.rst_n)
            wfifo_wen <= 0;
        else if(cnt == 15)
            wfifo_wen <= 1;
        else
            wfifo_wen <= 0;
    end

`else
    always_ff@(posedge icb_bus.clk or negedge icb_bus.rst_n)
    begin
        if(!icb_bus.rst_n)
            wfifo_wen <= 0;
        else if(icb_bus.icb_cmd_valid && icb_bus.icb_cmd_ready && icb_bus.icb_cmd_addr == `WDATA_ADDR && ~icb_bus.icb_cmd_read && ~wfifo_full)
            wfifo_wen <= 1;
        else 
            wfifo_wen <= 0;
    end
`endif
//rfifo_ren
always_comb
begin

    if(icb_bus.icb_cmd_valid  && icb_bus.icb_cmd_addr == `RDATA_ADDR && icb_bus.icb_cmd_read && ~rfifo_empty)
        rfifo_ren <= 1; 
    else 
        rfifo_ren <= 0;
end

//state
// always_ff@(posedge icb_bus.clk or negedge icb_bus.rst_n)
// begin
//     if(!icb_bus.rst_n)
// 	    state <= 0;
//     else
//         state <= {60'b0, wfifo_full, rfifo_empty, apb_state};
// end

assign state = {60'b0, wfifo_full, rfifo_empty, apb_state};

//rdata
// always_comb
// begin
//     if(rfifo_empty == 0)
//         rdata = rfifo_rdata;
//     else
//         rdata = 0;
// end

assign rdata = rfifo_rdata;

endmodule