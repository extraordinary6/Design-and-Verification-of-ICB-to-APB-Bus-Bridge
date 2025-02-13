`timescale 1ns/1ps
//=====================================================================
// Description:
// APB Master Module Based on State Machine
// Designer : Huang Chaofan, extraordinary.h@sjtu.edu.cn
// Revision History:
// V0 date: 11.03 Initial version, Huang Chaofan
// V1 date: 12.13 Second  version, Huang Chaofan, add the " `ifdef " for des
// ====================================================================
`define IDLE    0
`define SETUP   1
`define ACCESS  2

`define S0 6'b000001
`define S1 6'b000010
`define S2 6'b000100
`define S3 6'b001000

`include "cfig.svh"

module apb_master(
    
    // left ports
    input logic [63:0] control,               // apb master enbale signal from icb slave
    input logic        wfifo_empty,           // used to indicate the continuous data write or not
    input logic        rfifo_full,            
    input logic [31:0] wfifo_rdata,           // data input from WFIFO
    
    output logic       wfifo_ren,
    output logic       rfifo_wen,
    output logic [1:0] apb_state,             //0 is reset, 1 is free, 2 is read, 3 is write  
    output logic [31:0]rdata,                 // from apb slave to encrypt and rfifo
    output logic       rdata_vld,

    // right ports
    apb_bus.master apb_bus_0,
    apb_bus.master apb_bus_1,
    apb_bus.master apb_bus_2,
    apb_bus.master apb_bus_3
);

//state machine define
logic [1:0] state;
logic [1:0] next_state;

//register file
logic [31:0] wdata;
logic [31:0] addr;
logic [5:0] sel;
logic write;

logic valid_r; // valid input for wfifo


/* state machine */
always_ff@(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n)
begin
    if(!apb_bus_0.rst_n)
        state <= `IDLE;
    else if(control[0] == 0)    //apb master enable signal is low
        state <= `IDLE;
    else
        state <= next_state;
end

always_comb 
begin
    if(control == 0)
        next_state = `IDLE;
    else
    begin
        case(state)
        `IDLE:
            begin
                if(valid_r) 
                    next_state = `SETUP;
                else
                    next_state = `IDLE;
            end
        `SETUP:
            begin
                if(!valid_r)
                    next_state = `SETUP;      // changed on 12.13, debug for the mismatch speed between ICB and APB bus
                else
                    next_state = `ACCESS;
            end
        `ACCESS:
            begin
                if( (apb_bus_0.pready || apb_bus_1.pready || apb_bus_2.pready || apb_bus_3.pready) && valid_r)
                    next_state = `SETUP;
                else if( (apb_bus_0.pready || apb_bus_1.pready || apb_bus_2.pready || apb_bus_3.pready) && !valid_r)
                    next_state = `IDLE;
                else
                    next_state = `ACCESS;
            end
        default: next_state = `IDLE;
        endcase 
    end

end

/* Interactive signal with apb slave */

//read
always_ff@(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n)
begin
    if(!apb_bus_0.rst_n)
        rdata <= 0;
    else if(!write && state == `ACCESS && (apb_bus_0.pready || apb_bus_1.pready || apb_bus_2.pready || apb_bus_3.pready) )
    begin
        case(sel)
        `S0: rdata <= apb_bus_0.prdata;
        `S1: rdata <= apb_bus_1.prdata;
        `S2: rdata <= apb_bus_2.prdata;
        `S3: rdata <= apb_bus_3.prdata;
        default: rdata <= 0;
        endcase
    end
end

//slave 0
always_comb 
begin
    if((state == `SETUP || state == `ACCESS) && sel == `S0)
        apb_bus_0.psel = 1;
    else
        apb_bus_0.psel = 0;
end

always_comb 
begin
    if(state == `ACCESS && sel == `S0)
        apb_bus_0.penable = 1;
    else
        apb_bus_0.penable = 0;
end

assign apb_bus_0.pwrite = sel == `S0 ? write : 0;

assign apb_bus_0.paddr = sel == `S0 ? addr : 0;

always_comb 
begin
    if(sel == `S0 && state == `SETUP && valid_r && wfifo_rdata[0])
        apb_bus_0.pwdata = {1'b0, wfifo_rdata[31:1]};
    else if(sel == `S0 && state == `ACCESS && write)
        apb_bus_0.pwdata = wdata;
    else
        apb_bus_0.pwdata = 0;
end

//slave 1
always_comb 
begin
    if((state == `SETUP || state == `ACCESS) && sel == `S1)
        apb_bus_1.psel = 1;
    else
        apb_bus_1.psel = 0;
end

always_comb 
begin
    if(state == `ACCESS && sel == `S1)
        apb_bus_1.penable = 1;
    else
        apb_bus_1.penable = 0;
end

assign apb_bus_1.pwrite = sel == `S1 ? write : 0;

assign apb_bus_1.paddr = sel == `S1 ? addr : 0;

always_comb 
begin
    if(sel == `S1 && state == `SETUP && valid_r && wfifo_rdata[0])
        apb_bus_1.pwdata = {1'b0, wfifo_rdata[31:1]};
    else if(sel == `S1 && state == `ACCESS && write)
        apb_bus_1.pwdata = wdata;
    else
        apb_bus_1.pwdata = 0;
end

//slave 2
always_comb 
begin
    if((state == `SETUP || state == `ACCESS) && sel == `S2)
        apb_bus_2.psel = 1;
    else
        apb_bus_2.psel = 0;
end

always_comb 
begin
    if(state == `ACCESS && sel == `S2)
        apb_bus_2.penable = 1;
    else
        apb_bus_2.penable = 0;
end

assign apb_bus_2.pwrite = sel == `S2 ? write : 0;

assign apb_bus_2.paddr = sel == `S2 ? addr : 0;

always_comb 
begin
    if(sel == `S2 && state == `SETUP && valid_r && wfifo_rdata[0])
        apb_bus_2.pwdata = {1'b0, wfifo_rdata[31:1]};
    else if(sel == `S2 && state == `ACCESS && write)
        apb_bus_2.pwdata = wdata;
    else
        apb_bus_2.pwdata = 0;
end

//slave 3
always_comb 
begin
    if((state == `SETUP || state == `ACCESS) && sel == `S3)
        apb_bus_3.psel = 1;
    else
        apb_bus_3.psel = 0;
end

always_comb 
begin
    if(state == `ACCESS && sel == `S3)
        apb_bus_3.penable = 1;
    else
        apb_bus_3.penable = 0;
end

assign apb_bus_3.pwrite = sel == `S3 ? write : 0;

assign apb_bus_3.paddr = sel == `S3 ? addr : 0;

always_comb 
begin
    if(sel == `S3 && state == `SETUP && valid_r && wfifo_rdata[0])
        apb_bus_3.pwdata = {1'b0, wfifo_rdata[31:1]};
    else if(sel == `S3 && state == `ACCESS && write)
        apb_bus_3.pwdata = wdata;
    else
        apb_bus_3.pwdata = 0;
end


/* Interactive signal with fifo and codec*/

always_ff@(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n) 
begin
    if(!apb_bus_0.rst_n)
        wdata <= 0;
    else if(wfifo_rdata[0] && state == `SETUP && valid_r)
        wdata <= {1'b0, wfifo_rdata[31:1]};
end

always_ff@(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n)
begin
    if(!apb_bus_0.rst_n)
        write <= 0;
    else if(valid_r && !wfifo_rdata[0] && state == `IDLE || valid_r && !wfifo_rdata[0] && state == `ACCESS && 
                                                        (apb_bus_0.pready || apb_bus_1.pready || apb_bus_2.pready || apb_bus_3.pready))
        write <= wfifo_rdata[1];  
end

always_ff@(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n)
begin
    if(!apb_bus_0.rst_n)
        sel <= 6'b000000;
    else if(valid_r && !wfifo_rdata[0] && state == `IDLE || valid_r && !wfifo_rdata[0] && state == `ACCESS && 
                                                        (apb_bus_0.pready || apb_bus_1.pready || apb_bus_2.pready || apb_bus_3.pready))
        sel <= wfifo_rdata[7:2];  
end

always_ff@(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n)
begin
    if(!apb_bus_0.rst_n)
        addr <= 0;
    else if(valid_r && !wfifo_rdata[0] && state == `IDLE || valid_r && !wfifo_rdata[0] && state == `ACCESS && 
                                                        (apb_bus_0.pready || apb_bus_1.pready || apb_bus_2.pready || apb_bus_3.pready))
        addr <= {8'b0, wfifo_rdata[31:8]};  
end


// assign wfifo_ren =  wfifo_empty == 1 ? 0 : 1;
always_comb 
begin 
    if(control[0] == 0)
        wfifo_ren = 0;
    else
    begin
        if(wfifo_empty == 1) wfifo_ren = 0;
        else wfifo_ren = 1;
    end
end

`ifdef DES
    logic [3:0] cnt;
    logic start;

    always_ff @(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n) 
    begin
        if(!apb_bus_0.rst_n)
            start <= 0;
        else if(rdata_vld)
            start <= 1;
        else if(cnt == 15)
            start <= 0;
    end

    always_ff @(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n) 
    begin
        if(!apb_bus_0.rst_n)
            cnt <= 0;
        else if(start)
            cnt <= cnt + 1;
    end

    always_ff @(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n) 
    begin
        if(!apb_bus_0.rst_n)
            rfifo_wen <= 0;
        else if(cnt == 15)
            rfifo_wen <= 1;
        else
            rfifo_wen <= 0;
    end

`else
    always_ff@(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n)
    begin
        if(!apb_bus_0.rst_n)
            rfifo_wen <= 0;
        else if((apb_bus_0.pready || apb_bus_1.pready || apb_bus_2.pready || apb_bus_3.pready) && !rfifo_full && !write)
            rfifo_wen <= 1;
        else
            rfifo_wen <= 0;
    end
`endif

// add the rdata_vld, 12.13
always_ff@(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n)
begin
    if(!apb_bus_0.rst_n)
        rdata_vld <= 0;
    else if((apb_bus_0.pready || apb_bus_1.pready || apb_bus_2.pready || apb_bus_3.pready) && !rfifo_full && !write)
        rdata_vld <= 1;
    else
        rdata_vld <= 0;
end

always_comb
begin
    if(control[0] == 0)
        apb_state = 0;
    else if(state == `ACCESS || state == `SETUP)
        apb_state = write + 2;
    else
        apb_state = 1;
end

always_ff@(posedge apb_bus_0.clk or negedge apb_bus_0.rst_n)
begin
    if(!apb_bus_0.rst_n)
        valid_r <= 0;
    else if(!wfifo_empty && wfifo_ren)
        valid_r <= 1;
    else
        valid_r <= 0;
end
endmodule