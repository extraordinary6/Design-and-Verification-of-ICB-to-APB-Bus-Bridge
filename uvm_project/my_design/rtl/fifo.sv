`timescale 1ns/1ps
//=====================================================================
// Description:
// Template based design of asynchronous FIFO
// Designer : Huang Chaofan, extraordinary.h@sjtu.edu.cn
// Revision History:
// V0 date: 11.01 Initial version, Huang Chaofan
// ====================================================================

module fifo#(
    parameter BUF_SIZE = 16,
    parameter ADDR_SIZE = 4,    // ADDR_SIZE = log2(BUF_SIZE)
    parameter DATA_WIDTH = 64
)
(
    input logic                  wclk,
    input logic                  wrst_n,
    input logic                  wen,
    input logic [DATA_WIDTH-1:0] data_w,
    output logic                 full,
    output logic [ADDR_SIZE:0]   wr_ptr,      // for assertion
    output logic [ADDR_SIZE:0]   wr_ptr_g,    // for assertion
    output logic [ADDR_SIZE:0]   wr_ptr_gd2,  // for assertion

    input logic                  rclk,
    input logic                  rrst_n,
    input logic                  ren,
    output logic[DATA_WIDTH-1:0] data_r,
    output logic                 empty,
    output logic [ADDR_SIZE:0]   rd_ptr,     // for assertion
    output logic [ADDR_SIZE:0]   rd_ptr_g,   // for assertion
    output logic [ADDR_SIZE:0]   rd_ptr_gd2  // for assertion
);

// buffer
logic [DATA_WIDTH-1:0] buffer [BUF_SIZE-1:0];

// pointer
// logic [ADDR_SIZE:0] wr_ptr;  
// logic [ADDR_SIZE:0] rd_ptr;  

// gray code
// logic [ADDR_SIZE:0] wr_ptr_g;
// logic [ADDR_SIZE:0] rd_ptr_g;

// asynchronous delay logic
logic [ADDR_SIZE:0] wr_ptr_gd1;
logic [ADDR_SIZE:0] rd_ptr_gd1;
// logic [ADDR_SIZE:0] wr_ptr_gd2;
// logic [ADDR_SIZE:0] rd_ptr_gd2;


/* write pointer, binary -> gray, beat twice */
always_ff@(posedge wclk or negedge wrst_n)
begin
    if(!wrst_n)
        wr_ptr <= 0;
    else if(wen && !full)
        wr_ptr <= wr_ptr + 1;   
end

assign wr_ptr_g = wr_ptr ^ (wr_ptr >> 1'b1);

always_ff@(posedge rclk or negedge rrst_n)
begin
    if(!rrst_n)
        wr_ptr_gd1 <= 0;
    else
        wr_ptr_gd1 <= wr_ptr_g;   
end

always_ff@(posedge rclk or negedge rrst_n)
begin
    if(!rrst_n)
        wr_ptr_gd2 <= 0;
    else
        wr_ptr_gd2 <= wr_ptr_gd1;   
end

/* read pointer, binary -> gray, beat twice */
always_ff@(posedge rclk or negedge rrst_n)
begin
    if(!rrst_n)
        rd_ptr <= 0;
    else if(ren && !empty)
        rd_ptr <= rd_ptr + 1;   
end

assign rd_ptr_g = rd_ptr ^ (rd_ptr >> 1'b1);

always_ff@(posedge wclk or negedge wrst_n)
begin
    if(!wrst_n)
        rd_ptr_gd1 <= 0;
    else
        rd_ptr_gd1 <= rd_ptr_g;   
end

always_ff@(posedge wclk or negedge wrst_n)
begin
    if(!wrst_n)
        rd_ptr_gd2 <= 0;
    else
        rd_ptr_gd2 <= rd_ptr_gd1;   
end

/* Determination of Empty and Full Status */
assign full = (wr_ptr_g == {~rd_ptr_gd2[ADDR_SIZE:ADDR_SIZE-1], rd_ptr_gd2[ADDR_SIZE-2:0]}) ? 1 : 0;
assign empty = (rd_ptr_g == wr_ptr_gd2) ? 1 : 0;

/* write data into fifo */
int i; //loop variable
always_ff@(posedge wclk or negedge wrst_n)
begin
    if(!wrst_n)
    begin
        for(i = 0; i < BUF_SIZE; i = i + 1)
        begin
            buffer[i] <= 0;
        end
    end
    else if(wen && !full)
        buffer[wr_ptr[ADDR_SIZE-1:0]] <= data_w;
end

/* read data from fifo */
always_ff@(posedge rclk or negedge rrst_n) 
begin
    if(!rrst_n)
        data_r <= 0;
    else if(ren && !empty)
        data_r <= buffer[rd_ptr[ADDR_SIZE-1:0]];
end

endmodule