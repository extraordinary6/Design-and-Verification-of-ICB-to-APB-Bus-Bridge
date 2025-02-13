`timescale 1ns/1ps
//=====================================================================
// Description:
// The Testbench for ICB Slave Module
// Designer : Huang Chaofan, extraordinary.h@sjtu.edu.cn
// Revision History:
// V0 date: 11.9 Initial version, Huang Chaofan
// ====================================================================

module icb_tb;

logic clk;
logic rst_n;

icb_bus ibus(clk, rst_n);

logic wfifo_full;
logic rfifo_empty;
logic [1:0] apb_state;
logic [63:0] rfifo_rdata;
logic wfifo_wen;
logic rfifo_ren;
logic [63:0] control;
logic [63:0] wdata;
logic [63:0] key;

icb_slave u_icb_slave(
    .icb_bus     (ibus        ),
    .wfifo_full  (wfifo_full  ),
    .rfifo_empty (rfifo_empty ),
    .apb_state   (apb_state   ),
    .rfifo_rdata (rfifo_rdata ),
    .wfifo_wen   (wfifo_wen   ),
    .rfifo_ren   (rfifo_ren   ),
    .control     (control     ),
    .wdata       (wdata       ),
    .key         (key         )
);

initial begin
    rst_n <= 0;
    clk <= 1;
    ibus.icb_cmd_valid <= 0;
    ibus.icb_cmd_addr <= 0;
    ibus.icb_cmd_read <= 1;
    ibus.icb_cmd_wdata <= 0;
    ibus.icb_cmd_wmask <= 0;
    // ibus.icb_rsp_ready = 0;

    wfifo_full <= 0;
    rfifo_empty <= 1;
    rfifo_rdata <= 0;
    apb_state <= 2;

    #15
    rst_n <= 1;
    
    // test the write wdata Continuously
    #5
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000010;
    ibus.icb_cmd_read <= 0;
    ibus.icb_cmd_wdata <= 64'h1;

    #10
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000010;
    ibus.icb_cmd_read <= 0;
    ibus.icb_cmd_wdata <= 64'h2;

    #10
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000010;
    ibus.icb_cmd_read <= 0;
    ibus.icb_cmd_wdata <= 64'h3;

    #10
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000010;
    ibus.icb_cmd_read <= 0;
    ibus.icb_cmd_wdata <= 64'h4;
    
    #10
    ibus.icb_cmd_valid <= 0;
    ibus.icb_cmd_addr <= 32'h0;
    ibus.icb_cmd_read <= 1;
    ibus.icb_cmd_wdata <= 64'h0;

    
    // write wdata when wfifo is full
    #90
    wfifo_full <= 1;

    #10
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000010;
    ibus.icb_cmd_read <= 0;
    ibus.icb_cmd_wdata <= 64'h2;

    #10
    wfifo_full <= 0;
    #10
    ibus.icb_cmd_valid <= 0;
    ibus.icb_cmd_addr <= 32'h0;
    ibus.icb_cmd_read <= 1;
    ibus.icb_cmd_wdata <= 64'h0;

    // test the read rdata
    #100
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000018;
    ibus.icb_cmd_read <= 1;

    #50
    rfifo_empty <= 0;

    #10
    rfifo_empty <= 1;
    rfifo_rdata <= 64'h3;


    #10
    ibus.icb_cmd_valid <= 0;
    ibus.icb_cmd_addr <= 32'h0;
    ibus.icb_cmd_read <= 1;

    // test the read Continuously
    #90
    rfifo_empty <= 0;

    #10
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000018;
    ibus.icb_cmd_read <= 1;

    #10
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000018;
    ibus.icb_cmd_read <= 1;
    rfifo_rdata <= 64'h5;

    #10
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000018;
    ibus.icb_cmd_read <= 1;
    rfifo_rdata <= 64'h6;

    #10
    ibus.icb_cmd_valid <= 1;
    ibus.icb_cmd_addr <= 32'h20000018;
    ibus.icb_cmd_read <= 1;
    rfifo_rdata <= 64'h7;

    #10
    rfifo_rdata <= 64'h8;
    rfifo_empty <= 1;
    ibus.icb_cmd_valid <= 0;
    ibus.icb_cmd_addr <= 32'h0;
    ibus.icb_cmd_read <= 1;

end


always #5 clk = ~clk;

assign ibus.icb_rsp_ready = ibus.icb_rsp_valid; 


endmodule