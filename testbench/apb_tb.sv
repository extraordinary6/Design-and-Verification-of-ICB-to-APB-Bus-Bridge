`timescale 1ns/1ps
//=====================================================================
// Description:
// The Testbench for APB Master Module
// Designer : Huang Chaofan, extraordinary.h@sjtu.edu.cn
// Revision History:
// V0 date: 11.11 Initial version, Huang Chaofan
// ====================================================================

module apb_tb;


logic clk;
logic rst_n;

apb_bus apb_bus_0(clk, rst_n);
apb_bus apb_bus_1(clk, rst_n);
apb_bus apb_bus_2(clk, rst_n);
apb_bus apb_bus_3(clk, rst_n);

logic [63:0] control;
logic wfifo_empty;
logic rfifo_full;
logic [31:0] wfifo_rdata;

logic wfifo_ren;
logic rfifo_wen;
logic [1:0] apb_state;
logic [31:0] rdata;


apb_master u_apb_master(
    .control     (control     ),
    .wfifo_empty (wfifo_empty ),
    .rfifo_full  (rfifo_full  ),
    .wfifo_rdata (wfifo_rdata ),
    .wfifo_ren   (wfifo_ren   ),
    .rfifo_wen   (rfifo_wen   ),
    .apb_state   (apb_state   ),
    .rdata       (rdata       ),
    .apb_bus_0   (apb_bus_0   ),
    .apb_bus_1   (apb_bus_1   ),
    .apb_bus_2   (apb_bus_2   ),
    .apb_bus_3   (apb_bus_3   )
);



// just test the apb_slave0
initial begin
    rst_n <= 0;
    clk <= 1;
    apb_bus_0.prdata <= 0;
    apb_bus_0.pready <= 0;
    apb_bus_1.prdata <= 0;
    apb_bus_1.pready <= 0;
    control <= 0;
    wfifo_empty <= 1;
    rfifo_full <= 0;
    wfifo_rdata <= 0;

    #15
    rst_n <= 1;
    // test the write control and data

    
    #5
    control <= 64'h1;    //enable signal

    #10
    wfifo_empty <= 0;

    #10
    wfifo_rdata <= {24'h000001, 8'b00000110};  //control write
    
    #10
    wfifo_rdata <= {31'h8, 1'b1};  //data

    #10
    apb_bus_0.pready <= 1;
    wfifo_rdata <= {24'h000002, 8'b00001010};  //control write

    #10
    apb_bus_0.pready <= 0;
    wfifo_rdata <= {31'h7, 1'b1};  //data


    #10
    apb_bus_1.pready <= 1;
    wfifo_rdata <= {24'h000003, 8'b00000100};  //control  read
    wfifo_empty <= 1;

    #10
    apb_bus_1.pready <= 0;

    #10
    apb_bus_0.pready <= 1;
    apb_bus_0.prdata <= 32'h6;

    #10
    apb_bus_0.pready <= 0;




    
    
end

always #5 clk = ~clk;

endmodule