//===================================================================== 
/// Description: 
// the interface of apb
// Designer : sjl_519021910940@sjtu.edu.cn
// ==================================================================== 

/*
This is only the basic interface, you may change it by your own.
But don't change this signal discription.
*/

`timescale 1ns/1ps

interface apb_bus(input logic clk,input logic rst_n);
    logic pwrite;
    logic psel;
    logic [31:0] paddr;
    logic [31:0] pwdata;
    logic penable;

    logic [31:0] prdata;
    logic pready;

    clocking slv_cb @(posedge clk);
        default input #1ns output #1ns;

        input pwrite;
        input psel;
        input paddr;
        input pwdata;
        input penable;
        
        output prdata;
        output pready;
    endclocking

    modport slave(clocking slv_cb,
    output prdata,pready,
    input pwrite,psel,paddr,pwdata,penable,rst_n);

    modport master(output pwrite,psel,paddr,pwdata,penable,
    input prdata,pready,clk,rst_n);

endinterface:apb_bus //apb    