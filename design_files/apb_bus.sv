//===================================================================== 
/// Description: 
// the interface of apb
// Designer : sjl_519021910940@sjtu.edu.cn
// V0 date: 2024/10/23  Initial version, sjl_519021910940@sjtu.edu.cn
// V1 date: 2024/11/24  Add clocking blocks, extraordinary.h@sjtu.edu.cn
// V2 date: 2024/12/14  Adding "other" modport, extraordinary.h@sjtu.edu.cn
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

    // Mod ports
    modport slave(clocking slv_cb,
    output prdata,pready,
    input pwrite,psel,paddr,pwdata,penable,rst_n);

    modport master(output pwrite,psel,paddr,pwdata,penable,
    input prdata,pready,clk,rst_n);

    modport others (
        input    clk,
        input    rst_n,
        
        input    pwrite,
        input    psel,
        input    paddr,
        input    pwdata,
        input    penable,
        input    prdata,
        input    pready

    );

endinterface:apb_bus //apb    