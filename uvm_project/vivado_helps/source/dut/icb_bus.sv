//===================================================================== 
/// Description: 
// the interface of icb
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

interface icb_bus(input logic clk,input logic rst_n);
    //command channel
    logic icb_cmd_valid;
    logic icb_cmd_ready;
    logic [31:0] icb_cmd_addr;
    logic icb_cmd_read;
    logic [63:0] icb_cmd_wdata;
    logic [7:0] icb_cmd_wmask;

    //response channel
    logic icb_rsp_valid;
    logic icb_rsp_ready;
    logic [63:0] icb_rsp_rdata;
    logic icb_rsp_err;

    //clocking block
    clocking mst_cb @(posedge clk);
        default input #1ns output #1ns;

        output icb_cmd_valid;
        output icb_cmd_addr;
        output icb_cmd_read;
        output icb_cmd_wdata;
        output icb_cmd_wmask;
        output icb_rsp_ready;

        input icb_cmd_ready;
        input icb_rsp_valid;
        input icb_rsp_rdata;
        input icb_rsp_err;
    endclocking

    clocking mon_cb @(posedge clk);
        default input #1ns output #1ns;

        input icb_cmd_valid;
        input icb_cmd_addr;
        input icb_cmd_read;
        input icb_cmd_wdata;
        input icb_cmd_wmask;
        input icb_rsp_ready;

        input icb_cmd_ready;
        input icb_rsp_valid;
        input icb_rsp_rdata;
        input icb_rsp_err;
    endclocking

    // Mod ports
    
    modport slave(input icb_cmd_valid, icb_cmd_addr, icb_cmd_read, icb_cmd_wdata, icb_cmd_wmask, icb_rsp_ready, clk, rst_n,
    output icb_cmd_ready, icb_rsp_valid, icb_rsp_rdata, icb_rsp_err);
    
    modport master(clocking mst_cb, 
    output icb_cmd_valid, icb_cmd_addr, icb_cmd_read, icb_cmd_wdata, icb_cmd_wmask, icb_rsp_ready,
    input icb_cmd_ready, icb_rsp_valid, icb_rsp_rdata, icb_rsp_err, clk, rst_n);

    modport others (
        clocking mon_cb,
        input    clk,
        input    rst_n,
        
        input  icb_cmd_ready,
        input  icb_cmd_valid,
        input  icb_cmd_addr,
        input  icb_cmd_read,
        input  icb_cmd_wdata,
        input  icb_cmd_wmask,

        input  icb_rsp_ready,
        input  icb_rsp_valid,
        input  icb_rsp_rdata,
        input  icb_rsp_err
    );



endinterface:icb_bus //icb    