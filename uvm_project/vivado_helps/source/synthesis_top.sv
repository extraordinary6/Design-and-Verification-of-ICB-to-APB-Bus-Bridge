module synthesis_top (

    //clock and reset
    input clk,
    input rst_n,
    // input bus
    input icb_cmd_valid,
    output icb_cmd_ready,
    input [63:0] icb_cmd_addr,
    input icb_cmd_read,
    input [63:0] icb_cmd_wdata,
    input [7:0] icb_cmd_wmask,
    output icb_rsp_valid,
    input icb_rsp_ready,
    output [63:0] icb_rsp_rdata,
    output icb_rsp_err,

    // output bus 0
    output pwrite_0,
    output psel_0,
    output [31:0] paddr_0,
    output [31:0] pwdata_0,
    output penable_0,

    input [31:0] prdata_0,
    input pready_0,

    //output bus 1
    output pwrite_1,
    output psel_1,
    output [31:0] paddr_1,
    output [31:0] pwdata_1,
    output penable_1,

    input [31:0] prdata_1,
    input pready_1,

    //output bus 2
    output pwrite_2,
    output psel_2,
    output [31:0] paddr_2,
    output [31:0] pwdata_2,
    output penable_2,

    input [31:0] prdata_2,
    input pready_2,

    //output bus 3
    output pwrite_3,
    output psel_3,
    output [31:0] paddr_3,
    output [31:0] pwdata_3,
    output penable_3,

    input [31:0] prdata_3,
    input pready_3

);


icb_bus icb_bus(clk,rst_n);
apb_bus apb_bus_0(clk,rst_n);
apb_bus apb_bus_1(clk,rst_n);
apb_bus apb_bus_2(clk,rst_n);
apb_bus apb_bus_3(clk,rst_n);


assign icb_bus.icb_cmd_valid = icb_cmd_valid;
assign icb_cmd_ready = icb_bus.icb_cmd_ready;
assign icb_bus.icb_cmd_addr = icb_cmd_addr;
assign icb_bus.icb_cmd_read = icb_cmd_read;
assign icb_bus.icb_cmd_wdata = icb_cmd_wdata;
assign icb_bus.icb_cmd_wmask = icb_cmd_wmask;
assign icb_rsp_valid = icb_bus.icb_rsp_valid;
assign icb_bus.icb_rsp_ready = icb_rsp_ready;
assign icb_rsp_rdata = icb_bus.icb_rsp_rdata;
assign icb_rsp_err = icb_bus.icb_rsp_err;


assign pwrite_0 = apb_bus_0.pwrite;
assign psel_0 = apb_bus_0.psel;
assign paddr_0 = apb_bus_0.paddr;
assign pwdata_0 = apb_bus_0.pwdata;
assign penable_0 = apb_bus_0.penable;
assign apb_bus_0.prdata = prdata_0;
assign apb_bus_0.pready = pready_0;

assign pwrite_1 = apb_bus_1.pwrite;
assign psel_1 = apb_bus_1.psel;
assign paddr_1 = apb_bus_1.paddr;
assign pwdata_1 = apb_bus_1.pwdata;
assign penable_1 = apb_bus_1.penable;
assign apb_bus_1.prdata = prdata_1;
assign apb_bus_1.pready = pready_1;

assign pwrite_2 = apb_bus_2.pwrite;
assign psel_2 = apb_bus_2.psel;
assign paddr_2 = apb_bus_2.paddr;
assign pwdata_2 = apb_bus_2.pwdata;
assign penable_2 = apb_bus_2.penable;
assign apb_bus_2.prdata = prdata_2;
assign apb_bus_2.pready = pready_2;

assign pwrite_3 = apb_bus_3.pwrite;
assign psel_3 = apb_bus_3.psel;
assign paddr_3 = apb_bus_3.paddr;
assign pwdata_3 = apb_bus_3.pwdata;
assign penable_3 = apb_bus_3.penable;
assign apb_bus_3.prdata = prdata_3;
assign apb_bus_3.pready = pready_3;

dut_top dut_top(
    icb_bus,
    apb_bus_0,
    apb_bus_1,
    apb_bus_2,
    apb_bus_3
);




endmodule