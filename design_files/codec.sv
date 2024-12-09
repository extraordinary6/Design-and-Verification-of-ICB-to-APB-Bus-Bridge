`timescale 1ns/1ps
//=====================================================================
// Description:
// XOR based codec
// Designer : Huang Chaofan, extraordinary.h@sjtu.edu.cn
// Revision History:
// V0 date: 11.03 Initial version, Huang Chaofan
// ====================================================================

module codec(
    input [63:0] data_i,
    input [63:0] key,
    output[63:0] data_o
);

assign data_o = data_i ^ key;

endmodule
