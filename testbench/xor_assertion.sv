//=====================================================================
// Description:
// This file realize assertion of XOR based CODEC ports
// Designer : extraordinary.h@sjtu.edu.cn
// Revision History
// V0 date:2024/12/15 Initial version, extraordinary.h@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

module xor_assertion #(
    parameter ID = 0            // if ID = 0, codec is decrypt
                                // if ID = 1, codec is encrypt 
)
(
    input        clk,
    input        rst_n,
    input [63:0] data_i,
    input [63:0] key,
    input [63:0] data_o
);

    property xor_correct_check;
        @(posedge clk) disable iff(!rst_n)
        ( (!($isunknown(data_i))) && (!($isunknown(key))) ) |-> (data_o == (data_i ^ key));
    endproperty

    check_xor_correct: assert property (xor_correct_check) 
    else $error($stime, "\t\t FATAL: codec %0d encoding error!\n", ID);

endmodule