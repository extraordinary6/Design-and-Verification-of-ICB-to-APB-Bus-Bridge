//=====================================================================
// Description:
// This file realize assertion of XOR based DES ports
// Designer : extraordinary.h@sjtu.edu.cn
// Revision History
// V0 date:2024/12/15 Initial version, extraordinary.h@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

module des_assertion #(
    parameter ID = 0            // if ID = 0, codec is decrypt
                                // if ID = 1, codec is encrypt 
)
(
    input  logic         clk,
    input  logic         rst_n,
    input  logic [0:63]  data_i,
    input  logic         valid_i,
    input  logic [0:63]  key,

    input  logic [0:63]  data_o,
    input  logic         valid_o
);

// Valid_o Assertion
    property vldo_high_check;
        @(posedge clk) disable iff(!rst_n)
        valid_i |-> ##17 valid_o;
    endproperty

// Signals X Assertion
    property datai_no_x_check;
        @(posedge clk) disable iff(!rst_n)
        valid_i |-> (not ($isunknown(data_i)));
    endproperty

    property key_no_x_check;
        @(posedge clk) disable iff(!rst_n)
        valid_i |-> (not ($isunknown(key)));
    endproperty

    property datao_no_x_check;
        @(posedge clk) disable iff(!rst_n)
        valid_o |-> (not ($isunknown(data_o)));
    endproperty

// Signal Keep Assertion
    property key_keep_check;
        @(posedge clk) disable iff(!rst_n)
        $rose(valid_i) |-> ##[1:17] ($stable(key))
    endproperty
    
    check_vldo_high: assert property (vldo_high_check) 
    else $error($stime, "\t\t FATAL: codec %0d valid_o is not high when computation finished!\n", ID);
    check_datai_no_x: assert property (datai_no_x_check) 
    else $error($stime, "\t\t FATAL: codec %0d data_i exists X when valid_i is high!\n", ID);
    check_key_no_x: assert property (key_no_x_check) 
    else $error($stime, "\t\t FATAL: codec %0d key exists X when valid_i is high!\n", ID);
    check_datao_no_x: assert property (datao_no_x_check) 
    else $error($stime, "\t\t FATAL: codec %0d data_o exists X when valid_o is high!\n", ID);
    check_key_keep: assert property (key_keep_check) 
    else $error($stime, "\t\t FATAL: codec %0d key dosen't keep when computing!\n", ID);

    
endmodule


