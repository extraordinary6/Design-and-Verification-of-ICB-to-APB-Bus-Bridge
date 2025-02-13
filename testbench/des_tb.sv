`timescale 1ns/1ps
//=====================================================================
// Description:
// the testbench of DES based codec
// Designer : Huang Chaofan, extraordinary.h@sjtu.edu.cn
// Revision History:
// V0 date: 12.13 Initial version, Huang Chaofan
// ====================================================================

module des_tb;
    logic        clk;
    logic [63:0] data_i;
    logic        valid_i;
    logic [63:0] key;
    logic [63:0] data_o; 
    logic        valid_o;

    //clk
    always begin
        #5 clk = ~clk;
    end

    initial begin
        clk = 1'b0;
        valid_i <= 1'b0;
        #100;
        // data_i <= 64'b0110001101101111011011010111000001110101011101000110010101110010; //plaintext
        data_i <= 64'b0101100000001000001100000000101111001101110101100001100001101000;    //ciphertext
        valid_i <= 1'b1;
        key <=  64'b0001001100110100010101110111100110011011101111001101111111110001;
        #10;
        valid_i <= 1'b0;
    end


    codec_des #(
        .ENCRYPT(0)
    ) u_codec_des (
        .clk     (clk     ),
        .data_i  (data_i  ),
        .valid_i (valid_i ),
        .key     (key     ),
        .data_o  (data_o  ),
        .valid_o (valid_o )
    );


endmodule
