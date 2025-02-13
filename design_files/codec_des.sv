`timescale 1ns/1ps
//=====================================================================
// Description:
// DES based codec
// Designer : Huang Chaofan, extraordinary.h@sjtu.edu.cn
// Revision History:
// V0 date: 12.13 Initial version, Huang Chaofan
// ====================================================================

module codec_des#(
    parameter ENCRYPT = 1
)
(
    input  logic         clk,
    input  logic         rst_n,
    input  logic [0:63]  data_i,
    input  logic         valid_i,
    input  logic [0:63]  key,

    output logic [0:63]  data_o,
    output logic         valid_o

);
    // about the key define
    logic [0:55] key_init;        // initial 56bit key
    logic [0:27] key_set_c;       // left  28bit
    logic [0:27] key_set_d;       // right 28bit
    logic [0:55] key_merge;       // re-merge
    // logic [0:47] key_sub;         // sub key
    logic [0:47] key_sub [0:15];  // sub key

    // counter define
    logic [0:3]  round;           // count for the round
    logic        start;           // the symbol of the compute is running

    // sbox define
    logic [0:3] s_box1 [0:3][0:15];
    logic [0:3] s_box2 [0:3][0:15];
    logic [0:3] s_box3 [0:3][0:15];
    logic [0:3] s_box4 [0:3][0:15];
    logic [0:3] s_box5 [0:3][0:15];
    logic [0:3] s_box6 [0:3][0:15];
    logic [0:3] s_box7 [0:3][0:15];
    logic [0:3] s_box8 [0:3][0:15];

    // about the data define
    logic [0:63] data_init;       // the initial replacement of data_i or the input of every round
    logic [0:63] data_f;          // the output of the final round

    
    // the control signal
    always_ff @(posedge clk or negedge rst_n) 
    begin 
        if(!rst_n)
            start <= 0;
        else if(valid_i)
            start <= 1;
        else if(round == 15)
            start <= 0;
    end

    always_ff @(posedge clk or negedge rst_n)
    begin
        if(!rst_n)
            round <= 0;
        else if(valid_i)
            round <= 0;
        else if(start)
            round <= round + 1;
    end

    always_ff @(posedge clk or negedge rst_n)
    begin
        if(!rst_n)
            valid_o <= 0;
        else if(round == 15)
            valid_o <= 1;
        else
            valid_o <= 0;
    end

    // compute the subkey
    assign key_init = {
    key[56], key[48], key[40], key[32], key[24], key[16], key[8], key[0],  key[57], key[49], key[41], key[33], key[25], key[17],
    key[9],  key[1],  key[58], key[50], key[42], key[34], key[26], key[18], key[10], key[2],  key[59], key[51], key[43], key[35],
    key[62], key[54], key[46], key[38], key[30], key[22], key[14], key[6],  key[61], key[53], key[45], key[37], key[29], key[21],
    key[13], key[5],  key[60], key[52], key[44], key[36], key[28], key[20], key[12], key[4],  key[27], key[19], key[11], key[3]
    };

    // always_ff @(posedge clk) 
    // begin 
    //     if(valid_i)
    //         key_set_c <= {key_init[1:27], key_init[0]};
    //     else if(start)
    //     begin
    //         if(round == 0 || round == 7 || round == 14)
    //             key_set_c <= {key_set_c[1:27], key_set_c[0]};
    //         else
    //             key_set_c <= {key_set_c[2:27], key_set_c[0:1]};
    //     end 
    // end

    // always_ff @(posedge clk) 
    // begin 
    //     if(valid_i)
    //         key_set_d <= {key_init[29:55], key_init[28]};
    //     else if(start)
    //     begin
    //         if(round == 0 || round == 7 || round == 14)
    //             key_set_d <= {key_set_d[1:27], key_set_d[0]};
    //         else
    //             key_set_d <= {key_set_d[2:27], key_set_d[0:1]};
    //     end 
    // end

    // assign key_merge = {key_set_c, key_set_d};

    // assign key_sub = {
    // key_merge[13], key_merge[16], key_merge[10], key_merge[23], key_merge[0],  key_merge[4],  key_merge[2],  key_merge[27],
    // key_merge[14], key_merge[5],  key_merge[20], key_merge[9],  key_merge[22], key_merge[18], key_merge[11], key_merge[3],
    // key_merge[25], key_merge[7],  key_merge[15], key_merge[6],  key_merge[26], key_merge[19], key_merge[12], key_merge[1],
    // key_merge[40], key_merge[51], key_merge[30], key_merge[36], key_merge[46], key_merge[54], key_merge[29], key_merge[39],
    // key_merge[50], key_merge[44], key_merge[32], key_merge[47], key_merge[43], key_merge[48], key_merge[38], key_merge[55],
    // key_merge[33], key_merge[52], key_merge[45], key_merge[41], key_merge[49], key_merge[35], key_merge[28], key_merge[31]
    // };

    always_comb 
    begin
        for(int i = 0; i < 16; i = i + 1)
        begin
            if(i == 0)
            begin
                key_set_c = {key_init[1:27], key_init[0]};
                key_set_d = {key_init[29:55], key_init[28]};
            end
            else if(i == 1 || i == 8 || i == 15)
            begin
                key_set_c = {key_set_c[1:27], key_set_c[0]};
                key_set_d = {key_set_d[1:27], key_set_d[0]};
            end
            else
            begin
                key_set_c = {key_set_c[2:27], key_set_c[0:1]};
                key_set_d = {key_set_d[2:27], key_set_d[0:1]};
            end

            key_merge = {key_set_c, key_set_d};
            key_sub[i] = {
                        key_merge[13], key_merge[16], key_merge[10], key_merge[23], key_merge[0],  key_merge[4],  key_merge[2],  key_merge[27],
                        key_merge[14], key_merge[5],  key_merge[20], key_merge[9],  key_merge[22], key_merge[18], key_merge[11], key_merge[3],
                        key_merge[25], key_merge[7],  key_merge[15], key_merge[6],  key_merge[26], key_merge[19], key_merge[12], key_merge[1],
                        key_merge[40], key_merge[51], key_merge[30], key_merge[36], key_merge[46], key_merge[54], key_merge[29], key_merge[39],
                        key_merge[50], key_merge[44], key_merge[32], key_merge[47], key_merge[43], key_merge[48], key_merge[38], key_merge[55],
                        key_merge[33], key_merge[52], key_merge[45], key_merge[41], key_merge[49], key_merge[35], key_merge[28], key_merge[31]
                    };
        end
    end

    // data replacement
    always_ff @(posedge clk or negedge rst_n) 
    begin
        if(!rst_n)
            data_init <= 0;
        else if(valid_i)
            data_init <= {  data_i[57], data_i[49], data_i[41], data_i[33], data_i[25], data_i[17], data_i[9],  data_i[1],
                            data_i[59], data_i[51], data_i[43], data_i[35], data_i[27], data_i[19], data_i[11], data_i[3],
                            data_i[61], data_i[53], data_i[45], data_i[37], data_i[29], data_i[21], data_i[13], data_i[5],
                            data_i[63], data_i[55], data_i[47], data_i[39], data_i[31], data_i[23], data_i[15], data_i[7],
                            data_i[56], data_i[48], data_i[40], data_i[32], data_i[24], data_i[16], data_i[8],  data_i[0],
                            data_i[58], data_i[50], data_i[42], data_i[34], data_i[26], data_i[18], data_i[10], data_i[2],
                            data_i[60], data_i[52], data_i[44], data_i[36], data_i[28], data_i[20], data_i[12], data_i[4],
                            data_i[62], data_i[54], data_i[46], data_i[38], data_i[30], data_i[22], data_i[14], data_i[6]
                         };
        else if(start)
        begin
            if(ENCRYPT)
                data_init <= des(data_init, key_sub[round]);
            else
                data_init <= des(data_init, key_sub[15-round]);
        end
    end

    // final replacement
    assign data_f = {data_init[32:63], data_init[0:31]};   // the final round don't need change the left and the right

    assign data_o = {
                        data_f[39], data_f[7],  data_f[47], data_f[15], data_f[55], data_f[23], data_f[63], data_f[31],
                        data_f[38], data_f[6],  data_f[46], data_f[14], data_f[54], data_f[22], data_f[62], data_f[30],
                        data_f[37], data_f[5],  data_f[45], data_f[13], data_f[53], data_f[21], data_f[61], data_f[29],
                        data_f[36], data_f[4],  data_f[44], data_f[12], data_f[52], data_f[20], data_f[60], data_f[28],
                        data_f[35], data_f[3],  data_f[43], data_f[11], data_f[51], data_f[19], data_f[59], data_f[27],
                        data_f[34], data_f[2],  data_f[42], data_f[10], data_f[50], data_f[18], data_f[58], data_f[26],
                        data_f[33], data_f[1],  data_f[41], data_f[9],  data_f[49], data_f[17], data_f[57], data_f[25],
                        data_f[32], data_f[0],  data_f[40], data_f[8],  data_f[48], data_f[16], data_f[56], data_f[24]
                    };


    // s-box assignment 
    assign s_box1 = '{
        {4'd14, 4'd4, 4'd13, 4'd1, 4'd2, 4'd15, 4'd11, 4'd8, 4'd3, 4'd10, 4'd6, 4'd12, 4'd5, 4'd9, 4'd0, 4'd7},
        {4'd0, 4'd15, 4'd7, 4'd4, 4'd14, 4'd2, 4'd13, 4'd1, 4'd10, 4'd6, 4'd12, 4'd11, 4'd9, 4'd5, 4'd3, 4'd8},
        {4'd4, 4'd1, 4'd14, 4'd8, 4'd13, 4'd6, 4'd2, 4'd11, 4'd15, 4'd12, 4'd9, 4'd7, 4'd3, 4'd10, 4'd5, 4'd0},
        {4'd15, 4'd12, 4'd8, 4'd2, 4'd4, 4'd9, 4'd1, 4'd7, 4'd5, 4'd11, 4'd3, 4'd14, 4'd10, 4'd0, 4'd6, 4'd13}
    };

    assign s_box2 = '{
        {4'd15, 4'd1, 4'd8, 4'd14, 4'd6, 4'd11, 4'd3, 4'd4, 4'd9, 4'd7, 4'd2, 4'd13, 4'd12, 4'd0, 4'd5, 4'd10},
        {4'd3, 4'd13, 4'd4, 4'd7, 4'd15, 4'd2, 4'd8, 4'd14, 4'd12, 4'd0, 4'd1, 4'd10, 4'd6, 4'd9, 4'd11, 4'd5},
        {4'd0, 4'd14, 4'd7, 4'd11, 4'd10, 4'd4, 4'd13, 4'd1, 4'd5, 4'd8, 4'd12, 4'd6, 4'd9, 4'd3, 4'd2, 4'd15},
        {4'd13, 4'd8, 4'd10, 4'd1, 4'd3, 4'd15, 4'd4, 4'd2, 4'd11, 4'd6, 4'd7, 4'd12, 4'd0, 4'd5, 4'd14, 4'd9}
    };

    assign s_box3 = '{
        {4'd10, 4'd0, 4'd9, 4'd14, 4'd6, 4'd3, 4'd15, 4'd5, 4'd1, 4'd13, 4'd12, 4'd7, 4'd11, 4'd4, 4'd2, 4'd8},
        {4'd13, 4'd7, 4'd0, 4'd9, 4'd3, 4'd4, 4'd6, 4'd10, 4'd2, 4'd8, 4'd5, 4'd14, 4'd12, 4'd11, 4'd15, 4'd1},
        {4'd13, 4'd6, 4'd4, 4'd9, 4'd8, 4'd15, 4'd3, 4'd0, 4'd11, 4'd1, 4'd2, 4'd12, 4'd5, 4'd10, 4'd14, 4'd7},
        {4'd1, 4'd10, 4'd13, 4'd0, 4'd6, 4'd9, 4'd8, 4'd7, 4'd4, 4'd15, 4'd14, 4'd3, 4'd11, 4'd5, 4'd2, 4'd12}
    };

    assign s_box4 = '{
        {4'd7, 4'd13, 4'd14, 4'd3, 4'd0, 4'd6, 4'd9, 4'd10, 4'd1, 4'd2, 4'd8, 4'd5, 4'd11, 4'd12, 4'd4, 4'd15},
        {4'd13, 4'd8, 4'd11, 4'd5, 4'd6, 4'd15, 4'd0, 4'd3, 4'd4, 4'd7, 4'd2, 4'd12, 4'd1, 4'd10, 4'd14, 4'd9},
        {4'd10, 4'd6, 4'd9, 4'd0, 4'd12, 4'd11, 4'd7, 4'd13, 4'd15, 4'd1, 4'd3, 4'd14, 4'd5, 4'd2, 4'd8, 4'd4},
        {4'd3, 4'd15, 4'd0, 4'd6, 4'd10, 4'd1, 4'd13, 4'd8, 4'd9, 4'd4, 4'd5, 4'd11, 4'd12, 4'd7, 4'd2, 4'd14}
    };

    assign s_box5 = '{
        {4'd2, 4'd12, 4'd4, 4'd1, 4'd7, 4'd10, 4'd11, 4'd6, 4'd8, 4'd5, 4'd3, 4'd15, 4'd13, 4'd0, 4'd14, 4'd9},
        {4'd14, 4'd11, 4'd2, 4'd12, 4'd4, 4'd7, 4'd13, 4'd1, 4'd5, 4'd0, 4'd15, 4'd10, 4'd3, 4'd9, 4'd8, 4'd6},
        {4'd4, 4'd2, 4'd1, 4'd11, 4'd10, 4'd13, 4'd7, 4'd8, 4'd15, 4'd9, 4'd12, 4'd5, 4'd6, 4'd3, 4'd0, 4'd14},
        {4'd11, 4'd8, 4'd12, 4'd7, 4'd1, 4'd14, 4'd2, 4'd13, 4'd6, 4'd15, 4'd0, 4'd9, 4'd10, 4'd4, 4'd5, 4'd3}
    };

    assign s_box6 = '{
        {4'd12, 4'd1, 4'd10, 4'd15, 4'd9, 4'd2, 4'd6, 4'd8, 4'd0, 4'd13, 4'd3, 4'd4, 4'd14, 4'd7, 4'd5, 4'd11},
        {4'd10, 4'd15, 4'd4, 4'd2, 4'd7, 4'd12, 4'd9, 4'd5, 4'd6, 4'd1, 4'd13, 4'd14, 4'd0, 4'd11, 4'd3, 4'd8},
        {4'd9, 4'd14, 4'd15, 4'd5, 4'd2, 4'd8, 4'd12, 4'd3, 4'd7, 4'd0, 4'd4, 4'd10, 4'd1, 4'd13, 4'd11, 4'd6},
        {4'd4, 4'd3, 4'd2, 4'd12, 4'd9, 4'd5, 4'd15, 4'd10, 4'd11, 4'd14, 4'd1, 4'd7, 4'd6, 4'd0, 4'd8, 4'd13}
    };

    assign s_box7 = '{
        {4'd4, 4'd11, 4'd2, 4'd14, 4'd15, 4'd0, 4'd8, 4'd13, 4'd3, 4'd12, 4'd9, 4'd7, 4'd5, 4'd10, 4'd6, 4'd1},
        {4'd13, 4'd0, 4'd11, 4'd7, 4'd4, 4'd9, 4'd1, 4'd10, 4'd14, 4'd3, 4'd5, 4'd12, 4'd2, 4'd15, 4'd8, 4'd6},
        {4'd1, 4'd4, 4'd11, 4'd13, 4'd12, 4'd3, 4'd7, 4'd14, 4'd10, 4'd15, 4'd6, 4'd8, 4'd0, 4'd5, 4'd9, 4'd2},
        {4'd6, 4'd11, 4'd13, 4'd8, 4'd1, 4'd4, 4'd10, 4'd7, 4'd9, 4'd5, 4'd0, 4'd15, 4'd14, 4'd2, 4'd3, 4'd12}
    };

    assign s_box8 = '{
        {4'd13, 4'd2, 4'd8, 4'd4, 4'd6, 4'd15, 4'd11, 4'd1, 4'd10, 4'd9, 4'd3, 4'd14, 4'd5, 4'd0, 4'd12, 4'd7},
        {4'd1, 4'd15, 4'd13, 4'd8, 4'd10, 4'd3, 4'd7, 4'd4, 4'd12, 4'd5, 4'd6, 4'd11, 4'd0, 4'd14, 4'd9, 4'd2},
        {4'd7, 4'd11, 4'd4, 4'd1, 4'd9, 4'd12, 4'd14, 4'd2, 4'd0, 4'd6, 4'd10, 4'd13, 4'd15, 4'd3, 4'd5, 4'd8},
        {4'd2, 4'd1, 4'd14, 4'd7, 4'd4, 4'd10, 4'd8, 4'd13, 4'd15, 4'd12, 4'd9, 4'd0, 4'd3, 4'd5, 4'd6, 4'd11}
    };



    function logic [0:63] des(logic [0:63] data_init, logic [0:47] key_sub);
        logic [0:31] data_l;          // left data
        logic [0:31] data_r;          // right data

        logic [0:47] data_e;          // data after expansion replacement
        logic [0:47] data_x;          // data after xor key_sub
        logic [0:31] data_s;          // data after sbox replacement
        logic [0:31] data_p;          // data after pbox replacement

        /*   compute   */

        assign data_l = data_init[0:31];
        assign data_r = data_init[32:63];
    
        // expansion
        assign data_e = {
                            data_r[31], data_r[0],  data_r[1],  data_r[2],  data_r[3],  data_r[4],
                            data_r[3],  data_r[4],  data_r[5],  data_r[6],  data_r[7],  data_r[8],
                            data_r[7],  data_r[8],  data_r[9],  data_r[10], data_r[11], data_r[12],
                            data_r[11], data_r[12], data_r[13], data_r[14], data_r[15], data_r[16],
                            data_r[15], data_r[16], data_r[17], data_r[18], data_r[19], data_r[20],
                            data_r[19], data_r[20], data_r[21], data_r[22], data_r[23], data_r[24],
                            data_r[23], data_r[24], data_r[25], data_r[26], data_r[27], data_r[28],
                            data_r[27], data_r[28], data_r[29], data_r[30], data_r[31], data_r[0]
                        };
        
        // xor the subkey
        assign data_x = data_e ^ key_sub;

        // s-box
        assign data_s = {
                            s_box1[{data_x[0], data_x[5]}][{data_x[1:4]}], 
                            s_box2[{data_x[6], data_x[11]}][{data_x[7:10]}], 
                            s_box3[{data_x[12], data_x[17]}][{data_x[13:16]}], 
                            s_box4[{data_x[18], data_x[23]}][{data_x[19:22]}],
                            s_box5[{data_x[24], data_x[29]}][{data_x[25:28]}], 
                            s_box6[{data_x[30], data_x[35]}][{data_x[31:34]}], 
                            s_box7[{data_x[36], data_x[41]}][{data_x[37:40]}],
                            s_box8[{data_x[42], data_x[47]}][{data_x[43:46]}]

                        };
        
        // p-box
        assign data_p = {
                            data_s[15], data_s[6],  data_s[19], data_s[20], data_s[28], data_s[11], data_s[27], data_s[16],
                            data_s[0],  data_s[14], data_s[22], data_s[25], data_s[4],  data_s[17], data_s[30], data_s[9],
                            data_s[1],  data_s[7],  data_s[23], data_s[13], data_s[31], data_s[26], data_s[2],  data_s[8],
                            data_s[18], data_s[12], data_s[29], data_s[5],  data_s[21], data_s[10], data_s[3],  data_s[24]
                        };

        // return
        return {data_r, data_p ^ data_l};
    endfunction

endmodule