package my_sequence_pkg;

    import uvm_pkg::*;

    // Define the transaction item

    class icb_trans extends uvm_sequence_item;
        // `uvm_object_utils(icb_trans)
        
        rand logic          read;
        rand logic [7:0]    mask;
        rand logic [63:0]   wdata;
        rand logic [63:0]   rdata;
        rand logic [31:0]   addr;

        `uvm_object_utils_begin(icb_trans)
            `uvm_field_int(read, UVM_ALL_ON)
            `uvm_field_int(mask, UVM_ALL_ON)
            `uvm_field_int(wdata, UVM_ALL_ON)
            `uvm_field_int(rdata, UVM_ALL_ON)
            `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_object_utils_end

        constraint c_addr {
            (addr == 32'h20000000) ||
            (addr == 32'h20000008) ||
            (addr == 32'h20000010) ||
            (addr == 32'h20000018) ||
            (addr == 32'h20000020);
        }

        constraint c_wdata{
            if (wdata[0] == 0 && addr == 32'h20000010) {
                (wdata[7:2] == 6'b000001) || 
                (wdata[7:2] == 6'b000010) || 
                (wdata[7:2] == 6'b000100) || 
                (wdata[7:2] == 6'b001000);
            }
        }
            

        function new(string name = "");
            super.new(name);
        endfunction : new

        function logic [0:63] encrypt(input [0:63] data_i, input [0:63] key);

            logic [0:55] key_init;
            logic [0:27] key_set_c;       // left  28bit
            logic [0:27] key_set_d;       // right 28bit
            logic [0:55] key_merge;       // re-merge
            logic [0:47] key_sub [0:15];  // sub key

            logic [0:63] data_init;
            logic [0:63] data_f;
            logic [0:63] data_o;

            key_init = {
                        key[56], key[48], key[40], key[32], key[24], key[16], key[8], key[0],  key[57], key[49], key[41], key[33], key[25], key[17],
                        key[9],  key[1],  key[58], key[50], key[42], key[34], key[26], key[18], key[10], key[2],  key[59], key[51], key[43], key[35],
                        key[62], key[54], key[46], key[38], key[30], key[22], key[14], key[6],  key[61], key[53], key[45], key[37], key[29], key[21],
                        key[13], key[5],  key[60], key[52], key[44], key[36], key[28], key[20], key[12], key[4],  key[27], key[19], key[11], key[3]
                        };

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

            data_init = {  data_i[57], data_i[49], data_i[41], data_i[33], data_i[25], data_i[17], data_i[9],  data_i[1],
                            data_i[59], data_i[51], data_i[43], data_i[35], data_i[27], data_i[19], data_i[11], data_i[3],
                            data_i[61], data_i[53], data_i[45], data_i[37], data_i[29], data_i[21], data_i[13], data_i[5],
                            data_i[63], data_i[55], data_i[47], data_i[39], data_i[31], data_i[23], data_i[15], data_i[7],
                            data_i[56], data_i[48], data_i[40], data_i[32], data_i[24], data_i[16], data_i[8],  data_i[0],
                            data_i[58], data_i[50], data_i[42], data_i[34], data_i[26], data_i[18], data_i[10], data_i[2],
                            data_i[60], data_i[52], data_i[44], data_i[36], data_i[28], data_i[20], data_i[12], data_i[4],
                            data_i[62], data_i[54], data_i[46], data_i[38], data_i[30], data_i[22], data_i[14], data_i[6]
                         };

            for(int i = 0; i < 16; i = i + 1)
            begin
                data_init = des(data_init, key_sub[i]);
            end
            
            data_f = {data_init[32:63], data_init[0:31]};
            data_o = {
                        data_f[39], data_f[7],  data_f[47], data_f[15], data_f[55], data_f[23], data_f[63], data_f[31],
                        data_f[38], data_f[6],  data_f[46], data_f[14], data_f[54], data_f[22], data_f[62], data_f[30],
                        data_f[37], data_f[5],  data_f[45], data_f[13], data_f[53], data_f[21], data_f[61], data_f[29],
                        data_f[36], data_f[4],  data_f[44], data_f[12], data_f[52], data_f[20], data_f[60], data_f[28],
                        data_f[35], data_f[3],  data_f[43], data_f[11], data_f[51], data_f[19], data_f[59], data_f[27],
                        data_f[34], data_f[2],  data_f[42], data_f[10], data_f[50], data_f[18], data_f[58], data_f[26],
                        data_f[33], data_f[1],  data_f[41], data_f[9],  data_f[49], data_f[17], data_f[57], data_f[25],
                        data_f[32], data_f[0],  data_f[40], data_f[8],  data_f[48], data_f[16], data_f[56], data_f[24]
                    };

            return data_o;
        endfunction: encrypt

        function logic [0:63] des(logic [0:63] data_init, logic [0:47] key_sub);
            logic [0:31] data_l;          // left data
            logic [0:31] data_r;          // right data

            logic [0:47] data_e;          // data after expansion replacement
            logic [0:47] data_x;          // data after xor key_sub
            logic [0:31] data_s;          // data after sbox replacement
            logic [0:31] data_p;          // data after pbox replacement

            // s-box definition
            logic [0:3] s_box1 [0:3][0:15];
            logic [0:3] s_box2 [0:3][0:15];
            logic [0:3] s_box3 [0:3][0:15];
            logic [0:3] s_box4 [0:3][0:15];
            logic [0:3] s_box5 [0:3][0:15];
            logic [0:3] s_box6 [0:3][0:15];
            logic [0:3] s_box7 [0:3][0:15];
            logic [0:3] s_box8 [0:3][0:15];

            s_box1 = '{
                {4'd14, 4'd4, 4'd13, 4'd1, 4'd2, 4'd15, 4'd11, 4'd8, 4'd3, 4'd10, 4'd6, 4'd12, 4'd5, 4'd9, 4'd0, 4'd7},
                {4'd0, 4'd15, 4'd7, 4'd4, 4'd14, 4'd2, 4'd13, 4'd1, 4'd10, 4'd6, 4'd12, 4'd11, 4'd9, 4'd5, 4'd3, 4'd8},
                {4'd4, 4'd1, 4'd14, 4'd8, 4'd13, 4'd6, 4'd2, 4'd11, 4'd15, 4'd12, 4'd9, 4'd7, 4'd3, 4'd10, 4'd5, 4'd0},
                {4'd15, 4'd12, 4'd8, 4'd2, 4'd4, 4'd9, 4'd1, 4'd7, 4'd5, 4'd11, 4'd3, 4'd14, 4'd10, 4'd0, 4'd6, 4'd13}
            };
            
            s_box2 = '{
                {4'd15, 4'd1, 4'd8, 4'd14, 4'd6, 4'd11, 4'd3, 4'd4, 4'd9, 4'd7, 4'd2, 4'd13, 4'd12, 4'd0, 4'd5, 4'd10},
                {4'd3, 4'd13, 4'd4, 4'd7, 4'd15, 4'd2, 4'd8, 4'd14, 4'd12, 4'd0, 4'd1, 4'd10, 4'd6, 4'd9, 4'd11, 4'd5},
                {4'd0, 4'd14, 4'd7, 4'd11, 4'd10, 4'd4, 4'd13, 4'd1, 4'd5, 4'd8, 4'd12, 4'd6, 4'd9, 4'd3, 4'd2, 4'd15},
                {4'd13, 4'd8, 4'd10, 4'd1, 4'd3, 4'd15, 4'd4, 4'd2, 4'd11, 4'd6, 4'd7, 4'd12, 4'd0, 4'd5, 4'd14, 4'd9}
            };

            s_box3 = '{
                {4'd10, 4'd0, 4'd9, 4'd14, 4'd6, 4'd3, 4'd15, 4'd5, 4'd1, 4'd13, 4'd12, 4'd7, 4'd11, 4'd4, 4'd2, 4'd8},
                {4'd13, 4'd7, 4'd0, 4'd9, 4'd3, 4'd4, 4'd6, 4'd10, 4'd2, 4'd8, 4'd5, 4'd14, 4'd12, 4'd11, 4'd15, 4'd1},
                {4'd13, 4'd6, 4'd4, 4'd9, 4'd8, 4'd15, 4'd3, 4'd0, 4'd11, 4'd1, 4'd2, 4'd12, 4'd5, 4'd10, 4'd14, 4'd7},
                {4'd1, 4'd10, 4'd13, 4'd0, 4'd6, 4'd9, 4'd8, 4'd7, 4'd4, 4'd15, 4'd14, 4'd3, 4'd11, 4'd5, 4'd2, 4'd12}
            };

            s_box4 = '{
                {4'd7, 4'd13, 4'd14, 4'd3, 4'd0, 4'd6, 4'd9, 4'd10, 4'd1, 4'd2, 4'd8, 4'd5, 4'd11, 4'd12, 4'd4, 4'd15},
                {4'd13, 4'd8, 4'd11, 4'd5, 4'd6, 4'd15, 4'd0, 4'd3, 4'd4, 4'd7, 4'd2, 4'd12, 4'd1, 4'd10, 4'd14, 4'd9},
                {4'd10, 4'd6, 4'd9, 4'd0, 4'd12, 4'd11, 4'd7, 4'd13, 4'd15, 4'd1, 4'd3, 4'd14, 4'd5, 4'd2, 4'd8, 4'd4},
                {4'd3, 4'd15, 4'd0, 4'd6, 4'd10, 4'd1, 4'd13, 4'd8, 4'd9, 4'd4, 4'd5, 4'd11, 4'd12, 4'd7, 4'd2, 4'd14}
            };

            s_box5 = '{
                {4'd2, 4'd12, 4'd4, 4'd1, 4'd7, 4'd10, 4'd11, 4'd6, 4'd8, 4'd5, 4'd3, 4'd15, 4'd13, 4'd0, 4'd14, 4'd9},
                {4'd14, 4'd11, 4'd2, 4'd12, 4'd4, 4'd7, 4'd13, 4'd1, 4'd5, 4'd0, 4'd15, 4'd10, 4'd3, 4'd9, 4'd8, 4'd6},
                {4'd4, 4'd2, 4'd1, 4'd11, 4'd10, 4'd13, 4'd7, 4'd8, 4'd15, 4'd9, 4'd12, 4'd5, 4'd6, 4'd3, 4'd0, 4'd14},
                {4'd11, 4'd8, 4'd12, 4'd7, 4'd1, 4'd14, 4'd2, 4'd13, 4'd6, 4'd15, 4'd0, 4'd9, 4'd10, 4'd4, 4'd5, 4'd3}
            };

            s_box6 = '{
                {4'd12, 4'd1, 4'd10, 4'd15, 4'd9, 4'd2, 4'd6, 4'd8, 4'd0, 4'd13, 4'd3, 4'd4, 4'd14, 4'd7, 4'd5, 4'd11},
                {4'd10, 4'd15, 4'd4, 4'd2, 4'd7, 4'd12, 4'd9, 4'd5, 4'd6, 4'd1, 4'd13, 4'd14, 4'd0, 4'd11, 4'd3, 4'd8},
                {4'd9, 4'd14, 4'd15, 4'd5, 4'd2, 4'd8, 4'd12, 4'd3, 4'd7, 4'd0, 4'd4, 4'd10, 4'd1, 4'd13, 4'd11, 4'd6},
                {4'd4, 4'd3, 4'd2, 4'd12, 4'd9, 4'd5, 4'd15, 4'd10, 4'd11, 4'd14, 4'd1, 4'd7, 4'd6, 4'd0, 4'd8, 4'd13}
            };

            s_box7 = '{
                {4'd4, 4'd11, 4'd2, 4'd14, 4'd15, 4'd0, 4'd8, 4'd13, 4'd3, 4'd12, 4'd9, 4'd7, 4'd5, 4'd10, 4'd6, 4'd1},
                {4'd13, 4'd0, 4'd11, 4'd7, 4'd4, 4'd9, 4'd1, 4'd10, 4'd14, 4'd3, 4'd5, 4'd12, 4'd2, 4'd15, 4'd8, 4'd6},
                {4'd1, 4'd4, 4'd11, 4'd13, 4'd12, 4'd3, 4'd7, 4'd14, 4'd10, 4'd15, 4'd6, 4'd8, 4'd0, 4'd5, 4'd9, 4'd2},
                {4'd6, 4'd11, 4'd13, 4'd8, 4'd1, 4'd4, 4'd10, 4'd7, 4'd9, 4'd5, 4'd0, 4'd15, 4'd14, 4'd2, 4'd3, 4'd12}
            };

            s_box8 = '{
                {4'd13, 4'd2, 4'd8, 4'd4, 4'd6, 4'd15, 4'd11, 4'd1, 4'd10, 4'd9, 4'd3, 4'd14, 4'd5, 4'd0, 4'd12, 4'd7},
                {4'd1, 4'd15, 4'd13, 4'd8, 4'd10, 4'd3, 4'd7, 4'd4, 4'd12, 4'd5, 4'd6, 4'd11, 4'd0, 4'd14, 4'd9, 4'd2},
                {4'd7, 4'd11, 4'd4, 4'd1, 4'd9, 4'd12, 4'd14, 4'd2, 4'd0, 4'd6, 4'd10, 4'd13, 4'd15, 4'd3, 4'd5, 4'd8},
                {4'd2, 4'd1, 4'd14, 4'd7, 4'd4, 4'd10, 4'd8, 4'd13, 4'd15, 4'd12, 4'd9, 4'd0, 4'd3, 4'd5, 4'd6, 4'd11}
            };

            /*   compute   */

            data_l = data_init[0:31];
            data_r = data_init[32:63];
        
            // expansion
            data_e = {
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
            data_x = data_e ^ key_sub;

            // s-box
            data_s = {
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
            data_p = {
                                data_s[15], data_s[6],  data_s[19], data_s[20], data_s[28], data_s[11], data_s[27], data_s[16],
                                data_s[0],  data_s[14], data_s[22], data_s[25], data_s[4],  data_s[17], data_s[30], data_s[9],
                                data_s[1],  data_s[7],  data_s[23], data_s[13], data_s[31], data_s[26], data_s[2],  data_s[8],
                                data_s[18], data_s[12], data_s[29], data_s[5],  data_s[21], data_s[10], data_s[3],  data_s[24]
                            };

            // return
            return {data_r, data_p ^ data_l};
        endfunction: des

    endclass : icb_trans

    class apb_trans extends uvm_sequence_item;
        // `uvm_object_utils(apb_trans)
        
        rand logic          write;
        rand logic [31:0]   wdata;
        rand logic [31:0]   rdata;
        rand logic [63:0]   rdata_g; // Define for apb model 
        rand logic [31:0]   addr;

        `uvm_object_utils_begin(apb_trans)
            `uvm_field_int(write, UVM_ALL_ON)
            `uvm_field_int(wdata, UVM_ALL_ON)
            `uvm_field_int(rdata, UVM_ALL_ON)
            `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_object_utils_end

        constraint c_addr {
            addr >= 0;
            addr <= 'hffffff;
        }

        constraint c_wdata {
            wdata >= 0;
            wdata <= 'h7fff_ffff;
        }

        function new(string name = "");
            super.new(name);
        endfunction : new
    
    endclass : apb_trans

    // Define the sequence

    class icb_cfg_key extends uvm_sequence #(icb_trans);
        `uvm_object_utils(icb_cfg_key)

        string report_id = get_type_name();

        function new(string name = "");
            super.new(name);
        endfunction : new

        task body;
            icb_trans tx;
            tx = icb_trans::type_id::create("tx");

            start_item(tx);
                tx.read = 0;
                tx.addr = 32'h20000020;
                tx.wdata = 64'b0001001100110100010101110111100110011011101111001101111111110001;
                tx.mask = 8'h00;
            finish_item(tx);

        endtask : body

    endclass : icb_cfg_key

    class icb_enable_apb extends uvm_sequence #(icb_trans);
        `uvm_object_utils(icb_enable_apb)

        string report_id = get_type_name();

        function new(string name = "");
            super.new(name);
        endfunction : new

        task body;
            icb_trans tx;
            tx = icb_trans::type_id::create("tx");

            start_item(tx);
                tx.read = 0;
                tx.addr = 32'h20000000;
                tx.wdata = 64'h0000_0000_0000_0001;
                tx.mask = 8'h00;
            finish_item(tx);
        endtask : body

    endclass : icb_enable_apb

    class icb_disable_apb extends uvm_sequence #(icb_trans);
        `uvm_object_utils(icb_disable_apb)

        string report_id = get_type_name();

        function new(string name = "");
            super.new(name);
        endfunction : new

        task body;
            icb_trans tx;
            tx = icb_trans::type_id::create("tx");
            start_item(tx);
                tx.read = 0;
                tx.addr = 32'h20000000;
                tx.wdata = 64'h0000_0000_0000_0000;
                tx.mask = 8'h00;
            finish_item(tx);
        endtask : body
    
    endclass : icb_disable_apb

    class icb_read_state extends uvm_sequence #(icb_trans);
        `uvm_object_utils(icb_read_state)

        string report_id = get_type_name();

        function new(string name = "");
            super.new(name);
        endfunction : new

        task body;
            icb_trans tx;
            tx = icb_trans::type_id::create("tx");

            start_item(tx);
                tx.read = 1;
                tx.addr = 32'h20000008;
            finish_item(tx);

        endtask : body

    endclass : icb_read_state

    class icb_write_apb extends uvm_sequence #(icb_trans);
        `uvm_object_utils(icb_write_apb)

        string report_id = get_type_name();

        int num = 16;

        function new(string name = "");
            super.new(name);
        endfunction : new

        task body;

            icb_trans tx;
            tx = icb_trans::type_id::create("tx");

            // `uvm_info(report_id, "Starting ICB Write APB Process!", UVM_LOW); // for debug

            // write the KEY register
            // start_item(tx);
            //     tx.read = 0;
            //     tx.addr = 32'h20000020;
            //     tx.wdata = 64'b0001001100110100010101110111100110011011101111001101111111110001;
            //     tx.mask = 8'h00;
            // finish_item(tx);

            // write the CTRL register
            // start_item(tx);
            //     tx.read = 0;
            //     tx.addr = 32'h20000000;
            //     tx.wdata = 64'h0000_0000_0000_0001;
            //     tx.mask = 8'h00;
            // finish_item(tx);

            // try to write the STATE register (the read only register)
            start_item(tx);
                tx.read = 0;
                tx.addr = 32'h20000008;
                tx.wdata = {$urandom(), $urandom()};
                tx.mask = $urandom() & 8'hFF;
            finish_item(tx);

            // try to write the RDATA register (the read only register)
            start_item(tx);
                tx.read = 0;
                tx.addr = 32'h20000018;
                tx.wdata = {$urandom(), $urandom()};
                tx.mask = $urandom() & 8'hFF;
            finish_item(tx);

            // try to write the wrong address
            start_item(tx);
                tx.read = 0;
                tx.addr = 32'h20000021;
                tx.wdata = {$urandom(), $urandom()};
                tx.mask = $urandom() & 8'hFF;
            finish_item(tx);

            // write the WDATA register
            for(int i = 0; i < num * 2; i = i + 1)
            begin
                start_item(tx);
                    if(i % 2 == 0) begin
                        assert ( tx.randomize() with {tx.read == 0; tx.addr == 32'h20000010; tx.wdata[0] == 0; tx.wdata[1] == 1;} )
                        else `uvm_error("RANDOMIZE_FAILED", "Control packet randomize failed in icb_write_apb");
                    end
                    else begin
                        assert ( tx.randomize() with {tx.read == 0; tx.addr == 32'h20000010; tx.wdata[0] == 1;} )
                        else `uvm_error("RANDOMIZE_FAILED", "Data packet randomize failed in icb_write_apb");
                    end

                    tx.mask = 8'h00;
                    tx.wdata = tx.encrypt(tx.wdata, 64'b0001001100110100010101110111100110011011101111001101111111110001);
                    
                finish_item(tx);

                #200;
            end
        endtask : body
    
    endclass : icb_write_apb

    class icb_read_apb extends uvm_sequence #(icb_trans);
        `uvm_object_utils(icb_read_apb)

        int num = 16;

        function new(string name = "");
            super.new(name);
        endfunction : new

        task body;
            icb_trans tx;
            tx = icb_trans::type_id::create("tx");
            
            // write the KEY register
            // start_item(tx);
            //     tx.read = 0;
            //     tx.addr = 32'h20000020;
            //     tx.wdata = 64'b0001001100110100010101110111100110011011101111001101111111110001;
            //     tx.mask = 8'h00;
            // finish_item(tx);

            // write the CTRL register
            // start_item(tx);
            //     tx.read = 0;
            //     tx.addr = 32'h20000000;
            //     tx.wdata = 64'h0000_0000_0000_0001;
            //     tx.mask = 8'h00;
            // finish_item(tx);

            // read the CTRL register
            start_item(tx);
                tx.read = 1;
                tx.addr = 32'h20000000;
            finish_item(tx);

            // read the STATE register
            start_item(tx);
                tx.read = 1;
                tx.addr = 32'h20000008;
            finish_item(tx);

            // read the WDATA register
            start_item(tx);
                tx.read = 1;
                tx.addr = 32'h20000010;
            finish_item(tx);

            // read the KEY register
            start_item(tx);
                tx.read = 1;
                tx.addr = 32'h20000020;
            finish_item(tx);

            // try to read the wrong address
            start_item(tx);
                tx.read = 1;
                tx.addr = 32'h20000021;
            finish_item(tx);

            // send the read request to APB
            for (int i = 0; i < num * 2; i = i + 1 ) begin
                start_item(tx);
                    if(i % 2 == 0) begin
                        assert ( tx.randomize() with {tx.read == 0; tx.addr == 32'h20000010; tx.wdata[0] == 0; tx.wdata[1] == 0;} )
                        else `uvm_error("RANDOMIZE_FAILED", "Control packet randomize failed in icb_read_apb");
                    end
                    else begin
                        assert ( tx.randomize() with {tx.read == 0; tx.addr == 32'h20000010; tx.wdata[0] == 1;} )
                        else `uvm_error("RANDOMIZE_FAILED", "Data packet randomize failed in icb_read_apb");
                    end

                    tx.mask = 8'h00;
                    tx.wdata = tx.encrypt(tx.wdata, 64'b0001001100110100010101110111100110011011101111001101111111110001);
                finish_item(tx);
                #200;
            end
            
            // // read the RDATA register
            // for(int i = 0; i < 8; i = i + 1) begin
            //     start_item(tx);
            //         tx.read = 1;
            //         tx.addr = 32'h20000018;
            //     finish_item(tx);
            // end

        endtask : body

    endclass : icb_read_apb

    class icb_read_rdata extends uvm_sequence #(icb_trans);
        `uvm_object_utils(icb_read_rdata)

        int num = 16;

        function new(string name = "");
            super.new(name);
        endfunction : new

        task body;
            icb_trans tx;
            tx = icb_trans::type_id::create("tx");
            
            // read the RDATA register
            for(int i = 0; i < num; i = i + 1) begin
                start_item(tx);
                    tx.read = 1;
                    tx.addr = 32'h20000018;
                finish_item(tx);
            end

        endtask : body
    
    endclass : icb_read_rdata
    
    class apb_single_resp extends uvm_sequence #(apb_trans);
        `uvm_object_utils(apb_single_resp)

        function new(string name = "");
            super.new(name);
        endfunction : new

        task body;
            apb_trans tx;

            tx = apb_trans::type_id::create("tx");

            start_item(tx);
                tx.rdata = $urandom();
            finish_item(tx);
        endtask

    endclass : apb_single_resp

    class apb_cont_resp extends uvm_sequence #(apb_trans);
        `uvm_object_utils(apb_cont_resp)

        int num = 16;

        function new(string name = "");
            super.new(name);
        endfunction : new

        task body;
            apb_trans tx;

            tx = apb_trans::type_id::create("tx");

            for(int i = 0; i < num; i = i + 1) begin
                start_item(tx);
                    tx.rdata = $urandom();
                finish_item(tx);
            end
        endtask : body
    
    endclass : apb_cont_resp



endpackage : my_sequence_pkg