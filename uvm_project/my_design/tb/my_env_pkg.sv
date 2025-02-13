package my_env_pkg;

    import uvm_pkg::*;
    import my_sequence_pkg::*;
    import my_agent_pkg::*;

    class my_env_config extends uvm_object;
        virtual icb_bus icb_vif;
        virtual apb_bus apb_vif[4];
    endclass : my_env_config

    class icb_subscriber extends uvm_subscriber #(icb_trans);
    
        `uvm_component_utils(icb_subscriber)
    
        string report_id = get_type_name();
    
        logic          read;
        logic [7:0]    mask;
        logic [63:0]   wdata;
        logic [63:0]   rdata;
        logic [31:0]   addr;

        covergroup icb_coverbus;
            option.per_instance = 1;
            option.name = {get_full_name(), ".icb_coverbus"};

            cov_icb_read : coverpoint read {
                bins read = {1'b1};
                bins write = {1'b0};
            }

            cov_icb_addr : coverpoint addr {
                bins ctrl_read  = {32'h2000_0000} iff (read == 1'b1);
                bins state_read = {32'h2000_0008} iff (read == 1'b1); 
                bins wdata_read = {32'h2000_0010} iff (read == 1'b1); 
                bins rdata_read = {32'h2000_0018} iff (read == 1'b1); 
                bins key_read   = {32'h2000_0020} iff (read == 1'b1); 
                bins wrong_read = {[32'h2000_0021:32'hFFFF_FFFF]} iff (read == 1'b1);

                bins ctrl_write  = {32'h2000_0000} iff (read == 1'b0); 
                bins state_write = {32'h2000_0008} iff (read == 1'b0); 
                bins wdata_write = {32'h2000_0010} iff (read == 1'b0); 
                bins rdata_write = {32'h2000_0018} iff (read == 1'b0); 
                bins key_write   = {32'h2000_0020} iff (read == 1'b0); 
                bins wrong_write = {[32'h2000_0021:32'hFFFF_FFFF]} iff (read == 1'b0); 
            }

            cov_icb_start_apb : coverpoint wdata[0] {
                bins start = {1'b1} iff ((read == 1'b0) && (addr == 32'h2000_0000));
                bins stop  = {1'b0} iff ((read == 1'b0) && (addr == 32'h2000_0000)); 
            }

            cov_icb_apb_state : coverpoint rdata[1:0] {
                bins reset = {2'b00} iff ((read == 1'b1) && (addr == 32'h2000_0008));
                bins free  = {2'b01} iff ((read == 1'b1) && (addr == 32'h2000_0008));
                bins read  = {2'b10} iff ((read == 1'b1) && (addr == 32'h2000_0008));
                bins write = {2'b11} iff ((read == 1'b1) && (addr == 32'h2000_0008));
            }

            cov_icb_rfifo_state : coverpoint rdata[3:2]{
                bins empty = {2'b01} iff ((read == 1'b1) && (addr == 32'h2000_0008));
                bins full  = {2'b10} iff ((read == 1'b1) && (addr == 32'h2000_0008));
                bins intermediate = {2'b00} iff ((read == 1'b1) && (addr == 32'h2000_0008));
            }
            
            cov_icb_wfifo_state : coverpoint rdata[5:4]{
                bins empty = {2'b01} iff ((read == 1'b1) && (addr == 32'h2000_0008));
                bins full  = {2'b10} iff ((read == 1'b1) && (addr == 32'h2000_0008));
                bins intermediate = {2'b00} iff ((read == 1'b1) && (addr == 32'h2000_0008));
            }


        endgroup : icb_coverbus

        function new(string name = "icb_subscriber", uvm_component parent = null);
            super.new(name, parent);
            icb_coverbus = new();
        endfunction: new

        function void write(icb_trans t);
            `uvm_info(report_id, "Get a ICB transaction from ICB_AGT_MON AP", UVM_HIGH);

            read = t.read;
            mask = t.mask;
            wdata = t.wdata;
            rdata = t.rdata;
            addr = t.addr;
            icb_coverbus.sample();
        endfunction: write

    endclass : icb_subscriber

    class apb_subscriber extends uvm_subscriber #(apb_trans);

        `uvm_component_utils(apb_subscriber)
    
        string report_id = get_type_name();
    
        logic          write_s;
        logic [31:0]   wdata;
        logic [31:0]   rdata;
        logic [31:0]   addr;

        // ...
        covergroup apb_coverbus;
            option.per_instance = 1;
            option.name = {get_full_name(), ".apb_coverbus"};

            cov_apb_read : coverpoint write_s {
                bins reads = {1'b0};
                bins writes = {1'b1};
            }

        endgroup : apb_coverbus


        function new(string name = "apb_subscriber", uvm_component parent = null);
            super.new(name, parent);
            // ...
            apb_coverbus = new();
        endfunction: new

        function void write(apb_trans t);
            `uvm_info(report_id, "Get a APB transaction from APB_AGT_MON AP", UVM_HIGH);

            write_s = t.write;
            wdata = t.wdata;
            rdata = t.rdata;
            addr = t.addr;

            // ...
            apb_coverbus.sample();
        endfunction: write

    endclass : apb_subscriber

    class icb_model extends uvm_component;

        `uvm_component_utils(icb_model)
    
        uvm_blocking_get_port #(icb_trans) bgp;
        uvm_analysis_port #(icb_trans) ap;

        logic [63:0] masked_data;
        logic [63:0] key;

        function new(string name = "icb_model", uvm_component parent = null);
            super.new(name, parent);
        endfunction: new

        function void build_phase(uvm_phase phase);
            bgp = new("bgp", this);
            ap = new("ap", this);
        endfunction: build_phase
        

        // des decrypt
        function logic [0:63] decrypt(input [0:63] data_i, input [0:63] key);


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
                data_init = des(data_init, key_sub[15 - i]);
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
        endfunction: decrypt

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


        task run_phase(uvm_phase phase);
            const logic [31:0]  CTRL_ADDR = 32'h2000_0000;
            const logic [31:0]  STAT_ADDR = 32'h2000_0008;
            const logic [31:0]  WDATA_ADDR = 32'h2000_0010;
            const logic [31:0]  RDATA_ADDR = 32'h2000_0018;
            const logic [31:0]  KEY_ADDR = 32'h2000_0020;

            icb_trans tx_model_i;
            icb_trans tx_model_o;

            forever begin
                bgp.get(tx_model_i);
                
                // `uvm_info(get_type_name(), "Get a ICB transaction from ICB_AGT_MON BG", UVM_LOW);
                if(!tx_model_i.read) // if icb is write
                begin
                    for (int i = 0; i < 8; i++)
                    begin
                        masked_data[i*8 +: 8] = tx_model_i.wdata[i*8 +: 8] & {8{~tx_model_i.mask[i]}};
                    end

                    if (tx_model_i.addr == KEY_ADDR)
                    begin
                        key = masked_data;
                        // `uvm_info(get_type_name(), $sformatf("Get a key: %h", key), UVM_LOW);
                    end
                    else if (tx_model_i.addr == WDATA_ADDR)
                    begin
                        tx_model_o = icb_trans::type_id::create("tx_model_o");
                        tx_model_o.copy(tx_model_i);
                        // `uvm_info(get_type_name(), $sformatf("Get a data: %h", masked_data), UVM_LOW);
                        tx_model_o.wdata = decrypt(masked_data, key);
                        // `uvm_info(get_type_name(), $sformatf("Decrypt data: %h", tx_model_o.wdata), UVM_LOW);
                        ap.write(tx_model_o);
                    end
                end
                else // if icb is read
                begin
                    if(tx_model_i.addr == RDATA_ADDR)
                    begin
                        tx_model_o = icb_trans::type_id::create("tx_model_o");
                        tx_model_o.copy(tx_model_i);
                        ap.write(tx_model_o);
                    end
                end
            end
        endtask: run_phase

    endclass : icb_model

    class apb_model extends uvm_component;

        `uvm_component_utils(apb_model)
    
        uvm_blocking_get_port #(apb_trans) bgp;
        uvm_analysis_port #(apb_trans) ap;

        logic [63:0] key;

        function new(string name = "apb_model", uvm_component parent = null);
            super.new(name, parent);
        endfunction: new

        function void build_phase(uvm_phase phase);
            bgp = new("bgp", this);
            ap = new("ap", this);
        endfunction: build_phase

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

        task run_phase(uvm_phase phase);
            apb_trans tx_model_i;
            apb_trans tx_model_o;

            key = 64'b0001001100110100010101110111100110011011101111001101111111110001;

            forever begin
                bgp.get(tx_model_i);

                if(!tx_model_i.write) // if apb is read
                begin
                    tx_model_o = apb_trans::type_id::create("tx_model_o");
                    tx_model_o.copy(tx_model_i);
                    tx_model_o.rdata_g = {32'b0, tx_model_i.rdata};
                    tx_model_o.rdata_g = encrypt(tx_model_o.rdata_g, key);
                    ap.write(tx_model_o);
                end
                else // if apb is write
                begin
                    tx_model_o = apb_trans::type_id::create("tx_model_o");
                    tx_model_o.copy(tx_model_i);
                    // `uvm_info(get_type_name(), $sformatf("Get a data: %h", tx_model_o.wdata), UVM_LOW);
                    ap.write(tx_model_o);
                end
            end
        endtask: run_phase

    endclass : apb_model

    class my_scoreboard extends uvm_scoreboard;

        `uvm_component_utils(my_scoreboard)
    
        string report_id = get_type_name();

        logic [5:0] sel_queue [$]; //  "select" queue
        
        uvm_blocking_get_port #(icb_trans) icb_bgp;

        uvm_blocking_get_port #(apb_trans) apb_bgp0;
        uvm_blocking_get_port #(apb_trans) apb_bgp1;
        uvm_blocking_get_port #(apb_trans) apb_bgp2;
        uvm_blocking_get_port #(apb_trans) apb_bgp3;
        
        int total_cases;
        int wrong_cases;

        function new(string name = "my_scoreboard", uvm_component parent = null);
            super.new(name, parent);
        endfunction: new

        function void build_phase(uvm_phase phase);
            icb_bgp = new("icb_bgp", this);
            apb_bgp0 = new("apb_bgp0", this);
            apb_bgp1 = new("apb_bgp1", this);
            apb_bgp2 = new("apb_bgp2", this);
            apb_bgp3 = new("apb_bgp3", this);
        endfunction: build_phase

        task run_phase(uvm_phase phase);
            
            const logic [5:0]  S0 = 6'b000001;
            const logic [5:0]  S1 = 6'b000010;
            const logic [5:0]  S2 = 6'b000100;
            const logic [5:0]  S3 = 6'b001000;

            icb_trans icb_tx1;  // control packet
            icb_trans icb_tx2;  // wdata   packet
            apb_trans apb_tx;
            
            logic        write_g;
            logic [5:0]  sel_g;
            logic [31:0] addr_g;
            logic [31:0] wdata_g;
            logic [63:0] rdata_g;

            total_cases = 0;
            wrong_cases = 0;

            forever begin
                icb_bgp.get(icb_tx1);

                // `uvm_info(report_id, "Get a ICB transaction from ICB_MDL BG", UVM_LOW);
                if(!icb_tx1.read) // if icb is write, icb_tx1 is control packet now
                begin
                    if(icb_tx1.wdata[0] == 1'b0) // if control packet
                    begin
                        write_g = icb_tx1.wdata[1];
                        addr_g = icb_tx1.wdata[31:8];
                        sel_g = icb_tx1.wdata[7:2];

                        if(sel_g == S0 || sel_g == S1 || sel_g == S2 || sel_g == S3) // if select is valid
                        begin
                            sel_queue.push_back(sel_g);

                            icb_bgp.get(icb_tx2); // apb write: data    packet
                                                  // apb read : invalid packet

                            if(write_g == 1) // if apb master is write
                            begin
                                case (sel_queue.pop_front())
                                    S0: apb_bgp0.get(apb_tx);
                                    S1: apb_bgp1.get(apb_tx);
                                    S2: apb_bgp2.get(apb_tx);
                                    S3: apb_bgp3.get(apb_tx);
                                    default: `uvm_error(report_id, "Invalid APB Slave select signal!")
                                endcase

                                total_cases = total_cases + 1;

                                wdata_g = icb_tx2.wdata[31:1];

                                if(wdata_g == apb_tx.wdata && addr_g == apb_tx.addr && 
                                    write_g == apb_tx.write)
                                begin
                                    `uvm_info(report_id, $sformatf("Case %0d (Write) check PASSED!", total_cases), UVM_LOW);
                                    `uvm_info(report_id, $sformatf("Now error rate is %.2f%%", real'(wrong_cases) / total_cases * 100), UVM_LOW);
                                end
                                else begin
                                    wrong_cases = wrong_cases + 1;
                                    `uvm_error(report_id, $sformatf("Case %0d (Write) check FAILED!", total_cases));
                                    
                                    if(wdata_g != apb_tx.wdata)
                                        `uvm_info(report_id, "APB pwdata is not equal!", UVM_LOW);
                                    if(addr_g != apb_tx.addr)
                                        `uvm_info(report_id, "APB paddr is not equal!", UVM_LOW);
                                    if(write_g != apb_tx.write)
                                        `uvm_info(report_id, "APB pwrite is not equal!", UVM_LOW);
                                    
                                    `uvm_info(report_id, "Unexpected APB transaction is:", UVM_LOW);
                                    apb_tx.print();

                                    `uvm_info(report_id, $sformatf("Now error rate is %.2f%%", real'(wrong_cases) / total_cases * 100), UVM_LOW);
                                end

                            end
                        end
                        else
                        begin
                            total_cases = total_cases + 1;
                            wrong_cases = wrong_cases + 1;
                            `uvm_error(report_id, "Invalid APB Slave select signal!");

                            `uvm_info(report_id, "Unexpected ICB transaction is:", UVM_LOW);
                            icb_tx1.print();
                            
                            `uvm_info(report_id, $sformatf("Now error rate is %.2f%%", real'(wrong_cases) / total_cases * 100), UVM_LOW);
                        end
                    end
                end
                else // if icb is read, icb_tx1 is read data from APB now
                begin
                    case (sel_queue.pop_front())
                        S0: apb_bgp0.get(apb_tx);
                        S1: apb_bgp1.get(apb_tx);
                        S2: apb_bgp2.get(apb_tx);
                        S3: apb_bgp3.get(apb_tx);
                        default: `uvm_error(report_id, "Invalid APB Slave select signal!")
                    endcase

                    total_cases = total_cases + 1;
                    
                    rdata_g = apb_tx.rdata_g;

                    if(rdata_g == icb_tx1.rdata)
                    begin
                        `uvm_info(report_id, $sformatf("Case %0d (Read) check PASSED!", total_cases), UVM_LOW);
                        `uvm_info(report_id, $sformatf("Now error rate is %.2f%%", real'(wrong_cases) / total_cases * 100), UVM_LOW);
                    end
                    else begin
                        wrong_cases = wrong_cases + 1;
                        `uvm_error(report_id, $sformatf("Case %0d (Read) check FAILED!", total_cases));
                        
                        `uvm_info(report_id, "ICB rdata is not equal!", UVM_LOW);
                        
                        `uvm_info(report_id, "Unexpected ICB transaction is:", UVM_LOW);
                        icb_tx1.print();

                        `uvm_info(report_id, $sformatf("Now error rate is %.2f%%", real'(wrong_cases) / total_cases * 100), UVM_LOW);
                    end
                end
            end

        endtask: run_phase

    endclass : my_scoreboard

    class my_env extends uvm_env;

        `uvm_component_utils(my_env)
    
        string report_id = get_type_name();

        my_env_config env_cfg;
        icb_agent_config icb_agt_cfg;
        apb_agent_config apb_agt_cfg0;
        apb_agent_config apb_agt_cfg1;
        apb_agent_config apb_agt_cfg2;
        apb_agent_config apb_agt_cfg3;

        icb_agent icb_agt;
        apb_agent apb_agt0;
        apb_agent apb_agt1;
        apb_agent apb_agt2;
        apb_agent apb_agt3;

        icb_subscriber icb_sub;
        apb_subscriber apb_sub0;
        apb_subscriber apb_sub1;
        apb_subscriber apb_sub2;
        apb_subscriber apb_sub3;

        icb_model icb_mdl;
        apb_model apb_mdl0;
        apb_model apb_mdl1;
        apb_model apb_mdl2;
        apb_model apb_mdl3;

        my_scoreboard scb;

        uvm_tlm_analysis_fifo #(icb_trans) icb_agt_mdl_fifo;
        uvm_tlm_analysis_fifo #(icb_trans) icb_mdl_scb_fifo;
        uvm_tlm_analysis_fifo #(apb_trans) apb_agt_mdl_fifo0;
        uvm_tlm_analysis_fifo #(apb_trans) apb_mdl_scb_fifo0;
        uvm_tlm_analysis_fifo #(apb_trans) apb_agt_mdl_fifo1;
        uvm_tlm_analysis_fifo #(apb_trans) apb_mdl_scb_fifo1;
        uvm_tlm_analysis_fifo #(apb_trans) apb_agt_mdl_fifo2;
        uvm_tlm_analysis_fifo #(apb_trans) apb_mdl_scb_fifo2;
        uvm_tlm_analysis_fifo #(apb_trans) apb_agt_mdl_fifo3;
        uvm_tlm_analysis_fifo #(apb_trans) apb_mdl_scb_fifo3;

        function new(string name = "my_env", uvm_component parent = null);
            super.new(name, parent);    
        endfunction :  new

        function void build_phase(uvm_phase phase);
            icb_agt_cfg = new();
            apb_agt_cfg0 = new();
            apb_agt_cfg1 = new();
            apb_agt_cfg2 = new();
            apb_agt_cfg3 = new();

            if(!uvm_config_db #(my_env_config)::get(this, "", "env_cfg", env_cfg))
                `uvm_fatal("NO_ENV_CFG", "Class env_config was not set!");
            
            icb_agt_cfg.icb_vif = env_cfg.icb_vif;
            apb_agt_cfg0.apb_vif = env_cfg.apb_vif[0];
            apb_agt_cfg1.apb_vif = env_cfg.apb_vif[1];
            apb_agt_cfg2.apb_vif = env_cfg.apb_vif[2];
            apb_agt_cfg3.apb_vif = env_cfg.apb_vif[3];

            uvm_config_db #(icb_agent_config)::set(this, "icb_agt.*", "icb_agt_cfg", icb_agt_cfg);
            uvm_config_db #(apb_agent_config)::set(this, "apb_agt0.*", "apb_agt_cfg", apb_agt_cfg0); // dont know if it is correct
            uvm_config_db #(apb_agent_config)::set(this, "apb_agt1.*", "apb_agt_cfg", apb_agt_cfg1); // 
            uvm_config_db #(apb_agent_config)::set(this, "apb_agt2.*", "apb_agt_cfg", apb_agt_cfg2); //
            uvm_config_db #(apb_agent_config)::set(this, "apb_agt3.*", "apb_agt_cfg", apb_agt_cfg3); //
            `uvm_info(report_id, "AGENT_CFG(s) set into config_db", UVM_LOW);
            
            icb_agt = icb_agent::type_id::create("icb_agt", this);
            apb_agt0 = apb_agent::type_id::create("apb_agt0", this);
            apb_agt1 = apb_agent::type_id::create("apb_agt1", this);
            apb_agt2 = apb_agent::type_id::create("apb_agt2", this);
            apb_agt3 = apb_agent::type_id::create("apb_agt3", this);

            icb_agt.is_active = UVM_ACTIVE;
            apb_agt0.is_active = UVM_ACTIVE;
            apb_agt1.is_active = UVM_ACTIVE;
            apb_agt2.is_active = UVM_ACTIVE;
            apb_agt3.is_active = UVM_ACTIVE;

            icb_sub = icb_subscriber::type_id::create("icb_sub", this);
            apb_sub0 = apb_subscriber::type_id::create("apb_sub0", this);
            apb_sub1 = apb_subscriber::type_id::create("apb_sub1", this);
            apb_sub2 = apb_subscriber::type_id::create("apb_sub2", this);
            apb_sub3 = apb_subscriber::type_id::create("apb_sub3", this);

            icb_mdl = icb_model::type_id::create("icb_mdl", this);
            apb_mdl0 = apb_model::type_id::create("apb_mdl0", this);
            apb_mdl1 = apb_model::type_id::create("apb_mdl1", this);
            apb_mdl2 = apb_model::type_id::create("apb_mdl2", this);
            apb_mdl3 = apb_model::type_id::create("apb_mdl3", this);

            scb = my_scoreboard::type_id::create("scb", this);

            icb_agt_mdl_fifo = new("icb_agt_mdl_fifo", this);
            icb_mdl_scb_fifo = new("icb_mdl_scb_fifo", this);
            apb_agt_mdl_fifo0 = new("apb_agt_mdl_fifo0", this);
            apb_mdl_scb_fifo0 = new("apb_mdl_scb_fifo0", this);
            apb_agt_mdl_fifo1 = new("apb_agt_mdl_fifo1", this);
            apb_mdl_scb_fifo1 = new("apb_mdl_scb_fifo1", this);
            apb_agt_mdl_fifo2 = new("apb_agt_mdl_fifo2", this);
            apb_mdl_scb_fifo2 = new("apb_mdl_scb_fifo2", this);
            apb_agt_mdl_fifo3 = new("apb_agt_mdl_fifo3", this);
            apb_mdl_scb_fifo3 = new("apb_mdl_scb_fifo3", this);

        endfunction : build_phase
        
        function void connect_phase(uvm_phase phase);
            icb_agt.icb_ap.connect(icb_sub.analysis_export);
            apb_agt0.apb_ap.connect(apb_sub0.analysis_export);
            apb_agt1.apb_ap.connect(apb_sub1.analysis_export);
            apb_agt2.apb_ap.connect(apb_sub2.analysis_export);
            apb_agt3.apb_ap.connect(apb_sub3.analysis_export);

            icb_agt.icb_ap.connect(icb_agt_mdl_fifo.analysis_export);
            apb_agt0.apb_ap.connect(apb_agt_mdl_fifo0.analysis_export);
            apb_agt1.apb_ap.connect(apb_agt_mdl_fifo1.analysis_export);
            apb_agt2.apb_ap.connect(apb_agt_mdl_fifo2.analysis_export);
            apb_agt3.apb_ap.connect(apb_agt_mdl_fifo3.analysis_export);

            icb_mdl.bgp.connect(icb_agt_mdl_fifo.blocking_get_export);
            apb_mdl0.bgp.connect(apb_agt_mdl_fifo0.blocking_get_export);
            apb_mdl1.bgp.connect(apb_agt_mdl_fifo1.blocking_get_export);
            apb_mdl2.bgp.connect(apb_agt_mdl_fifo2.blocking_get_export);
            apb_mdl3.bgp.connect(apb_agt_mdl_fifo3.blocking_get_export);

            icb_mdl.ap.connect(icb_mdl_scb_fifo.analysis_export);
            apb_mdl0.ap.connect(apb_mdl_scb_fifo0.analysis_export);
            apb_mdl1.ap.connect(apb_mdl_scb_fifo1.analysis_export);
            apb_mdl2.ap.connect(apb_mdl_scb_fifo2.analysis_export);
            apb_mdl3.ap.connect(apb_mdl_scb_fifo3.analysis_export);

            scb.icb_bgp.connect(icb_mdl_scb_fifo.blocking_get_export);
            scb.apb_bgp0.connect(apb_mdl_scb_fifo0.blocking_get_export);
            scb.apb_bgp1.connect(apb_mdl_scb_fifo1.blocking_get_export);
            scb.apb_bgp2.connect(apb_mdl_scb_fifo2.blocking_get_export);
            scb.apb_bgp3.connect(apb_mdl_scb_fifo3.blocking_get_export);

        endfunction : connect_phase

    endclass : my_env


endpackage : my_env_pkg