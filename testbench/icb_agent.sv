//=====================================================================
// Description:
// This file realize the ICB AGENT, includes data generator, driver and
// monitor.
// Designer : lynnxie@sjtu.edu.cn
// Revision History
// V0 date:2024/11/07 Initial version, lynnxie@sjtu.edu.cn
// V1 data:2024/11/24 Second version, extraordinary.h@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

package icb_agent_pkg;
    import objects_pkg::*;
    
    // Generator: Generate data for driver to transfer
    class icb_generator;

        // BUILD
        //=============================================================
        mailbox #(icb_trans)    gen2drv; // generator need a mailbox to transfer data to driver

        function new(
            mailbox #(icb_trans) gen2drv
        );
            this.gen2drv = gen2drv; // the mailbox will be create in agent
        endfunction //new()

        // FUNC : generate a data for transaction
        // **Optional** The random data generation can be realized here
        //=============================================================
        task automatic data_gen(
            input           read = 1'b1,
            input [7:0]     mask = 8'h00,
            input [63:0]    data = 64'h0000_0000_0000_0000,
            input [31:0]    addr = 32'h2000_0000
        );
            icb_trans   tran_data;
            tran_data = new();
            
            // set tran data according to input
            tran_data.read = read;
            tran_data.mask = mask;
            tran_data.wdata = data;
            tran_data.addr = addr;

            // send the generated data to driver
            this.gen2drv.put(tran_data);

        endtask

        task automatic data_seq_gen(
            input           read = 1'b1,
            input [7:0]     mask = 8'h00, 
            input int       num = 4,
            input           cmd_read = 1'b0
        );
            icb_trans   tran_data;
            
            logic [31:0] rand_val;
            logic [5:0] sel;
            logic [1:0] sel_tmp;

            for (int i = 0; i < num; i++) begin
                tran_data = new();

                tran_data.read = read;
                tran_data.mask = mask;
                // tran_data.wdata = $urandom();

                if(i % 2 ==  0)
                begin
                    rand_val = $urandom();
                    sel_tmp = rand_val[2:1];
                    sel = ~{1 << sel_tmp};
                    // $display("sel = %b", sel);
                    tran_data.wdata = {32'b0, rand_val[31:8], sel, cmd_read, 1'b1};
                end
                if(i % 2 ==  1)
                begin
                    rand_val = $urandom();
                    tran_data.wdata = {32'b0, rand_val[31:1], 1'b0};
                end
                    
                if(read == 1'b0)
                    tran_data.addr = 32'h2000_0010;
                else
                    tran_data.addr = 32'h2000_0018;
                // send the generated data to driver
                this.gen2drv.put(tran_data);
                // $display("Time=%t: Generated %d wdata=%h", $time, i+1, tran_data.wdata);

            end

        endtask       
    endclass //icb_generator

    // Driver: Converts the received packets to the format of the ICB protocol
    class icb_driver;

        // BUILD
        //=============================================================
        mailbox #(icb_trans)    gen2drv; // receive the data from generator

        function new(
            mailbox #(icb_trans)    gen2drv
        );
            this.gen2drv = gen2drv;
        endfunction //new()
        
        // CONNECT
        //=============================================================
        local virtual icb_bus.master active_channel;

        function void set_intf(
            virtual icb_bus.master icb
        );
            this.active_channel = icb;

            // port initialization to avoid 'x' state in dut
            this.active_channel.mst_cb.icb_cmd_valid <= 1'b0;
            this.active_channel.mst_cb.icb_cmd_read <= 1'b0;
            this.active_channel.mst_cb.icb_cmd_addr <= 32'h0000_0000;
            this.active_channel.mst_cb.icb_cmd_wdata <= 64'h0000_0000_0000_0000;
            this.active_channel.mst_cb.icb_cmd_wmask <= 8'h00;

            this.active_channel.mst_cb.icb_rsp_ready <= 1'b1;
        endfunction

        // FUNC : data transfer
        //=============================================================
        task automatic data_trans();
            icb_trans   get_trans;

            // get the input data and address from mailbox
            this.gen2drv.get(get_trans);

            // setup the transaction
            @(this.active_channel.mst_cb)
            this.active_channel.mst_cb.icb_cmd_valid <= 1'b1;
            this.active_channel.mst_cb.icb_cmd_read <= get_trans.read;
            this.active_channel.mst_cb.icb_cmd_wmask <= get_trans.mask;
            this.active_channel.mst_cb.icb_cmd_wdata <= get_trans.wdata;
            this.active_channel.mst_cb.icb_cmd_addr <= get_trans.addr;
            this.active_channel.mst_cb.icb_rsp_ready <= 1'b1;

            // wait until the handshake finished
            while(!this.active_channel.icb_cmd_ready) begin
                @(this.active_channel.mst_cb);
            end

            // end the transaction
            // @(this.active_channel.mst_cb)
            this.active_channel.mst_cb.icb_cmd_valid <= 1'b0;

            
        endtask //automatic

        task automatic data_seq_trans(
            input int       num = 4
        );
            icb_trans   get_trans;

            for (int i = 0; i < num; i++) begin

                // get the input data and address from mailbox
                this.gen2drv.get(get_trans);
                // $display("Time=%t: Transmitting wdata=%h", $time, get_trans.wdata);
                
                this.active_channel.mst_cb.icb_cmd_valid <= 1'b1;
                this.active_channel.mst_cb.icb_cmd_read <= get_trans.read;
                this.active_channel.mst_cb.icb_cmd_wmask <= get_trans.mask;
                this.active_channel.mst_cb.icb_cmd_wdata <= get_trans.wdata;
                this.active_channel.mst_cb.icb_cmd_addr <= get_trans.addr;
                this.active_channel.mst_cb.icb_rsp_ready <= 1'b1;
                
                @(this.active_channel.mst_cb);
                while(!this.active_channel.icb_cmd_ready) begin
                    @(this.active_channel.mst_cb);
                end

                
            end
            this.active_channel.mst_cb.icb_cmd_valid <= 1'b0;
        endtask //automatic

    endclass //icb_driver

    // **Optional** 
    // Monitor: Collect ICB data and convert it to data package for
    //          scoreboard to compare result.
    class icb_monitor;

        // BUILD
        //=============================================================
        // ...
        mailbox #(icb_trans) icb2sb;

        function new(
            mailbox #(icb_trans) icb2sb
        );
            this.icb2sb = icb2sb;
        endfunction

        // CONNECT
        //=============================================================
        // ...
        local virtual icb_bus.master active_channel;
        function void set_intf(
            virtual icb_bus.master icb
        );
            this.active_channel = icb;
        endfunction // set_intf

        // FUNC: Collect command (write) and response (read) transactions
        //=============================================================
        // ...
        task automatic collect_data();
            icb_trans transaction;

            $display("[TB- IAG ] ICB Agent Collect Data Program Begin !");
            

            forever begin
                while(!((this.active_channel.mst_cb.icb_cmd_valid && !this.active_channel.mst_cb.icb_cmd_read) 
                     || (this.active_channel.icb_rsp_valid && this.active_channel.mst_cb.icb_cmd_read)))
                begin
                    @(this.active_channel.mst_cb);
                end
                
                transaction = new();

                
                // processing write channel
                if(this.active_channel.mst_cb.icb_cmd_valid 
                                                            && !this.active_channel.mst_cb.icb_cmd_read)
                begin
                    transaction.read = this.active_channel.mst_cb.icb_cmd_read;
                    transaction.mask = this.active_channel.mst_cb.icb_cmd_wmask;
                    transaction.wdata = this.active_channel.mst_cb.icb_cmd_wdata;
                    transaction.addr = this.active_channel.mst_cb.icb_cmd_addr;
                    // $display("sample wdata = %h", this.active_channel.mst_cb.icb_cmd_wdata);

                    // send data to scoreboard
                    this.icb2sb.put(transaction);
                    @(this.active_channel.mst_cb);
                end

                // processing read channel
                if(this.active_channel.mst_cb.icb_rsp_ready && this.active_channel.icb_rsp_valid
                                                            && this.active_channel.mst_cb.icb_cmd_read)
                begin
                    transaction.read = this.active_channel.mst_cb.icb_cmd_read;
                    transaction.rdata = this.active_channel.icb_rsp_rdata;
                    transaction.addr = this.active_channel.mst_cb.icb_cmd_addr;
                    
                    // $display("sample rdata = %h", this.active_channel.icb_rsp_rdata);
                    // send data to scoreboard
                    this.icb2sb.put(transaction);
                    @(this.active_channel.mst_cb);
                end

            end
        endtask
    endclass //icb_monitor

    // Agent: The top class that connects generator, driver and monitor
    class icb_agent;
        
        // BUILD
        //=============================================================
        mailbox #(icb_trans)    gen2drv;
        mailbox #(icb_trans)    icb2sb;
        icb_generator           icb_generator;
        icb_driver              icb_driver;
        icb_monitor             icb_monitor;

        function new(
            mailbox #(icb_trans) icb2sb
        );
            this.gen2drv = new(32);
            this.icb2sb = icb2sb;
            this.icb_generator = new(this.gen2drv);
            this.icb_driver = new(this.gen2drv);
            this.icb_monitor = new(this.icb2sb);
        endfunction //new()

        // CONNECT
        //=============================================================
        function void set_intf(
            virtual icb_bus icb
        );   
            // connect to icb_driver
            this.icb_driver.set_intf(icb);

            // connect to icb_monitor
            this.icb_monitor.set_intf(icb);
        endfunction //automatic

        // FUN : single data tran
        //=============================================================
        task automatic single_tran(
            input           read = 1'b1,
            input [7:0]     mask = 8'h00,
            input [63:0]    data = 64'h0000_0000_0000_0000,
            input [31:0]    addr = 32'h2000_0000
        );
            // generate data
            this.icb_generator.data_gen(read, mask, data, addr);

            // drive data
            this.icb_driver.data_trans();
                
        endtask //automatic

        task automatic seq_tran(
            input           read = 1'b0,
            input [7:0]     mask = 8'h00,
            input           cmd_read = 1'b0,
            input int       num = 4
        );
            this.icb_generator.data_seq_gen(read, mask, num, cmd_read);

            this.icb_driver.data_seq_trans(num);

        endtask



    endclass //icb_agent
endpackage


