//=====================================================================
// Description:
// This file realize the APB AGENT, includes data generator, driver and
// monitor.
// Designer : lynnxie@sjtu.edu.cn
// Revision History
// V0 date:2024/11/11 Initial version, lynnxie@sjtu.edu.cn
// V1 data:2024/11/24 Second version, extraordinary.h@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

package apb_agent_pkg;
    import objects_pkg::*;

    // Generator: Generate data for driver to transfer
    class apb_generator;
        // BUILD
        //=============================================================
        // ...
        mailbox #(apb_trans)    gen2drv;

        function new(
            mailbox #(apb_trans) gen2drv
        );
            this.gen2drv = gen2drv; // the mailbox will be create in agent
        endfunction //new()

        // FUNC
        //=============================================================
        // ...
        task automatic data_gen(
            input [31:0]    rdata = 32'h0000_0000
        );
            apb_trans   tran_data;
            tran_data = new();
            
            // set tran data according to input
            tran_data.rdata = rdata;

            // send the generated data to driver
            this.gen2drv.put(tran_data);
        endtask
    endclass //apb_generator

    // Driver: Converts the received packets to the format of the APB protocol
    class apb_driver;

        // BUILD
        //=============================================================
        // ...
        mailbox #(apb_trans)    gen2drv; // receive the data from generator

        function new(
            mailbox #(apb_trans)    gen2drv
        );
            this.gen2drv = gen2drv;
        endfunction //new()
        
        // CONNECT
        //=============================================================
        // ...
        local virtual apb_bus.slave active_channel;

        function void set_intf(
            virtual apb_bus.slave apb
        );
            this.active_channel = apb;

            // port initialization to avoid 'x' state in dut
            this.active_channel.slv_cb.prdata <= 32'h0000_0000;
            this.active_channel.slv_cb.pready <= 1'b0;

        endfunction

        // FUNC
        //=============================================================
        // ...
        task automatic data_trans();
            apb_trans   get_trans;

            // get the input data and address from mailbox
            this.gen2drv.get(get_trans);        

            // wait until the handshake begin
            while(!(this.active_channel.psel && this.active_channel.penable)) begin
                @(this.active_channel.slv_cb);
            end

            // begin the transaction
            this.active_channel.slv_cb.pready <= 1'b1;
            this.active_channel.slv_cb.prdata <= get_trans.rdata;

            // end the transaction
            @(this.active_channel.slv_cb)
            this.active_channel.slv_cb.pready <= 1'b0;

            // get_trans.delete();

        endtask //automatic
    endclass //apb_driver

    // **Optional** 
    // Monitor: Collect APB data and convert it to data package for
    //          scoreboard to compare result.
    class apb_monitor;

        // BUILD
        //=============================================================
        // ...
        mailbox #(apb_trans) apb2sb;
        static int instance_cnt = 0;
        int ins_id;

        function new(
            mailbox #(apb_trans) apb2sb
        );
            this.apb2sb = apb2sb;
            instance_cnt++; 
            ins_id = instance_cnt;
        endfunction //new()

        // CONNECT
        //=============================================================
        // ...
        local virtual apb_bus.slave active_channel;

        function void set_intf(
            virtual apb_bus.slave apb
        );
            this.active_channel = apb;
        endfunction // set_intf
        
        // FUNC
        //=============================================================
        // ...
        task automatic collect_data();
            apb_trans   rsp_trans;
            $display("[TB- AAG ] APB Agent %0d Collect Data Program Begin !", ins_id);
            
            forever begin
                while(!(this.active_channel.penable))
                begin
                    @(this.active_channel.slv_cb.pready);
                end

                rsp_trans = new();

                rsp_trans.write = this.active_channel.pwrite;
                rsp_trans.addr = this.active_channel.paddr;
                rsp_trans.wdata = this.active_channel.pwdata;
                rsp_trans.rdata = this.active_channel.slv_cb.prdata;

                // $display("sample prdata = %h", this.active_channel.slv_cb.prdata);
                // $display("sample pwdata = %h", this.active_channel.pwdata);
                this.apb2sb.put(rsp_trans);
                @(this.active_channel.slv_cb);
            end
        endtask // collect_data
    endclass //apb_monitor

    // Agent: The top class that connects generator, driver and monitor
    class apb_agent;
        
        // BUILD
        //=============================================================
        // ...
        mailbox #(apb_trans)    gen2drv;
        mailbox #(apb_trans)    apb2sb;
        apb_generator           apb_generator;
        apb_driver              apb_driver;
        apb_monitor             apb_monitor;

        function new(
            mailbox #(apb_trans) apb2sb
        );
            // ...
            this.gen2drv = new(32);
            this.apb2sb = apb2sb;
            this.apb_generator = new(this.gen2drv);
            this.apb_driver = new(this.gen2drv);
            this.apb_monitor = new(this.apb2sb);
        endfunction //new()

        // CONNECT
        //=============================================================
        function void set_intf(
            virtual apb_bus apb
        );   
            // connect to apb_driver
            // ...
            this.apb_driver.set_intf(apb);

            // connect to apb_monitor
            this.apb_monitor.set_intf(apb);
        endfunction //automatic

        // FUN : single data tran
        //=============================================================
        task automatic single_tran(
            // ...
            input [31:0]    rdata = 32'h0000_0000
        );
            // generate data
            // ...
            this.apb_generator.data_gen(rdata);

            // drive data
            // ...
            this.apb_driver.data_trans();
                
        endtask //automatic

        task automatic seq_tran(
            int num = 4
        );
            for(int i = 0; i < num; i++)
            begin
                single_tran($urandom());
            end
        endtask
    endclass //apb_agent
endpackage


