package my_agent_pkg;

    import uvm_pkg::*;
    import my_sequence_pkg::*;

    class icb_agent_config extends uvm_object;
        virtual icb_bus icb_vif;
    endclass : icb_agent_config

    class apb_agent_config extends uvm_object;
        virtual apb_bus apb_vif;
    endclass : apb_agent_config

    typedef uvm_sequencer #(icb_trans) icb_sequencer;
    typedef uvm_sequencer #(apb_trans) apb_sequencer;

    class icb_driver extends uvm_driver #(icb_trans);
        `uvm_component_utils(icb_driver)

        string report_id = get_type_name();

        icb_agent_config icb_agt_cfg;
        virtual icb_bus.master icb_vif;

        function new(string name = "icb_driver", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new

        function void build_phase(uvm_phase phase);
            // super.build_phase(phase);
            if(!uvm_config_db #(icb_agent_config)::get(this, "", "icb_agt_cfg", icb_agt_cfg))
                `uvm_fatal(report_id, "Class icb_agent_config not found!")
            icb_vif = icb_agt_cfg.icb_vif;
        endfunction : build_phase

        task run_phase(uvm_phase phase);
            forever begin
                seq_item_port.get_next_item(req);

                // `uvm_info(report_id, "ICB driver gets the data!", UVM_LOW);
                
                @(posedge icb_vif.mst_cb);
                icb_vif.mst_cb.icb_cmd_valid <= 1'b1;
                icb_vif.mst_cb.icb_cmd_addr <= req.addr;
                icb_vif.mst_cb.icb_cmd_read <= req.read;
                icb_vif.mst_cb.icb_cmd_wdata <= req.wdata;
                icb_vif.mst_cb.icb_cmd_wmask <= req.mask;
                icb_vif.mst_cb.icb_rsp_ready <= 1'b1;

                // @(posedge icb_vif.mst_cb);
                while (!icb_vif.icb_cmd_ready) begin
                    @(posedge icb_vif.mst_cb);
                end

                icb_vif.mst_cb.icb_cmd_valid <= 0;

                // `uvm_info(report_id, "ICB drive data ing", UVM_LOW);

                seq_item_port.item_done();
            end
        endtask : run_phase

    endclass : icb_driver

    class apb_driver extends uvm_driver #(apb_trans);
        `uvm_component_utils(apb_driver)

        string report_id = get_type_name();

        apb_agent_config apb_agt_cfg;
        virtual apb_bus.slave apb_vif;

        function new(string name = "apb_driver", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new

        function void build_phase(uvm_phase phase);
            // super.build_phase(phase);
            if(!uvm_config_db #(apb_agent_config)::get(this, "", "apb_agt_cfg", apb_agt_cfg))
                `uvm_fatal(report_id, "Class apb_agent_config not found!")
            apb_vif = apb_agt_cfg.apb_vif;
        endfunction : build_phase

        task run_phase(uvm_phase phase);
            forever begin
                seq_item_port.get_next_item(req);
                
                while (!(apb_vif.psel && apb_vif.penable)) begin
                    @(posedge apb_vif.slv_cb);
                end

                apb_vif.slv_cb.pready <= 1'b1;
                apb_vif.slv_cb.prdata <= req.rdata;

                @(posedge apb_vif.slv_cb);
                apb_vif.slv_cb.pready <= 1'b0;
                
                seq_item_port.item_done();
            end
        endtask : run_phase

    endclass : apb_driver

    class icb_monitor extends uvm_monitor;
        `uvm_component_utils(icb_monitor)

        string report_id = get_type_name();

        uvm_analysis_port #(icb_trans) icb_ap;

        icb_agent_config icb_agt_cfg;
        virtual icb_bus.others icb_vif;

        function new(string name = "icb_monitor", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new

        function void build_phase(uvm_phase phase);
            icb_ap = new("icb_ap", this);
            if(!uvm_config_db #(icb_agent_config)::get(this, "", "icb_agt_cfg", icb_agt_cfg))
                `uvm_fatal(report_id, "Class icb_agent_config not found!")
            icb_vif = icb_agt_cfg.icb_vif;
        endfunction : build_phase

        task run_phase(uvm_phase phase);
            icb_trans tx_monitor_o;
            forever begin
                
                while(!( (icb_vif.icb_cmd_valid && !icb_vif.icb_cmd_read) 
                    || (icb_vif.icb_rsp_valid && icb_vif.icb_cmd_read) ))
                begin
                    @(icb_vif.mon_cb);
                end
                
                // `uvm_info(report_id, "ICB monitor is running!", UVM_LOW);

                tx_monitor_o = icb_trans::type_id::create("tx_monitor_o");
                // $display("icb_cmd_valid: %b, icb_cmd_read: %b", icb_vif.icb_cmd_valid, icb_vif.icb_cmd_read);
                if(icb_vif.icb_cmd_valid && !icb_vif.icb_cmd_read)
                begin
                    // `uvm_info(report_id, "ICB monitor is running!", UVM_LOW);
                    tx_monitor_o.read = icb_vif.icb_cmd_read;
                    tx_monitor_o.mask = icb_vif.icb_cmd_wmask;
                    tx_monitor_o.wdata = icb_vif.icb_cmd_wdata;
                    tx_monitor_o.addr = icb_vif.icb_cmd_addr;

                    `uvm_info(report_id, $sformatf("%b %x %x %x", 
                                tx_monitor_o.read, tx_monitor_o.mask, tx_monitor_o.wdata, tx_monitor_o.addr), UVM_HIGH);
                    icb_ap.write(tx_monitor_o);

                    @(icb_vif.mon_cb);
                end

                if(icb_vif.icb_rsp_ready && icb_vif.icb_rsp_valid && icb_vif.icb_cmd_read)
                begin
                    tx_monitor_o.read = icb_vif.icb_cmd_read;
                    tx_monitor_o.addr = icb_vif.icb_cmd_addr;
                    tx_monitor_o.rdata = icb_vif.icb_rsp_rdata;

                    `uvm_info(report_id, $sformatf("%b %x %x", 
                                tx_monitor_o.read, tx_monitor_o.addr, tx_monitor_o.rdata), UVM_HIGH);
                    icb_ap.write(tx_monitor_o);

                    @(icb_vif.mon_cb);
                end       
            end
        endtask : run_phase
    
    endclass : icb_monitor

    class apb_monitor extends uvm_monitor;
        `uvm_component_utils(apb_monitor)

        string report_id = get_type_name();

        uvm_analysis_port #(apb_trans) apb_ap;

        apb_agent_config apb_agt_cfg;
        virtual apb_bus.others apb_vif;

        function new(string name = "apb_monitor", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new

        function void build_phase(uvm_phase phase);
            apb_ap = new("apb_ap", this);
            if(!uvm_config_db #(apb_agent_config)::get(this, "", "apb_agt_cfg", apb_agt_cfg))
                `uvm_fatal(report_id, "Class apb_agent_config not found!")
            apb_vif = apb_agt_cfg.apb_vif;
        endfunction : build_phase

        task run_phase(uvm_phase phase);
            apb_trans tx_monitor_o;
            forever begin
                while (!(apb_vif.penable)) begin
                    @(apb_vif.pready);
                end

                // `uvm_info(report_id, "APB monitor is running!", UVM_LOW);
                
                tx_monitor_o = apb_trans::type_id::create("tx_monitor_o");
                tx_monitor_o.write = apb_vif.pwrite;
                tx_monitor_o.wdata = apb_vif.pwdata;
                tx_monitor_o.addr = apb_vif.paddr;
                tx_monitor_o.rdata = apb_vif.prdata;

                `uvm_info(report_id, $sformatf("%b %x %x %x", 
                            tx_monitor_o.write, tx_monitor_o.wdata, tx_monitor_o.addr, tx_monitor_o.rdata), UVM_HIGH)
                apb_ap.write(tx_monitor_o);

                @(apb_vif.mon_cb);
            end
        endtask : run_phase
    endclass : apb_monitor

    class icb_agent extends uvm_agent;
        `uvm_component_utils(icb_agent)

        uvm_analysis_port #(icb_trans) icb_ap;

        icb_sequencer icb_sqr;
        icb_driver icb_drv;
        icb_monitor icb_mon;

        function new(string name = "icb_agent", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new

        function void build_phase(uvm_phase phase);
            if(is_active == UVM_ACTIVE) begin
                icb_sqr = icb_sequencer::type_id::create("icb_sqr", this);
                icb_drv = icb_driver::type_id::create("icb_drv", this);
            end
            icb_mon = icb_monitor::type_id::create("icb_mon", this);
        endfunction : build_phase

        function void connect_phase(uvm_phase phase);
            if(is_active == UVM_ACTIVE) begin
                icb_drv.seq_item_port.connect(icb_sqr.seq_item_export);
            end
            icb_ap = icb_mon.icb_ap;
        endfunction : connect_phase
        
    endclass : icb_agent

    class apb_agent extends uvm_agent;
        `uvm_component_utils(apb_agent)

        uvm_analysis_port #(apb_trans) apb_ap;

        apb_sequencer apb_sqr;
        apb_driver apb_drv;
        apb_monitor apb_mon;

        function new(string name = "apb_agent", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new

        function void build_phase(uvm_phase phase);
            if(is_active == UVM_ACTIVE) begin
                apb_sqr = apb_sequencer::type_id::create("apb_sqr", this);
                apb_drv = apb_driver::type_id::create("apb_drv", this);
            end
            apb_mon = apb_monitor::type_id::create("apb_mon", this);
        endfunction : build_phase

        function void connect_phase(uvm_phase phase);
            if(is_active == UVM_ACTIVE) begin
                apb_drv.seq_item_port.connect(apb_sqr.seq_item_export);
            end
            apb_ap = apb_mon.apb_ap;
        endfunction : connect_phase

    endclass : apb_agent
    
endpackage : my_agent_pkg
