package my_test_pkg;

    parameter NUM_ENV = 3;

    import uvm_pkg::*;
    import my_sequence_pkg::*;
    import my_agent_pkg::*;
    import my_env_pkg::*;

    class icb_vsqr extends uvm_sequencer;
        `uvm_component_utils(icb_vsqr)

        icb_sequencer p_icb_sqr[NUM_ENV];

        function new(string name = "icb_vsqr", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new

    endclass : icb_vsqr

    class apb_vsqr extends uvm_sequencer;
        `uvm_component_utils(apb_vsqr)

        apb_sequencer p_apb_sqr[NUM_ENV];

        function new(string name = "apb_vsqr", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new
    
    endclass : apb_vsqr

    class my_test extends uvm_test;

        `uvm_component_utils(my_test)

        string report_id = get_type_name();
        int i;

        my_env_config env_cfg[NUM_ENV];
        my_env env[NUM_ENV];
        icb_vsqr icb_vsqr_h;
        apb_vsqr apb_vsqr_h0;
        apb_vsqr apb_vsqr_h1;
        apb_vsqr apb_vsqr_h2;
        apb_vsqr apb_vsqr_h3;

        function new(string name = "my_test", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new

        function void build_phase(uvm_phase phase);
            for(i = 0; i < NUM_ENV; i++) begin
                env_cfg[i] = new();
            end
            
            for(i = 0; i < NUM_ENV; i++) begin
                if(!uvm_config_db #(virtual icb_bus) :: get(this, "", $sformatf("icb_vif%1d", i), env_cfg[i].icb_vif))
                    `uvm_fatal("NO_VIF", $sformatf("Virtual interface icb_vif%1d was not set!", i));
                for(int j = 0; j < 4; j++) begin
                    if(!uvm_config_db #(virtual apb_bus) :: get(this, "", $sformatf("apb_vif%1d %1d", i, j), env_cfg[i].apb_vif[j]))
                        `uvm_fatal("NO_VIF", $sformatf("Virtual interface apb_vif%1d %1d was not set!", i, j));
                end
            end

            for(i = 0; i < NUM_ENV; i++) begin                    
                uvm_config_db #(my_env_config)::set(this, $sformatf("env[%1d]", i), "env_cfg", env_cfg[i]);
            end

            `uvm_info(report_id, "ENV_CFG(s) set into config_db", UVM_LOW);

            for(i = 0; i < NUM_ENV; i++) begin
                env[i] = my_env::type_id::create($sformatf("env[%1d]", i), this);
            end

            icb_vsqr_h = icb_vsqr::type_id::create("icb_vsqr_h", this);
            apb_vsqr_h0 = apb_vsqr::type_id::create("apb_vsqr_h0", this);
            apb_vsqr_h1 = apb_vsqr::type_id::create("apb_vsqr_h1", this);
            apb_vsqr_h2 = apb_vsqr::type_id::create("apb_vsqr_h2", this);
            apb_vsqr_h3 = apb_vsqr::type_id::create("apb_vsqr_h3", this);

        endfunction : build_phase

        function void connect_phase(uvm_phase phase);
            for(i = 0; i < NUM_ENV; i++) begin
                icb_vsqr_h.p_icb_sqr[i] = env[i].icb_agt.icb_sqr;
                apb_vsqr_h0.p_apb_sqr[i] = env[i].apb_agt0.apb_sqr;
                apb_vsqr_h1.p_apb_sqr[i] = env[i].apb_agt1.apb_sqr;
                apb_vsqr_h2.p_apb_sqr[i] = env[i].apb_agt2.apb_sqr;
                apb_vsqr_h3.p_apb_sqr[i] = env[i].apb_agt3.apb_sqr;
            end
            
            // uvm_top.print_topology();
        endfunction : connect_phase
        
        function void report_phase(uvm_phase phase);
            uvm_report_server report_server_h;
            int num_err;
            int num_fatal;

            report_server_h = uvm_report_server::get_server();
            num_err = report_server_h.get_severity_count(UVM_ERROR);
            num_fatal = report_server_h.get_severity_count(UVM_FATAL);

            //Final result
            if(num_err==0 && num_fatal==0) begin
                $display("###########################################");
                $display("############    TEST PASSED    ############");
                $display("###########################################");
            end else begin
                $display("###########################################");
                $display("############    TEST FAILED    ############");
                $display("###########################################");
            end
        endfunction : report_phase

    endclass : my_test

    class test0 extends my_test;
        `uvm_component_utils(test0)

        string report_id = get_type_name();

        function new(string name = "test0", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new
    
        task run_phase(uvm_phase phase);

            fork
                // env[0]: icb write apb, icb read apb, and apb return data to icb
                begin 
                    icb_cfg_key cfg_key;
                    icb_enable_apb enable_apb;
                    icb_disable_apb disable_apb;
                    icb_write_apb wr_req;
                    icb_read_apb rd_req;
                    icb_read_rdata rd_rdata;
                    apb_cont_resp apb_resp0, apb_resp1, apb_resp2, apb_resp3;
                    apb_cont_resp apb_resp4, apb_resp5, apb_resp6, apb_resp7;
                    icb_read_state rd_state;

                    cfg_key = icb_cfg_key::type_id::create("cfg_key");
                    enable_apb = icb_enable_apb::type_id::create("enable_apb");
                    disable_apb = icb_disable_apb::type_id::create("disable_apb");
                    wr_req = icb_write_apb::type_id::create("wr_req");
                    rd_req = icb_read_apb::type_id::create("rd_req");
                    rd_rdata = icb_read_rdata::type_id::create("rd_rdata");
                    apb_resp0 = apb_cont_resp::type_id::create("apb_resp0");
                    apb_resp1 = apb_cont_resp::type_id::create("apb_resp1");
                    apb_resp2 = apb_cont_resp::type_id::create("apb_resp2");
                    apb_resp3 = apb_cont_resp::type_id::create("apb_resp3");
                    apb_resp4 = apb_cont_resp::type_id::create("apb_resp4");
                    apb_resp5 = apb_cont_resp::type_id::create("apb_resp5");
                    apb_resp6 = apb_cont_resp::type_id::create("apb_resp6");
                    apb_resp7 = apb_cont_resp::type_id::create("apb_resp7");
                    rd_state = icb_read_state::type_id::create("rd_state");

                    phase.phase_done.set_drain_time(this, 1000);

                    phase.raise_objection(this);

                    wait(env[0].env_cfg.icb_vif.rst_n == 1);

                    cfg_key.start(icb_vsqr_h.p_icb_sqr[0]);
                    enable_apb.start(icb_vsqr_h.p_icb_sqr[0]);
                    rd_state.start(icb_vsqr_h.p_icb_sqr[0]);

                    fork
                        wr_req.start(icb_vsqr_h.p_icb_sqr[0]);
                        
                        apb_resp0.start(apb_vsqr_h0.p_apb_sqr[0]);
                        apb_resp1.start(apb_vsqr_h1.p_apb_sqr[0]);
                        apb_resp2.start(apb_vsqr_h2.p_apb_sqr[0]);
                        apb_resp3.start(apb_vsqr_h3.p_apb_sqr[0]);

                    join_any

                    rd_state.start(icb_vsqr_h.p_icb_sqr[0]);


                    #2000;

                    disable fork;

                    fork
                        rd_req.start(icb_vsqr_h.p_icb_sqr[0]);

                        apb_resp4.start(apb_vsqr_h0.p_apb_sqr[0]);
                        apb_resp5.start(apb_vsqr_h1.p_apb_sqr[0]);
                        apb_resp6.start(apb_vsqr_h2.p_apb_sqr[0]);
                        apb_resp7.start(apb_vsqr_h3.p_apb_sqr[0]);
                    join_any
                    rd_state.start(icb_vsqr_h.p_icb_sqr[0]);

                    rd_rdata.start(icb_vsqr_h.p_icb_sqr[0]);

                    rd_state.start(icb_vsqr_h.p_icb_sqr[0]);


                    #2000;

                    disable fork;
                    
                    disable_apb.start(icb_vsqr_h.p_icb_sqr[0]);

                    phase.drop_objection(this);
                end
                
                // env[1]: WFIFO empty/full test
                begin
                    icb_cfg_key cfg_key1;
                    icb_enable_apb enable_apb1;
                    icb_disable_apb disable_apb1;
                    icb_write_apb wr_req1;
                    apb_cont_resp apb_resp10, apb_resp11, apb_resp12, apb_resp13;
                    icb_read_state rd_state1;

                    cfg_key1 = icb_cfg_key::type_id::create("cfg_key1");
                    enable_apb1 = icb_enable_apb::type_id::create("enable_apb1");
                    disable_apb1 = icb_disable_apb::type_id::create("disable_apb1");
                    wr_req1 = icb_write_apb::type_id::create("wr_req1");
                    apb_resp10 = apb_cont_resp::type_id::create("apb_resp10");
                    apb_resp11 = apb_cont_resp::type_id::create("apb_resp11");
                    apb_resp12 = apb_cont_resp::type_id::create("apb_resp12");
                    apb_resp13 = apb_cont_resp::type_id::create("apb_resp13");
                    rd_state1 = icb_read_state::type_id::create("rd_state1");

                    phase.phase_done.set_drain_time(this, 1000);

                    phase.raise_objection(this);

                    wait(env[1].env_cfg.icb_vif.rst_n == 1);

                    cfg_key1.start(icb_vsqr_h.p_icb_sqr[1]);
                    rd_state1.start(icb_vsqr_h.p_icb_sqr[1]);
                    
                    wr_req1.num = 8;
                    apb_resp10.num = 8;
                    apb_resp11.num = 8;
                    apb_resp12.num = 8;
                    apb_resp13.num = 8;

                    wr_req1.start(icb_vsqr_h.p_icb_sqr[1]);

                    #1000; // make the wfifo full
                    rd_state1.start(icb_vsqr_h.p_icb_sqr[1]);

                    enable_apb1.start(icb_vsqr_h.p_icb_sqr[1]);

                    fork
                        apb_resp10.start(apb_vsqr_h0.p_apb_sqr[1]);
                        apb_resp11.start(apb_vsqr_h1.p_apb_sqr[1]);
                        apb_resp12.start(apb_vsqr_h2.p_apb_sqr[1]);
                        apb_resp13.start(apb_vsqr_h3.p_apb_sqr[1]);
                        
                    join_none
                    rd_state1.start(icb_vsqr_h.p_icb_sqr[1]);
                    #2000;

                    disable_apb1.start(icb_vsqr_h.p_icb_sqr[1]);
                    disable fork;

                    phase.drop_objection(this);

                end

                // env[2]: RFIFO empty/full test
                begin 
                    icb_cfg_key cfg_key2;
                    icb_enable_apb enable_apb2;
                    icb_disable_apb disable_apb2;
                    icb_read_apb rd_req2;
                    icb_read_rdata rd_rdata2;
                    apb_cont_resp apb_resp20, apb_resp21, apb_resp22, apb_resp23;
                    icb_read_state rd_state2;

                    cfg_key2 = icb_cfg_key::type_id::create("cfg_key2");
                    enable_apb2 = icb_enable_apb::type_id::create("enable_apb2");
                    disable_apb2 = icb_disable_apb::type_id::create("disable_apb2");
                    rd_req2 = icb_read_apb::type_id::create("rd_req2");
                    rd_rdata2 = icb_read_rdata::type_id::create("rd_rdata2");
                    apb_resp20 = apb_cont_resp::type_id::create("apb_resp20");
                    apb_resp21 = apb_cont_resp::type_id::create("apb_resp21");
                    apb_resp22 = apb_cont_resp::type_id::create("apb_resp22");
                    apb_resp23 = apb_cont_resp::type_id::create("apb_resp23");
                    rd_state2 = icb_read_state::type_id::create("rd_state2");

                    phase.phase_done.set_drain_time(this, 1000);

                    phase.raise_objection(this);

                    wait(env[2].env_cfg.icb_vif.rst_n == 1);
                    
                    cfg_key2.start(icb_vsqr_h.p_icb_sqr[2]);
                    enable_apb2.start(icb_vsqr_h.p_icb_sqr[2]);
                    rd_state2.start(icb_vsqr_h.p_icb_sqr[2]);

                    fork
                        rd_req2.start(icb_vsqr_h.p_icb_sqr[2]);

                        apb_resp20.start(apb_vsqr_h0.p_apb_sqr[2]);
                        apb_resp21.start(apb_vsqr_h1.p_apb_sqr[2]);
                        apb_resp22.start(apb_vsqr_h2.p_apb_sqr[2]);
                        apb_resp23.start(apb_vsqr_h3.p_apb_sqr[2]);

                        
                    join_any
                    rd_state2.start(icb_vsqr_h.p_icb_sqr[2]);
                    #3000; // make the rfifo full
                    rd_state2.start(icb_vsqr_h.p_icb_sqr[2]);

                    rd_rdata2.start(icb_vsqr_h.p_icb_sqr[2]);

                    rd_state2.start(icb_vsqr_h.p_icb_sqr[2]);


                    #1000;

                    disable_apb2.start(icb_vsqr_h.p_icb_sqr[2]);

                    phase.drop_objection(this);
                end
            join
        endtask : run_phase
    
    endclass : test0


    // just test the icb read apb, and apb return data to icb
    class test1 extends my_test;
        `uvm_component_utils(test1)

        string report_id = get_type_name();

        function new(string name = "test1", uvm_component parent = null);
            super.new(name, parent);
        endfunction : new
    
        task run_phase(uvm_phase phase);
            icb_cfg_key cfg_key;
            icb_enable_apb enable_apb;
            icb_disable_apb disable_apb;
            icb_read_apb rd_req;
            icb_read_rdata rd_rdata;
            apb_cont_resp apb_resp0, apb_resp1, apb_resp2, apb_resp3;


            cfg_key = icb_cfg_key::type_id::create("cfg_key");
            enable_apb = icb_enable_apb::type_id::create("enable_apb");
            disable_apb = icb_disable_apb::type_id::create("disable_apb");
            rd_req = icb_read_apb::type_id::create("rd_req");
            rd_rdata = icb_read_rdata::type_id::create("rd_rdata");
            apb_resp0 = apb_cont_resp::type_id::create("apb_resp0");
            apb_resp1 = apb_cont_resp::type_id::create("apb_resp1");
            apb_resp2 = apb_cont_resp::type_id::create("apb_resp2");
            apb_resp3 = apb_cont_resp::type_id::create("apb_resp3");

            phase.phase_done.set_drain_time(this, 1000);

            phase.raise_objection(this);
            
            wait(env[0].env_cfg.icb_vif.rst_n == 1);
            
            cfg_key.start(icb_vsqr_h.p_icb_sqr[0]);
            enable_apb.start(icb_vsqr_h.p_icb_sqr[0]);

            fork
                rd_req.start(icb_vsqr_h.p_icb_sqr[0]);

                apb_resp0.start(apb_vsqr_h0.p_apb_sqr[0]);
                apb_resp1.start(apb_vsqr_h1.p_apb_sqr[0]);
                apb_resp2.start(apb_vsqr_h2.p_apb_sqr[0]);
                apb_resp3.start(apb_vsqr_h3.p_apb_sqr[0]);
            join_any

            rd_rdata.start(icb_vsqr_h.p_icb_sqr[0]);
            
            #2000;

            disable_apb.start(icb_vsqr_h.p_icb_sqr[0]);

            phase.drop_objection(this);

        endtask : run_phase

    endclass : test1

endpackage : my_test_pkg