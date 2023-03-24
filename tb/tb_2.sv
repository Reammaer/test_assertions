let CLK_PERIOD      = 10;
let RESET_DURATION  = 100;

// Delays in clock
let MIN_DELAY       = 1;
let MAX_DELAY       = 2; 

`include "uvm_macros.svh"
import uvm_pkg::*;

module tb_2;

    // Time units
    timeunit 1ns;
    timeprecision 1ns;

    // Initialize global clock
    bit clk;
    always #(CLK_PERIOD) clk = ~clk;
    global clocking @(posedge clk);
    endclocking

    // Initialize default clocking for assertions
    default clocking @($global_clock); 
    endclocking

    // Initialize global reset
    bit reset;
    initial begin
        #(RESET_DURATION) reset = 1;
        #(RESET_DURATION) reset = 0;
    end


    // *********** Assertions ************* //
    
    // *** THROUGHTOUT *** //
    // Three consecutive enabled occurrences of 
    // "read" followed by four enabled occurrences
    // of "write". The occurrences of "read" and
    // "write" are enabled if "en" is asserted
    bit     read;
    bit     write;
    bit     en;
    initial begin
        #400;
        en = 1;
        #300;
        read = 1;
        repeat(3) @($global_clock);
        read = 0;
        write = 1;
        repeat(4) @($global_clock);
        write = 0;
    end

    // property en_read_write_throughout;
    //     (read && en) [*3] |=> (write && en) [*4];
    // endproperty: en_read_write_throughout
    // EN_READ_WRITE_THROUGHTOUT: assert property(en_read_write_throughout) else begin
    //     `uvm_error("A1_RAISE", $sformatf("Assertion is failing in time=%0tns", $time))
    // end
                    // ***** OR ***** //
    property en_read_write_throughout;
        en throughout read[*3] |=> write[*4];
    endproperty: en_read_write_throughout
    EN_READ_WRITE_THROUGHTOUT: assert property(en_read_write_throughout) else begin
        `uvm_error("EN_READ_WRITE_THROUGHTOUT", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    EN_READ_WRITE_THROUGHTOUT_CV: cover property(en_read_write_throughout);

    // *** GOto REPETITION **
    // After request "req1" is serviced by "done" asserted, signa; "ready" should be asaserted
    // We need to check "ready" in the clock tick following the clock tock
    // when "done" became high for the first time after "req1" is asserted
    bit req1;
    bit done;
    bit ready;
    initial begin
        #1000;
        req1 = 1;
        #400;
        done = 1;
        @($global_clock);
        ready = 1;
    end

    // property req_done_ready;
    //     req1 ##1 !done[*] ##1 done |=> ready;
    // endproperty: req_done_ready
                        
                        // ***** OR ***** //
    property req_done_ready;
        req1 ##1 done[->1] |=> ready;
    endproperty: req_done_ready
    
    REQ_DONE_READY: assert property(req_done_ready) else begin
        `uvm_error("REQ_DONE_READY", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    REQ_DONE_READY_CV: cover property(req_done_ready);

    // After "start2" is asserted, at each occurence of request "req2",
    // starting from the fourth end ending with the fifth one,
    // enable "en2" must be asserted
    task wait_n_cycles(int n);
        repeat(n) @($global_clock);
    endtask: wait_n_cycles

    // bit req2, start2, en2;
    // initial begin
    //     #500;
    //     start2 = 1;
    //     wait_n_cycles(3);
    //     req2 = 1;
    //     en2 = 1;
    //     start2 = 0;
    //     wait_n_cycles(1);
    //     req2 = 0;
    //     en2 = 0;
    // end

    // property start_req_en;
    //     start2 ##1 req2[->4:5] |-> en2;
    // endproperty: start_req_en
    // START_REQ_EN: assert property(start_req_en) else begin
    //     `uvm_error("START_REQ_EN", $sformatf("Assertion is failing in time=%0tns", $time))
    // end
    // START_REQ_EN_CV: cover property(start_req_en);

    // After "start_ev", signal "next" should be asserted at least ten times;
    bit start_ev, next;
    initial begin
        #500;
        start_ev = 1;
        wait_n_cycles(1);
        next = 1;
        wait_n_cycles(1);
        start_ev = 0;
        wait_n_cycles(10);
        next = 0;
        
    end

    START_ENV:      assert property(start_ev |=> strong(next[->10]));  
    START_ENV_CV:   cover property(start_ev |=> strong(next[->10]));

endmodule: tb_2