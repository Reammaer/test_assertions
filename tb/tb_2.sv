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
        `uvm_error("A1_RAISE", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    EN_READ_WRITE_THROUGHTOUT_CV: cover property(en_read_write_throughout);






endmodule: tb_2