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
endmodule: tb_2