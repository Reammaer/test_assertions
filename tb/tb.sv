

let CLK_PERIOD      = 10;
let RESET_DURATION  = 100;

// Delays in clock
let MIN_DELAY       = 1;
let MAX_DELAY       = 2; 

`include "uvm_macros.svh"
import uvm_pkg::*;

module tb;

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

    // Initialize DUT

    // Run stimulus

    // Additional function
    task wait_n_cycles(int n);
        ##n;
    endtask: wait_n_cycles

    // Assertion block
    // Test assert 1
    logic a;
    logic b;
    initial begin
        forever begin
            a = 0;
            b = 0;
            #($urandom_range(100, 1000));
            @(posedge clk)
            a = 1;
            wait_n_cycles($urandom_range(MIN_DELAY+1,MAX_DELAY+1));
            b = 1;
            #($urandom_range(100, 1000));
            a = 0;
            b = 0; 
            #($urandom_range(1000, 3000));
        end
    end

    // Check b's raising edge
    property b_raising(min, max);
        disable iff (reset)
        $rose(a) |-> ##[min:max] $rose(b);
    endproperty: b_raising
    A1_RAISE: assert property(b_raising(MIN_DELAY, MAX_DELAY)) else begin
        `uvm_fatal("A1_RAISE", $sformatf("Assertion is failing in time=%0tns", $time))
    end

    // Check a's falling edge
    property b_fallins;
        disable iff (reset)
        $fell(b) |-> $fell(b);
    endproperty: b_fallins
    A1_FALL: assert property(b_fallins) else begin
        `uvm_fatal("A1_FALL", $sformatf("Assertion is failing in time=%0tns", $time))
    end

    // Check X or Z states
    property a_b_x_z_states;
        disable iff (reset)
        $rose(a) |-> !$isunknown(b) until_with $fell(a);
    endproperty: a_b_x_z_states
    A1_IS_UNKNOWN: assert property(a_b_x_z_states) else begin
        `uvm_fatal("A1_IS_UNKNOWN", $sformatf("Assertion is failing in time=%0tns", $time))
    end

    // Check b is stable during a
    property b_stable(min, max);
        disable iff (reset)
        $rose(a) |-> ##[min:max] $stable(b) until_with $fell(b);
    endproperty:b_stable
    A1_IS_STABLE: assert property(b_stable(MIN_DELAY, MAX_DELAY)) else begin
        `uvm_fatal("A1_IS_STABLE", $sformatf("Assertion is failing in time=%0tns", $time))
    end

endmodule: tb