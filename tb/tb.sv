

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

    initial begin
        $assertoff();
        #1000;
        $asserton();
    end

    // Check b's raising edge
    property b_raising(min, max);
        disable iff (reset)
        $rose(a) |-> ##[min:max] $rose(b);
    endproperty: b_raising
    A1_RAISE: assert property(b_raising(MIN_DELAY, MAX_DELAY)) else begin
        `uvm_error("A1_RAISE", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    A1_RAISE_CV: cover property(b_raising(MIN_DELAY, MAX_DELAY));

    // Check a's falling edge
    property b_fallins;
        disable iff (reset)
        $fell(a) |-> $fell(b);
    endproperty: b_fallins
    A1_FALL: assert property(b_fallins) else begin
        `uvm_error("A1_FALL", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    A1_FALL_CV: cover property(b_fallins);

    // Check X or Z states
    property a_b_x_z_states;
        disable iff (reset)
        $rose(a) |-> !$isunknown(b) until_with $fell(a);
    endproperty: a_b_x_z_states
    A1_IS_UNKNOWN: assert property(a_b_x_z_states) else begin
        `uvm_error("A1_IS_UNKNOWN", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    A1_IS_UNKNOWN_CV: cover property(a_b_x_z_states);

    // Check b is stable during a
    property b_stable(min, max);
        disable iff (reset)
        $rose(a) |-> ##[min:max] $stable(b) until_with $fell(a);
    endproperty:b_stable
    A1_IS_STABLE: assert property(b_stable(MIN_DELAY, MAX_DELAY)) else begin
        `uvm_error("A1_IS_STABLE", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    A1_IS_STABLE_CV: cover property(b_stable(MIN_DELAY, MAX_DELAY));

    // Check a and b always not X or Z
    property a_b_x_z_always_states;
        ##[*] ( !$isunknown(a) && !$isunknown(b) );
    endproperty: a_b_x_z_always_states
    A1_A_B_UNKNOWN: assert property(a_b_x_z_always_states) else begin
        `uvm_error("A1_A_B_UNKONOWN", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    A1_A_B_UNKNOWN_CV: cover property(a_b_x_z_always_states);


    // Working with implies
    logic c;
    logic d;
    logic e;
    logic g;
    initial begin
        c = 0;
        d = 0;
        e = 0;
        g = 0;
        forever begin
            #2000;
            @(posedge clk);
            c = 1;
            @(posedge clk);
            c = 0;
            d = 1;
            e = 1;
            @(posedge clk);
            d = 0;
            e = 0;
            g = 1;
            @(posedge clk);
            g = 0;
        end
    end

    // Implies operation
    // In the case of |-> the consequent e ##1 g will start evaluating
    // when c ##1 d matches
    property c_d_e_g_no_implies;
       (c ##1 d) |-> (e ##1 g);
    endproperty: c_d_e_g_no_implies
    C_D_E_G_NO_IMPLIES: assert property(c_d_e_g_no_implies) else begin
        `uvm_error("C_D_E_G_NO_IMPLIES", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    C_D_E_G_NO_IMPLIES_CV: cover property(c_d_e_g_no_implies);


    logic k;
    logic l;
    logic m;
    logic n;
    initial begin
        k = 0;
        l = 0;
        m = 0;
        n = 0;
        forever begin
            #2000;
            @(posedge clk);
            k = 1;
            m = 1;
            @(posedge clk);
            k = 0;
            m = 0;
            l = 1;
            n = 1;
            @(posedge clk);
            l = 0;
            n = 0;
        end
    end

    // In the case of implies, both c ##1 d and e ##1 g start evaluation
    // at the same clock tick
    property k_l_m_n_implies;
        (k ##1 l) implies (m ##1 n);
    endproperty: k_l_m_n_implies
    K_L_M_N_IMPLIES: assert property(k_l_m_n_implies) else begin
        `uvm_error("K_L_M_N_IMPLIES", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    K_L_M_N_IMPLIES_CV: cover property(k_l_m_n_implies);


    // Strong assertions (well, no diference in modelsim)
    logic a1;
    logic a2;
    initial begin
        a1 = 0;
        a2 = 0;
        #1000;
        a1 = 1;
    end

    A1_WEAK: assert property(weak(a1 ##[+] a2)) else begin
        `uvm_error("A1_WEAK", $sformatf("Assertion is failing in time=%0tns", $time))
    end
    A1_STRONG: assert property(strong (a1 ##[+] a2)) else begin
        `uvm_error("A1_STRONG", $sformatf("Assertion is failing in time=%0tns", $time))
    end


    // If / else
    logic aa1;
    logic aa2;
    initial begin
        aa1 = 0;
        aa2 = 0;
        forever begin
            #2000;
            @(posedge clk);
            aa1 = 1;
            ##2;
            aa1 = 0;
            aa2 = 1;
            ##1;
            aa2 = 0;
        end
    end

    A1_IF_ELSE: assert property(if (aa1) ##1 aa2);


    // Conjuction
    bit reset_conj;
    initial begin
        #3000;
        reset_conj = 1;
        #300;
        reset_conj = 0;
    end

    initial A_RESET_CONJ: assume property(reset_conj[*10] #=# always !reset_conj);


    // Until_with

endmodule: tb