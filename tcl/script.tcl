

quit -sim

cd ../modelsim

vlib work

vlog -work work ../tb/tb.sv

vsim -novopt -t 1ns -sv_seed random -assertcover work.tb

add wave -divider "Top-level signals"
add wave -radix unsigned tb/*

# Add assertions with covering
add wave -divider "Assertion List"
add wave tb/A1_RAISE
add wave tb/A1_RAISE_CV
#
add wave tb/A1_FALL
add wave tb/A1_FALL_CV
#
add wave tb/A1_IS_UNKNOWN
add wave tb/A1_IS_UNKNOWN_CV
#
add wave tb/A1_IS_STABLE
add wave tb/A1_IS_STABLE_CV
#
add wave tb/A1_A_B_UNKNOWN
add wave tb/A1_A_B_UNKNOWN_CV
#
add wave tb/C_D_E_IMPLIES

run 10us