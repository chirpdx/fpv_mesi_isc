fpv: clean compile verify debug

compile:
	vlib work
	vmap work work
	vlog ./../src/rtl/mesi_isc_define.v
	vlog ./../src/rtl/mesi_isc.v
	vlog ./../src/rtl/mesi_isc_basic_fifo.v
	vlog ./../src/rtl/mesi_isc_breq_fifos.v
	vlog ./../src/rtl/mesi_isc_breq_fifos_cntl.v
	vlog ./../src/rtl/mesi_isc_broad.v
	vlog ./../src/rtl/mesi_isc_broad_cntl.v
	vlog -sv -mfcu -cuname my_bind_sva \
		./../src/rtl/sva_bind.sv ./../src/rtl/sva_mesi_isc.sv


verify:
	qverify -c -od Output_Results -do "\
		do qs_files/directives.tcl; \
		formal compile -d mesi_isc -cuname my_bind_sva \
			-target_cover_statements; \
		formal init -file qs_files/myinit.init; \
		formal verify -timeout 5m; \
		exit"

debug: 
	qverify Output_Results/propcheck.db &

clean:
	qverify_clean
	\rm -rf work modelsim.ini *.wlf *.log replay* transcript *.db
	\rm -rf Output_Results *.tcl 

