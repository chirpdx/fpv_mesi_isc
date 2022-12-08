This project has a Makefile in fpv directory containing two higher level receipes.
1. fpv  - It runs the fpv for original design.
2. fpv_errinj  - It runs the fpv for the design with errors/bugs injected in RTL code using ifdef.

To run the formal property verification for this mesi intersection controller
Run the following commands

1. Original design

cd fpv
make

2. Design with injected errors

cd fpv
make fpv_errinj

