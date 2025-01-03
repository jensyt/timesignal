import sys

if len(sys.argv) < 2:
	print("Usage:", sys.argv[0], "filename")
	exit(-1)

with open(sys.argv[1], 'wb') as f:
	lfsr = 0
	for i in range(0, 512):
		chip = lfsr & 1
		f.write(chip.to_bytes())
		lfsr = lfsr >> 1
		if (chip or lfsr == 0):
			lfsr = lfsr ^ 0x110

