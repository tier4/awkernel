import matplotlib.pyplot as plt
import numpy as np

# Read RTT data from file
rtts = []
with open('rtt_log_20250630_113907.txt', 'r') as f:
    for line in f:
        try:
            rtt = float(line.strip())
            rtts.append(rtt)
        except ValueError:
            continue

rtts = rtts[:5000]

# Create time points (x-axis)
times = np.arange(len(rtts))

# Create the plot
plt.figure(figsize=(12, 6))
plt.plot(times, rtts, 'b-', linewidth=1)
plt.grid(True)

# Set labels and title
plt.xlabel('Iteration')
plt.ylabel('RTT [us]')
plt.title('RTT (e1000)')

# Show the plot
plt.show()
