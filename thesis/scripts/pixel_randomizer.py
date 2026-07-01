"""
This script was generated using ChatGPT.
"""
# TODO: Specify in which section of the report this script was used

import numpy as np
from PIL import Image

# Load image (convert to grayscale just in case)
input_path = "input.png"
output_path = "output_modified.png"

img = Image.open(input_path).convert("L")
arr = np.array(img, dtype=np.int16)  # use int16 to avoid overflow during changes

# Generate random noise in range [-5, +5]
noise = np.random.randint(-5, 6, size=arr.shape)

# Apply noise
modified = arr + noise

# Clip values to valid grayscale range [0, 255]
modified = np.clip(modified, 0, 255)

# Convert back to uint8
modified = modified.astype(np.uint8)

# Save image
Image.fromarray(modified).save(output_path)

print("Modified image saved as:", output_path)

# Optional: create a difference image to visualize changes
diff = np.abs(arr - modified)
diff = (diff * 40).clip(0, 255).astype(np.uint8)
Image.fromarray(diff).save("difference.png")import numpy as np
from PIL import Image

# Load image (convert to grayscale just in case)
input_path = "input.png"
output_path = "output_modified.png"

img = Image.open(input_path).convert("L")
arr = np.array(img, dtype=np.int16)  # use int16 to avoid overflow during changes

# Generate random noise in range [-5, +5]
noise = np.random.randint(-10, 9, size=arr.shape)

# Apply noise
modified = arr + noise

# Clip values to valid grayscale range [0, 255]
modified = np.clip(modified, 0, 255)

# Convert back to uint8
modified = modified.astype(np.uint8)

# Save image
Image.fromarray(modified).save(output_path)

print("Modified image saved as:", output_path)
