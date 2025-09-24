import random

def generate_bytes_file(filename: str, n: int):
    """Generate a text file with n lines, each line a random byte [0, 255]."""
    with open(filename, "w") as f:
        for _ in range(n):
            f.write(f"{random.randint(0, 255)}\n")

generate_bytes_file("bytes.txt", 90 * (2 ** 20))  # creates bytes.txt with 90 MiB of random bytes
