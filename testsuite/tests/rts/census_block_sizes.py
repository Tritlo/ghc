import re
import sys
from pathlib import Path

word_bytes = int(Path(sys.argv[1]).read_text().strip())
lines = Path(sys.argv[2]).read_text().splitlines()
pattern = re.compile(
    r"Allocator (\d+) \((\d+) bytes - (\d+) bytes\): "
    r"\d+ active segs, \d+ filled segs, (\d+) live blocks, "
    r"(\d+) live words \(([\d.]+)% occupancy\)"
)
rows = [tuple(map(float, match.groups())) for line in lines if (match := pattern.search(line))]
assert rows, "no live-word census"
class_0 = [row for row in rows if row[0] == 0]
class_1 = [row for row in rows if row[0] == 1]
assert class_0 and all(row[1:3] == (0, 8) for row in class_0)
assert class_1 and all(row[1:3] == (8, 8 + word_bytes) for row in class_1)
assert any(row[3] > 0 for row in class_1), "no live blocks in allocator 1"
assert any(row[3] == 0 for row in rows), "no zero-block allocator"
for _, _, block_size, blocks, words, occupancy in rows:
    expected = 100.0 if blocks == 0 else 100.0 * words * word_bytes / (blocks * block_size)
    assert abs(occupancy - expected) <= 0.051, (occupancy, expected)
