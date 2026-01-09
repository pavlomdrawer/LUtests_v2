# LineUtils library

## Usage in IronPython

```python
import sys
import os

# Name of the environment variable to read
VAR_NAME = "DRAWER_PROJECT_ROOT"
sys.path.append(os.environ.get(VAR_NAME) + "Gh\Line_utils")

from LineUtils import LineUtils as LineUtils
```

To update LineUtils.py:

```python
if refresh:
   reload(sys.modules["LineUtils"])
```

To test:

```python
LineUtils_wiki = LineUtils.generate_wiki(LineUtils)
```

check version:

```python
LineUtils_version = LineUtils.VERSION
```

if version got stuck, bulletproof load:
```python
import sys
import os
import imp

VAR_NAME = "DRAWER_PROJECT_ROOT"
root = os.environ.get(VAR_NAME)
line_utils_dir = os.path.join(root, "Gh", "Line_utils")
line_utils_file = os.path.join(line_utils_dir, "LineUtils.py")

if "LineUtils" in sys.modules:
    del sys.modules["LineUtils"]

LineUtils = imp.load_source("LineUtils", line_utils_file)

from LineUtils import LineUtils as LineUtils
```