import imp
import os
import sys

from .core import LineUtils
from . import spacing as spacing_module
from . import conduitlookup as conduitlookup_module
from . import selftest as selftest_module

spacing_module.LineUtils = LineUtils
conduitlookup_module.LineUtils = LineUtils
selftest_module.LineUtils = LineUtils
LineUtils.Spacing = spacing_module.Spacing
LineUtils.ConduitLookup = conduitlookup_module.ConduitLookup
LineUtils.SelfTest = selftest_module.SelfTest

_repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
_panelconnections_path = os.path.join(
    _repo_root, "Panelconnections_test", "Py", "panelconnections.py"
)
_underground_path = os.path.join(
    _repo_root, "Underground_test", "Py", "underground.py"
)

for _module_name in ("LineUtils.Panelconnections", "LineUtils.Underground"):
    if _module_name in sys.modules:
        del sys.modules[_module_name]

panelconnections = imp.load_source("LineUtils.Panelconnections", _panelconnections_path)
underground = imp.load_source("LineUtils.Underground", _underground_path)

LineUtils.Panelconnections = panelconnections
LineUtils.Underground = underground

__all__ = [
    "LineUtils",
    "panelconnections",
    "underground",
    "spacing_module",
    "conduitlookup_module",
    "selftest_module",
]
