"""dynacert: machine-checked reachability certificates for Modelica models.

    import dynacert
    cert = dynacert.check("examples/ClosedLoop.mo", "ClosedLoop")  # rumoca -> search -> Lean
    cert = dynacert.load("ClosedLoop")                             # an existing certificate
    runs = cert.simulate(30)
    cert.plot(runs)

Everything in Python is untrusted search and illustration; the verified statement is the Lean
theorem `cert.theorem` (see `cert.claim`), checked by `cert.verify()`.
"""

from .api import Certificate, check, find_root, load
from .pipeline import CertError

__all__ = ["Certificate", "CertError", "check", "find_root", "load"]
__version__ = "0.1.0"
