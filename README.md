# Rust Name Server

provides a casual DNS service like a dnsmasq.

```
Usage: rns [options...]

Options:
  -h, --help               Show this help message and exit
  -v, --verbose            Increase verbosity
  -4, --ipv4-only          Listen on 0.0.0.0:53 instead of [::]:53
  -H, --addn-hosts <path>  Hosts files to be read in addition to /etc/hosts
  -T, --local-ttl  <int>   Time-to-live in seconds for replies from /etc/hosts
```
