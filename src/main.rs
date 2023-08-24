use std::collections::HashMap;
use std::env::args;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::fs::{metadata, read_to_string};
use std::io::{ErrorKind, Result as IOResult};
use std::mem::transmute;
use std::net::{IpAddr, Ipv4Addr, UdpSocket};
use std::str::{FromStr, from_utf8};
use std::sync::{Arc, RwLock};
use std::thread::{sleep, spawn};
use std::time::{Duration, SystemTime};

#[allow(dead_code)]
#[repr(u8)]
#[derive(Clone, Copy, Default, Eq, PartialEq)]
enum Opcode {
    #[default]
    QUERY  = 0,
    IQUERY = 1,
    STATUS = 2,
}

#[allow(dead_code)]
#[repr(u8)]
#[derive(Clone, Copy, Default, Eq, PartialEq)]
enum Rcode {
    #[default]
    NOERROR  = 0,
    FORMERR  = 1,
    SERVFAIL = 2,
    NXDOMAIN = 3,
    NOTIMP   = 4,
    REFUSED  = 5,
}

#[allow(dead_code)]
#[repr(u16)]
#[derive(Clone, Copy, Eq, PartialEq)]
enum Qtype {
    A     = 1,
    NS    = 2,
    CNAME = 5,
    SOA   = 6,
    PTR   = 12,
    MX    = 15,
    TXT   = 16,
    AAAA  = 28,
    ALL   = 255,
}

#[allow(dead_code)]
#[repr(u16)]
#[derive(Clone, Copy, Eq, PartialEq)]
enum Qclass {
    IN  = 1,
    ANY = 255,
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
struct Header {
    id     : u16,
    qr     : bool,
    opcode : Opcode,
    aa     : bool,
    tc     : bool,
    rd     : bool,
    ra     : bool,
    rcode  : Rcode,
    qdcount: u16,
    ancount: u16,
    nscount: u16,
    arcount: u16,
}

struct Qname<'a> {
    packet: &'a [u8],
    labels: Vec<&'a [u8]>,
}

struct Question<'a> {
    qname : Qname<'a>,
    qtype : Qtype,
    qclass: Qclass,
}

struct Record<'a> {
    name  : Qname<'a>,
    rtype : Qtype,
    class : Qclass,
    ttl   : u32,
    rdata : &'a [u8],
}

impl Header {
    fn answer(id: u16, opcode: Opcode, qdcount: u16, ancount: u16) -> Header {
        Header {
            id,
            qr: true,
            opcode,
            aa: false,
            tc: false,
            rd: false,
            ra: true,
            rcode: Rcode::NOERROR,
            qdcount,
            ancount,
            nscount: 0,
            arcount: 0,
        }
    }

    fn error(id: u16, opcode: Opcode, rcode: Rcode) -> Header {
        Header {
            id,
            qr: true,
            opcode,
            aa: false,
            tc: false,
            rd: false,
            ra: false,
            rcode,
            qdcount: 0,
            ancount: 0,
            nscount: 0,
            arcount: 0,
        }
    }

    fn from_bytes(packet: &[u8]) -> Header {
        assert!(packet.len() >= 12);
        assert!((packet[3] & 0x70) == 0);
        Header {
            id     : u16::from_be_bytes(packet[0..2].try_into().unwrap()),
            qr     : (packet[2] & 0x80) != 0,
            opcode : unsafe { transmute((packet[2] & 0x78) >> 3) },
            aa     : (packet[2] & 0x04) != 0,
            tc     : (packet[2] & 0x02) != 0,
            rd     : (packet[2] & 0x01) != 0,
            ra     : (packet[3] & 0x80) != 0,
            rcode  : unsafe { transmute((packet[3] & 0x0F) >> 0) },
            qdcount: u16::from_be_bytes(packet[4..6].try_into().unwrap()),
            ancount: u16::from_be_bytes(packet[6..8].try_into().unwrap()),
            nscount: u16::from_be_bytes(packet[8..10].try_into().unwrap()),
            arcount: u16::from_be_bytes(packet[10..12].try_into().unwrap()),
        }
    }

    fn to_bytes(&self) -> [u8; 12] {
        let mut packet = [0; 12];
        packet[0..2].clone_from_slice(&self.id.to_be_bytes());
        packet[2] = if self.qr { 0x80 } else { 0 }
                  | (self.opcode as u8) << 3
                  | if self.aa { 0x04 } else { 0 }
                  | if self.tc { 0x02 } else { 0 }
                  | if self.rd { 0x01 } else { 0 };
        packet[3] = if self.ra { 0x80 } else { 0 }
                  | (self.rcode  as u8) << 0;
        packet[4..6].clone_from_slice(&self.qdcount.to_be_bytes());
        packet[6..8].clone_from_slice(&self.ancount.to_be_bytes());
        packet[8..10].clone_from_slice(&self.nscount.to_be_bytes());
        packet[10..12].clone_from_slice(&self.arcount.to_be_bytes());
        packet
    }
}

impl Qname<'_> {
    fn from_bytes(packet: &[u8], offset: usize) -> (Qname, usize) {
        assert!(offset + 1 < packet.len());
        let mut cursor = offset;
        let mut qname = Qname { packet, labels: Vec::new() };
        loop {
            let length = packet[cursor] as usize;
            cursor += 1;
            if length == 0 { break }
            if (length & 0xC0) == 0xC0 {
                let ptr = (length & 0x3F) << 8 | packet[cursor] as usize;
                qname.labels.append(&mut Qname::from_bytes(packet, ptr).0.labels);
                return (qname, cursor + 1);
            }
            qname.labels.push(&packet[cursor..][..length]);
            cursor += length;
        }
        (qname, cursor)
    }
}

impl Question<'_> {
    fn from_bytes(packet: &[u8], offset: usize) -> (Question, usize) {
        assert!(offset + 5 < packet.len());
        let (qname, offset) = Qname::from_bytes(&packet, offset);
        (Question {
            qname,
            qtype : unsafe { transmute(u16::from_be_bytes(packet[offset..][0..2].try_into().unwrap())) },
            qclass: unsafe { transmute(u16::from_be_bytes(packet[offset..][2..4].try_into().unwrap())) },
        }, offset + 4)
    }
}

impl Record<'_> {
    fn from_bytes(packet: &[u8], offset: usize) -> (Record, usize) {
        assert!(offset + 11 < packet.len());
        let (name, offset) = Qname::from_bytes(&packet, offset);
        let rtype: Qtype  = unsafe { transmute(u16::from_be_bytes(packet[offset..][0..2].try_into().unwrap())) };
        let class: Qclass = unsafe { transmute(u16::from_be_bytes(packet[offset..][2..4].try_into().unwrap())) };
        let ttl      = u32::from_be_bytes(packet[offset..][4..8].try_into().unwrap());
        let rdlength = u16::from_be_bytes(packet[offset..][8..10].try_into().unwrap());
        let rdata: &[u8]  = &packet[offset+10..][..rdlength as usize];
        (Record { name, rtype, class, ttl, rdata }, offset + 10 + rdlength as usize)
    }
}

impl Display for Opcode {
    #[allow(unreachable_patterns)]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", match self {
            Opcode::QUERY  => "QUERY",
            Opcode::IQUERY => "IQUERY",
            Opcode::STATUS => "STATUS",
            _              => "?",
        })
    }
}

impl Display for Rcode {
    #[allow(unreachable_patterns)]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", match self {
            Rcode::NOERROR  => "NOERROR",
            Rcode::FORMERR  => "FORMERR",
            Rcode::SERVFAIL => "SERVFAIL",
            Rcode::NXDOMAIN => "NXDOMAIN",
            Rcode::NOTIMP   => "NOTIMP",
            Rcode::REFUSED  => "REFUSED",
            _               => "?",
        })
    }
}

impl Display for Qtype {
    #[allow(unreachable_patterns)]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", match self {
            Qtype::A     => "A",
            Qtype::NS    => "NS",
            Qtype::CNAME => "CNAME",
            Qtype::SOA   => "SOA",
            Qtype::PTR   => "PTR",
            Qtype::MX    => "MX",
            Qtype::TXT   => "TXT",
            Qtype::AAAA  => "AAAA",
            Qtype::ALL   => "*",
            _            => "?"
        })
    }
}

impl Display for Qclass {
    #[allow(unreachable_patterns)]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", match self {
            Qclass::IN  => "IN",
            Qclass::ANY => "*",
            _           => "?",
        })
    }
}

impl Display for Header {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}.{} {} {}/{}/{}/{} {} QD[{}] AN[{}] NS[{}] AR[{}]",
            if self.qr { "R" } else { "Q" }, self.id, self.opcode,
            if self.aa { "AA" } else { "--" },
            if self.tc { "TC" } else { "--" },
            if self.rd { "RD" } else { "--" },
            if self.ra { "RA" } else { "--" },
            self.rcode, self.qdcount, self.ancount, self.nscount, self.arcount)
    }
}

impl Display for Qname<'_> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Ok(for (i, label) in self.labels.iter().enumerate() {
            if i > 0 { write!(f, ".")? }
            write!(f, "{}", from_utf8(&label).unwrap())?
        })
    }
}

impl Display for Question<'_> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{} {} {}", self.qname, self.qtype, self.qclass)
    }
}

impl Display for Record<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} {} {} {}", self.name, self.rtype, self.class, self.ttl)?;
        match self.rtype {
            Qtype::A     => write!(f, " {}", IpAddr::from(TryInto::<[u8; 4]>::try_into(self.rdata).unwrap())),
            Qtype::NS    |
            Qtype::CNAME |
            Qtype::PTR   => {
                let offset = self.rdata.as_ptr() as usize - self.name.packet.as_ptr() as usize;
                write!(f, " {}", Qname::from_bytes(self.name.packet, offset).0)
            }
            Qtype::SOA   => {
                let offset = self.rdata.as_ptr() as usize - self.name.packet.as_ptr() as usize;
                let (mname, offset) = Qname::from_bytes(self.name.packet, offset);
                let (rname, offset) = Qname::from_bytes(self.name.packet, offset);
                let octets = &self.name.packet[offset..];
                let serial  = u32::from_be_bytes(octets[0..4].try_into().unwrap());
                let refresh = u32::from_be_bytes(octets[4..8].try_into().unwrap());
                let retry   = u32::from_be_bytes(octets[8..12].try_into().unwrap());
                let expire  = u32::from_be_bytes(octets[12..16].try_into().unwrap());
                let minimum = u32::from_be_bytes(octets[16..20].try_into().unwrap());
                write!(f, " {} {} {} {} {} {} {}", mname, rname, serial, refresh, retry, expire, minimum)
            }
            Qtype::MX    => {
                let offset = self.rdata.as_ptr() as usize - self.name.packet.as_ptr() as usize;
                let preference = u16::from_be_bytes(self.rdata[0..2].try_into().unwrap());
                let (exchange, _) = Qname::from_bytes(self.name.packet, offset + 2);
                write!(f, " {} {}", preference, exchange)
            }
            Qtype::TXT   => {
                let length = self.rdata[0] as usize;
                write!(f, " \"{}\"", from_utf8(&self.rdata[1..][..length]).unwrap())
            }
            Qtype::AAAA  => write!(f, " {}", IpAddr::from(TryInto::<[u8; 16]>::try_into(self.rdata).unwrap())),
            _            => Ok(for x in self.rdata { write!(f, " {:02X}", x)? }),
        }
    }
}

fn parse_hosts(content: &str, hosts: &mut HashMap<String, Vec<IpAddr>>) {
    for line in content.split('\n').filter(|s| s.len() > 0 && !s.starts_with('#')) {
        let mut addr: Option<IpAddr> = None;
        for (i, s) in line.split(char::is_whitespace).filter(|s| s.len() > 0).enumerate() {
            if i == 0 {
                addr = Some(IpAddr::from_str(s).unwrap_or(IpAddr::V4(Ipv4Addr::UNSPECIFIED)));
            } else {
                hosts.entry(s.to_string()).or_default().push(addr.unwrap());
                if s.starts_with("*.") {
                    hosts.entry(s[2..].to_string()).or_default().push(addr.unwrap());
                }
            }
        }
    }
}

fn main() -> IOResult<()> {
    if args().any(|a| a == "-h" || a == "--help") {
        eprintln!("Usage: rns [options...]");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  -h, --help               Show this help message and exit");
        eprintln!("  -v, --verbose            Increase verbosity");
        eprintln!("  -H, --addn-hosts <path>  Hosts files to be read in addition to /etc/hosts");
        eprintln!("  -T, --local-ttl  <int>   Time-to-live in seconds for replies from /etc/hosts");
        return Ok(());
    }
    let (verbose, hosts_files, local_ttl) = {
        let mut verbose = false;
        let mut files = vec!["/etc/hosts".to_string()];
        let mut ttl: u32 = 0;
        let mut it = args();
        while let Some(k) = it.next() {
            if k == "-v" || k == "--verbose" {
                verbose = true;
            } else if k == "-H" || k == "--addn-hosts" {
                if let Some(v) = it.next() { files.push(v) }
            } else if k == "-T" || k == "--local-ttl" {
                if let Some(v) = it.next() { ttl = v.parse().unwrap_or(0) }
            }
        }
        (verbose, Arc::new(files), ttl)
    };
    let hosts_reader = Arc::new(RwLock::new({
        let mut hosts = HashMap::new();
        for path in hosts_files.iter() {
            parse_hosts(&read_to_string(path).unwrap_or_default(), &mut hosts);
        }
        hosts
    }));
    let hosts_writer = hosts_reader.clone();
    let hosts_files_clone = hosts_files.clone();
    let hosts_files_watch_interval = Duration::from_secs(4);
    spawn(move || {
        let hosts_files = hosts_files_clone;
        let min_mtime = SystemTime::UNIX_EPOCH;
        let get_mtime = |path: &str|
            if let Ok(m) = metadata(path) { m.modified().unwrap() } else { min_mtime };
        let mut lastmtime = hosts_files.iter().fold(min_mtime, |t, p| get_mtime(p).max(t));
        loop {
            sleep(hosts_files_watch_interval);
            let mtime = hosts_files.iter().fold(min_mtime, |t, p| get_mtime(p).max(t));
            if mtime == lastmtime { continue }
            lastmtime = mtime;
            let mut hosts = HashMap::new();
            for path in hosts_files.iter() {
                parse_hosts(&read_to_string(path).unwrap_or_default(), &mut hosts);
            }
            let mut writer = hosts_writer.write().unwrap();
            writer.clear();
            for (k, v) in hosts {
                writer.insert(k, v);
            }
            if verbose { eprintln!("Reloaded {}", hosts_files.join(" and ")) }
        }
    });
    let nameservers: Vec<IpAddr> = read_to_string("/etc/resolv.conf")?.split('\n')
        .filter(|line| line.starts_with("nameserver "))
        .map(|line| IpAddr::from_str(line[11..].trim()).unwrap())
        .collect();
    let timeout = Duration::from_secs(15);
    let server = UdpSocket::bind("0.0.0.0:53")?;
    let client = UdpSocket::bind("0.0.0.0:0")?;
    server.set_read_timeout(Some(timeout))?;
    server.set_write_timeout(Some(timeout))?;
    client.set_read_timeout(Some(timeout))?;
    client.set_write_timeout(Some(timeout))?;
    'accept: loop {
        let mut qbuffer = [0; 512];
        match server.recv_from(&mut qbuffer) {
            Ok((qlength, remote)) => {
                let qpacket = &qbuffer[..qlength];
                let qheader = Header::from_bytes(&qpacket);
                if verbose { eprintln!("{} from {}", qheader, remote) }
                if qheader.qr || qheader.aa || qheader.ra || qheader.rcode != Rcode::NOERROR || qheader.ancount > 0 {
                    server.send_to(&Header::error(qheader.id, qheader.opcode, Rcode::FORMERR).to_bytes(), remote).unwrap_or(0);
                    continue 'accept
                }
                if qheader.opcode != Opcode::QUERY || qheader.tc || qheader.qdcount != 1 || qheader.nscount > 0 || qheader.arcount > 0 {
                    server.send_to(&Header::error(qheader.id, qheader.opcode, Rcode::NOTIMP).to_bytes(), remote).unwrap_or(0);
                    continue 'accept
                }
                let (question, qend) = Question::from_bytes(&qpacket, 12);
                if verbose { eprintln!("  {}", question) }
                let mut patterns = vec![question.qname.to_string()];
                if let Some(dot) = patterns[0].find('.') {
                    patterns.push(format!("*{}", &patterns[0][dot..]));
                }
                for pattern in patterns {
                    if let Some(addrs) = hosts_reader.read().unwrap().get(&pattern) {
                        for addr in addrs {
                            let rdata: Option<Vec<u8>> = match (question.qtype, *addr) {
                                (Qtype::A | Qtype::ALL, IpAddr::V4(addr)) => {
                                    if verbose {
                                        eprintln!("Found in {}", hosts_files.join(" or "));
                                        eprintln!("  {} {}", addr, pattern);
                                    }
                                    Some(addr.octets().to_vec())
                                }
                                (Qtype::AAAA | Qtype::ALL, IpAddr::V6(addr)) => {
                                    if verbose {
                                        eprintln!("Found in {}", hosts_files.join(" or "));
                                        eprintln!("  {} {}", addr, pattern);
                                    }
                                    Some(addr.octets().to_vec())
                                }
                                _ => None
                            };
                            match rdata {
                                Some(rdata) if rdata.iter().any(|x| *x != 0) => {
                                    let qtype = match (question.qtype, rdata.len()) {
                                        (Qtype::ALL, 4) => Qtype::A,
                                        (Qtype::ALL, 8) => Qtype::AAAA,
                                        _               => question.qtype,
                                    };
                                    let aheader = Header::answer(qheader.id, qheader.opcode, 1, 1);
                                    let mut apacket: [u8; 512] = [0; 512];
                                    apacket[0..12].clone_from_slice(&aheader.to_bytes());
                                    apacket[12..qend].clone_from_slice(&qpacket[12..qend]);
                                    apacket[qend..][0..2].clone_from_slice(&[0xC0, 12]);
                                    apacket[qend..][2..4].clone_from_slice(&(qtype as u16).to_be_bytes());
                                    apacket[qend..][4..6].clone_from_slice(&(question.qclass as u16).to_be_bytes());
                                    apacket[qend..][6..10].clone_from_slice(&local_ttl.to_be_bytes());
                                    apacket[qend..][10..12].clone_from_slice(&(rdata.len() as u16).to_be_bytes());
                                    apacket[qend..][12..12+rdata.len()].clone_from_slice(&rdata);
                                    let apacket = &apacket[..qend+12+rdata.len()];
                                    server.send_to(&apacket, remote).unwrap_or(0);
                                    continue 'accept
                                }
                                Some(_) => {
                                    server.send_to(&Header::error(qheader.id, qheader.opcode, Rcode::NXDOMAIN).to_bytes(), remote).unwrap_or(0);
                                    continue 'accept
                                }
                                None => {}
                            }
                        }
                    }
                }
                let nameserver = nameservers[0];
                client.send_to(&qpacket, (nameservers[0], 53))?;
                let mut apacket = [0; 512];
                let alength = client.recv(&mut apacket)?;
                let apacket = &apacket[..alength];
                if verbose {
                    let aheader = Header::from_bytes(&apacket);
                    eprintln!("{} from {}", aheader, nameserver);
                    let mut offset = 12;
                    for _ in 0..aheader.qdcount {
                        let (question, qend) = Question::from_bytes(&apacket, offset);
                        eprintln!("  {}", question);
                        offset = qend;
                    }
                    for (count, kind) in [(aheader.ancount, "AN"), (aheader.nscount, "NS"), (aheader.arcount, "AR")] {
                        for i in 0..count {
                            let (record, rend) = Record::from_bytes(&apacket, offset);
                            if i == 0 { eprintln!("{}", kind) }
                            eprintln!("  {}", record);
                            offset = rend;
                        }
                    }
                }
                server.send_to(&apacket, remote).unwrap_or(0);
            }
            Err(e) if e.kind() == ErrorKind::WouldBlock => {
                // not an error, ignore
            }
            Err(e) => {
                eprintln!("Error: {:?}", e)
            }
        }
    }
}
