use std::cmp::Ordering;
use std::collections::HashMap;
use std::env::args;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::fs::{metadata, read_to_string};
use std::io::{ErrorKind, Result as IoResult};
use std::mem::transmute;
use std::net::{IpAddr, Ipv4Addr, SocketAddr, UdpSocket, Ipv6Addr};
use std::process::exit;
use std::sync::{Arc, RwLock};
use std::thread::{sleep, spawn};
use std::time::{Duration, UNIX_EPOCH};

#[inline]
fn unmap_ipv4_in_ipv6(addr: &IpAddr) -> IpAddr {
    match addr {
        IpAddr::V6(v6) => match v6.segments() {
            [0, 0, 0, 0, 0, 0xFFFF, hi, lo] => IpAddr::V4(((hi as u32) << 16 | lo as u32).into()),
            _ => *addr,
        }
        _ => *addr,
    }
}

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
enum Type {
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
enum Class {
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

struct Name<'a> {
    packet: &'a [u8],
    labels: Vec<&'a [u8]>,
}

struct Question<'a> {
    qname : Name<'a>,
    qtype : Type,
    qclass: Class,
}

struct Record<'a> {
    rname : Name<'a>,
    rtype : Type,
    rclass: Class,
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

impl Name<'_> {
    fn from_bytes(packet: &[u8], offset: usize) -> (Name, usize) {
        assert!(offset + 1 < packet.len());
        let mut cursor = offset;
        let mut qname = Name { packet, labels: Vec::new() };
        loop {
            let length = packet[cursor] as usize;
            cursor += 1;
            if length == 0 { break }
            if (length & 0xC0) == 0xC0 {
                let ptr = (length & 0x3F) << 8 | packet[cursor] as usize;
                qname.labels.append(&mut Name::from_bytes(packet, ptr).0.labels);
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
        let (qname, offset) = Name::from_bytes(&packet, offset);
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
        let (rname, offset) = Name::from_bytes(&packet, offset);
        let rtype: Type   = unsafe { transmute(u16::from_be_bytes(packet[offset..][0..2].try_into().unwrap())) };
        let rclass: Class = unsafe { transmute(u16::from_be_bytes(packet[offset..][2..4].try_into().unwrap())) };
        let ttl      = u32::from_be_bytes(packet[offset..][4..8].try_into().unwrap());
        let rdlength = u16::from_be_bytes(packet[offset..][8..10].try_into().unwrap());
        let rdata: &[u8]  = &packet[offset+10..][..rdlength as usize];
        (Record { rname, rtype, rclass, ttl, rdata }, offset + 10 + rdlength as usize)
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

impl Display for Type {
    #[allow(unreachable_patterns)]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", match self {
            Type::A     => "A",
            Type::NS    => "NS",
            Type::CNAME => "CNAME",
            Type::SOA   => "SOA",
            Type::PTR   => "PTR",
            Type::MX    => "MX",
            Type::TXT   => "TXT",
            Type::AAAA  => "AAAA",
            Type::ALL   => "*",
            _           => "?"
        })
    }
}

impl Display for Class {
    #[allow(unreachable_patterns)]
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", match self {
            Class::IN  => "IN",
            Class::ANY => "*",
            _          => "?",
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

impl Display for Name<'_> {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Ok(for (i, label) in self.labels.iter().enumerate() {
            if i > 0 { write!(f, ".")? }
            write!(f, "{}", String::from_utf8_lossy(label))?
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
        write!(f, "{} {} {} {}", self.rname, self.rtype, self.rclass, self.ttl)?;
        match self.rtype {
            Type::A     => write!(f, " {}", IpAddr::from(TryInto::<[u8; 4]>::try_into(self.rdata).unwrap())),
            Type::NS    |
            Type::CNAME |
            Type::PTR   => {
                let offset = self.rdata.as_ptr() as usize - self.rname.packet.as_ptr() as usize;
                write!(f, " {}", Name::from_bytes(self.rname.packet, offset).0)
            }
            Type::SOA   => {
                let offset = self.rdata.as_ptr() as usize - self.rname.packet.as_ptr() as usize;
                let (mname, offset) = Name::from_bytes(self.rname.packet, offset);
                let (rname, offset) = Name::from_bytes(self.rname.packet, offset);
                let octets = &self.rname.packet[offset..];
                let serial  = u32::from_be_bytes(octets[0..4].try_into().unwrap());
                let refresh = u32::from_be_bytes(octets[4..8].try_into().unwrap());
                let retry   = u32::from_be_bytes(octets[8..12].try_into().unwrap());
                let expire  = u32::from_be_bytes(octets[12..16].try_into().unwrap());
                let minimum = u32::from_be_bytes(octets[16..20].try_into().unwrap());
                write!(f, " {} {} {} {} {} {} {}", mname, rname, serial, refresh, retry, expire, minimum)
            }
            Type::MX    => {
                let offset = self.rdata.as_ptr() as usize - self.rname.packet.as_ptr() as usize;
                let preference = u16::from_be_bytes(self.rdata[0..2].try_into().unwrap());
                let (exchange, _) = Name::from_bytes(self.rname.packet, offset + 2);
                write!(f, " {} {}", preference, exchange)
            }
            Type::TXT   => {
                let length = self.rdata[0] as usize;
                write!(f, " \"{}\"", String::from_utf8_lossy(&self.rdata[1..][..length]))
            }
            Type::AAAA  => write!(f, " {}", IpAddr::from(TryInto::<[u8; 16]>::try_into(self.rdata).unwrap())),
            _            => Ok(for x in self.rdata { write!(f, " {:02X}", x)? }),
        }
    }
}

fn parse_hosts(content: &str, hosts: &mut HashMap<String, Vec<IpAddr>>) {
    for line in content.split('\n').filter(|s| s.len() > 0 && !s.starts_with('#')) {
        let mut iter = line.split_ascii_whitespace().filter(|s| s.len() > 0);
        if let Some(addr) = iter.next().and_then(|s| s.parse::<IpAddr>().ok()) {
            for host in iter {
                hosts.entry(host.to_string()).or_default().push(addr)
            }
        }
    }
}

fn match_hosts(hosts: &HashMap<String, Vec<IpAddr>>, host: &str) -> Vec<(String, Vec<IpAddr>)> {
    let patterns = match host.find('.') {
        Some(dot) => vec![host.to_string(), format!("*{}", &host[dot..])],
        None => vec![host.to_string()]
    };
    let mut matches = Vec::new();
    for pat in patterns {
        if let Some((_, addrs)) = hosts.get_key_value(&pat) {
            matches.push((pat, addrs.clone()))
        }
    }
    if let Some((pat, addrs)) = hosts.iter().find(|(pat, _)| {
        pat.starts_with("**.") && (host == &pat[3..] || host.ends_with(&pat[2..]))
    }) {
        matches.push((pat.clone(), addrs.clone()))
    }
    matches
}

fn main() -> IoResult<()> {
    let show_help_and_exit = |code| {
        eprintln!("Usage: rns [options...]");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  -h, --help               Show this help message and exit");
        eprintln!("  -v, --verbose            Increase verbosity");
        eprintln!("  -4, --ipv4-only          Listen on 0.0.0.0:53 instead of [::]:53");
        eprintln!("  -H, --addn-hosts <path>  Hosts files to be read in addition to /etc/hosts");
        eprintln!("  -T, --local-ttl  <int>   Time-to-live in seconds for replies from /etc/hosts");
        exit(code)
    };
    let (verbose, ipv4only, hosts_files, local_ttl) = {
        let mut verbose = false;
        let mut ipv4only = false;
        let mut files = vec!["/etc/hosts".to_string()];
        let mut ttl: u32 = 0;
        let mut iter = args().skip(1);
        while let Some(k) = iter.next() {
            match k.as_str() {
                "-h" | "--help" => show_help_and_exit(0),
                "-v" | "--verbose" => verbose = true,
                "-4" | "--ipv4-only" => ipv4only = true,
                "-H" | "--addn-hosts" => match iter.next() {
                    Some(v) => files.push(v),
                    None => show_help_and_exit(1)
                }
                "-T" | "--local-ttl" => match iter.next().and_then(|v| v.parse::<u32>().ok()) {
                    Some(v) => ttl = v,
                    None => show_help_and_exit(1)
                }
                _ => show_help_and_exit(1)
            }
        }
        (verbose, ipv4only, Arc::new(files), ttl)
    };
    let hosts_reader = Arc::new(RwLock::new({
        let mut hosts = HashMap::new();
        for content in hosts_files.iter().filter_map(|path| read_to_string(&path).ok()) {
            parse_hosts(&content, &mut hosts);
        }
        hosts
    }));
    let hosts_writer = hosts_reader.clone();
    let hosts_files_reader = hosts_files.clone();
    spawn(move || {
        let hosts_files = hosts_files_reader;
        let f = |mtime, path|
            metadata(path).and_then(|m| m.modified()).unwrap_or(UNIX_EPOCH).max(mtime);
        let mut lastmtime = hosts_files.iter().fold(UNIX_EPOCH, f);
        loop {
            sleep(Duration::from_secs(4));
            let mtime = hosts_files.iter().fold(UNIX_EPOCH, f);
            if mtime == lastmtime { continue }
            lastmtime = mtime;
            let mut hosts = HashMap::new();
            for content in hosts_files.iter().filter_map(|path| read_to_string(path).ok()) {
                parse_hosts(&content, &mut hosts);
            }
            let mut writer = hosts_writer.write().unwrap();
            writer.clear();
            for (k, v) in hosts {
                writer.insert(k, v);
            }
            if verbose { eprintln!("Reloaded {}", hosts_files.join(" and ")) }
        }
    });
    let nameservers = Arc::new(read_to_string("/etc/resolv.conf")?.split('\n')
        .filter(|line| line.starts_with("nameserver "))
        .filter_map(|line| line[11..].trim().parse::<IpAddr>().ok())
        .map(|addr| (addr, 53).into())
        .collect::<Vec<SocketAddr>>());
    let timeout = Duration::from_secs(15);
    let server = UdpSocket::bind(if ipv4only {
        SocketAddr::new(Ipv4Addr::UNSPECIFIED.into(), 53)
    } else {
        SocketAddr::new(Ipv6Addr::UNSPECIFIED.into(), 53)
    })?;
    server.set_read_timeout(Some(timeout))?;
    server.set_write_timeout(Some(timeout))?;
    loop {
        let mut qbuffer = [0; 512];
        match server.recv_from(&mut qbuffer) {
            Ok((qlength, remote)) => {
                let qpacket = qbuffer[..qlength].to_vec();
                let remote_addr = unmap_ipv4_in_ipv6(&remote.ip());
                let hosts_files = hosts_files.clone();
                let hosts_reader = hosts_reader.clone();
                let nameservers = nameservers.clone();
                let server = server.try_clone()?;
                spawn(move || {
                    let qheader = Header::from_bytes(&qpacket);
                    if verbose { eprintln!("{} from {}", qheader, remote_addr) }
                    if qheader.qr || qheader.aa || qheader.ra || qheader.rcode != Rcode::NOERROR || qheader.ancount > 0 {
                        let rheader = Header::error(qheader.id, qheader.opcode, Rcode::FORMERR);
                        return server.send_to(&rheader.to_bytes(), remote).unwrap_or_default()
                    }
                    if qheader.opcode != Opcode::QUERY || qheader.tc || qheader.qdcount != 1 || qheader.nscount > 0 || qheader.arcount > 0 {
                        let rheader = Header::error(qheader.id, qheader.opcode, Rcode::NOTIMP);
                        return server.send_to(&rheader.to_bytes(), remote).unwrap_or_default()
                    }
                    let (question, qend) = Question::from_bytes(&qpacket, 12);
                    if verbose { eprintln!("  {}", question) }
                    let matches = match_hosts(&hosts_reader.read().unwrap(), &question.qname.to_string());
                    if matches.len() > 0 {
                        if verbose {
                            eprintln!("Found in {}", hosts_files.join(" or "));
                            for (host, addrs) in matches.iter() {
                                for addr in addrs.iter() {
                                    eprintln!("  {} {}", addr, host)
                                }
                            }
                        }
                        let mut addrs = matches.into_iter()
                            .flat_map(|(_, addrs)| addrs)
                            .filter(|addr| match question.qtype {
                                Type::A    => addr.is_ipv4() || remote_addr.is_ipv6(),
                                Type::AAAA => addr.is_ipv6(),
                                Type::ALL  => true,
                                _          => false,
                            })
                            .collect::<Vec<IpAddr>>();
                        addrs.sort_by(|a, b| {
                            if a.is_ipv4() == b.is_ipv4() { return Ordering::Equal }
                            if question.qtype != Type::AAAA && a.is_ipv4() { Ordering::Less } else { Ordering::Greater }
                        });
                        if addrs.is_empty() || addrs.iter().all(|addr| addr.is_unspecified()) {
                            let rheader = Header::error(qheader.id, qheader.opcode, Rcode::NXDOMAIN);
                            return server.send_to(&rheader.to_bytes(), remote).unwrap_or_default()
                        }
                        let ancount = addrs.iter().filter(|addr| !addr.is_unspecified()).count() as u16;
                        let rheader = Header::answer(qheader.id, qheader.opcode, 1, ancount);
                        let mut rbuffer = [0; 512];
                        rbuffer[0..12].clone_from_slice(&rheader.to_bytes());
                        rbuffer[12..qend].clone_from_slice(&qpacket[12..qend]);
                        let mut rslice = &mut rbuffer[qend..];
                        for addr in addrs.iter().filter(|addr| !addr.is_unspecified()) {
                            let (rtype, rdata) = match addr {
                                IpAddr::V4(addr) => (Type::A, addr.octets().to_vec()),
                                IpAddr::V6(addr) => (Type::AAAA, addr.octets().to_vec()),
                            };
                            rslice[0..2].clone_from_slice(&[0xC0, 12]);
                            rslice[2..4].clone_from_slice(&(rtype as u16).to_be_bytes());
                            rslice[4..6].clone_from_slice(&(question.qclass as u16).to_be_bytes());
                            rslice[6..10].clone_from_slice(&local_ttl.to_be_bytes());
                            rslice[10..12].clone_from_slice(&(rdata.len() as u16).to_be_bytes());
                            rslice[12..][..rdata.len()].clone_from_slice(&rdata);
                            rslice = &mut rslice[12+rdata.len()..];
                        }
                        let rlength = rslice.as_ptr() as usize - rbuffer.as_ptr() as usize;
                        let rpacket = &rbuffer[..rlength];
                        return server.send_to(&rpacket, remote).unwrap_or_default()
                    }
                    let query_nameserver = |qpacket: &[u8], rbuffer: &mut [u8]| -> IoResult<(usize, IpAddr)> {
                        let client = UdpSocket::bind(if nameservers.iter().all(|a| a.is_ipv4()) {
                            SocketAddr::new(Ipv4Addr::UNSPECIFIED.into(), 0)
                        } else {
                            SocketAddr::new(Ipv6Addr::UNSPECIFIED.into(), 0)
                        })?;
                        client.connect(&nameservers[..])?;
                        client.set_read_timeout(Some(timeout))?;
                        client.set_write_timeout(Some(timeout))?;
                        client.send(&qpacket)?;
                        let rlength = client.recv(rbuffer)?;
                        Ok((rlength, client.peer_addr().unwrap().ip()))
                    };
                    let mut rbuffer = [0; 512];
                    match query_nameserver(&qpacket, &mut rbuffer) {
                        Ok((rlength, peer_addr)) => {
                            let rpacket = &rbuffer[..rlength];
                            if verbose {
                                let rheader = Header::from_bytes(&rpacket);
                                eprintln!("{} from {}", rheader, peer_addr);
                                let mut offset = 12;
                                for _ in 0..rheader.qdcount {
                                    let (question, end) = Question::from_bytes(&rpacket, offset);
                                    eprintln!("  {}", question);
                                    offset = end;
                                }
                                for (count, kind) in [
                                    (rheader.ancount, "AN"),
                                    (rheader.nscount, "NS"),
                                    (rheader.arcount, "AR"),
                                ] {
                                    for i in 0..count {
                                        let (record, end) = Record::from_bytes(&rpacket, offset);
                                        if i == 0 { eprintln!("{}", kind) }
                                        eprintln!("  {}", record);
                                        offset = end;
                                    }
                                }
                            }
                            return server.send_to(&rpacket, remote).unwrap_or_default();
                        }
                        Err(e) => {
                            eprintln!("Error: {:?}", e);
                            return 0
                        }
                    }
                });
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
