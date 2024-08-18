/// Ideally we wouldn't have a list like this, but unfortunately we do.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Vendor {
    Debian,
    Ubuntu,
    Kali,
}

impl From<&str> for Vendor {
    fn from(s: &str) -> Self {
        match s {
            "debian" | "Debian" => Vendor::Debian,
            "ubuntu" | "Ubuntu" => Vendor::Ubuntu,
            "kali" | "Kali" => Vendor::Kali,
            _ => panic!("Unknown vendor"),
        }
    }
}

impl std::fmt::Display for Vendor {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Vendor::Debian => write!(f, "Debian"),
            Vendor::Ubuntu => write!(f, "Ubuntu"),
            Vendor::Kali => write!(f, "Kali"),
        }
    }
}

pub fn initial_debian_revision(vendor: Vendor) -> &'static str {
    match vendor {
        Vendor::Debian => "1",
        Vendor::Ubuntu => "0ubuntu1",
        Vendor::Kali => "0kali1",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vendor_from_str() {
        assert_eq!(Vendor::from("debian"), Vendor::Debian);
        assert_eq!(Vendor::from("Debian"), Vendor::Debian);
        assert_eq!(Vendor::from("ubuntu"), Vendor::Ubuntu);
        assert_eq!(Vendor::from("Ubuntu"), Vendor::Ubuntu);
        assert_eq!(Vendor::from("kali"), Vendor::Kali);
        assert_eq!(Vendor::from("Kali"), Vendor::Kali);
    }

    #[test]
    fn test_vendor_display() {
        assert_eq!(Vendor::Debian.to_string(), "Debian");
        assert_eq!(Vendor::Ubuntu.to_string(), "Ubuntu");
        assert_eq!(Vendor::Kali.to_string(), "Kali");
    }

    #[test]
    fn test_initial_debian_revision() {
        assert_eq!(initial_debian_revision(Vendor::Debian), "1");
        assert_eq!(initial_debian_revision(Vendor::Ubuntu), "0ubuntu1");
        assert_eq!(initial_debian_revision(Vendor::Kali), "0kali1");
    }
}
