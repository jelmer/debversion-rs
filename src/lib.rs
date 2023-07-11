//! Debian version type, consistent with Section 5.6.12 in the Debian Policy Manual
//!
//! This structure can be used for validating, dissecting and comparing Debian version strings.
//!
//! # Examples
//!
//! ```
//! use debversion::Version;
//!
//! let version1: Version = "1.2.3".parse().unwrap();
//! assert_eq!(version1.upstream_version.as_str(), "1.2.3");
//! assert_eq!(version1.debian_revision, None);
//! assert_eq!(version1.epoch, None);
//!
//! let version2: Version = "1:1.2.3".parse().unwrap();
//! assert_eq!(version2.upstream_version.as_str(), "1.2.3");
//! assert_eq!(version2.debian_revision, None);
//! assert_eq!(version2.epoch, Some(1));
//!
//! assert_eq!(version1, version1);
//! assert!(version1 < version2);

use lazy_regex::regex;
use std::cmp::Ordering;
use std::str::FromStr;

/// A Debian version string
///
///
#[derive(Debug, Clone)]
pub struct Version {
    pub epoch: Option<u32>,
    pub upstream_version: String,
    pub debian_revision: Option<String>,
}

fn version_cmp_string(va: &str, vb: &str) -> Ordering {
    fn order(x: char) -> i32 {
        match x {
            '~' => -1,
            '0'..='9' => x.to_digit(10).unwrap_or(0) as i32 + 1,
            'A'..='Z' | 'a'..='z' => x as i32,
            _ => x as i32 + 256,
        }
    }

    let la: Vec<i32> = va.chars().map(order).collect();
    let lb: Vec<i32> = vb.chars().map(order).collect();
    let mut la_iter = la.iter();
    let mut lb_iter = lb.iter();
    while la_iter.len() > 0 || lb_iter.len() > 0 {
        let a = if let Some(a) = la_iter.next() { *a } else { 0 };
        let b = if let Some(b) = lb_iter.next() { *b } else { 0 };
        if a < b {
            return Ordering::Less;
        }
        if a > b {
            return Ordering::Greater;
        }
    }
    Ordering::Equal
}

fn version_cmp_part(va: &str, vb: &str) -> Ordering {
    let mut la_iter = va.chars();
    let mut lb_iter = vb.chars();
    let mut la = String::new();
    let mut lb = String::new();
    let mut res = Ordering::Equal;

    while let (Some(a), Some(b)) = (la_iter.next(), lb_iter.next()) {
        if a.is_ascii_digit() && b.is_ascii_digit() {
            la.clear();
            lb.clear();
            la.push(a);
            lb.push(b);
            for digit_a in la_iter.by_ref() {
                if digit_a.is_ascii_digit() {
                    la.push(digit_a);
                } else {
                    break;
                }
            }
            for digit_b in lb_iter.by_ref() {
                if digit_b.is_ascii_digit() {
                    lb.push(digit_b);
                } else {
                    break;
                }
            }
            let aval = la.parse::<i32>().unwrap();
            let bval = lb.parse::<i32>().unwrap();
            if aval < bval {
                res = Ordering::Less;
                break;
            }
            if aval > bval {
                res = Ordering::Greater;
                break;
            }
        } else {
            res = version_cmp_string(&a.to_string(), &b.to_string());
            if res != Ordering::Equal {
                break;
            }
        }
    }
    res
}

impl Ord for Version {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let self_norm = self.explicit();
        let other_norm = other.explicit();
        if self_norm.0 != other_norm.0 {
            return std::cmp::Ord::cmp(&self_norm.0, &other_norm.0);
        }

        if self.upstream_version != other.upstream_version {
            return self.upstream_version.cmp(&other.upstream_version);
        }

        match version_cmp_part(self_norm.1.as_str(), other_norm.1.as_str()) {
            Ordering::Equal => (),
            ordering => return ordering,
        }

        version_cmp_part(self_norm.2.as_str(), other_norm.2.as_str())
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Version {
    fn eq(&self, other: &Self) -> bool {
        self.partial_cmp(other) == Some(std::cmp::Ordering::Equal)
    }
}

impl Eq for Version {}

#[derive(Debug, PartialEq, Eq)]
pub struct ParseError(String);

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ParseError {}

impl FromStr for Version {
    type Err = ParseError;

    fn from_str(text: &str) -> Result<Self, Self::Err> {
        let c = regex!(
            r"^((?P<epoch>\d+):)?(?P<upstream_version>[A-Za-z0-9.+:~-]+?)(-(?P<debian_revision>[A-Za-z0-9+.~]+))?$").captures(text).ok_or(ParseError("Invalid debian version".to_string()))?;

        let epoch = c
            .name("epoch")
            .map(|e| {
                e.as_str()
                    .parse()
                    .map_err(|e| ParseError(format!("Error parsing epoch: {}", e)))
            })
            .transpose()?;
        let upstream_version = c.name("upstream_version").unwrap().as_str().to_string();
        let debian_revision = c.name("debian_revision").map(|r| r.as_str().to_string());

        Ok(Version {
            epoch,
            upstream_version,
            debian_revision,
        })
    }
}

impl ToString for Version {
    fn to_string(&self) -> String {
        let mut ret = vec![self.upstream_version.clone()];
        if let Some(epoch) = self.epoch.as_ref() {
            ret.insert(0, format!("{}:", epoch));
        }
        if let Some(debian_revision) = self.debian_revision.as_ref() {
            ret.push(format!("-{}", debian_revision));
        }
        ret.concat()
    }
}

impl Version {
    /// Return explicit tuple of this version
    ///
    /// This will return an explicit 0 for epochs and debian revisions
    /// that are not set.
    fn explicit(&self) -> (u32, String, String) {
        (
            self.epoch.unwrap_or(0),
            self.upstream_version.trim_start_matches('0').to_string(),
            self.debian_revision.as_deref().unwrap_or("0").to_string(),
        )
    }

    /// Return canonicalized version of this version
    pub fn canonicalize(&self) -> Version {
        let epoch = match self.epoch {
            Some(0) | None => None,
            Some(epoch) => Some(epoch),
        };

        let upstream_version = self.upstream_version.trim_start_matches('0');

        let debian_revision = match self.debian_revision.as_ref() {
            Some(r) if r.chars().all(|c| c == '0') => None,
            None => None,
            Some(revision) => Some(revision.clone()),
        };

        Version {
            epoch,
            upstream_version: upstream_version.to_string(),
            debian_revision,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ParseError, Version};

    #[test]
    fn test_canonicalize() {
        assert_eq!(
            "1.0-1".parse::<Version>().unwrap().canonicalize(),
            "1.0-1".parse::<Version>().unwrap()
        );
        assert_eq!(
            "1.0-0".parse::<Version>().unwrap().canonicalize(),
            "1.0".parse::<Version>().unwrap()
        );
        assert_eq!(
            "0:1.0-2".parse::<Version>().unwrap().canonicalize(),
            "1.0-2".parse::<Version>().unwrap()
        );
    }

    #[test]
    fn test_explicit() {
        assert_eq!(
            (0, "1.0".to_string(), "1".to_string()),
            "1.0-1".parse::<Version>().unwrap().explicit()
        );
        assert_eq!(
            (1, "1.0".to_string(), "1".to_string()),
            "1:1.0-1".parse::<Version>().unwrap().explicit()
        );
        assert_eq!(
            (0, "1.0".to_string(), "0".to_string()),
            "1.0".parse::<Version>().unwrap().explicit()
        );
        assert_eq!(
            (0, "1.0".to_string(), "0".to_string()),
            "1.0-0".parse::<Version>().unwrap().explicit()
        );
        assert_eq!(
            (1, "1.0".to_string(), "0".to_string()),
            "1:1.0-0".parse::<Version>().unwrap().explicit()
        );
    }

    macro_rules! assert_cmp(
        ($a:expr, $b:expr, $cmp:tt) => {
            assert_eq!($a.parse::<Version>().unwrap().cmp(&$b.parse::<Version>().unwrap()), std::cmp::Ordering::$cmp);
        }
    );

    #[test]
    fn test_cmp() {
        assert_cmp!("1.0-1", "1.0-1", Equal);
        assert_cmp!("1.0-1", "1.0-2", Less);
        assert_cmp!("1.0-2", "1.0-1", Greater);
        assert_cmp!("1.0-1", "1.0", Greater);
        assert_cmp!("1.0", "1.0-1", Less);

        // Epoch
        assert_cmp!("1:1.0-1", "1.0-1", Greater);
        assert_cmp!("1.0-1", "1:1.0-1", Less);
        assert_cmp!("1:1.0-1", "1:1.0-1", Equal);
        assert_cmp!("1:1.0-1", "2:1.0-1", Less);
        assert_cmp!("2:1.0-1", "1:1.0-1", Greater);

        // ~ symbol
        assert_cmp!("1.0~rc1-1", "1.0-1", Greater);
        assert_cmp!("1.0-1", "1.0~rc1-1", Less);
        assert_cmp!("1.0~rc1-1", "1.0~rc1-1", Equal);
        assert_cmp!("1.0~rc1-1", "1.0~rc2-1", Less);
        assert_cmp!("1.0~rc2-1", "1.0~rc1-1", Greater);

        // letters
        assert_cmp!("1.0a-1", "1.0-1", Greater);
        assert_cmp!("1.0-1", "1.0a-1", Less);
        assert_cmp!("1.0a-1", "1.0a-1", Equal);
    }

    #[test]
    fn test_parse() {
        assert_eq!(
            Version {
                epoch: None,
                upstream_version: "1.0".to_string(),
                debian_revision: Some("1".to_string())
            },
            "1.0-1".parse().unwrap()
        );

        assert_eq!(
            Version {
                epoch: None,
                upstream_version: "1.0".to_string(),
                debian_revision: None
            },
            "1.0".parse().unwrap()
        );

        assert_eq!(
            Version {
                epoch: Some(1),
                upstream_version: "1.0".to_string(),
                debian_revision: Some("1".to_string())
            },
            "1:1.0-1".parse().unwrap()
        );
        assert_eq!(
            "1:;a".parse::<Version>().unwrap_err(),
            ParseError("Invalid debian version".to_string())
        );
    }

    #[test]
    fn test_to_string() {
        assert_eq!(
            "1.0-1",
            Version {
                epoch: None,
                upstream_version: "1.0".to_string(),
                debian_revision: Some("1".to_string())
            }
            .to_string()
        );
        assert_eq!(
            "1.0",
            Version {
                epoch: None,
                upstream_version: "1.0".to_string(),
                debian_revision: None,
            }
            .to_string()
        );
    }

    #[test]
    fn test_eq() {
        assert_eq!(
            "1.0-1".parse::<Version>().unwrap(),
            "1.0-1".parse::<Version>().unwrap()
        );
    }
}

#[cfg(feature = "sqlx")]
use sqlx::{postgres::PgTypeInfo, Postgres};

#[cfg(feature = "sqlx")]
impl sqlx::Type<Postgres> for Version {
    fn type_info() -> PgTypeInfo {
        PgTypeInfo::with_name("debversion")
    }
}

#[cfg(feature = "sqlx")]
impl sqlx::Encode<'_, Postgres> for Version {
    fn encode_by_ref(&self, buf: &mut sqlx::postgres::PgArgumentBuffer) -> sqlx::encode::IsNull {
        sqlx::Encode::encode_by_ref(&self.to_string().as_str(), buf)
    }
}

#[cfg(feature = "sqlx")]
impl sqlx::Decode<'_, Postgres> for Version {
    fn decode(
        value: sqlx::postgres::PgValueRef<'_>,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let s: &str = sqlx::Decode::decode(value)?;
        Ok(s.parse::<Version>()?)
    }
}
