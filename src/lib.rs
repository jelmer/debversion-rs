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

use lazy_regex::{regex_captures, regex_replace};
use std::cmp::Ordering;
use std::str::FromStr;

/// A Debian version string
///
///
#[derive(Debug, Clone)]
pub struct Version {
    /// The epoch of the version, if any
    pub epoch: Option<u32>,

    /// The upstream version
    pub upstream_version: String,

    /// The Debian revision, if any
    pub debian_revision: Option<String>,
}

fn non_digit_cmp(va: &str, vb: &str) -> Ordering {
    fn order(x: char) -> i32 {
        match x {
            '~' => -1,
            '0'..='9' => unreachable!(),
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

#[test]
fn test_non_digit_cmp() {
    assert_eq!(non_digit_cmp("a", "b"), Ordering::Less);
    assert_eq!(non_digit_cmp("b", "a"), Ordering::Greater);
    assert_eq!(non_digit_cmp("a", "a"), Ordering::Equal);
    assert_eq!(non_digit_cmp("a", "-"), Ordering::Less);
    assert_eq!(non_digit_cmp("a", "+"), Ordering::Less);
    assert_eq!(non_digit_cmp("a", ""), Ordering::Greater);
    assert_eq!(non_digit_cmp("", "a"), Ordering::Less);
    assert_eq!(non_digit_cmp("", ""), Ordering::Equal);
    assert_eq!(non_digit_cmp("~", ""), Ordering::Less);
    assert_eq!(non_digit_cmp("~~", "~"), Ordering::Less);
    assert_eq!(non_digit_cmp("~~", "~~a"), Ordering::Less);
    assert_eq!(non_digit_cmp("~~a", "~"), Ordering::Less);
    assert_eq!(non_digit_cmp("~", "a"), Ordering::Less);
}

fn version_cmp_part(mut a: &str, mut b: &str) -> Ordering {
    while !a.is_empty() || !b.is_empty() {
        // First, create a slice for the non-digit leading part of each string
        let a_non_digit = a
            .chars()
            .take_while(|c| !c.is_ascii_digit())
            .collect::<String>();
        let b_non_digit = b
            .chars()
            .take_while(|c| !c.is_ascii_digit())
            .collect::<String>();

        // Compare the non-digit leading part
        match non_digit_cmp(&a_non_digit, &b_non_digit) {
            Ordering::Equal => (),
            ordering => return ordering,
        }

        // Remove the non-digit leading part from the strings
        a = &a[a_non_digit.len()..];
        b = &b[b_non_digit.len()..];

        // Then, create a slice for the digit part of each string
        let a_digit = a
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect::<String>();
        let b_digit = b
            .chars()
            .take_while(|c| c.is_ascii_digit())
            .collect::<String>();

        let a_num = if a_digit.is_empty() {
            0
        } else {
            a_digit.parse::<i32>().unwrap()
        };

        let b_num = if b_digit.is_empty() {
            0
        } else {
            b_digit.parse::<i32>().unwrap()
        };

        // Compare the digit part
        match a_num.cmp(&b_num) {
            Ordering::Equal => (),
            ordering => return ordering,
        }

        // Remove the digit part from the strings
        a = &a[a_digit.len()..];
        b = &b[b_digit.len()..];
    }
    Ordering::Equal
}

impl Ord for Version {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let self_norm = self.explicit();
        let other_norm = other.explicit();
        if self_norm.0 != other_norm.0 {
            return std::cmp::Ord::cmp(&self_norm.0, &other_norm.0);
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
        let (_, epoch, upstream_version, debian_revision) = match regex_captures!(
            r"^(?:(\d+):)?([A-Za-z0-9.+:~-]+?)(?:-([A-Za-z0-9+.~]+))?$",
            text
        ) {
            Some(c) => c,
            None => return Err(ParseError(format!("Invalid version string: {}", text))),
        };

        let epoch = Some(epoch)
            .filter(|e| !e.is_empty())
            .map(|e| {
                e.parse()
                    .map_err(|e| ParseError(format!("Error parsing epoch: {}", e)))
            })
            .transpose()?;

        let debian_revision = Some(debian_revision).filter(|e| !e.is_empty());

        Ok(Version {
            epoch,
            upstream_version: upstream_version.to_string(),
            debian_revision: debian_revision.map(|e| e.to_string()),
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

impl std::hash::Hash for Version {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (
            self.epoch,
            self.upstream_version.as_str(),
            self.debian_revision.as_deref(),
        )
            .hash(state);
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
    ///
    /// # Examples
    ///
    /// ```
    /// use debversion::Version;
    /// assert_eq!("1.0-0".parse::<Version>().unwrap().canonicalize(), "1.0".parse::<Version>().unwrap());
    /// assert_eq!("1.0-1".parse::<Version>().unwrap().canonicalize(), "1.0-1".parse::<Version>().unwrap());
    /// ```
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

    /// Increment the Debian revision.
    ///
    /// For native packages, increment the upstream version number.
    /// For other packages, increment the debian revision.
    pub fn increment_debian(&mut self) {
        if self.debian_revision.is_some() {
            self.debian_revision = self.debian_revision.as_ref().map(|v| {
                {
                    regex_replace!(r"\d+$", v, |x: &str| (x.parse::<i32>().unwrap() + 1)
                        .to_string())
                }
                .to_string()
            });
        } else {
            self.upstream_version =
                regex_replace!(r"\d+$", self.upstream_version.as_ref(), |x: &str| (x
                    .parse::<i32>()
                    .unwrap()
                    + 1)
                .to_string())
                .to_string();
        }
    }

    /// Return true if this is a native package
    pub fn is_native(&self) -> bool {
        self.debian_revision.is_none()
    }
}

#[cfg(test)]
mod tests {
    use super::{version_cmp_part, ParseError, Version};
    use std::cmp::Ordering;

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
    fn test_version_cmp_part() {
        assert_eq!(version_cmp_part("1.0", "1.0"), Ordering::Equal);
        assert_eq!(version_cmp_part("1.0", "2.0"), Ordering::Less);
        assert_eq!(version_cmp_part("1.0", "0.0"), Ordering::Greater);
        assert_eq!(version_cmp_part("10.0", "2.0"), Ordering::Greater);
        assert_eq!(version_cmp_part("1.0~rc1", "1.0"), Ordering::Less);
    }

    #[test]
    fn test_cmp() {
        assert_cmp!("1.0-1", "1.0-1", Equal);
        assert_cmp!("1.0-1", "1.0-2", Less);
        assert_cmp!("1.0-2", "1.0-1", Greater);
        assert_cmp!("1.0-1", "1.0", Greater);
        assert_cmp!("1.0", "1.0-1", Less);
        assert_cmp!("2.50.0", "10.0.1", Less);

        // Epoch
        assert_cmp!("1:1.0-1", "1.0-1", Greater);
        assert_cmp!("1.0-1", "1:1.0-1", Less);
        assert_cmp!("1:1.0-1", "1:1.0-1", Equal);
        assert_cmp!("1:1.0-1", "2:1.0-1", Less);
        assert_cmp!("2:1.0-1", "1:1.0-1", Greater);

        // ~ symbol
        assert_cmp!("1.0~rc1-1", "1.0-1", Less);
        assert_cmp!("1.0-1", "1.0~rc1-1", Greater);
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
            ParseError("Invalid version string: 1:;a".to_string())
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

    #[test]
    fn test_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();
        let mut hasher3 = DefaultHasher::new();

        "1.0-1".parse::<Version>().unwrap().hash(&mut hasher1);
        "1.0-1".parse::<Version>().unwrap().hash(&mut hasher2);
        "0:1.0-1".parse::<Version>().unwrap().hash(&mut hasher3);

        let hash1 = hasher1.finish();
        let hash2 = hasher2.finish();
        let hash3 = hasher3.finish();

        assert_eq!(hash1, hash2);
        assert_ne!(hash1, hash3);
    }

    #[test]
    fn to_string() {
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
    fn partial_eq() {
        assert!("1.0-1"
            .parse::<Version>()
            .unwrap()
            .eq(&"1.0-1".parse::<Version>().unwrap()));
    }

    #[test]
    fn increment() {
        let mut v = "1.0-1".parse::<Version>().unwrap();
        v.increment_debian();

        assert_eq!("1.0-2".parse::<Version>().unwrap(), v);

        let mut v = "1.0".parse::<Version>().unwrap();
        v.increment_debian();
        assert_eq!("1.1".parse::<Version>().unwrap(), v);

        let mut v = "1.0ubuntu1".parse::<Version>().unwrap();
        v.increment_debian();
        assert_eq!("1.0ubuntu2".parse::<Version>().unwrap(), v);

        let mut v = "1.0-0ubuntu1".parse::<Version>().unwrap();
        v.increment_debian();
        assert_eq!("1.0-0ubuntu2".parse::<Version>().unwrap(), v);
    }

    #[test]
    fn is_native() {
        assert!(!"1.0-1".parse::<Version>().unwrap().is_native());
        assert!("1.0".parse::<Version>().unwrap().is_native());
        assert!(!"1.0-0".parse::<Version>().unwrap().is_native());
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
        sqlx::Encode::<Postgres>::encode_by_ref(&self.to_string().as_str(), buf)
    }
}

#[cfg(feature = "sqlx")]
impl sqlx::Decode<'_, Postgres> for Version {
    fn decode(
        value: sqlx::postgres::PgValueRef<'_>,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let s: &str = sqlx::Decode::<Postgres>::decode(value)?;
        Ok(s.parse::<Version>()?)
    }
}

#[cfg(all(feature = "sqlx", test))]
mod sqlx_tests {
    #[test]
    fn type_info() {
        use super::Version;
        use sqlx::postgres::PgTypeInfo;
        use sqlx::Type;

        assert_eq!(PgTypeInfo::with_name("debversion"), Version::type_info());
    }
}

#[cfg(feature = "python-debian")]
use pyo3::prelude::*;

#[cfg(feature = "python-debian")]
impl FromPyObject<'_> for Version {
    fn extract(ob: &PyAny) -> PyResult<Self> {
        let debian_support = Python::import(ob.py(), "debian.debian_support")?;
        let version_cls = debian_support.getattr("Version")?;
        if !ob.is_instance(version_cls)? {
            return Err(pyo3::exceptions::PyTypeError::new_err("Expected a Version"));
        }
        Ok(Version {
            epoch: ob
                .getattr("epoch")?
                .extract::<Option<String>>()?
                .map(|s| s.parse().unwrap()),
            upstream_version: ob.getattr("upstream_version")?.extract::<String>()?,
            debian_revision: ob.getattr("debian_revision")?.extract::<Option<String>>()?,
        })
    }
}

#[cfg(feature = "python-debian")]
impl ToPyObject for Version {
    fn to_object(&self, py: Python) -> PyObject {
        let debian_support = py.import("debian.debian_support").unwrap();
        let version_cls = debian_support.getattr("Version").unwrap();
        version_cls
            .call1((self.to_string(),))
            .unwrap()
            .to_object(py)
    }
}

#[cfg(feature = "python-debian")]
impl IntoPy<PyObject> for Version {
    fn into_py(self, py: Python) -> PyObject {
        self.to_object(py)
    }
}

#[cfg(feature = "python-debian")]
mod python_tests {
    #[test]
    fn test_from_pyobject() {
        use super::Version;
        use pyo3::prelude::*;

        Python::with_gil(|py| {
            let globals = pyo3::types::PyDict::new(py);
            globals
                .set_item(
                    "debian_support",
                    py.import("debian.debian_support").unwrap(),
                )
                .unwrap();
            let v = py
                .eval("debian_support.Version('1.0-1')", Some(globals), None)
                .unwrap()
                .extract::<Version>()
                .unwrap();
            assert_eq!(
                v,
                Version {
                    epoch: None,
                    upstream_version: "1.0".to_string(),
                    debian_revision: Some("1".to_string())
                }
            );
        });
    }

    #[test]
    fn test_to_pyobject() {
        use super::Version;
        use pyo3::prelude::*;

        Python::with_gil(|py| {
            let v = Version {
                epoch: Some(1),
                upstream_version: "1.0".to_string(),
                debian_revision: Some("1".to_string()),
            };
            let v = v.to_object(py);
            let expected: Version = "1:1.0-1".parse().unwrap();
            assert_eq!(v.extract::<Version>(py).unwrap(), expected);
            assert_eq!(v.as_ref(py).get_type().name().unwrap(), "Version");
        });
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Version {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Version {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let concatenated: String = String::deserialize(deserializer)?;
        concatenated.parse().map_err(serde::de::Error::custom)
    }
}

pub trait AsVersion {
    fn as_version(self) -> Result<Version, ParseError>;
}

impl AsVersion for &str {
    fn as_version(self) -> Result<Version, ParseError> {
        self.parse()
    }
}

impl AsVersion for String {
    fn as_version(self) -> Result<Version, ParseError> {
        self.parse()
    }
}

impl AsVersion for Version {
    fn as_version(self) -> Result<Version, ParseError> {
        Ok(self.clone())
    }
}
