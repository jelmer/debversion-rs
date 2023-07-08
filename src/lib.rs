//! Debian version type, consistent with Section 5.6.12 in the Debian Policy Manual
//!
//! This structure can be used for validating, dissecting and comparing Debian version strings.

use std::str::FromStr;
use lazy_regex::regex;

/// A Debian version string
///
///
#[derive(Debug)]
struct Version {
    epoch: Option<u32>,
    upstream_version: String,
    debian_revision: Option<String>
}

#[derive(Debug, PartialEq, Eq)]
struct ParseError(String);

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

        let epoch = c.name("epoch").map(|e| e.as_str().parse().map_err(|e| ParseError(format!("Error parsing epoch: {}", e)))).transpose()?;
        let upstream_version = c.name("upstream_version").unwrap().as_str().to_string();
        let debian_revision = c.name("debian_revision").map(|r| r.as_str().to_string());

        Ok(Version {
            epoch,
            upstream_version,
            debian_revision
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

impl PartialEq for Version {
    fn eq(&self, other: &Self) -> bool {
        let self_epoch = self.epoch.unwrap_or(0);
        let other_epoch = other.epoch.unwrap_or(0);
        if self_epoch != other_epoch {
            return false;
        }

        if self.upstream_version != other.upstream_version {
            return false;
        }

        let self_deb_revision = self.debian_revision.as_deref().unwrap_or("0");
        let other_deb_revision = other.debian_revision.as_deref().unwrap_or("0");

        self_deb_revision == other_deb_revision
    }
}

impl Eq for Version {}

#[cfg(test)]
mod tests {
    use super::{Version, ParseError};

    #[test]
    fn test_parse() {
        assert_eq!(Version {
            epoch: None,
            upstream_version: "1.0".to_string(),
            debian_revision: Some("1".to_string())
        }, "1.0-1".parse().unwrap());

        assert_eq!(Version {
            epoch: None,
            upstream_version: "1.0".to_string(),
            debian_revision: None
        }, "1.0".parse().unwrap());

        assert_eq!(Version {
            epoch: Some(1),
            upstream_version: "1.0".to_string(),
            debian_revision: Some("1".to_string())
        }, "1:1.0-1".parse().unwrap());
        assert_eq!("1:1:1:1:".parse::<Version>().unwrap_err(), ParseError("Foo".to_string()));
    }

    #[test]
    fn test_to_string() {
        assert_eq!("1.0-1", Version {
            epoch: None,
            upstream_version: "1.0".to_string(),
            debian_revision: Some("1".to_string())
        }.to_string());
        assert_eq!("1.0", Version {
            epoch: None,
            upstream_version: "1.0".to_string(),
            debian_revision: None,
        }.to_string());
    }

    #[test]
    fn test_eq() {
        assert_eq!("1.0-1".parse::<Version>().unwrap(), "1.0-1".parse::<Version>().unwrap());
    }
}

#[cfg(feature = "sqlx")]
impl sqlx::Type<Postgres> for Debversion {
    fn type_info() -> PgTypeInfo {
        PgTypeInfo::with_name("debversion")
    }
}

impl sqlx::Encode<'_, Postgres> for Debversion {
    fn encode_by_ref(&self, buf: &mut sqlx::postgres::PgArgumentBuffer) -> sqlx::encode::IsNull {
        sqlx::Encode::encode_by_ref(&self.0.as_str(), buf)
    }
}

impl sqlx::Decode<'_, Postgres> for Debversion {
    fn decode(
        value: sqlx::postgres::PgValueRef<'_>,
    ) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let s: &str = sqlx::Decode::decode(value)?;
        Ok(Debversion(s.to_string()))
    }
}

