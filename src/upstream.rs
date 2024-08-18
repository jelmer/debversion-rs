//! Utilities for working with upstream versions.

static DFSG_REGEX: &lazy_regex::Lazy<lazy_regex::Regex> =
    lazy_regex::regex!(r"^(.*)([\+~])(dfsg|ds)([0-9]*)$");
const DFSG_DEFAULT_STYLE: &str = "+ds";

/// Strip the DFSG suffix from a version.
pub fn strip_dfsg_suffix(version: &str) -> Option<&str> {
    if let Some(m) = DFSG_REGEX.captures(version) {
        Some(m.get(1).unwrap().as_str())
    } else {
        None
    }
}

/// Add a dfsg suffix to an version version string.
///
/// Allow old_upstream_version to be passed in so optionally the format can be
/// kept consistent.
pub fn add_dfsg_suffix(upstream_version: &str, old_upstream_version: Option<&str>) -> String {
    let style = if let Some(m) = old_upstream_version.and_then(|d| DFSG_REGEX.captures(d)) {
        let mut style = m.get(2).unwrap().as_str().to_string() + m.get(3).unwrap().as_str();
        if !m.get(4).unwrap().as_str().is_empty() {
            style.push('1');
        }
        style
    } else {
        DFSG_DEFAULT_STYLE.to_string()
    };
    upstream_version.to_string() + style.as_str()
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_strip_dfsg_suffix() {
        assert_eq!(super::strip_dfsg_suffix("1.2.3+dfsg1"), Some("1.2.3"));
        assert_eq!(super::strip_dfsg_suffix("1.2.3+ds1"), Some("1.2.3"));
        assert_eq!(super::strip_dfsg_suffix("1.2.3"), None);
    }

    #[test]
    fn test_add_dfsg_suffix() {
        assert_eq!(super::add_dfsg_suffix("1.2.3", None), "1.2.3+ds");
        assert_eq!(
            super::add_dfsg_suffix("1.2.3", Some("1.2.3+dfsg1")),
            "1.2.3+dfsg1"
        );
        assert_eq!(
            super::add_dfsg_suffix("1.2.3", Some("1.2.3+ds1")),
            "1.2.3+ds1"
        );
        assert_eq!(super::add_dfsg_suffix("1.2.3", Some("1.2.3")), "1.2.3+ds");
    }
}
