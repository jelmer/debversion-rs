use crate::Version;

pub fn mangle_version_for_git(version: &Version) -> String {
    let version = version.to_string();
    // See https://dep-team.pages.debian.net/deps/dep14/
    let mut manipulated = version
        .replace("~", "_")
        .replace(":", "%")
        .replace("..", ".#.");
    if manipulated.ends_with(".") {
        manipulated.push('#');
    }
    if let Some(prefix) = manipulated.strip_suffix(".lock") {
        manipulated = prefix.to_string() + "#lock"
    }
    manipulated
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mangle_version_for_git() {
        assert_eq!(mangle_version_for_git(&"1.0.0".parse().unwrap()), "1.0.0");
        assert_eq!(
            mangle_version_for_git(&"1.0.0~rc1".parse().unwrap()),
            "1.0.0_rc1"
        );
        assert_eq!(
            mangle_version_for_git(&"2:1.0.0-1".parse().unwrap()),
            "2%1.0.0-1"
        );
        assert_eq!(
            mangle_version_for_git(&"1.0.0..rc1".parse().unwrap()),
            "1.0.0.#.rc1"
        );
        assert_eq!(
            mangle_version_for_git(&"1.0.0.lock".parse().unwrap()),
            "1.0.0#lock"
        );
    }
}