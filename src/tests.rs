use crate::{Link, PkgConfig};
use std::error::Error;

#[test]
fn libs() -> Result<(), Box<dyn Error>> {
    #[rustfmt::skip]
    let pc = PkgConfig::from_bytes(
br#"pcfiledir="C:\Program Files (x86)\Test"
libdir=${pcfiledir}\test\ path # Comment

Libs: -L${libdir} -llib -F/Library/Frameworks -framework Fw1 -Wl,-framework,Fw2 -weak_framework \
    Wfw1 -Wl,-weak_framework,Wfw2 ${libdir}/"static library.a" -rpath rpath1 -Wl,-rpath,rpath2
"#,
    )?;

    let mut search_lib = 0;
    let mut search_framework = 0;
    let mut lib = 0;
    let mut framework = 0;
    let mut weak_framework = 0;
    let mut rpath = 0;
    let mut verbatim = 0;

    for link in pc.libs()? {
        match link {
            Link::SearchLib(path) => {
                search_lib += 1;
                assert_eq!(
                    format!("{}", path.display()),
                    r#"C:\Program Files (x86)\Test\test path"#
                )
            }

            Link::SearchFramework(path) => {
                search_framework += 1;
                assert_eq!(format!("{}", path.display()), "/Library/Frameworks")
            }

            Link::Lib(path) => {
                lib += 1;
                assert_eq!(format!("{}", path.display()), "lib")
            }

            Link::Framework(path) => {
                framework += 1;
                match framework {
                    1 => assert_eq!(format!("{}", path.display()), "Fw1"),
                    2 => assert_eq!(format!("{}", path.display()), "Fw2"),
                    _ => unreachable!(),
                }
            }

            Link::WeakFramework(path) => {
                weak_framework += 1;
                match weak_framework {
                    1 => assert_eq!(format!("{}", path.display()), "Wfw1"),
                    2 => assert_eq!(format!("{}", path.display()), "Wfw2"),
                    _ => unreachable!(),
                }
            }

            Link::Rpath(path) => {
                rpath += 1;
                match rpath {
                    1 => assert_eq!(format!("{}", path.display()), "rpath1"),
                    2 => assert_eq!(format!("{}", path.display()), "rpath2"),
                    _ => unreachable!(),
                }
            }

            Link::Verbatim(path) => {
                verbatim += 1;
                assert_eq!(
                    format!("{}", path.display()),
                    r#"C:\Program Files (x86)\Test\test path/static library.a"#
                )
            }
        }
    }

    assert_eq!(search_lib, 1);
    assert_eq!(search_framework, 1);
    assert_eq!(lib, 1);
    assert_eq!(framework, 2);
    assert_eq!(weak_framework, 2);
    assert_eq!(rpath, 2);
    assert_eq!(verbatim, 1);

    Ok(())
}
