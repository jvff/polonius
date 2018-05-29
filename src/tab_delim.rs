use crate::facts::AllFacts;
use crate::intern::{InternTo, InternerTables};
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, prelude::*};
use std::path::Path;
use std::process;

trait FromTabDelimited<'input>: Sized {
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self>;
}

crate fn load_tab_delimited_facts(
    tables: &mut InternerTables,
    facts_dir: &Path,
) -> io::Result<AllFacts> {
    macro_rules! load_facts {
        (from ($tables:expr, $facts_dir:expr) load AllFacts { $($t:ident $( : $bind:pat => $map:expr)*,)* }) => {
            Ok(AllFacts {
                $(
                    $t: {
                        let filename = format!("{}.facts", stringify!($t));
                        let facts_file = $facts_dir.join(&filename);
                        load_tab_delimited_file($tables, &facts_file)?
                            $(.into_iter()
                                .map(|$bind| $map)
                                .fold(HashMap::new(), |mut map, (k, v)| {
                                    map.entry(k).or_insert(Vec::new()).push(v);
                                    map
                                }))*
                    },
                )*
            })
        }
    }

    load_facts! {
        from (tables, facts_dir) load AllFacts {
            borrow_region: (r, l, p) => (p, (r, l)),
            universal_region,
            cfg_edge,
            killed: (l, p) => (p, l),
            outlives: (r1, r2, p) => (p, (r1, r2)),
            region_live_at: (r, p) => (p, r),
            invalidates: (p, l) => (p, l),
        }
    }
}

fn load_tab_delimited_file<Row>(tables: &mut InternerTables, path: &Path) -> io::Result<Vec<Row>>
where
    Row: for<'input> FromTabDelimited<'input>,
{
    let file = File::open(path)?;
    let mut result = Vec::new();
    for (index, line) in io::BufReader::new(file).lines().enumerate() {
        let line = line?;
        let mut columns = line.split("\t");
        let row = match FromTabDelimited::parse(tables, &mut columns) {
            None => {
                eprintln!("error parsing line {} of `{}`", index + 1, path.display());
                process::exit(1);
            }

            Some(v) => v,
        };

        if columns.next().is_some() {
            eprintln!("extra data on line {} of `{}`", index + 1, path.display());
            process::exit(1);
        }

        result.push(row);
    }
    Ok(result)
}

impl<T> FromTabDelimited<'input> for T
where
    &'input str: InternTo<T>,
{
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self> {
        let input = inputs.next()?;
        Some(InternTo::intern(tables, input))
    }
}

impl<A, B> FromTabDelimited<'input> for (A, B)
where
    A: FromTabDelimited<'input>,
    B: FromTabDelimited<'input>,
{
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self> {
        let a = A::parse(tables, inputs)?;
        let b = B::parse(tables, inputs)?;
        Some((a, b))
    }
}

impl<A, B, C> FromTabDelimited<'input> for (A, B, C)
where
    A: FromTabDelimited<'input>,
    B: FromTabDelimited<'input>,
    C: FromTabDelimited<'input>,
{
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self> {
        let a = A::parse(tables, inputs)?;
        let b = B::parse(tables, inputs)?;
        let c = C::parse(tables, inputs)?;
        Some((a, b, c))
    }
}

impl<A, B, C, D> FromTabDelimited<'input> for (A, B, C, D)
where
    A: FromTabDelimited<'input>,
    B: FromTabDelimited<'input>,
    C: FromTabDelimited<'input>,
    D: FromTabDelimited<'input>,
{
    fn parse(
        tables: &mut InternerTables,
        inputs: &mut dyn Iterator<Item = &'input str>,
    ) -> Option<Self> {
        let a = A::parse(tables, inputs)?;
        let b = B::parse(tables, inputs)?;
        let c = C::parse(tables, inputs)?;
        let d = D::parse(tables, inputs)?;
        Some((a, b, c, d))
    }
}
