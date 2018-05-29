use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// The "facts" which are the basis of the NLL borrow analysis.
#[derive(Clone)]
pub struct AllFacts<R: Atom, L: Atom, P: Atom> {
    /// `borrow_region(R, B, P)` -- the region R may refer to data
    /// from borrow B starting at the point P (this is usually the
    /// point *after* a borrow rvalue)
    pub borrow_region: HashMap<P, Vec<(R, L)>>,

    /// `universal_region(R)` -- this is a "free region" within fn body
    pub universal_region: Vec<R>,

    /// `cfg_edge(P,Q)` for each edge P -> Q in the control flow
    pub cfg_edge: Vec<(P, P)>,

    /// `killed(B,P)` when some prefix of the path borrowed at B is assigned at point P
    pub killed: HashMap<P, Vec<L>>,

    /// `outlives(R1, R2, P)` when we require `R1@P: R2@P`
    pub outlives: HashMap<P, Vec<(R, R)>>,

    /// `region_live_at(R, P)` when the region R appears in a live variable at P
    pub region_live_at: HashMap<P, Vec<R>>,

    ///  `invalidates(P, L)` when the loan L is invalidated at point P
    pub invalidates: HashMap<P, Vec<L>>,
}

impl<Region: Atom, Loan: Atom, Point: Atom> AllFacts<Region, Loan, Point> {
    pub fn simplify_cfg(&mut self) {
        for chain in self.isolated_chains() {
            self.simplify_chain(chain);
        }
    }

    fn isolated_chains(&self) -> Vec<Vec<Point>> {
        let mut isolated_edges = self.isolated_edges();
        let mut chain_heads: HashSet<_> = isolated_edges.keys().cloned().collect();
        let mut chains = Vec::new();

        for (_p, q) in &isolated_edges {
            chain_heads.remove(q);
        }

        for head in chain_heads {
            let mut current = head;
            let mut chain = Vec::with_capacity(2);

            chain.push(current);

            while let Some(next) = isolated_edges.remove(&current) {
                chain.push(next);
                current = next;
            }

            chains.push(chain);
        }

        chains
    }

    fn isolated_edges(&self) -> HashMap<Point, Point> {
        let mut successors = HashMap::new();
        let mut predecessors = HashMap::new();

        for &(p, q) in &self.cfg_edge {
            if successors.contains_key(&p) {
                successors.insert(p, None);
            } else {
                successors.insert(p, Some(q));
            }

            if predecessors.contains_key(&q) {
                predecessors.insert(q, None);
            } else {
                predecessors.insert(q, Some(p));
            }
        }

        let unique_successors = successors
            .into_iter()
            .filter_map(|(p, q)| q.map(|q| (p, q)));

        unique_successors
            .filter(|(_p, q)| {
                predecessors
                    .get(q)
                    .map(|predecessor| predecessor.is_some())
                    .unwrap_or(false)
            })
            .collect()
    }

    fn simplify_chain(&mut self, chain: Vec<Point>) {
        let first = chain[0];
        let rest = &chain[1..];
        let mut current = first;

        for successor in rest {
            if self.is_edge_collapsible(current, *successor) {
                self.collapse_edge(current, *successor);
            } else {
                current = *successor;
            }
        }
    }

    fn is_edge_collapsible(&self, first: Point, second: Point) -> bool {
        self.live_regions_at(first) == self.live_regions_at(second)
            && self.killed_loans_at(first).is_empty()
            && self.killed_loans_at(second).is_empty()
            && self.outlives_at(first).is_empty()
            && self.outlives_at(second).is_empty()
            && self.invalidates_at(first).is_empty()
            && self.invalidates_at(second).is_empty()
    }

    fn live_regions_at(&self, point: Point) -> Vec<&Region> {
        self.region_live_at
            .get(&point)
            .map(|live_regions| live_regions.iter().collect())
            .unwrap_or_else(|| Vec::new())
    }

    fn killed_loans_at(&self, point: Point) -> Vec<&Loan> {
        self.killed
            .get(&point)
            .map(|killed| killed.iter().collect())
            .unwrap_or_else(|| Vec::new())
    }

    fn outlives_at(&self, point: Point) -> Vec<&(Region, Region)> {
        self.outlives
            .get(&point)
            .map(|outlives| outlives.iter().collect())
            .unwrap_or_else(|| Vec::new())
    }

    fn invalidates_at(&self, point: Point) -> Vec<&Loan> {
        self.invalidates
            .get(&point)
            .map(|invalidates| invalidates.iter().collect())
            .unwrap_or_else(|| Vec::new())
    }

    fn collapse_edge(&mut self, first: Point, second: Point) {
        if !self.is_endpoint(second) {
            self.collapse_edge_keeping_first_point(first, second);
        } else if !self.is_startpoint(first) {
            self.collapse_edge_keeping_second_point(first, second);
        }
    }

    fn is_endpoint(&self, queried_point: Point) -> bool {
        self.cfg_edge.iter().all(|&(p, _q)| p != queried_point)
    }

    fn is_startpoint(&self, queried_point: Point) -> bool {
        self.cfg_edge.iter().all(|&(_p, q)| q != queried_point)
    }

    fn collapse_edge_keeping_first_point(&mut self, first: Point, second: Point) {
        self.borrow_region.remove(&second);
        self.killed.remove(&second);
        self.outlives.remove(&second);
        self.region_live_at.remove(&second);
        self.invalidates.remove(&second);

        self.cfg_edge.retain(|(_p, q)| *q != second);

        for (p, _q) in &mut self.cfg_edge {
            if *p == second {
                *p = first;
            }
        }
    }

    fn collapse_edge_keeping_second_point(&mut self, first: Point, second: Point) {
        self.borrow_region.remove(&first);
        self.killed.remove(&first);
        self.outlives.remove(&first);
        self.region_live_at.remove(&first);
        self.invalidates.remove(&first);

        self.cfg_edge.retain(|(p, _q)| *p != first);

        for (_p, q) in &mut self.cfg_edge {
            if *q == first {
                *q = second;
            }
        }
    }
}

impl<R: Atom, L: Atom, P: Atom> Default for AllFacts<R, L, P> {
    fn default() -> Self {
        AllFacts {
            borrow_region: HashMap::default(),
            universal_region: Vec::default(),
            cfg_edge: Vec::default(),
            killed: HashMap::default(),
            outlives: HashMap::default(),
            region_live_at: HashMap::default(),
            invalidates: HashMap::default(),
        }
    }
}

pub trait Atom: From<usize> + Into<usize> + Copy + Clone + Eq + Ord + Hash + 'static {
    fn index(self) -> usize;
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Atom for usize {
        fn index(self) -> usize {
            self
        }
    }

    #[test]
    fn short_chain() {
        assert_reduction(vec![(0, 1), (1, 2)], vec![(0, 2)]);
    }

    #[test]
    fn long_chain() {
        assert_reduction(
            vec![(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6)],
            vec![(0, 6)],
        );
    }

    #[test]
    fn two_chains() {
        assert_reduction(
            vec![(0, 1), (1, 2), (2, 3), (4, 5), (5, 6)],
            vec![(0, 3), (4, 6)],
        );
    }

    #[test]
    fn chain_with_fork() {
        assert_reduction(
            vec![(0, 1), (1, 2), (2, 3), (3, 4), (2, 5), (5, 6)],
            vec![(0, 4), (0, 6)],
        );
    }

    #[test]
    fn chain_with_loop() {
        assert_reduction(
            vec![
                (0, 1),
                (1, 2),
                (2, 3),
                (3, 4),
                (4, 5),
                (5, 6),
                (6, 7),
                (7, 8),
                (8, 9),
                (3, 10),
                (10, 11),
                (11, 8),
            ],
            vec![(0, 4), (4, 9), (0, 10), (10, 9)],
        );
    }

    fn assert_reduction(original: Vec<(usize, usize)>, reduced: Vec<(usize, usize)>) {
        let mut facts = <AllFacts<usize, usize, usize>>::default();

        facts.cfg_edge.extend(original);
        facts.simplify_cfg();

        assert_eq!(facts.cfg_edge, reduced);
    }
}
