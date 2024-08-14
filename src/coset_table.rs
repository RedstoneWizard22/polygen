use std::{collections::VecDeque, rc::Rc};

/**
 * An implementation of the Todd-Coxeter algorithm using the HLT (Hasselgrove, Leech
 * and Trotter) strategy.
 *
 * @param generators - Generators of the group G (e.g. "abc") (inverses can be omitted)
 * @param relations - Relations between the generators
 *   (e.g. ["aa", "bbb", "ababab"] means a^2 = b^3 = (ab)^3 = I)
 * @param subgroup - Generators of stabilizing subgroup H (e.g. ["a", "c"])
 * @param isCoxeter - If true the generators are self-inverse (i.e. A = a^-1)
 *
 * this code was originally based on the implementation linked below:
 * https://github.com/neozhaoliang/pywonderland/blob/master/src/polytopes/polytopes/todd_coxeter.py
 */
pub struct CosetTable {
    /// number of generators (including inverses)
    gen_count: usize,
    /// true if the generators are self-inverse
    is_coxeter: bool,
    /// generator relations represented as integer arrays
    /// odd integers are inverses
    /// the inverse of 0 is 1, inverse of 2 is 3, inverse of 4 is 5 etc...
    /// e.g. a^2 = b^3 = (ab)^3 = I
    /// is represented as [[0, 0], [2, 2, 2], [0, 2, 0, 2, 0, 2]]
    relations: Rc<Vec<Vec<usize>>>,
    /// generators of stabilising subgroup H represented as integer arrays
    /// (same format as relations)
    subgens: Rc<Vec<Vec<usize>>>,

    /// holds the equivalence classes of the cosets. equivalence[i] = j means that
    /// coset i is equivalent to j. If equivalence[i] = i then coset i is "alive",
    /// otherwise it is considered "dead". note equivalence[i] <= i always holds.
    equivalence: Vec<usize>,
    /// queue holding "dead" cosets for processing. this is needed as when handling
    /// a coincidence, more coincidences may be discovered.
    dead_queue: VecDeque<usize>,
    /// the coset table itself :D
    table: Vec<Vec<Option<usize>>>,
    /// true if the coset table is solved
    is_solved: bool,
}

impl CosetTable {
    /// gen_count: total number of generators
    /// is_coxeter: set to true if generators are self-inverse
    /// relations: generator relations represented as integer arrays
    ///     odd integers are inverses
    ///     the inverse of 0 is 1, inverse of 2 is 3, inverse of 4 is 5 etc...
    ///     e.g. a^2 = b^3 = (ab)^3 = I
    ///     is represented as [[0, 0], [2, 2, 2], [0, 2, 0, 2, 0, 2]]
    /// subgens: generators of stabilising subgroup H represented as integer arrays
    ///     (same format as relations)
    pub fn new(
        gen_count: usize,
        is_coxeter: bool,
        relations: Vec<Vec<usize>>,
        subgens: Vec<Vec<usize>>,
    ) -> Self {
        for relation in relations.iter() {
            for generator in relation {
                if generator > &gen_count {
                    todo!("error handling");
                }
            }
        }

        for subgen in subgens.iter() {
            for generator in subgen {
                if generator > &gen_count {
                    todo!("error handling");
                }
            }
        }

        // TODO: checks
        Self {
            gen_count,
            is_coxeter,
            relations: Rc::new(relations),
            subgens: Rc::new(subgens),
            equivalence: Vec::new(),
            dead_queue: VecDeque::new(),
            table: vec![vec![None; gen_count]],
            is_solved: false,
        }
    }

    /// returns the inverse of a generator
    fn inv(&self, gen: usize) -> usize {
        if self.is_coxeter {
            gen
        } else {
            gen ^ 1
        }
    }

    /// mark that coset_a · gen = coset_b
    fn deduce(&mut self, coset_a: usize, coset_b: usize, gen: usize) {
        let g_inv = self.inv(gen);
        self.table[coset_a][gen] = Some(coset_b);
        self.table[coset_b][g_inv] = Some(coset_b);
    }

    /// create a new coset for which coset · gen = the new coset
    fn define(&mut self, coset: usize, gen: usize) {
        let n = self.table.len();
        self.table.push(vec![None; self.gen_count]);
        self.deduce(coset, n, gen);
        self.equivalence.push(n);
    }

    /// returns true if a coset is alive
    #[inline]
    fn is_alive(&self, coset: usize) -> bool {
        self.equivalence[coset] == coset
    }

    /// returns the smallest (index wise) coset that is equivalent to `coset`.
    /// this method will also compress the equivalence chain as an optimisation
    fn rep(&mut self, coset: usize) -> usize {
        let mut equivalent = coset;
        while coset != self.equivalence[equivalent] {
            equivalent = self.equivalence[equivalent];
        }

        // path compression
        // e.g. if coset is 6, and equivalence is [0, 0, 2, 3, 1, 5, 4]
        // r would be 0 and equivalcence is compressed to [0, 0, 2, 3, 0, 5, 0]
        let mut c = coset;
        while c != equivalent {
            let tmp = self.equivalence[c];
            self.equivalence[c as usize] = equivalent;
            c = tmp;
        }

        equivalent
    }

    /// given two equivalent cosets, declare the larger one to be dead and add
    /// it to the dead queue
    fn merge(&mut self, coset_a: usize, coset_b: usize) {
        let a = self.rep(coset_a);
        let b = self.rep(coset_b);
        if a != b {
            // Remember equivalence[i] <= i must hold
            let min = a.min(b);
            let max = a.max(b);
            self.equivalence[max] = min;
            self.dead_queue.push_back(max);
        }
    }

    /// process the coincidence that coset_a and coset_b are equivalent
    fn coincidence(&mut self, coset_a: usize, coset_b: usize) {
        self.merge(coset_a, coset_b);

        // process all dead cosets
        // the queue holds only one coset at this point, but more may be added
        while let Some(dead) = self.dead_queue.pop_front() {
            // for each coset `next` this dead one connects to
            for g in 0..self.gen_count {
                if let Some(next) = self.table[dead][g] {
                    let g_inv = self.inv(g);
                    // delete `next`'s reference to the dead coset
                    self.table[next][g_inv] = None;

                    // copy the existing information to the representative of the dead coset
                    // but watch out for new coincidences. next may be dead already, so
                    // we need to watch out for that too
                    let dead_rep = self.rep(dead);
                    let next_rep = self.rep(next);

                    let dead_existing = self.table[next_rep][g_inv];
                    let next_existing = self.table[dead_rep][g];

                    if next_existing.is_some_and(|v| v != next_rep) {
                        // we have a coincidence
                        self.merge(next_rep, next_existing.unwrap());
                    } else if dead_existing.is_some_and(|v| v != dead_rep) {
                        // we have a coincidence
                        self.merge(dead_rep, dead_existing.unwrap());
                    } else {
                        // No coincidence, so we can just copy the information
                        self.deduce(dead_rep, next_rep, g)
                    }
                }
            }
        }
    }

    /// scan the row of a coset under a given word, defining cosets as needed
    fn scan_and_fill(&mut self, coset: usize, word: &[usize]) {
        let mut lv = coset; // left value
        let mut rv = coset; // right value
        let mut lp = 0; // left position
        let mut rp = word.len() - 1; // right position

        let mut iter = 0;
        while iter < word.len() {
            iter += 1;

            // scan forwards as far as possible
            while lp <= rp && self.table[lv][word[lp]].is_some() {
                lv = self.table[lv][word[lp]].unwrap();
                lp += 1;
            }

            // scan backwards as far as possible
            // untill it meets the forward scan
            while rp >= lp && self.table[rv][self.inv(word[rp])].is_some() {
                rv = self.table[rv][self.inv(word[rp])].unwrap();
                rp -= 1;
            }

            // if rp and lp overlap, a coincidence has been found
            if rp < lp {
                self.coincidence(lv, rv);
                return;
            }

            // if they are about to meet, a deduction can be made
            if rp == lp {
                self.deduce(lv, rv, word[lp]);
                return;
            }

            // otherwise, define a new coset and continue scanning forwards
            self.define(lv, word[lp]);
        }

        panic!("over scanned, this should never happen");
    }

    /// run the HLT strategy with the provided iteration limit
    fn hlt(&mut self, max_iter: usize) {
        for subgen in self.subgens.clone().iter() {
            self.scan_and_fill(0, subgen);
        }

        let mut current = 0;
        let mut iter = 0;
        while current < self.table.len() && iter < max_iter {
            for relation in self.relations.clone().iter() {
                if !self.is_alive(current) {
                    break;
                }
                self.scan_and_fill(current, relation);
            }

            if self.is_alive(current) {
                for g in 0..self.gen_count {
                    if self.table[current][g].is_none() {
                        self.define(current, g);
                    }
                }
            }

            iter += 1;
            current += 1;
        }

        if iter > max_iter {
            todo!("Error handling: Iteration limit exceeded");
        }
    }

    /// delete all dead cosets in the table, renumbering the live ones
    fn compress(&mut self) {
        let mut ind = 0;
        for coset in 0..self.table.len() {
            if self.is_alive(coset) {
                if ind != coset {
                    for g in 0..self.gen_count {
                        if let Some(next) = self.table[coset][g] {
                            if next == coset {
                                self.table[ind][g] = Some(ind);
                            } else {
                                self.deduce(ind, next, g);
                            }
                        } else {
                            todo!("Error handling: Compress should not be called before the coset table is solved");
                        }
                    }
                }
                ind += 1; // make sure is at end
            }
        }

        self.equivalence = (0..ind + 1).collect();
        self.table.truncate(ind + 1);
    }

    /// solves the coset table
    pub fn solve(&mut self, max_iter: usize) {
        if !self.is_solved {
            self.hlt(max_iter);
            self.compress();
            self.is_solved = true;
        }
    }

    pub fn len(&self) -> usize {
        self.table.len()
    }
}
