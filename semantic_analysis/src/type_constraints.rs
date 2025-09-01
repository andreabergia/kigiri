use crate::semantic_analyzer::SemanticAnalysisError;
use crate::Type;
use kigiri_memory::{resolve_string_id, StringId};
use std::collections::{HashMap, HashSet};

enum Constraint {
    TypeEqual {
        symbol: StringId,
        required_type: Type,
    },
    TypeSameAs {
        symbol: StringId,
        other: StringId,
    },
}

pub type SymbolToType = HashMap<StringId, Type>;

struct ConstraintSolver {
    to_assign: HashSet<StringId>,
    assigned: SymbolToType,
}

impl ConstraintSolver {
    fn new(symbol_universe: &[StringId]) -> Self {
        Self {
            to_assign: symbol_universe.iter().copied().collect(),
            assigned: HashMap::new(),
        }
    }

    fn solve(
        &mut self,
        constraints: Vec<Constraint>,
    ) -> Result<SymbolToType, SemanticAnalysisError> {
        let mut current = constraints;
        while !current.is_empty() {
            current = self.iteration(&current)?;
        }

        let unresolved = self.to_assign.iter().next();
        if let Some(unresolved) = unresolved {
            Err(SemanticAnalysisError::UnableToInferTypeOfSymbol {
                symbol: Self::name(*unresolved)?,
            })
        } else {
            Ok(std::mem::take(&mut self.assigned))
        }
    }

    fn iteration(
        &mut self,
        constraints: &[Constraint],
    ) -> Result<Vec<Constraint>, SemanticAnalysisError> {
        let mut new_constraints = Vec::new();

        for constraint in constraints {
            match constraint {
                Constraint::TypeEqual {
                    symbol,
                    required_type,
                } => self.assign_type(symbol, required_type)?,
                Constraint::TypeSameAs { symbol, other } => {
                    if let Some(type_1) = self.assigned.get(symbol).cloned() {
                        self.assign_type(other, &type_1)?;
                    } else if let Some(type_2) = self.assigned.get(other).cloned() {
                        self.assign_type(symbol, &type_2)?;
                    } else {
                        // Leave it for next iteration
                        new_constraints.push(Constraint::TypeSameAs {
                            symbol: *symbol,
                            other: *other,
                        })
                    }
                }
            }
        }

        Ok(new_constraints)
    }

    fn assign_type(
        &mut self,
        symbol: &StringId,
        required_type: &Type,
    ) -> Result<(), SemanticAnalysisError> {
        match self.assigned.get(symbol) {
            None => {
                self.assigned.insert(*symbol, *required_type);
                let removed = self.to_assign.remove(symbol);
                if !removed {
                    return Err(SemanticAnalysisError::InternalError {
                        message: format!(
                            "symbol \"{}\" was not present in to_assign set",
                            Self::name(*symbol)?
                        ),
                    });
                }
            }
            Some(previously_assigned_type) => {
                if previously_assigned_type != required_type {
                    return Err(SemanticAnalysisError::ConflictingTypeRequirements {
                        symbol: Self::name(*symbol)?,
                        first_type: previously_assigned_type.to_string(),
                        second_type: required_type.to_string(),
                    });
                }
            }
        }
        Ok(())
    }

    fn name(string_id: StringId) -> Result<String, SemanticAnalysisError> {
        resolve_string_id(string_id)
            .map(|s| s.to_string())
            .ok_or_else(|| SemanticAnalysisError::InternalError {
                message: format!("failed to resolve symbol name for {:?}", string_id),
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use kigiri_memory::intern_string;

    #[test]
    fn valid_simple() {
        let symbol_a = intern_string("a");

        let constraint = vec![Constraint::TypeEqual {
            symbol: symbol_a,
            required_type: Type::I32,
        }];
        let mut solver = ConstraintSolver::new(&[symbol_a]);
        let result = solver.solve(constraint).unwrap();

        assert_eq!(result.len(), 1);
        assert_eq!(result.get(&symbol_a), Some(&Type::I32));
    }

    #[test]
    fn can_propagate_types() {
        let symbol_a = intern_string("a");
        let symbol_b = intern_string("b");

        let constraint = vec![
            Constraint::TypeSameAs {
                symbol: symbol_a,
                other: symbol_b,
            },
            Constraint::TypeEqual {
                symbol: symbol_a,
                required_type: Type::U64,
            },
        ];

        let mut solver = ConstraintSolver::new(&[symbol_a, symbol_b]);
        let result = solver.solve(constraint).unwrap();

        assert_eq!(result.len(), 2);
        assert_eq!(result.get(&symbol_a), Some(&Type::U64));
        assert_eq!(result.get(&symbol_a), Some(&Type::U64));
    }

    #[test]
    fn incoherent_simple() {
        let symbol_a = intern_string("a");

        let constraint = vec![
            Constraint::TypeEqual {
                symbol: symbol_a,
                required_type: Type::U64,
            },
            Constraint::TypeEqual {
                symbol: symbol_a,
                required_type: Type::I32,
            },
        ];

        let mut solver = ConstraintSolver::new(&[symbol_a]);
        let result = solver.solve(constraint).expect_err("should be invalid");

        assert_eq!(
            result.to_string(),
            "conflicting type requirements for symbol \"a\": first type u64, second type i32"
        );
    }

    #[test]
    fn incoherent_after_propagation() {
        let symbol_a = intern_string("a");
        let symbol_b = intern_string("b");
        let symbol_c = intern_string("c");

        let constraint = vec![
            Constraint::TypeSameAs {
                symbol: symbol_a,
                other: symbol_b,
            },
            Constraint::TypeSameAs {
                symbol: symbol_b,
                other: symbol_c,
            },
            Constraint::TypeEqual {
                symbol: symbol_a,
                required_type: Type::U64,
            },
            Constraint::TypeEqual {
                symbol: symbol_c,
                required_type: Type::I32,
            },
        ];

        let mut solver = ConstraintSolver::new(&[symbol_a, symbol_b, symbol_c]);
        let result = solver.solve(constraint).expect_err("should be invalid");

        assert_eq!(
            result.to_string(),
            "conflicting type requirements for symbol \"c\": first type i32, second type u64"
        );
    }

    #[test]
    fn constraint_for_symbol_not_marked_to_assign() {
        let symbol_a = intern_string("a");

        let constraint = vec![Constraint::TypeEqual {
            symbol: symbol_a,
            required_type: Type::U64,
        }];

        let mut solver = ConstraintSolver::new(&[]);
        let result = solver.solve(constraint).expect_err("should be invalid");

        assert_eq!(
            result.to_string(),
            "internal error: symbol \"a\" was not present in to_assign set"
        );
    }

    #[test]
    fn symbol_type_unsolvable() {
        let symbol_a = intern_string("a");
        let symbol_b = intern_string("b");

        let constraint = vec![Constraint::TypeEqual {
            symbol: symbol_a,
            required_type: Type::U64,
        }];

        let mut solver = ConstraintSolver::new(&[symbol_a, symbol_b]);
        let result = solver.solve(constraint).expect_err("should be invalid");

        assert_eq!(result.to_string(), "unable to infer type for symbol \"b\"");
    }
}
