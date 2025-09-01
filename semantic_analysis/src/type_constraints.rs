use crate::Type;
use crate::semantic_analyzer::SemanticAnalysisError;
use kigiri_memory::{StringId, resolve_string_id};
use std::collections::HashMap;

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
    assigned_symbols: SymbolToType,
}

impl ConstraintSolver {
    fn new() -> Self {
        Self {
            assigned_symbols: HashMap::new(),
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

        // TODO: check all symbols got assigned

        Ok(std::mem::take(&mut self.assigned_symbols))
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
                    if let Some(type_1) = self.assigned_symbols.get(symbol).cloned() {
                        self.assign_type(other, &type_1)?;
                    } else if let Some(type_2) = self.assigned_symbols.get(other).cloned() {
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
        match self.assigned_symbols.get(symbol) {
            None => {
                self.assigned_symbols.insert(*symbol, *required_type);
            }
            Some(previously_assigned_type) => {
                if previously_assigned_type != required_type {
                    let symbol_name =
                        resolve_string_id(*symbol).ok_or(SemanticAnalysisError::InternalError {
                            message: "failed to resolve symbol name".to_string(),
                        })?;

                    return Err(SemanticAnalysisError::ConflictingTypeRequirements {
                        symbol: symbol_name.to_string(),
                        first_type: previously_assigned_type.to_string(),
                        second_type: required_type.to_string(),
                    });
                }
            }
        }
        Ok(())
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
        let mut solver = ConstraintSolver::new();
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

        let mut solver = ConstraintSolver::new();
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

        let mut solver = ConstraintSolver::new();
        let result = solver.solve(constraint).expect_err("should be invalid");

        assert_eq!(
            result.to_string(),
            "conflicting type requirements for symbol \"a\": first type u64, second type i32"
        )
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

        let mut solver = ConstraintSolver::new();
        let result = solver.solve(constraint).expect_err("should be invalid");

        assert_eq!(
            result.to_string(),
            "conflicting type requirements for symbol \"c\": first type i32, second type u64"
        )
    }
}
