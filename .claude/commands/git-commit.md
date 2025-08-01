# Git Commit Guidelines

Follow the project's git commit conventions from CLAUDE.md:

## Commit Message Format

- **Length**: Write succinct commit messages that fit in 80 characters, subject line only
- **Format**: Use conventional commit format: `type: description`
- **Body**: Only add a description body when warranted - try hard to avoid needing it
- **Focus**: Keep messages focused on what changed, not why (the code should explain why)
- **Footers**: Do not add "Generated with Claude Code" or "Co-Authored-By: Claude" footers

## Conventional Commit Types

- `feat:` - New feature
- `fix:` - Bug fix
- `docs:` - Documentation changes
- `refactor:` - Code refactoring
- `test:` - Adding or updating tests
- `chore:` - Maintenance tasks
- `style:` - Code style changes (formatting, etc.)
- `perf:` - Performance improvements
- `ai`: configuration of AI tools, such as Claude. Prefer to `docs` when relevant

## Examples

Good commit messages:
- `feat: add while loop support to parser`
- `fix: resolve type inference in nested blocks`
- `refactor: simplify IR builder logic`
- `test: add snapshot tests for expressions`

Avoid:
- Long messages over 80 characters
- Explaining why instead of what
- Adding Claude footers
- Unnecessary description bodies
