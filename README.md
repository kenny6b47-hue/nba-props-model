# NBA props model

`props.py` projects NBA player stat lines, compares them with sportsbook prop lines from The Odds API, and ranks bets by expected value.

- **Hosted:** the `Update props` workflow runs daily (and on demand from the Actions tab) and publishes the dashboard to GitHub Pages. It needs a repository secret named `ODDS_API_KEY`.
- **Local:** `ODDS_API_KEY=... python3 props.py`, then open http://localhost:8000. `--demo` uses made-up data.

Each run costs 5 Odds API credits per game on the slate. The model does not see injury news and has not been backtested.
