# ZK-SNARKs for Dummies

Needs [Typst](https://typst.app) (0.15+) and Python 3.

## PDF

```bash
typst compile main.typ
```

Writes `main.pdf`.

## Site

```bash
python3 web/build_site.py
```

Writes `web/site/index.html`. It's a static page: open it directly, or host the `web/site/` folder.
