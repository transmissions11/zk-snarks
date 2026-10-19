// Behaviour for the web version of the document (HTML export). Inlined by `page` in web.typ.
(() => {
  const body = document.body;

  // Contents drawer on narrower screens.
  const toggle = document.querySelector(".toc-toggle");
  if (toggle) toggle.addEventListener("click", () => body.classList.toggle("toc-open"));
  document.querySelectorAll(".toc a").forEach(a => a.addEventListener("click", () => body.classList.remove("toc-open")));
  document.addEventListener("click", e => {
    if (body.classList.contains("toc-open") && !e.target.closest(".toc, .toc-toggle")) body.classList.remove("toc-open");
  });

  // Without a margin column, tapping a sidenote's number opens it inline.
  document.querySelectorAll(".sn-wrap > .sn-ref").forEach(ref => {
    ref.addEventListener("click", () => ref.nextElementSibling.classList.toggle("open"));
  });

  // Margin column, laid out the way marginalia does it in the PDF. Each sidenote's first line sits
  // level with the line it's attached to and each figure caption with its figure, unless that
  // would overlap the item above, in which case it moves down. A wide figure's caption goes just
  // above the figure, and if the notes before it don't fit in the space left, they shift up (or,
  // failing that, move below the figure). Without a margin column (narrow screens) CSS shows them
  // inline instead and none of this applies.
  const article = document.querySelector("article");
  const narrow = matchMedia("(max-width: 1000px)");
  // Between margin items: marginalia's 12pt clearance (20px here), less the space CSS puts above
  // the first and below the last line of a note, which Typst doesn't count.
  const gap = 13;
  const pageY = el => el.getBoundingClientRect().top + scrollY;
  const baseline = (el, atStart) => {
    const probe = document.createElement("span");
    probe.style.cssText = "display:inline-block;width:0;height:0";
    atStart ? el.prepend(probe) : el.before(probe);
    const y = probe.getBoundingClientRect().bottom + scrollY;
    probe.remove();
    return y;
  };
  const layoutMargin = () => {
    const items = [...article.querySelectorAll(".sidenote, figcaption")];
    items.forEach(el => (el.style.top = el.style.left = ""));
    if (narrow.matches) return;
    const left = article.getBoundingClientRect().right + parseFloat(getComputedStyle(article).getPropertyValue("--gap"));
    const wides = [...article.querySelectorAll(".wide")].map(el => ({ el, top: pageY(el), bottom: pageY(el) + el.offsetHeight }));
    // Where each item would like to be (measured before anything moves).
    const entries = items.map(el => {
      const h = el.offsetHeight, wide = el.closest(".wide");
      if (el.tagName === "FIGCAPTION" && wide) {
        const w = wides.find(w => w.el === wide);
        return { el, h, want: w.top - gap - h, pinnedAbove: w };
      }
      let want = pageY(el);
      if (el.classList.contains("sidenote") && !el.classList.contains("marginnote")) {
        want += baseline(el.parentElement, false) - baseline(el, true); // Line up the baselines.
      }
      return { el, h, want };
    });
    // Split the column into stretches between wide figures, and lay each out top to bottom.
    const stretches = wides.map(() => []).concat([[]]);
    for (const e of entries) {
      const i = e.pinnedAbove ? wides.indexOf(e.pinnedAbove) : wides.filter(w => w.top <= e.want).length;
      stretches[i].push(e);
    }
    stretches.forEach((stretch, i) => {
      const start = i > 0 ? wides[i - 1].bottom + gap : -Infinity;
      const end = i < wides.length ? wides[i].top - gap : Infinity;
      while (true) {
        let y = start;
        for (const e of stretch) { e.top = Math.max(e.want, y); y = e.top + e.h + gap; }
        let limit = end; // Shift up from the bottom until everything clears the wide figure.
        for (let k = stretch.length - 1; k >= 0 && stretch[k].top + stretch[k].h > limit; k--) {
          stretch[k].top = limit - stretch[k].h;
          limit = stretch[k].top - gap;
        }
        if (!stretch.length || stretch[0].top >= start) break;
        // Not enough room above the figure: the last note goes below it instead.
        const k = stretch.findLastIndex(e => !e.pinnedAbove);
        if (k < 0) break;
        const [moved] = stretch.splice(k, 1);
        moved.want = wides[i].bottom + gap;
        stretches[i + 1].unshift(moved);
      }
    });
    // Positions are relative to each item's containing block (usually the article).
    for (const e of entries) {
      const cb = e.el.offsetParent.getBoundingClientRect();
      e.el.style.top = `${e.top - scrollY - cb.top - e.el.offsetParent.clientTop}px`;
      e.el.style.left = `${left - cb.left - e.el.offsetParent.clientLeft}px`;
    }
  };
  let pending = 0;
  const relayout = () => { cancelAnimationFrame(pending); pending = requestAnimationFrame(layoutMargin); };
  // Lay out once the fonts are in (they change line heights), then show the column, already in
  // place. Don't wait more than a few seconds for slow fonts.
  const reveal = () => { layoutMargin(); body.classList.remove("margin-pending"); };
  Promise.race([document.fonts.ready, new Promise(r => setTimeout(r, 3000))]).then(reveal);
  addEventListener("resize", relayout);
  addEventListener("load", relayout);

  // The top bar only shows once the title block has scrolled away. The page starts with it hidden;
  // correct that straight away if we load part-way down (e.g. a link to a section).
  const titleblock = document.querySelector(".titleblock");
  const setAtTop = visible => body.classList.toggle("at-top", visible);
  setAtTop(titleblock.getBoundingClientRect().bottom > 0);
  new IntersectionObserver(([e]) => setAtTop(e.isIntersecting)).observe(titleblock);

  // Reading progress in the top bar, and the current section highlighted in the contents.
  const topbar = document.querySelector(".topbar");
  const links = new Map([...document.querySelectorAll(".toc a")].map(a => [a.getAttribute("href").slice(1), a]));
  const headings = [...document.querySelectorAll("article h2[id], article h3[id]")].filter(h => links.has(h.id));
  let active = null;
  // Scroll the contents just enough to show the current section with some room around it
  // (scrollIntoView would put it flush against the edge, hiding the title and padding).
  const toc = document.querySelector(".toc");
  const allLinks = [...links.values()];
  const keepInView = link => {
    if (link === allLinks[0]) return (toc.scrollTop = 0);
    if (link === allLinks[allLinks.length - 1]) return (toc.scrollTop = toc.scrollHeight);
    const room = 64, l = link.getBoundingClientRect(), t = toc.getBoundingClientRect();
    if (l.top < t.top + room) toc.scrollTop -= t.top + room - l.top;
    else if (l.bottom > t.bottom - room) toc.scrollTop += l.bottom - (t.bottom - room);
  };
  const update = () => {
    const max = document.documentElement.scrollHeight - innerHeight;
    topbar.style.setProperty("--progress", max > 0 ? Math.min(1, scrollY / max) : 0);
    let current = null;
    for (const h of headings) {
      if (h.getBoundingClientRect().top < innerHeight * 0.3) current = h; else break;
    }
    const link = current && links.get(current.id);
    if (link !== active) {
      if (active) active.classList.remove("active");
      if (link) {
        link.classList.add("active");
        keepInView(link);
      }
      active = link;
    }
  };
  addEventListener("scroll", update, { passive: true });
  addEventListener("resize", update);
  update();

  // Hovering a link to a theorem (or definition, ...), equation or figure previews it in a popup
  // (and a link to a section shows the section's title):
  // a copy of the real thing, minus any proof (the statement is what you want at a glance),
  // sidenotes and equation numbers (the link already says which one it is). The popup stays open while the mouse moves into it. Only for mice; on touch
  // screens links just jump.
  if (matchMedia("(hover: hover)").matches) {
    const popup = document.createElement("div");
    popup.className = "ref-popup";
    popup.setAttribute("role", "tooltip");
    document.body.append(popup);
    let showTimer = 0, hideTimer = 0, current = null;
    const preview = target => {
      const copy = target.cloneNode(true);
      copy.querySelectorAll(".thm-proof, .sn-wrap, .eqnum").forEach(el => el.remove());
      // A theorem stated entirely in its title has nothing left in its body.
      copy.querySelectorAll(".thm-body").forEach(el => {
        if (!el.textContent.trim() && !el.querySelector("svg, img")) el.remove();
      });
      copy.querySelectorAll("[id]").forEach(el => el.removeAttribute("id"));
      copy.removeAttribute("id");
      copy.querySelectorAll("[style]").forEach(el => { if (el.matches("figcaption")) el.removeAttribute("style"); });
      return copy;
    };
    const show = link => {
      const target = document.getElementById(link.getAttribute("href").slice(1));
      if (!target) return;
      popup.replaceChildren(preview(target));
      popup.classList.toggle("is-box", target.matches(".thm")); // A box is its own card.
      popup.classList.toggle("is-eqn", target.matches(".eqn")); // Just the equation, snugly.
      popup.classList.toggle("is-heading", target.matches("h2, h3, h4, h5")); // Likewise a title.
      popup.classList.add("open");
      // Below the link if it fits, otherwise above; kept inside the window.
      const r = link.getBoundingClientRect(), p = popup.getBoundingClientRect(), pad = 12;
      const below = r.bottom + 8 + p.height <= innerHeight - pad || r.top - 8 - p.height < pad;
      popup.style.top = `${below ? r.bottom + 8 : r.top - 8 - p.height}px`;
      popup.style.left = `${Math.max(pad, Math.min(r.left, innerWidth - pad - p.width))}px`;
      current = link;
    };
    const hide = () => { popup.classList.remove("open"); current = null; };
    const isPreviewable = link => {
      const target = document.getElementById(link.getAttribute("href").slice(1));
      return target && target.matches(".thm, .eqn, figure, h2, h3, h4, h5");
    };
    article.addEventListener("mouseover", e => {
      const link = e.target.closest('a[href^="#"]');
      if (!link || !isPreviewable(link)) return;
      clearTimeout(hideTimer);
      if (link === current) return;
      clearTimeout(showTimer);
      showTimer = setTimeout(() => show(link), 150);
    });
    article.addEventListener("mouseout", e => {
      const link = e.target.closest('a[href^="#"]');
      if (!link || link.contains(e.relatedTarget)) return;
      clearTimeout(showTimer);
      hideTimer = setTimeout(hide, 200);
    });
    popup.addEventListener("mouseenter", () => clearTimeout(hideTimer));
    popup.addEventListener("mouseleave", () => { hideTimer = setTimeout(hide, 200); });
    addEventListener("scroll", hide, { passive: true });
  }
})();
