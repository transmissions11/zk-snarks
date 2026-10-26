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

  // Sidenotes and captions sit in the middle of the text they annotate, so a selection dragged
  // through the text would take them in too. Unless it starts in one, web.css leaves them out.
  document.addEventListener("pointerdown", e => {
    body.classList.toggle("selecting-text", !e.target.closest(".sidenote, figcaption"));
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
  const percentRead = document.querySelector(".topbar-read"); // How far through the page, as the bar.
  const update = () => {
    const max = document.documentElement.scrollHeight - innerHeight;
    const progress = max > 0 ? Math.min(1, scrollY / max) : 0;
    topbar.style.setProperty("--progress", progress);
    percentRead.textContent = `${Math.round(progress * 100)}%`;
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

  // Selecting text in the document offers to ask Claude about it: type a question (or don't) and
  // a new chat opens in the reader's own account, starting with the passage quoted, the section
  // it's from and a link back to it. Equations are pictures with no text in them, so they're
  // quoted from the plain-text version web.typ hides beside each (.math-text). Links can't be very
  // long, so long passages are cut short.
  const ask = document.createElement("form");
  ask.className = "ask";
  // The button shows Claude's logo, from Simple Icons (simple-icons@15.22.0, icons/claude.svg).
  ask.innerHTML = '<textarea name="q" rows="1" placeholder="Ask Claude about this…" aria-label="Your question" enterkeyhint="send"></textarea>'
    + '<button type="submit" aria-label="Ask Claude" title="Ask Claude"><svg viewBox="0 0 24 24" aria-hidden="true"><path d="'
    + 'm4.7144 15.9555 4.7174-2.6471.079-.2307-.079-.1275h-.2307l-.7893-.0486-2.6956-.0729-2.3375-.0971-2.2646-.1214-.5707-.1215-.5343-.7042.0546-.3522.4797-.3218.686.0608 1.5179.1032 2.2767.1578 1.6514.0972 2.4468.255h.3886l.0546-.1579-.1336-.0971-.1032-.0972L6.973 9.8356l-2.55-1.6879-1.3356-.9714-.7225-.4918-.3643-.4614-.1578-1.0078.6557-.7225.8803.0607.2246.0607.8925.686 1.9064 1.4754 2.4893 1.8336.3643.3035.1457-.1032.0182-.0728-.164-.2733-1.3539-2.4467-1.445-2.4893-.6435-1.032-.17-.6194c-.0607-.255-.1032-.4674-.1032-.7285L6.287.1335 6.6997 0l.9957.1336.419.3642.6192 1.4147 1.0018 2.2282 1.5543 3.0296.4553.8985.2429.8318.091.255h.1579v-.1457l.1275-1.706.2368-2.0947.2307-2.6957.0789-.7589.3764-.9107.7468-.4918.5828.2793.4797.686-.0668.4433-.2853 1.8517-.5586 2.9021-.3643 1.9429h.2125l.2429-.2429.9835-1.3053 1.6514-2.0643.7286-.8196.85-.9046.5464-.4311h1.0321l.759 1.1293-.34 1.1657-1.0625 1.3478-.8804 1.1414-1.2628 1.7-.7893 1.36.0729.1093.1882-.0183 2.8535-.607 1.5421-.2794 1.8396-.3157.8318.3886.091.3946-.3278.8075-1.967.4857-2.3072.4614-3.4364.8136-.0425.0304.0486.0607 1.5482.1457.6618.0364h1.621l3.0175.2247.7892.522.4736.6376-.079.4857-1.2142.6193-1.6393-.3886-3.825-.9107-1.3113-.3279h-.1822v.1093l1.0929 1.0686 2.0035 1.8092 2.5075 2.3314.1275.5768-.3218.4554-.34-.0486-2.2039-1.6575-.85-.7468-1.9246-1.621h-.1275v.17l.4432.6496 2.3436 3.5214.1214 1.0807-.17.3521-.6071.2125-.6679-.1214-1.3721-1.9246L14.38 17.959l-1.1414-1.9428-.1397.079-.674 7.2552-.3156.3703-.7286.2793-.6071-.4614-.3218-.7468.3218-1.4753.3886-1.9246.3157-1.53.2853-1.9004.17-.6314-.0121-.0425-.1397.0182-1.4328 1.9672-2.1796 2.9446-1.7243 1.8456-.4128.164-.7164-.3704.0667-.6618.4008-.5889 2.386-3.0357 1.4389-1.882.929-1.0868-.0062-.1579h-.0546l-6.3385 4.1164-1.1293.1457-.4857-.4554.0608-.7467.2307-.2429 1.9064-1.3114Z"/></svg></button>';
  document.body.append(ask);
  const input = ask.elements.q;
  // The box grows to fit the question (scrolling once it's very long), and the popover moves to
  // stay clear of the passage. Enter sends it; Shift-Enter starts a new line.
  const fitInput = () => {
    input.style.height = "auto";
    input.style.height = `${input.scrollHeight}px`;
    if (selected) placeAsk();
  };
  input.addEventListener("input", fitInput);
  input.addEventListener("keydown", e => {
    if (e.key === "Enter" && !e.shiftKey && !e.isComposing) {
      e.preventDefault();
      ask.requestSubmit();
    }
  });
  // While the box is in use (pressed or typed in), the page's selection has gone, but the passage
  // it was asked about stays highlighted.
  let selected = null, pressedAsk = false;
  const asking = () => selected && (pressedAsk || ask.contains(document.activeElement));

  // Equations are pictures, which browsers don't highlight when they're selected, so mark the
  // ones in the selection for web.css to highlight.
  const pictures = [...article.querySelectorAll(".im, .eq-scroll")];
  let highlighted = [];
  const markPictures = range => {
    // Like their text, those in a sidenote or caption only count if the selection's inside it.
    const inSelection = el => {
      const note = el.closest(".sidenote, figcaption");
      return range.intersectsNode(el) && (!note || note.contains(range.commonAncestorContainer));
    };
    const now = range ? pictures.filter(inSelection) : [];
    highlighted.forEach(el => el.classList.remove("selected"));
    now.forEach(el => el.classList.add("selected"));
    highlighted = now;
  };
  const selectedRange = () => {
    const sel = getSelection();
    return sel.rangeCount && !sel.isCollapsed ? sel.getRangeAt(0) : null;
  };
  document.addEventListener("selectionchange", () => { if (!asking()) markPictures(selectedRange()); });

  const BLOCK = /^(P|LI|UL|OL|DIV|FIGURE|FIGCAPTION|H[1-6]|BLOCKQUOTE|TABLE|TR)$/;
  // The text of a range, with paragraphs and display equations on lines of their own. Sidenotes
  // are left out, as they sit in the middle of the sentence they annotate, unless it's in one.
  // An equation's own text comes before any notes beside it. Typst writes its line breaks as <br>s.
  const mathText = eq => [...eq.querySelector(".math-text").childNodes].map(n => (n.nodeName === "BR" ? "\n" : n.textContent)).join("");
  const plainText = range => {
    const root = range.commonAncestorContainer;
    // Inside an equation (but not a sidenote written beside one), it's the whole equation.
    const inside = (root.nodeType === Node.ELEMENT_NODE ? root : root.parentElement).closest(".im, .eq-scroll, .sidenote");
    if (inside?.matches(".im, .eq-scroll")) return mathText(inside);
    let out = "";
    const walk = node => {
      if (!range.intersectsNode(node)) return;
      if (node.nodeType === Node.TEXT_NODE) {
        const start = node === range.startContainer ? range.startOffset : 0;
        const end = node === range.endContainer ? range.endOffset : node.length;
        out += node.data.slice(start, end).replace(/\s+/g, " ");
        return;
      }
      if (node.nodeType !== Node.ELEMENT_NODE || node.matches(".sn-num")) return;
      if (node.matches(".sidenote, .sn-ref") && !node.contains(root)) return;
      const block = BLOCK.test(node.tagName) || node.matches(".eq-scroll");
      if (block) out += "\n";
      if (node.matches(".im, .eq-scroll")) out += mathText(node);
      else if (node.matches(".thm-head")) { // Shown as its name, then its kind (and number).
        const [name, kind] = [".thm-name", ".thm-kind"].map(c => {
          const range = document.createRange();
          range.selectNodeContents(node.querySelector(c));
          return plainText(range);
        });
        out += name ? `${kind} (${name})` : kind;
      }
      else node.childNodes.forEach(walk);
      if (block) out += "\n";
    };
    walk(root);
    return out.replace(/[​⁠]/g, "").split("\n").map(line => line.replace(/ +/g, " ").trim())
      .join("\n").replace(/\n{3,}/g, "\n\n").trim();
  };
  // Copying gives the same text, so equations come along instead of leaving gaps.
  document.addEventListener("copy", e => {
    const sel = getSelection();
    if (!sel.rangeCount || sel.isCollapsed || !article.contains(sel.getRangeAt(0).commonAncestorContainer)) return;
    e.clipboardData.setData("text/plain", plainText(sel.getRangeAt(0)));
    e.preventDefault();
  });
  const headingText = h => {
    const range = document.createRange(), num = h.querySelector(".secnum");
    range.selectNodeContents(h);
    if (num) range.setStartAfter(num);
    return (num ? num.textContent + " " : "") + plainText(range);
  };
  // The last heading at or before a node: the section it's in.
  const sectionOf = (node, withId) => {
    let found = null;
    for (const h of article.querySelectorAll(withId ? ":is(h2, h3, h4, h5)[id]" : "h2, h3, h4, h5")) {
      if (h.compareDocumentPosition(node) & Node.DOCUMENT_POSITION_FOLLOWING) found = h; else break;
    }
    return found;
  };
  const MAX_QUOTE = 1500; // Characters.
  const message = (range, question) => {
    let quote = plainText(range);
    // Too long, it's cut in the middle (between words), keeping how the passage starts and ends.
    if (quote.length > MAX_QUOTE) {
      const half = MAX_QUOTE / 2;
      quote = `${quote.slice(0, half).replace(/\s+\S*$/, "")} […] ${quote.slice(-half).replace(/^\S*\s+/, "")}`;
    }
    const section = sectionOf(range.startContainer), anchor = sectionOf(range.startContainer, true);
    // No link from a copy opened from disk, which nobody else can open.
    const link = /^https?:$/.test(location.protocol)
      ? ` (${location.origin}${location.pathname}${anchor ? "#" + anchor.id : ""})` : "";
    const where = section ? `In the section "${headingText(section)}", it says:` : "It says:";
    return `I'm reading "${document.title}"${link}. ${where}\n\n${quote.replace(/^/gm, "> ")}\n\n${question || "Can you help me understand this?"}`;
  };
  let pointerDown = false, pointerUpAt = 0, askTimer = 0;
  const hideAsk = () => {
    if (!selected) return;
    ask.classList.remove("open");
    selected = null;
    pressedAsk = false;
    if (ask.contains(document.activeElement)) document.activeElement.blur();
    if (window.CSS?.highlights) CSS.highlights.delete("ask");
    markPictures(selectedRange());
  };
  // Above the selection's first line, or below its last if there's no room or on touch screens
  // (where the system's own menu goes above). Kept in the window while it scrolls.
  const placeAsk = () => {
    const rects = [...selected.getClientRects()].filter(r => r.width || r.height);
    if (!rects.length) return hideAsk();
    // The selected part of a line is several boxes (text, equations), so centre on all of them.
    const line = r => {
      const on = rects.filter(s => s.top < r.bottom && s.bottom > r.top);
      return { top: r.top, bottom: r.bottom, mid: (Math.min(...on.map(s => s.left)) + Math.max(...on.map(s => s.right))) / 2 };
    };
    const first = line(rects[0]), last = line(rects[rects.length - 1]), a = ask.getBoundingClientRect(), pad = 8;
    const top = topbar.offsetHeight + pad;
    const above = matchMedia("(hover: hover)").matches && first.top - pad - a.height >= top;
    const y = above ? first.top - pad - a.height : last.bottom + pad;
    const x = (above ? first.mid : last.mid) - a.width / 2;
    ask.style.top = `${Math.max(top, Math.min(y, innerHeight - pad - a.height))}px`;
    ask.style.left = `${Math.max(pad, Math.min(x, innerWidth - pad - a.width))}px`;
  };
  const showAsk = () => {
    const range = selectedRange();
    if (!range || !article.contains(range.commonAncestorContainer) || !plainText(range)) return hideAsk();
    selected = range.cloneRange(); // The selection's own range changes as soon as it does.
    input.value = ""; // A new passage, so a new question.
    ask.classList.add("open");
    fitInput(); // Also places it.
  };
  const scheduleAsk = delay => { clearTimeout(askTimer); askTimer = setTimeout(showAsk, delay); };
  // Shown once a selection is finished: when the mouse is let go, or (as touch screens' selection
  // handles send no pointer events) when it's stopped changing for a moment.
  document.addEventListener("pointerdown", e => {
    pressedAsk = ask.contains(e.target);
    if (pressedAsk) return;
    pointerDown = true;
    clearTimeout(askTimer);
    hideAsk();
  });
  const pointerUp = () => {
    if (!pointerDown) return;
    pointerDown = false;
    pointerUpAt = performance.now();
    scheduleAsk(10);
  };
  document.addEventListener("pointerup", pointerUp);
  document.addEventListener("pointercancel", pointerUp);
  document.addEventListener("keyup", e => {
    if (e.key === "Escape") hideAsk();
    else if (!ask.contains(e.target)) scheduleAsk(10);
  });
  document.addEventListener("selectionchange", () => {
    if (asking()) return;
    if (getSelection().isCollapsed) { clearTimeout(askTimer); hideAsk(); }
    else if (!pointerDown && performance.now() - pointerUpAt > 100) scheduleAsk(400); // Not as the mouse is let go.
  });
  // Typing moves the selection into the box, so highlight the passage another way meanwhile. The
  // range runs through any sidenotes and captions in the text, which the selection left out (and
  // so does the quote), so it's highlighted in pieces around them.
  const passagePieces = range => {
    const root = range.commonAncestorContainer, pieces = [];
    let rest = range.cloneRange();
    for (const note of article.querySelectorAll(".sidenote, figcaption")) {
      if (!rest.intersectsNode(note) || note.contains(root)) continue;
      const before = rest.cloneRange();
      before.setEndBefore(note);
      pieces.push(before);
      rest.setStartAfter(note);
    }
    return [...pieces, rest].filter(r => !r.collapsed);
  };
  ask.addEventListener("focusin", () => {
    if (selected && window.Highlight) CSS.highlights.set("ask", new Highlight(...passagePieces(selected)));
  });
  ask.elements[1].addEventListener("mousedown", e => e.preventDefault()); // Keep the selection.
  ask.addEventListener("submit", e => {
    e.preventDefault();
    if (!selected) return;
    window.open("https://claude.ai/new?q=" + encodeURIComponent(message(selected, input.value.trim())), "_blank", "noopener");
    input.value = "";
    hideAsk();
  });
  const replaceAsk = () => { if (selected) placeAsk(); };
  addEventListener("scroll", replaceAsk, { passive: true });
  addEventListener("resize", replaceAsk);
})();
