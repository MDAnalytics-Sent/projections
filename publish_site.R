# Projections web page: builds the page on this Mac and puts it on GitHub Pages.
#
#   In RStudio:   source("~/Desktop/publish_site.R")
#
# That is the only step. The first run asks once for a GitHub token (a GitHub page opens
# with everything filled in), creates the repository, switches on GitHub Pages and sets the
# page to rebuild itself every 30 minutes while this Mac is awake. Run the same line any
# time for an immediate update. To stop the automatic updates: site_schedule_off()
#
# Everything is computed here, by the same Projections.R with the same caches and ledgers
# as the app, and published as a finished page: opening it computes nothing, so it loads in
# about a second, and with no server behind it there is no connection to drop.
#
#   Page:   https://dsentes24.github.io/projections/
#   Copy:   ~/Projections site     Log: ~/Library/Logs/projections-site.log

SITE <- list(
  user  = "dsentes24",
  repo  = "projections",
  home  = getOption("site.home", path.expand("~/Projections site")),
  state = path.expand("~/Library/Application Support/Projections"),
  log   = path.expand("~/Library/Logs/projections-site.log"),
  label = "com.projections.site"
)
site_owner <- function(login) {        # the GitHub account the page belongs to
  SITE$user   <<- login
  SITE$url    <<- sprintf("https://%s.github.io/%s/", tolower(login), SITE$repo)
  SITE$remote <<- getOption("site.remote", sprintf("https://github.com/%s/%s.git", login, SITE$repo))
}
site_owner(SITE$user)

# the folder holding Projections.R and its data: this script's own folder (the Desktop)
SITE$app <- local({
  d <- getOption("site.app_dir")
  if (is.null(d)) {
    here <- tryCatch(sys.frame(1)$ofile, error = function(e) NULL)
    d <- if (is.character(here) && length(here) == 1L) dirname(normalizePath(here)) else ""
  }
  if (!file.exists(file.path(d, "Projections.R"))) d <- path.expand("~/Desktop")
  d
})

site_log <- function(...) cat(format(Sys.time(), "%Y-%m-%d %H:%M:%S"), " ", ..., "\n", sep = "")

# ---- 1. compute: the app's own server, run without a browser ------------------------------
# Every day and week a visitor can pick is computed by the app's own server, opened with the
# inputs a visitor would have, and saved as a small file the page loads when it is picked.
# Days and weeks still in play (yesterday onward; last, this and next week) are redone every
# run; older ones are done once and kept, a few per run until the window is full.
SITE_FMT      <- 2L     # page format: changing it redoes every stored day and week
SITE_BACK     <- 14L    # days of MLB, NHL and NBA results kept
SITE_AHEAD    <- 3L     # days ahead
SITE_BACKFILL <- 10L     # older days or weeks added per league per run

site_dt_html <- function(id, j) {
  if (is.null(j)) return("")
  j <- gsub("</", "<\\/", as.character(j), fixed = TRUE)
  sprintf(paste0('<div id="%s" class="datatables html-widget html-fill-item" style="width:100%%;height:auto;"></div>',
                 '<script type="application/json" data-for="%s">%s</script>'), id, id, j)
}
# a section's HTML, with its own tables drawn where the app would draw them
site_fill <- function(h, dts) {
  if (is.null(h)) return("")
  h <- sub(" Try Run Forecast or select another date.", "", h, fixed = TRUE)   # the app's buttons are not here
  for (t in names(dts)) {
    m <- regexpr(sprintf('<div[^>]*\\bid="%s"[^>]*>\\s*</div>', t), h, perl = TRUE)
    if (m > 0) h <- paste0(substr(h, 1, m - 1), site_dt_html(t, dts[[t]]), substr(h, m + attr(m, "match.length"), nchar(h)))
  }
  h
}
site_frag <- function(pieces, data = NULL) {
  js <- if (is.null(data)) "" else sprintf('<script type="application/json" class="frag-data">%s</script>',
    gsub("</", "<\\/", as.character(jsonlite::toJSON(data, auto_unbox = TRUE, null = "null")), fixed = TRUE))
  paste0(paste(pieces, collapse = "\n"), js)
}
site_day_label <- function(days, today) {
  d <- as.Date(days)
  lab <- gsub("  +", " ", format(d, "%a %b %e"))
  ifelse(d == today, paste(lab, "\u00b7 today"), ifelse(d == today - 1, paste(lab, "\u00b7 yesterday"),
    ifelse(d == today + 1, paste(lab, "\u00b7 tomorrow"), lab)))
}

site_capture <- function(app, tz, out_dir) {
  today <- as.Date(format(Sys.time(), tz = tz))
  ver <- paste0(SITE_FMT, "-", unname(tools::md5sum(file.path(SITE$app, "Projections.R"))))
  dir.create(file.path(out_dir, "d"), recursive = TRUE, showWarnings = FALSE)
  M <- new.env()
  M$file <- file.path(out_dir, "d", "manifest.json")
  M$man <- tryCatch(jsonlite::fromJSON(M$file, simplifyVector = FALSE), error = function(e) list())
  R <- new.env(); R$states <- list(); R$inline <- list(); R$err <- list(); R$season <- list()
  R$today <- ""; R$today_date <- ""
  # The server moves its selectors (to this week, to the next game day) by asking the
  # browser to; here those requests are caught and applied as the browser would.
  moved <- new.env(); moved$v <- list()
  app$updateSelectInput <- function(session = NULL, inputId, label = NULL, choices = NULL, selected = NULL, ...) {
    if (!is.null(selected)) moved$v[[inputId]] <- as.character(selected); invisible()
  }
  app$updateDateInput <- function(session = NULL, inputId, label = NULL, value = NULL, ...) {
    if (!is.null(value)) moved$v[[inputId]] <- as.Date(value); invisible()
  }
  app$updateNavlistPanel <- function(...) invisible()
  app$updateQueryString <- function(...) invisible()

  shiny::testServer(app$server, {
    set <- function(...) {
      session$setInputs(...)
      for (k in 1:8) {
        v <- moved$v; moved$v <- list()
        if (!length(v)) break
        do.call(session$setInputs, v)
      }
    }
    out <- function(id) tryCatch(session$getOutput(id), error = function(e) {
      if (!inherits(e, "shiny.silent.error")) R$err[[id]] <- conditionMessage(e)
      NULL
    })
    ui <- function(id) { v <- out(id); if (is.null(v)) NULL else v$html }
    dts_of <- function(ids) { v <- lapply(ids, out); names(v) <- ids; Filter(Negate(is.null), v) }
    gids <- function(j) {             # each board row's game id (its hidden 8th column)
      if (is.null(j)) return(character(0))
      d <- tryCatch(jsonlite::fromJSON(j, simplifyVector = FALSE)$x$data, error = function(e) NULL)
      if (length(d) < 8L) character(0) else vapply(d[[8]], function(z) if (is.null(z)) NA_character_ else as.character(z), "")
    }

    # one league: each of its days or weeks built (or kept) and listed for the page's selector
    league <- function(lg, keys, labels, cur, live, render) {
      t0 <- Sys.time(); dir <- file.path(out_dir, "d", lg); dir.create(dir, recursive = TRUE, showWarnings = FALSE)
      shown <- character(0); added <- 0L; built <- 0L
      for (i in seq_along(keys)) {
        k <- keys[i]; id <- paste(lg, k, sep = "/"); f <- file.path(dir, paste0(k, ".html"))
        m <- M$man[[id]]; have <- file.exists(f) && !is.null(m)
        redo <- k %in% live || !(have && identical(m$ver, ver))
        # A day page built while that night's games were still being played was frozen
        # with no winners the moment it aged out of the live window. Rebuild any dated
        # page that was written before its own games could possibly have finished.
        if (!redo && have) {
          kd <- suppressWarnings(as.Date(k, format = "%Y-%m-%d"))
          if (!is.na(kd)) {
            settled <- as.POSIXct(paste(format(kd + 1L), "09:00"), tz = "America/New_York")
            built_at <- tryCatch(as.POSIXct(m$at, tz = "UTC"), error = function(e) NA)
            stale <- is.null(m$at) || is.na(built_at) ||
                     isTRUE(suppressWarnings(built_at < settled))
            if (stale) redo <- TRUE
          }
        }
        if (redo && !(k %in% live) && added >= SITE_BACKFILL) redo <- FALSE      # the next runs fill in the rest
        if (redo) {
          r <- tryCatch(render(k), error = function(e) { R$err[[id]] <- conditionMessage(e); NULL })
          if (!is.null(r)) {
            writeLines(enc2utf8(r$html), f, useBytes = TRUE)
            M$man[[id]] <- list(ver = ver, games = isTRUE(r$games),
                                at = format(Sys.time(), tz = "UTC", usetz = FALSE))
            m <- M$man[[id]]; have <- TRUE
            built <- built + 1L; if (!(k %in% live)) added <- added + 1L
          }
        }
        if (have && (isTRUE(m$games) || identical(k, cur))) shown <- c(shown, k)
      }
      gone <- setdiff(sub("[.]html$", "", list.files(dir, pattern = "[.]html$")), keys)   # left the window
      unlink(file.path(dir, paste0(gone, ".html")))
      for (g in gone) M$man[[paste(lg, g, sep = "/")]] <- NULL
      if (!cur %in% shown && length(shown)) cur <- shown[length(shown)]
      R$states[[lg]] <- list(keys = shown, labels = labels[match(shown, keys)], cur = cur)
      if (length(cur) && file.exists(file.path(dir, paste0(cur, ".html")))) {
        h <- readChar(file.path(dir, paste0(cur, ".html")), file.size(file.path(dir, paste0(cur, ".html"))), useBytes = TRUE)
        Encoding(h) <- "UTF-8"; R$inline[[lg]] <- h
      }
      site_log(sprintf("  %-5s %5.1fs  %d built, %d to pick from", lg,
                       as.numeric(difftime(Sys.time(), t0, units = "secs")), built, length(shown)))
    }
    step <- function(lg, f) {
      r <- tryCatch({ f(); "ok" }, error = function(e) conditionMessage(e))
      if (!identical(r, "ok")) { R$err[[paste0(lg, "_tab")]] <- r; site_log(sprintf("  %-5s could not be built: %s", lg, r)) }
    }

    nfl_state <- function(w) {
      set(week = w)
      dts <- dts_of(c("board", "td_tbl", "ry_tbl"))
      g <- gids(dts$board); tdx <- list(); det <- list()
      for (i in seq_along(g)) {
        if (is.na(g[i])) next
        set(board_pick = i)
        h <- ui("detail"); if (!is.null(h)) det[[g[i]]] <- h
        tdx[[g[i]]] <- nfl_tdx_html(g[i])
      }
      set(board_pick = NULL)
      list(games = length(g) > 0, html = site_frag(c(
        site_fill(ui("record"), dts), site_dt_html("board", dts$board),
        '<div class="hint">Tap a game for its likely touchdown scorers and the full matchup breakdown.</div>',
        '<div id="board-detail"></div>',
        site_fill(ui("td_section"), dts), site_fill(ui("ry_section"), dts), site_fill(ui("leak_note"), dts)),
        list(tdx = list(board = tdx), detail = list(board = det))))
    }
    cfb_state <- function(w) {
      set(cweek = w)
      dts <- dts_of(c("cboard", "ctd_tbl"))
      tdx <- list(); for (x in stats::na.omit(gids(dts$cboard))) tdx[[x]] <- cfb_tdx_html(x)
      list(games = !is.null(dts$cboard), html = site_frag(c(
        site_fill(ui("crecord"), dts), site_dt_html("cboard", dts$cboard),
        '<div class="hint">Tap a game for its likely touchdown scorers.</div>',
        site_fill(ui("cdetail"), dts), site_fill(ui("ctd_section"), dts), site_fill(ui("cleak"), dts)),
        list(tdx = list(cboard = tdx))))
    }
    mlb_state <- function(d) {
      set(date_picker = as.Date(d))
      dts <- dts_of(c("games_tbl", "nrfi_tbl", "hr_tbl", "k_tbl"))
      list(games = !is.null(dts$games_tbl), html = site_frag(c(
        site_fill(ui("header_badges"), dts), site_fill(ui("accuracy_ui"), dts), site_fill(ui("games_section"), dts),
        site_fill(ui("nrfi_section"), dts), site_fill(ui("hr_section"), dts), site_fill(ui("k_section"), dts),
        site_fill(ui("diag_section"), dts))))
    }
    nhl_state <- function(d) {
      set(ndate = as.Date(d))
      dts <- dts_of(c("nboard", "ngoal"))
      list(games = !is.null(dts$nboard), html = site_frag(c(
        site_fill(ui("nrecord"), dts), site_fill(ui("nboard_sec"), dts), site_fill(ui("ngoal_sec"), dts),
        site_fill(ui("nleak"), dts))))
    }
    nba_state <- function(d) {
      set(bdate = as.Date(d))
      dts <- dts_of(c("bboard", "bfb"))
      list(games = !is.null(dts$bboard), html = site_frag(c(
        site_fill(ui("brecord"), dts), site_fill(ui("bboard_sec"), dts), site_fill(ui("bfb_sec"), dts),
        site_fill(ui("bleak"), dts))))
    }
    window_days <- format(seq(today - SITE_BACK, today + SITE_AHEAD, by = 1))
    game_days <- function(dates, cur) {
      d <- dates[!is.na(dates)]
      sort(unique(c(format(d[d >= today - SITE_BACK & d <= today + SITE_AHEAD]), cur)))
    }

    set(client_today = format(today), client_tz = tz,
        season = as.character(max(app$PICK_SEASONS)), week = "1",
        cseason = as.character(max(app$CFB_PICK)), cweek = "1",
        date_picker = today, ndate = today, bdate = today,
        refresh = 0L, crefresh = 0L, refresh_btn = 0L, nrefresh = 0L, brefresh = 0L, dash_refresh = 0L)

    step("today", function() {
      t0 <- Sys.time()
      set(lg = "today")
      for (i in 1:40) {         # the overview loads one league per tick
        if (all(vapply(DASH_ORDER, function(k) isTRUE(isolate(dash[[k]])), TRUE))) break
        session$elapse(250)
      }
      R$today_date <- ui("dash_date"); R$today <- ui("dash_sports")
      site_log(sprintf("  %-5s %5.1fs", "today", as.numeric(difftime(Sys.time(), t0, units = "secs"))))
    })
    step("nfl", function() {
      set(lg = "nfl")
      d <- dat(); s <- as.integer(input$season); cw <- as.integer(input$week)
      mx <- suppressWarnings(max(d$sch$week[d$sch$season == s], na.rm = TRUE)); if (!is.finite(mx)) mx <- 18L
      keys <- as.character(seq_len(max(1L, min(mx, cw + 1L))))
      R$season$nfl <- s
      league("nfl", keys, paste("Week", keys), as.character(cw), as.character(cw + (-1:1)), nfl_state)
    })
    step("cfb", function() {
      set(lg = "cfb")
      d <- cdat(); s <- as.integer(input$cseason); cw <- as.integer(input$cweek)
      mx <- suppressWarnings(max(d$sch$week[d$sch$season == s], na.rm = TRUE))
      if (!is.finite(mx)) mx <- app$CFB_MAX_WEEK
      keys <- as.character(seq_len(max(1L, min(mx, app$CFB_MAX_WEEK, cw + 1L))))
      R$season$cfb <- s
      league("cfb", keys, paste("Week", keys), as.character(cw), as.character(cw + (-1:1)), cfb_state)
    })
    step("mlb", function() {
      set(lg = "mlb", date_picker = today)
      league("mlb", window_days, site_day_label(window_days, today), format(today),
             window_days[as.Date(window_days) >= today - 1], mlb_state)
    })
    step("nhl", function() {
      set(lg = "nhl")
      cur <- format(as.Date(input$ndate)); keys <- game_days(ndat()$sch$date, cur)
      league("nhl", keys, site_day_label(keys, today), cur, keys[as.Date(keys) >= today - 1], nhl_state)
    })
    step("nba", function() {
      set(lg = "nba")
      cur <- format(as.Date(input$bdate)); keys <- game_days(bdat()$sch$date, cur)
      league("nba", keys, site_day_label(keys, today), cur, keys[as.Date(keys) >= today - 1], nba_state)
    })
  })
  jsonlite::write_json(M$man, M$file, auto_unbox = TRUE, null = "null")
  R
}

# ---- 2. assemble: one static page with the app's look ------------------------------------
site_page <- function(app, R, built, tz, out_dir) {
  H <- htmltools::HTML
  pick <- function(lg, what) {
    st <- R$states[[lg]]
    if (is.null(st) || !length(st$keys)) return(NULL)
    opts <- paste0(sprintf('<option value="%s"%s>%s</option>', st$keys,
                           ifelse(st$keys == st$cur, " selected", ""), htmltools::htmlEscape(st$labels)), collapse = "")
    H(sprintf(paste0('<div class="pick" data-lg="%s"><button type="button" class="pk-b pk-prev" aria-label="Earlier">&#8249;</button>',
                     '<select class="pk-sel" aria-label="%s">%s</select>',
                     '<button type="button" class="pk-b pk-next" aria-label="Later">&#8250;</button></div>'), lg, what, opts))
  }
  body <- function(lg) {
    st <- R$states[[lg]]
    htmltools::div(class = "lg-body", id = paste0("body-", lg), `data-key` = if (is.null(st)) "" else st$cur,
                   H(if (is.null(R$inline[[lg]])) '<div class="err">Not available in this update; the next one will try again.</div>'
                     else R$inline[[lg]]))
  }
  season <- function(lg) if (is.null(R$season[[lg]])) NULL else htmltools::span(class = "pk-lbl", paste(R$season[[lg]], "season"))
  panes <- list(
    htmltools::div(class = "lg-pane", `data-lg` = "today",
      htmltools::div(class = "content dash",
        htmltools::div(class = "dash-top", htmltools::div(htmltools::div(class = "hdr", "Today"), H(R$today_date))),
        H(if (nzchar(R$today)) R$today else '<div class="err">Not available in this update; the next one will try again.</div>'))),
    htmltools::div(class = "lg-pane", `data-lg` = "nfl",
      htmltools::div(class = "content",
        htmltools::div(class = "hdr", "NFL matchup confidence"),
        htmltools::div(class = "sub", "Every game ranked from most predictable to coin toss."),
        htmltools::div(class = "pickrow", season("nfl"), pick("nfl", "Week")), body("nfl"))),
    htmltools::div(class = "lg-pane", `data-lg` = "cfb",
      htmltools::div(class = "content",
        htmltools::div(class = "hdr", "College football matchup confidence"),
        htmltools::div(class = "sub", "Every FBS matchup ranked from most predictable to coin toss."),
        htmltools::div(class = "pickrow", season("cfb"), pick("cfb", "Week")), body("cfb"))),
    htmltools::div(class = "lg-pane", `data-lg` = "mlb",
      htmltools::div(class = "controls-bar", pick("mlb", "Date")), htmltools::div(class = "content", body("mlb"))),
    htmltools::div(class = "lg-pane", `data-lg` = "nhl",
      htmltools::div(class = "controls-bar", pick("nhl", "Date")), htmltools::div(class = "content", body("nhl"))),
    htmltools::div(class = "lg-pane", `data-lg` = "nba",
      htmltools::div(class = "controls-bar", pick("nba", "Date")), htmltools::div(class = "content", body("nba")))
  )

  nav <- list(c("today", "\U0001F4CB", "Today"), c("nfl", "\U0001F3C8", "NFL"), c("cfb", "\U0001F3C8", "NCAAF"),
              c("mlb", "\u26be", "MLB"), c("nhl", "\U0001F3D2", "NHL"), c("nba", "\U0001F3C0", "NBA"))
  nav_ul <- htmltools::tags$ul(class = "nav nav-pills nav-stacked", id = "lg",
    lapply(nav, function(x) htmltools::tags$li(
      htmltools::tags$a(href = paste0("#", x[1]), `data-value` = x[1], app$nav_item(x[2], x[3])))))

  stamp <- gsub("  +", " ", trimws(format(built, "%a %l:%M %p", tz = tz)))
  zone <- format(built, "%Z", tz = tz)
  states <- lapply(R$states, function(s) list(keys = I(s$keys), cur = s$cur))
  site_data <- list(built = as.numeric(built), stamp = paste(stamp, zone), states = states,
                    tdx = list(board = structure(list(), names = character(0)), cboard = structure(list(), names = character(0))),
                    detail = list(board = structure(list(), names = character(0))))
  sj <- gsub("</", "<\\/", as.character(jsonlite::toJSON(site_data, auto_unbox = TRUE, null = "null")), fixed = TRUE)

  page <- htmltools::tagList(
    htmltools::tags$head(
      htmltools::tags$meta(name = "viewport", content = "width=device-width, initial-scale=1"),
      htmltools::tags$title("Projections"),
      htmltools::tags$link(rel = "stylesheet",
        href = "https://fonts.googleapis.com/css2?family=Barlow+Condensed:wght@400;600;700;800&family=IBM+Plex+Mono:wght@400;500;600&family=Barlow:wght@400;500;600&display=swap"),
      htmltools::tags$style(H(paste0(app$PROJ_CSS_BASE, app$PROJ_CSS_EXTRA, app$PROJ_CSS_DASH, SITE_CSS))),
      htmltools::tags$script(H(paste0("window.SITE = ", sj, ";\n", SITE_JS_HEAD)))),
    htmltools::div(class = "app-header",
      htmltools::div(class = "logo-badge", "\U0001F4C8"),
      htmltools::div(htmltools::div(class = "header-title", "Projections"),
                     htmltools::div(class = "header-sub", "NFL \u00b7 NCAAF \u00b7 MLB \u00b7 NHL \u00b7 NBA")),
      htmltools::div(class = "header-pills",
        htmltools::span(id = "upd", class = "pill green", paste("Updated", stamp, zone)))),
    htmltools::div(class = "shell",
      htmltools::div(class = "side", htmltools::div(class = "grp", "League"), nav_ul),
      htmltools::div(class = "main", panes)),
    htmltools::tags$script(H(SITE_JS_BODY))
  )
  dir.create(out_dir, recursive = TRUE, showWarnings = FALSE)
  unlink(file.path(out_dir, "lib"), recursive = TRUE)
  htmltools::save_html(htmltools::attachDependencies(page, site_deps()), file.path(out_dir, "index.html"), libdir = "lib")
  writeLines("", file.path(out_dir, ".nojekyll"))
  invisible(file.path(out_dir, "index.html"))
}

# tables (DataTables through htmlwidgets, as in the app) and Bootstrap's stylesheet only
site_deps <- function() {
  w <- DT::datatable(data.frame(a = 1))
  d <- htmltools::renderTags(w)$dependencies
  b <- Filter(function(x) identical(x$name, "bootstrap"), htmltools::findDependencies(shiny::fluidPage()))
  if (length(b)) { b <- b[[1]]; b$script <- NULL; d <- c(list(b), d) }
  d
}

SITE_CSS <- "
      .lg-pane{display:none}
      .lg-pane.on{display:block}
      #upd.amber{background:rgba(245,158,11,.15);border-color:rgba(245,158,11,.3);color:#fcd34d}
      #board-detail:empty{display:none}
      .pickrow{display:flex;align-items:center;gap:12px;flex-wrap:wrap;margin:10px 0 16px}
      .pk-lbl{font-family:'IBM Plex Mono',monospace;font-size:12px;color:#94a3b8}
      .pick{display:inline-flex;align-items:center;gap:6px}
      .pick select{background:#0a0d14;border:1px solid #334155;border-radius:6px;color:#e2e8f0;height:36px;
        padding:0 10px;font-family:'IBM Plex Mono',monospace;font-size:13px;max-width:62vw}
      .pk-b{background:#111827;border:1px solid #334155;border-radius:6px;color:#cbd5e1;width:36px;height:36px;
        font-size:20px;line-height:1;cursor:pointer;padding:0}
      .pk-b:hover{background:#1e293b;color:#f1f5f9}
      .pk-b:disabled{opacity:.35;cursor:default}
      .lg-body.loading{opacity:.4;transition:opacity .15s;pointer-events:none}
"

SITE_JS_HEAD <- "
// a tap on a board row opens that game's likely scorers under it (built in, no server)
window.tdxBind = function(table, tbl, inputId, col, pickId) {
  table.on('click', 'tbody tr', function() {
    var row = table.row(this), d = row.data();
    if (!d || d[col] === undefined || d[col] === null) return;
    var gid = String(d[col]), tr = $(this), det = document.getElementById(tbl + '-detail');
    if (row.child.isShown()) {
      row.child.hide(); tr.removeClass('tdx-open');
      if (det) det.innerHTML = '';
      return;
    }
    var html = ((SITE.tdx || {})[tbl] || {})[gid] ||
      '<div class=tdx><div class=tdx-none>No player projections for this game.</div></div>';
    row.child(html, 'tdx-cell').show(); tr.addClass('tdx-open');
    if (det) det.innerHTML = ((SITE.detail || {})[tbl] || {})[gid] || '';
  });
};
"

SITE_JS_BODY <- "
(function() {
  var known = ['today', 'nfl', 'cfb', 'mlb', 'nhl', 'nba'];
  // a day or week's own data: the scorers and matchup panels behind its board
  function applyFrag(body) {
    var s = body && body.querySelector('script.frag-data');
    if (!s) return;
    try {
      var j = JSON.parse(s.textContent);
      ['tdx', 'detail'].forEach(function(k) { if (j[k]) for (var t in j[k]) SITE[k][t] = j[k][t]; });
    } catch (e) {}
  }
  function adjust() {
    $(document).trigger('shown.htmlwidgets');      // tables in a tab that was hidden draw now
    if ($.fn.dataTable) $.fn.dataTable.tables({ visible: true, api: true }).columns.adjust();
  }
  function arrows(lg) {
    var p = $('.pick[data-lg=' + lg + ']'), st = SITE.states[lg];
    if (!p.length || !st) return;
    var i = st.keys.indexOf(p.find('select').val());
    p.find('.pk-prev').prop('disabled', i <= 0);
    p.find('.pk-next').prop('disabled', i < 0 || i >= st.keys.length - 1);
  }
  function load(lg, key, user) {
    var body = document.getElementById('body-' + lg), st = SITE.states[lg];
    if (!body || !st || st.keys.indexOf(key) < 0) return;
    $('.pick[data-lg=' + lg + '] select').val(key); arrows(lg);
    if (user) { try { history.replaceState(null, '', '#' + lg + '/' + key); } catch (e) {} }
    if (body.getAttribute('data-key') === key) { applyFrag(body); return; }
    body.classList.add('loading');
    fetch('d/' + lg + '/' + encodeURIComponent(key) + '.html?v=' + Math.round(SITE.built))
      .then(function(r) { if (!r.ok) throw new Error(r.status); return r.text(); })
      .then(function(h) {
        $(body).find('table.dataTable').each(function() { try { $(this).DataTable().destroy(); } catch (e) {} });
        body.innerHTML = h; body.setAttribute('data-key', key);
        applyFrag(body);
        if (window.HTMLWidgets) HTMLWidgets.staticRender();
        adjust();
      })
      .catch(function() {
        body.innerHTML = '<div class=\"err\">That one could not be loaded. Check the connection and pick it again.</div>';
        body.removeAttribute('data-key');
      })
      .then(function() { body.classList.remove('loading'); });
  }
  function show(lg) {
    if (known.indexOf(lg) < 0) lg = 'today';
    $('.lg-pane').removeClass('on').filter('[data-lg=' + lg + ']').addClass('on');
    $('#lg > li').removeClass('active');
    $('#lg a[data-value=' + lg + ']').parent().addClass('active');
    applyFrag(document.getElementById('body-' + lg));
    adjust();
    return lg;
  }
  function route() {
    var h = (location.hash || '').slice(1).split('/'), q = (location.search.match(/[?&]lg=([a-z]+)/) || [])[1];
    var lg = show(h[0] || q || 'today');
    if (h[1]) load(lg, decodeURIComponent(h[1]), false);
  }
  $(document).on('click', '#lg a[data-value]', function(e) {
    e.preventDefault();
    var lg = $(this).attr('data-value');
    try { history.replaceState(null, '', '#' + lg); } catch (err) {}
    show(lg); window.scrollTo(0, 0);
  });
  $(document).on('change', '.pick select', function() { load($(this).closest('.pick').attr('data-lg'), this.value, true); });
  $(document).on('click', '.pick .pk-b', function() {
    var p = $(this).closest('.pick'), lg = p.attr('data-lg'), st = SITE.states[lg];
    var i = st.keys.indexOf(p.find('select').val()) + ($(this).hasClass('pk-prev') ? -1 : 1);
    if (i >= 0 && i < st.keys.length) load(lg, st.keys[i], true);
  });
  known.forEach(arrows);
  route();
  $(window).on('hashchange', route);
  // say so when the page has gone stale (the Mac that updates it is asleep or off)
  var up = document.getElementById('upd'), age = (Date.now() / 1000 - SITE.built) / 60;
  if (up && age > 90) {
    up.className = 'pill amber';
    up.textContent = 'Updated ' + SITE.stamp + ' \\u00b7 ' + (age < 1440 ? Math.round(age / 60) + ' h ago' : Math.round(age / 1440) + ' d ago');
  }
})();
"

site_build <- function(out_dir = SITE$home) {
  old <- setwd(SITE$app); on.exit(setwd(old), add = TRUE)
  # the app's hosted mode: no background warm-up loop while the page is computed
  sp <- Sys.getenv("SHINY_PORT", NA); Sys.setenv(SHINY_PORT = "0")
  on.exit(if (is.na(sp)) Sys.unsetenv("SHINY_PORT") else Sys.setenv(SHINY_PORT = sp), add = TRUE)
  app <- new.env(parent = globalenv())
  sys.source(file.path(SITE$app, "Projections.R"), envir = app, keep.source = FALSE)
  tz <- Sys.timezone(); if (is.na(tz) || !nzchar(tz)) tz <- "America/Edmonton"
  built <- Sys.time()
  R <- site_capture(app, tz, out_dir)
  if (length(R$err)) site_log("  could not compute: ", paste(sprintf("%s (%s)", names(R$err), unlist(R$err)), collapse = "; "))
  if (!nzchar(R$today) && !length(R$inline)) stop("nothing could be computed (see the log above)")
  site_page(app, R, built, tz, out_dir)
}

# ---- 3. publish: GitHub sign-in, repository, Pages ------------------------------------------
GH_KEY <- "Projections GitHub token"    # the macOS keychain item that keeps the token

site_gh <- function(method, path, token, body = NULL) {
  h <- httr::add_headers(Authorization = paste("Bearer", token), Accept = "application/vnd.github+json",
                         `X-GitHub-Api-Version` = "2022-11-28", `User-Agent` = "projections-publisher",
                         `Content-Type` = "application/json")
  r <- tryCatch(httr::VERB(method, paste0("https://api.github.com", path), h, httr::timeout(30),
                           body = if (is.null(body)) NULL else as.character(jsonlite::toJSON(body, auto_unbox = TRUE)),
                           encode = "raw"), error = function(e) NULL)
  if (is.null(r)) return(list(status = 0L, data = NULL))
  list(status = httr::status_code(r),
       data = tryCatch(httr::content(r, as = "parsed", simplifyVector = TRUE), error = function(e) NULL))
}

site_login <- function(token) {          # whose token this is, or NULL if GitHub refuses it
  if (!length(token) || !nzchar(token)) return(NULL)
  # A GitHub Actions token is scoped to one repository and cannot answer /user, so when the
  # workflow supplies the account name we take it and skip the call entirely.
  env <- Sys.getenv("SITE_GITHUB_LOGIN")
  if (nzchar(env)) return(env)
  r <- site_gh("GET", "/user", token)
  if (r$status == 200 && length(r$data$login)) r$data$login else NULL
}

# a token kept from before: this script's keychain item, else the GitHub sign-in git keeps
site_token_saved <- function() {
  t <- Sys.getenv("SITE_GITHUB_TOKEN")
  if (nzchar(t)) return(list(token = t, ours = TRUE))
  if (nzchar(Sys.which("security"))) {
    t <- suppressWarnings(system2("security", c("find-generic-password", "-s", shQuote(GH_KEY), "-w"),
                                  stdout = TRUE, stderr = FALSE, timeout = 15))
    if (length(t) && is.null(attr(t, "status")) && nzchar(t[1])) return(list(token = t[1], ours = TRUE))
  }
  out <- suppressWarnings(system2("git", c("credential", "fill"), input = c("protocol=https", "host=github.com", ""),
                                  stdout = TRUE, stderr = FALSE, timeout = 15,
                                  env = c("GIT_TERMINAL_PROMPT=0", "GCM_INTERACTIVE=never",
                                          "GIT_ASKPASS=/usr/bin/true", "SSH_ASKPASS=/usr/bin/true")))
  if (!is.null(attr(out, "status")) && attr(out, "status") != 0) out <- character(0)
  pw <- sub("^password=", "", grep("^password=", out, value = TRUE))
  list(token = if (length(pw)) pw[1] else "", ours = FALSE)
}

site_token_ask <- function() {
  if (!interactive())
    stop("GitHub sign-in needed: in RStudio run  source(\"~/Desktop/publish_site.R\")  once.")
  message("\nOne-time GitHub sign-in. A GitHub page is opening in your browser:",
          "\n  1. set Expiration to \"No expiration\"",
          "\n  2. click \"Generate token\" at the bottom and copy the token it shows",
          "\n  3. paste it here\n")
  utils::browseURL("https://github.com/settings/tokens/new?scopes=repo&description=Projections%20page")
  ask <- paste("On the GitHub page that just opened: set Expiration to 'No expiration',",
               "click 'Generate token', copy the token and paste it here.")
  t <- if (requireNamespace("rstudioapi", quietly = TRUE) && rstudioapi::isAvailable())
    rstudioapi::askForPassword(ask) else readline("Paste the GitHub token and press Enter: ")
  if (is.null(t)) "" else trimws(t)
}

site_token_keep <- function(token, login) {
  if (nzchar(Sys.which("security")))
    system2("security", c("add-generic-password", "-U", "-a", shQuote(login), "-s", shQuote(GH_KEY),
                          "-w", shQuote(token)), stdout = FALSE, stderr = FALSE, timeout = 15)
}

# Signs in (asking once), and makes sure the repository exists; returns the sign-in.
site_github <- function(ask = interactive()) {
  s <- site_token_saved(); login <- site_login(s$token)
  if (is.null(login)) {
    if (!ask) stop("GitHub sign-in needed: in RStudio run  source(\"~/Desktop/publish_site.R\")  once.")
    s <- list(token = site_token_ask(), ours = FALSE); login <- site_login(s$token)
    if (is.null(login)) stop("GitHub did not accept that token. Run the line again and paste the whole token.")
  }
  if (!s$ours) site_token_keep(s$token, login)
  site_owner(login)
  gh <- list(token = s$token, login = login)
  r <- site_gh("GET", sprintf("/repos/%s/%s", login, SITE$repo), gh$token)
  if (nzchar(Sys.getenv("SITE_GITHUB_LOGIN")) && r$status != 200) return(gh)   # CI: the repo is a given
  if (r$status == 404) {
    site_log("creating the public repository ", login, "/", SITE$repo)
    c1 <- site_gh("POST", "/user/repos", gh$token,
                  list(name = SITE$repo, private = FALSE, description = "Projections, updated automatically",
                       homepage = SITE$url, has_issues = FALSE, has_wiki = FALSE, has_projects = FALSE))
    if (c1$status %in% c(401, 403) && ask) {     # a saved sign-in that may not create repositories
      s <- list(token = site_token_ask(), ours = FALSE); login <- site_login(s$token)
      if (is.null(login)) stop("GitHub did not accept that token. Run the line again and paste the whole token.")
      site_token_keep(s$token, login); site_owner(login); gh <- list(token = s$token, login = login)
      c1 <- site_gh("POST", "/user/repos", gh$token, list(name = SITE$repo, private = FALSE,
                    description = "Projections, updated automatically", homepage = SITE$url))
    }
    if (!c1$status %in% c(201, 422)) stop("GitHub would not create the repository (status ", c1$status, ").")
  } else if (r$status != 200) stop("GitHub did not answer (status ", r$status, "); the next update will retry.")
  gh
}

# switches GitHub Pages on for the repository (TRUE the first time)
site_pages_on <- function(gh) {
  path <- sprintf("/repos/%s/%s/pages", gh$login, SITE$repo)
  if (site_gh("GET", path, gh$token)$status == 200) return(FALSE)
  p <- site_gh("POST", path, gh$token, list(source = list(branch = "main", path = "/")))
  if (!p$status %in% c(201, 409))
    stop("GitHub would not switch on Pages (status ", p$status, "). The repository must be public.")
  TRUE
}

site_git <- function(..., timeout = 120) {
  # never wait for a password prompt; commit as this repository's own identity
  who <- c("Projections", sprintf("%s@users.noreply.github.com", SITE$user))
  # (RStudio sets GIT_ASKPASS to its own username popup; a no-op keeps git from asking)
  env <- c("GIT_TERMINAL_PROMPT=0", "GCM_INTERACTIVE=never", "GIT_ASKPASS=/usr/bin/true", "SSH_ASKPASS=/usr/bin/true",
           paste0("GIT_AUTHOR_NAME=", who[1]), paste0("GIT_AUTHOR_EMAIL=", who[2]),
           paste0("GIT_COMMITTER_NAME=", who[1]), paste0("GIT_COMMITTER_EMAIL=", who[2]))
  out <- suppressWarnings(system2("git", c("-C", shQuote(SITE$home), "-c", "credential.helper=", ...),
                                  stdout = TRUE, stderr = TRUE, env = env, timeout = timeout))
  st <- attr(out, "status")
  list(ok = is.null(st) || st == 0L, out = paste(out, collapse = "\n"))
}

site_git_ready <- function() {
  if (!nzchar(Sys.which("git"))) stop("git is not installed: run  xcode-select --install  in Terminal")
  dir.create(SITE$home, recursive = TRUE, showWarnings = FALSE)
  if (!dir.exists(file.path(SITE$home, ".git"))) {
    r <- site_git("init", "-q"); if (!r$ok) stop("git init failed: ", r$out)
    site_git("checkout", "-q", "-b", "main")
    site_git("remote", "add", "origin", SITE$remote)
  } else site_git("remote", "set-url", "origin", SITE$remote)
}

site_push <- function(label, gh) {
  site_git_ready()
  site_git("add", "-A")
  # one commit, replaced every time: the repository stays the size of a single page
  has <- site_git("rev-parse", "--verify", "-q", "HEAD")$ok
  r <- site_git("commit", "-q", if (has) c("--amend", "--reset-author"), "-m", shQuote(label))
  if (!r$ok) stop("git commit failed: ", r$out)
  # the sign-in travels as one header line (base64_enc wraps long output in lines; a line
  # break inside a header makes GitHub drop the connection)
  user <- if (nzchar(Sys.getenv("SITE_GITHUB_LOGIN")) && grepl("^gh[sp]_", gh$token))
    "x-access-token" else gh$login
  b64 <- gsub("[\r\n]", "", jsonlite::base64_enc(charToRaw(paste0(user, ":", gh$token))))
  auth <- paste0("http.https://github.com/.extraheader=AUTHORIZATION: basic ", b64)
  site_log("uploading to GitHub")
  p <- site_git("-c", shQuote(auth), "push", "-q", "--force", "origin", "main", timeout = 300)
  if (!p$ok && grepl("HTTP/2|stream|unexpected disconnect|RPC failed|early EOF", p$out))   # a network that dislikes HTTP/2
    p <- site_git("-c", shQuote(auth), "-c", "http.version=HTTP/1.1", "-c", "http.postBuffer=524288000",
                  "push", "-q", "--force", "origin", "main", timeout = 300)
  if (!p$ok) stop("could not upload the page to GitHub:\n", gsub(gh$token, "<token>", p$out, fixed = TRUE))
  site_git("reflog", "expire", "--expire=now", "--all")
  site_git("gc", "-q", "--prune=now")
  invisible(TRUE)
}

# macOS notification for a scheduled run that failed (at most every 3 hours)
site_notify <- function(msg) {
  if (interactive() || Sys.info()[["sysname"]] != "Darwin") return(invisible())
  f <- file.path(SITE$state, "notified")
  if (file.exists(f) && difftime(Sys.time(), file.mtime(f), units = "hours") < 3) return(invisible())
  dir.create(SITE$state, recursive = TRUE, showWarnings = FALSE); writeLines("", f)
  s <- gsub('[\\\\"]', "'", substr(msg, 1, 180))
  system2("osascript", c("-e", shQuote(sprintf('display notification "%s" with title "Projections page not updated"', s))))
  invisible()
}

# A run that starts while the Mac is awake must be allowed to finish. Under launchd the
# process is suspended the moment the machine sleeps, with the wall clock still running, so
# a nine minute build was taking hours and launchd will not start the next run while one is
# still in flight -- which is why the page only went up two or three times a day. caffeinate
# holds off idle and disk sleep for exactly as long as this process lives, and no longer.
site_keep_awake <- function() {
  if (Sys.info()[["sysname"]] != "Darwin") return(invisible(FALSE))
  if (!file.exists("/usr/bin/caffeinate")) return(invisible(FALSE))
  ok <- tryCatch({
    system2("/usr/bin/caffeinate", c("-i", "-m", "-s", "-w", Sys.getpid()),
            stdout = FALSE, stderr = FALSE, wait = FALSE)
    TRUE
  }, error = function(e) FALSE, warning = function(w) TRUE)
  if (isTRUE(ok)) site_log("holding the Mac awake until this run finishes")
  invisible(ok)
}

site_publish <- function() {
  # On GitHub the workflow owns the git side: it checks the branch out, calls this to build
  # the page into _site, then commits the page and the ledgers itself. So there is no
  # sign-in, no push and no schedule here -- just the build, and a non-zero exit if it
  # cannot be done, so a broken run shows up red instead of quietly publishing nothing.
  if (identical(Sys.getenv("SITE_BUILD_ONLY"), "1")) {
    t0 <- Sys.time()
    site_log("building the page from ", file.path(SITE$app, "Projections.R"))
    site_build()
    kb <- sum(file.size(list.files(SITE$home, recursive = TRUE, full.names = TRUE)), na.rm = TRUE) / 1024
    site_log(sprintf("built %.0f KB in %.0fs", kb, as.numeric(difftime(Sys.time(), t0, units = "secs"))))
    return(invisible(TRUE))
  }
  dir.create(SITE$state, recursive = TRUE, showWarnings = FALSE)
  lock <- file.path(SITE$state, "build.lock"); done <- file.path(SITE$state, "published")
  if (!interactive() && dir.exists(lock) && difftime(Sys.time(), file.mtime(lock), units = "mins") < 45) {
    pid <- suppressWarnings(as.integer(readLines(file.path(lock, "pid"), warn = FALSE)[1]))
    if (length(pid) && !is.na(pid) && isTRUE(tools::pskill(pid, 0L))) {
      site_log("skipped: the previous update is still running"); return(invisible(FALSE))
    }
  }
  if (!interactive() && file.exists(done) && difftime(Sys.time(), file.mtime(done), units = "mins") < 10) {
    site_log("skipped: published less than 10 minutes ago"); return(invisible(FALSE))
  }
  unlink(lock, recursive = TRUE); dir.create(lock); writeLines(as.character(Sys.getpid()), file.path(lock, "pid"))
  on.exit(unlink(lock, recursive = TRUE), add = TRUE)
  site_keep_awake()
  t0 <- Sys.time(); first <- FALSE
  res <- tryCatch({
    gh <- site_github()                                   # sign-in (asks once) and repository
    site_log("building the page from ", file.path(SITE$app, "Projections.R"))
    site_build()
    kb <- sum(file.size(list.files(SITE$home, recursive = TRUE, full.names = TRUE))) / 1024
    site_log(sprintf("built %.0f KB in %.0fs", kb, as.numeric(difftime(Sys.time(), t0, units = "secs"))))
    site_push(paste("Projections", format(Sys.time(), "%Y-%m-%d %H:%M %Z")), gh)
    first <- site_pages_on(gh)                            # GitHub Pages (switched on once)
    "ok"
  }, error = function(e) conditionMessage(e))
  if (!identical(res, "ok")) {
    site_log("FAILED: ", res)
    site_notify(res)
    if (interactive()) stop(res, call. = FALSE)
    return(invisible(FALSE))
  }
  writeLines(format(Sys.time()), done)
  site_log("published ", SITE$url, sprintf(" (%.0fs)", as.numeric(difftime(Sys.time(), t0, units = "secs"))))
  if (interactive()) {
    auto <- tryCatch(site_schedule_on(quiet = TRUE), error = function(e) { message(conditionMessage(e)); FALSE })
    message("\nDone. Your page: ", SITE$url,
            if (first) "\n(GitHub needs about a minute to put it up the first time.)" else "",
            if (isTRUE(auto)) "\nIt now updates itself every 30 minutes while this Mac is awake." else "",
            if (isTRUE(auto)) "\nIf macOS asks whether Rscript may access your Desktop, click Allow." else "")
  }
  invisible(TRUE)
}

# ---- 4. schedule: every 30 minutes through launchd (macOS) ---------------------------------
# launchd starts a small starter kept outside the Desktop, so that if macOS keeps R out of
# the Desktop folder the starter can still put up a notification saying how to allow it.
site_schedule_files <- function(minutes = 30) {
  dir.create(SITE$state, recursive = TRUE, showWarnings = FALSE)
  dir.create(dirname(SITE$log), recursive = TRUE, showWarnings = FALSE)
  agents <- path.expand("~/Library/LaunchAgents"); dir.create(agents, recursive = TRUE, showWarnings = FALSE)
  runner <- file.path(SITE$state, "run_site.R")
  writeLines(c(
    "# Started every 30 minutes by launchd (~/Library/LaunchAgents/com.projections.site.plist).",
    "# Turn it off from RStudio with  source(\"~/Desktop/publish_site.R\"); site_schedule_off()",
    sprintf("app <- %s", deparse(SITE$app)),
    sprintf("log <- %s", deparse(SITE$log)),
    "if (file.exists(log) && file.size(log) > 2e6) writeLines(tail(readLines(log), 2000), log)",
    "options(site.app_dir = app)",
    "tryCatch({",
    "  setwd(app)",
    "  source(file.path(app, \"publish_site.R\"))",
    "}, error = function(e) {",
    "  msg <- conditionMessage(e)",
    "  cat(format(Sys.time(), \"%Y-%m-%d %H:%M:%S\"), \" could not start: \", msg, \"\\n\", sep = \"\")",
    "  if (grepl(\"not permitted|cannot change working directory|cannot open\", msg))",
    "    try(system2(\"osascript\", c(\"-e\", shQuote(paste(",
    "      \"display notification \\\"macOS is keeping R out of the Desktop: System Settings > Privacy & Security >\",",
    "      \"Files and Folders > Rscript > Desktop Folder (or add R to Full Disk Access).\\\"\",",
    "      \"with title \\\"Projections page not updated\\\"\")))), silent = TRUE)",
    "})"
  ), runner)
  x <- function(v) gsub("<", "&lt;", gsub("&", "&amp;", v, fixed = TRUE), fixed = TRUE)
  plist <- file.path(agents, paste0(SITE$label, ".plist"))
  writeLines(c(
    '<?xml version="1.0" encoding="UTF-8"?>',
    '<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">',
    '<plist version="1.0"><dict>',
    sprintf('  <key>Label</key><string>%s</string>', SITE$label),
    sprintf(paste0('  <key>ProgramArguments</key><array>',
                   '<string>/usr/bin/caffeinate</string><string>-i</string><string>-m</string>',
                   '<string>%s</string><string>%s</string></array>'),
            x(file.path(R.home("bin"), "Rscript")), x(runner)),
    sprintf('  <key>WorkingDirectory</key><string>%s</string>', x(SITE$state)),
    sprintf('  <key>StartInterval</key><integer>%d</integer>', as.integer(minutes * 60)),
    '  <key>RunAtLoad</key><true/>',
    sprintf('  <key>StandardOutPath</key><string>%s</string>', x(SITE$log)),
    sprintf('  <key>StandardErrorPath</key><string>%s</string>', x(SITE$log)),
    '  <key>EnvironmentVariables</key><dict>',
    '    <key>PATH</key><string>/usr/local/bin:/opt/homebrew/bin:/usr/bin:/bin:/usr/sbin:/sbin</string>',
    '    <key>LANG</key><string>en_US.UTF-8</string>',
    '    <key>LC_ALL</key><string>en_US.UTF-8</string>',
    '  </dict>',
    '  <key>ProcessType</key><string>Standard</string>',
    '  <key>LowPriorityIO</key><false/>',
    '</dict></plist>'), plist)
  invisible(c(runner = runner, plist = plist))
}

site_schedule_on <- function(minutes = 30, quiet = FALSE) {
  if (Sys.info()[["sysname"]] != "Darwin") return(invisible(FALSE))
  plist <- file.path(path.expand("~/Library/LaunchAgents"), paste0(SITE$label, ".plist"))
  if (quiet && file.exists(plist)) return(invisible(TRUE))          # already on
  f <- site_schedule_files(minutes)
  uid <- system2("id", "-u", stdout = TRUE)
  dom <- paste0("gui/", uid)
  suppressWarnings(system2("launchctl", c("bootout", dom, shQuote(f[["plist"]])), stdout = FALSE, stderr = FALSE))
  r <- suppressWarnings(system2("launchctl", c("bootstrap", dom, shQuote(f[["plist"]])), stdout = TRUE, stderr = TRUE))
  if (!is.null(attr(r, "status")) && attr(r, "status") != 0)
    stop("Automatic updates could not be switched on: ", paste(r, collapse = " "))
  if (!quiet) message(sprintf("The page now updates every %d minutes while this Mac is awake.", minutes),
                      "
If macOS asks whether Rscript may access your Desktop, click Allow.",
                      "
To stop: site_schedule_off()")
  invisible(TRUE)
}

site_schedule_off <- function() {
  plist <- file.path(path.expand("~/Library/LaunchAgents"), paste0(SITE$label, ".plist"))
  uid <- system2("id", "-u", stdout = TRUE)
  suppressWarnings(system2("launchctl", c("bootout", paste0("gui/", uid), shQuote(plist)), stdout = FALSE, stderr = FALSE))
  unlink(plist)
  message("Automatic updates are off. The page keeps its last version until you publish again.")
  invisible(TRUE)
}

if (!isTRUE(getOption("site.no_run"))) site_publish()
