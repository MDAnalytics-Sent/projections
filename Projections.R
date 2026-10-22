suppressPackageStartupMessages({
  library(shiny)
  library(httr)
  library(jsonlite)
  library(dplyr)
  library(tidyr)
  library(purrr)
  library(lubridate)
  library(DT)
  library(nflreadr)
  library(Matrix)
})

APP_NAME <- "Projections"

# ==================== SHARED ====================
# Replaces a ledger file in one step (a temporary copy renamed over the old one), so another
# R process reading it -- the app and the scheduled page build can run at the same time --
# never sees a half-written file.
csv_replace <- function(x, path) {
  tmp <- sprintf("%s.%d.tmp", path, Sys.getpid())
  utils::write.csv(x, tmp, row.names = FALSE)
  if (!file.rename(tmp, path)) { unlink(tmp); stop("could not replace ", path) }
  invisible(TRUE)
}
SDV_REL <- "https://github.com/sportsdataverse/sportsdataverse-data/releases/download"
SDV_REFRESH_MIN <- 6 * 60
SDV_MISS_MIN    <- 60

sdv_fetch <- function(tag, file, dest) {
  if (file.exists(dest) && file.size(dest) > 512) return(TRUE)
  ms <- paste0(dest, ".miss")
  if (age_min(ms) < SDV_MISS_MIN) return(FALSE)
  u <- sprintf("%s/%s/%s", SDV_REL, tag, file)
  tmp <- paste0(dest, ".part")
  ok <- suppressWarnings(try(
    utils::download.file(u, tmp, mode = "wb", quiet = TRUE), silent = TRUE))
  if (inherits(ok, "try-error") || !file.exists(tmp) || file.size(tmp) < 512) {
    unlink(tmp)
    try(file.create(ms), silent = TRUE)
    return(FALSE)
  }
  unlink(ms)
  file.rename(tmp, dest)
  TRUE
}

prob_pill <- function(p, hi = 1) {
  ifelse(is.na(p), "&mdash;", sprintf(
    '<div class="cf"><span class="cfn">%.0f%%</span><span class="cft"><span class="cfb" style="width:%.0f%%;background:%s"></span></span></div>',
    100 * p, 100 * pmin(pmax(p / hi, 0.04), 1), cfb_conf_col(0.5 + 0.45 * pmin(p / hi, 1))))
}

grade_state <- function(pid, team, board, rows) {
  n <- length(pid)
  st <- rep("pending", n)
  attr(st, "row") <- rep(NA_integer_, n)
  if (is.null(board) || is.null(rows) || !nrow(rows) || !n) return(st)
  tg <- stats::setNames(c(board$g$game_id, board$g$game_id),
                        c(board$g$home, board$g$away))
  gid <- unname(tg[team])
  r <- rows[rows$game_id %in% board$g$game_id, , drop = FALSE]
  if (!nrow(r)) return(st)
  graded <- !is.na(gid) & gid %in% unique(r$game_id)
  st[graded] <- "dnp"
  j <- match(paste(pid, gid), paste(r$pid, r$game_id))
  st[graded & !is.na(j)] <- "played"
  attr(st, "row") <- j
  attr(st, "src") <- r
  st
}

lg_badge <- function(url, col = "#334155") {
  ifelse(is.na(url) | url == "",
         sprintf('<span class="bdg" style="background:%s"></span>', col),
         sprintf('<span class="bdg"><img src="%s" alt=""></span>', url))
}

# ==================== MLB ====================
MLB_CACHE_VER  <- 1L
MLB_CACHE_DIR  <- file.path("proj_cache", "mlb")
MLB_LIVE_TTL   <- 90
MLB_DEAD_AFTER <- 6L
MLB_PROBE_SEC  <- 5
.mlb_disk <- new.env(hash = TRUE, parent = emptyenv())
.mlb_disk$fail <- 0L
.mlb_disk$dead <- FALSE
.mlb_disk$alive <- NULL
.mlb_disk$hits <- 0L
.mlb_disk$miss <- 0L
dir.create(MLB_CACHE_DIR, showWarnings = FALSE, recursive = TRUE)

mlb_today <- function() {
  x <- getOption("mlb.today")
  if (is.null(x)) Sys.Date() else as.Date(x)
}

mlb_cur_season <- function() as.integer(format(mlb_today(), "%Y"))

.hash32 <- function(s) {
  b <- as.integer(charToRaw(paste0(s, "|", MLB_CACHE_VER)))
  h1 <- 0; h2 <- 0
  for (x in b) {
    h1 <- (h1 * 31 + x) %% 4294967291
    h2 <- (h2 * 131 + x) %% 4294967279
  }
  sprintf("%08x%08x", as.integer(h1 %% 2147483647), as.integer(h2 %% 2147483647))
}

mlb_url_class <- function(url) {
  u <- as.character(url)
  sea <- suppressWarnings(as.integer(sub(".*season=([0-9]{4}).*", "\\1", u)))
  cur <- mlb_cur_season()
  if (grepl("personIds=", u, fixed = TRUE) || grepl("/people/[0-9]+$", u)) return("perm")
  if (grepl("date=", u, fixed = TRUE)) {
    d <- suppressWarnings(as.Date(sub(".*date=([0-9-]{10}).*", "\\1", u)))
    if (!is.na(d) && d < mlb_today()) return("perm")
    return("live")
  }
  if (grepl("/game/[0-9]+/(boxscore|linescore|lineups)", u) ||
      grepl("gamePk=", u, fixed = TRUE)) return("game")
  if (!is.na(sea) && sea < cur) return("perm")
  if (grepl("gameLog", u, fixed = TRUE) || grepl("roster", u, fixed = TRUE) ||
      grepl("csv=true", u, fixed = TRUE)) return("day")
  "live"
}

.mlb_file <- function(url) file.path(MLB_CACHE_DIR, paste0(.hash32(url), ".rds"))

# stale_ok = TRUE returns the last saved copy whatever its age. Used only when the
# API is down, so an outage degrades to yesterday's numbers instead of to blanks
# (a missing starter log used to drop that pitcher to league-average priors).
mlb_disk_read <- function(url, cls, stale_ok = FALSE) {
  f <- .mlb_file(url)
  if (!file.exists(f)) return(NULL)
  obj <- try(readRDS(f), silent = TRUE)
  if (inherits(obj, "try-error") || !is.list(obj) || is.null(obj$v)) { unlink(f); return(NULL) }
  age <- as.numeric(difftime(Sys.time(), obj$t, units = "secs"))
  ok <- switch(cls,
    perm = TRUE,
    game = isTRUE(obj$final) || age < MLB_LIVE_TTL,
    day  = as.Date(obj$t) >= mlb_today(),
    live = age < MLB_LIVE_TTL,
    FALSE)
  if (!ok && !stale_ok) return(NULL)
  obj$v
}

.is_final_game <- function(v) {
  s <- tryCatch({
    g <- v[["gameData"]][["status"]][["abstractGameState"]]
    if (is.null(g)) g <- v[["status"]][["abstractGameState"]]
    if (is.null(g)) g <- v[["dates"]][[1]][["games"]][[1]][["status"]][["abstractGameState"]]
    as.character(g)
  }, error = function(e) NULL)
  isTRUE(length(s) == 1L && s == "Final")
}

mlb_disk_write <- function(url, v, cls) {
  if (is.null(v)) return(invisible(FALSE))
  f <- .mlb_file(url)
  tmp <- paste0(f, ".tmp")
  obj <- list(v = v, t = Sys.time(), u = url,
              final = if (cls == "game") .is_final_game(v) else NA)
  ok <- try({ saveRDS(obj, tmp, compress = TRUE); file.rename(tmp, f) }, silent = TRUE)
  if (inherits(ok, "try-error")) unlink(tmp)
  invisible(!inherits(ok, "try-error"))
}

mlb_cache_stats <- function() {
  f <- list.files(MLB_CACHE_DIR, pattern = "\\.rds$", full.names = TRUE)
  list(files = length(f), mb = round(sum(file.size(f), na.rm = TRUE) / 1048576, 1),
       hits = .mlb_disk$hits, miss = .mlb_disk$miss, offline = .mlb_disk$dead)
}

mlb_cache_reset_session <- function() {
  .mlb_disk$fail <- 0L; .mlb_disk$dead <- FALSE; .mlb_disk$alive <- NULL
  .mlb_disk$hits <- 0L; .mlb_disk$miss <- 0L
}

mlb_cache_prune <- function(keep_days = 45L) {
  f <- list.files(MLB_CACHE_DIR, pattern = "\\.rds$", full.names = TRUE)
  if (!length(f)) return(invisible(0L))
  old <- f[difftime(Sys.time(), file.mtime(f), units = "days") > keep_days]
  drop <- character(0)
  for (p in old) {
    o <- try(readRDS(p), silent = TRUE)
    if (inherits(o, "try-error") || is.null(o$u) ||
        mlb_url_class(o$u) != "perm") drop <- c(drop, p)
  }
  unlink(drop); invisible(length(drop))
}

mlb_api_alive <- function() {
  if (isTRUE(.mlb_disk$dead)) return(FALSE)
  if (!is.null(.mlb_disk$alive)) return(.mlb_disk$alive)
  u <- sprintf("%s/schedule?sportId=1&date=%s", MLB_API_BASE, format(mlb_today(), "%Y-%m-%d"))
  ok <- tryCatch({
    r <- httr::GET(u, httr::timeout(MLB_PROBE_SEC))
    isTRUE(httr::status_code(r) == 200L)
  }, error = function(e) FALSE)
  .mlb_disk$alive <- ok
  if (!ok) {
    .mlb_disk$dead <- TRUE
    mlog("Network    | the MLB API did not answer; serving cached data only")
  }
  ok
}


USE_STATCAST         <- FALSE   
STRICT_POINT_IN_TIME <- TRUE

# ============================================================================
# CONSOLE LOGGING
# One funnel for every status line the model prints, so the console stays a
# signal and not a wall. Three rules:
#   1. quiet mode  -- backfill/catch-up runs print nothing (they used to emit one
#      calibration line per day, i.e. 30+ lines before a single slate loaded).
#   2. de-duplication -- an identical consecutive message prints once, so
#      re-running the same slate does not repeat the same block verbatim.
#   3. LOG_LEVEL    -- "info" (default), or "quiet" to silence everything.
# ============================================================================
LOG_LEVEL  <- "info"                        # "info" | "quiet"
.log_state <- new.env(parent = emptyenv())
.log_state$quiet <- FALSE
.log_state$last  <- ""

mlog <- function(...) {
  if (isTRUE(.log_state$quiet) || identical(LOG_LEVEL, "quiet")) return(invisible(FALSE))
  msg <- paste0(...)
  if (identical(msg, .log_state$last)) return(invisible(FALSE))   # collapse consecutive repeats
  .log_state$last <- msg
  cat(msg, "\n", sep = "")
  invisible(TRUE)
}

# Monte Carlo seed for one game. Was MC_SEED + i, where i is the game's ROW INDEX
# in the schedule -- so if the schedule came back in a different order (or a game
# was postponed out of it), every other game silently drew a different simulation
# and probabilities near 50% could flip on a reload. Keyed to the immutable MLB
# gamePk instead, one game always gets the same 25,000 simulations.
game_seed <- function(game_id, side = 1L) {
  gid <- suppressWarnings(as.numeric(game_id))
  if (!is.finite(gid)) gid <- 0
  as.integer(MC_SEED + (abs(gid) %% 1e6) * 2 + side)
}

# Network chatter. Every failed request used to raise its own warning() (and 404s
# a message()), so a slow API turned the console into a wall of red that told you
# nothing you could act on -- the fetchers already retry and fall back. They are
# counted instead, and one line is printed per run.
.log_state$http_fail <- 0L
mlog_debug <- function(...) {
  if (identical(LOG_LEVEL, "debug")) mlog(...) else invisible(FALSE)
}
mlog_http_fail <- function(url) {
  .log_state$http_fail <- .log_state$http_fail + 1L
  mlog_debug("  http fail: ", url)
}
mlog_http_report <- function() {
  n <- .log_state$http_fail
  .log_state$http_fail <- 0L
  if (n > 0L)
    mlog(sprintf("Network    | %d request(s) failed after retries and fell back (set LOG_LEVEL=\"debug\" for URLs)", n))
  invisible(n)
}

# Run an expression with all model logging suppressed (used by the backfills).
with_quiet_log <- function(expr) {
  old <- .log_state$quiet
  .log_state$quiet <- TRUE
  on.exit({ .log_state$quiet <- old; .log_state$last <- "" }, add = TRUE)
  force(expr)
}

MLB_API_BASE    <- "https://statsapi.mlb.com/api/v1"
SAVANT_BASE     <- "https://baseballsavant.mlb.com"
FIP_CONSTANT    <- 3.10
DEFAULT_TIMEOUT <- 25
HTTP_RETRIES    <- 3
RETRY_BACKOFF   <- 1.6
MC_SIMS         <- 25000L
MC_SEED         <- 2025L

LG_AVG_WOBA          <- 0.312
LG_AVG_XWOBA         <- 0.310
LG_AVG_ERA           <- 4.35
LG_AVG_FIP           <- 4.20
LG_AVG_HR_PER_PA     <- 0.030
LG_AVG_RUNS_PER_GAME <- 4.45
LG_AVG_BB_PCT        <- 0.100
LG_AVG_K_PCT         <- 0.228
LG_AVG_SB_PER_G      <- 0.62
LG_AVG_BARREL_PCT    <- 0.076
LG_AVG_HARD_HIT_PCT  <- 0.380
LG_AVG_GB_PCT        <- 0.438
LG_AVG_FB_PCT        <- 0.352
LG_AVG_PULL_PCT      <- 0.400
LG_AVG_SPRINT_SPEED  <- 27.0
LG_AVG_EXIT_VELO     <- 88.3
LG_AVG_LAUNCH_ANGLE  <- 11.8
LG_AVG_WHIFF_PCT     <- 0.242
HOME_FIELD_EDGE      <- 0.026

LG_AVG_PITCHES_PER_IP  <- 16.0
HIGH_WORKLOAD_PIP      <- 17.5
CRITICAL_WORKLOAD_PIP  <- 19.0
PITCH_EFF_ERA_MULT     <- 1.18

WHIP_GATE_DIFF  <- 0.40
WHIP_GATE_BOOST <- 0.065

BB_COLLAPSE_THRESHOLD   <- 0.120
BB_COLLAPSE_ERA_MULT    <- 1.30
BB_GAME_CLIFF_THRESHOLD <- 3

SIERA_W_XFIP  <- 0.35
SIERA_W_FIP   <- 0.20
SIERA_W_SIERA <- 0.35
SIERA_W_ERA   <- 0.10

ERA_RAW_BLEND_W  <- 0.25
ERA_XERA_BLEND_W <- 0.75

KBB_RUN_MODEL_SENSITIVITY <- 2.8

NB_SHAPE_DEFAULT      <- 8.0
NB_SHAPE_HIGH_OFFENSE <- 5.5

PITCHING_OUTCOME_WEIGHT  <- 0.70
STARTER_VS_BULLPEN_SPLIT <- 0.68

SP_ERA_AVG_SPLIT            <- 4.50
SP_BATAVG_SENSITIVITY       <- 0.90
SP_ISO_SUPPRESSION_ELITE    <- 0.72
SP_ISO_SUPPRESSION_GOOD     <- 0.85
SP_ISO_BOOST_STRUGGLING     <- 1.28
SP_WOBA_SUPPRESSION_ELITE   <- 0.84
SP_WOBA_BOOST_STRUGGLING    <- 1.22
SP_ERA_ELITE_THRESHOLD      <- 3.0
SP_ERA_GOOD_THRESHOLD       <- 4.0
SP_ERA_STRUGGLING_THRESHOLD <- 7.0
SP_BB_CLIFF_THRESHOLD       <- 3
SP_K9_DOMINANCE_THRESHOLD   <- 10.0
SP_WHIFF_ELITE              <- 0.280
SP_WHIFF_POOR               <- 0.200
SP_VELO_SUPPRESSION <- list(
  elite_plus = 0.85, elite = 0.90, above = 0.95,
  avg = 1.00, below = 1.06, soft = 1.14)

ISO_POWER_THRESHOLD  <- 0.175
ISO_ELITE_THRESHOLD  <- 0.215
MIN_PA_SEASON        <- 50
MIN_PA_RECENT        <- 15
MIN_IP_PITCHER       <- 5
MIN_IP_SEASON        <- 20
MIN_PA_BAYES_PRIOR   <- 50
EARLY_SEASON_GAMES   <- 15

STARTER_INNINGS_DEFAULT <- 5.0
RELIEVER_INNINGS_GAME   <- 4.0
BULLPEN_FATIGUE_DAYS    <- 3
N_RECENT_STARTS         <- 3

SERIES_MOMENTUM_BOOST       <- 0.018
EXTRA_INN_VARIANCE_MULT     <- 1.12
EXTRA_INN_WIN_PULL          <- 0.030
CLOSE_GAME_THRESHOLD        <- 0.50
PYTHAG_REGRESSION_THRESHOLD <- 4.0
PYTHAG_REGRESSION_STRENGTH  <- 0.04
LG_AVG_LOB_PCT              <- 0.720
LOB_RUN_SENSITIVITY         <- 3.2
FIRST_INN_ERA_WEIGHT        <- 0.15
BULLPEN_PLATOON_SENSITIVITY <- 0.08

OPS_WIN_WEIGHT         <- 0.28
OPS_RUN_TRANSLATION    <- 14.0
ISO_CLUSTER_THRESHOLD  <- 0.300
ISO_CLUSTER_HR_BOOST   <- 1.35
WHIP_WIN_CORRELATION   <- 0.88
SLG_HR_THRESHOLD       <- 0.600
SLG_HR_CLUSTER_MULT    <- 1.28

LINEUP_PA_BY_SLOT <- c(4.72, 4.51, 4.41, 4.32, 4.12, 3.92, 3.81, 3.71, 3.61)

WOBA_WEIGHTS <- list(bb=0.690, hbp=0.720, single=0.888, double=1.271,
                     triple=1.616, hr=2.101)
PLATOON_WOBA_MULT <- list(LL=0.935, LR=1.050, RL=1.055, RR=0.980,
                          SL=1.055, SR=1.045)
PLATOON_HR_RATE   <- list(LL=0.025, LR=0.029, RL=0.030, RR=0.027,
                          SL=0.030, SR=0.025)
REGRESS_PA <- list(power=120L, balanced=200L, contact=300L)
TTO_HR_MULTIPLIERS <- c(0.88, 1.10, 1.32)

VELO_TIERS <- list(
  elite_plus=list(min=97.0, hr_factor=0.76, name="elite_plus"),
  elite     =list(min=94.0, hr_factor=0.84, name="elite"),
  above     =list(min=91.0, hr_factor=0.94, name="above"),
  avg       =list(min=88.0, hr_factor=1.00, name="avg"),
  below     =list(min=85.0, hr_factor=1.12, name="below"),
  soft      =list(min=0.0,  hr_factor=1.26, name="soft"))

BATTER_VELO_ADJUSTMENT <- list(
  power   =list(vs_elite=0.93, vs_soft=1.20),
  balanced=list(vs_elite=0.86, vs_soft=1.09),
  contact =list(vs_elite=0.78, vs_soft=1.04))

ARSENAL_HR_FACTORS <- list(fb_heavy=1.12, fb_balanced=1.00,
                           breaking=0.89, offspeed=0.86, mixed=0.96)

UMPIRE_ADJUSTMENTS <- list(
  "Hernandez" =list(k_delta= 0.018, bb_delta=-0.010, runs_delta=-0.14),
  "Meals"     =list(k_delta=-0.012, bb_delta= 0.008, runs_delta= 0.12),
  "Tumpane"   =list(k_delta= 0.016, bb_delta=-0.008, runs_delta=-0.12),
  "Kulpa"     =list(k_delta= 0.014, bb_delta=-0.007, runs_delta=-0.10),
  "Cederstrom"=list(k_delta=-0.010, bb_delta= 0.006, runs_delta= 0.09),
  "Nauert"    =list(k_delta= 0.013, bb_delta=-0.007, runs_delta=-0.08),
  "Carlson"   =list(k_delta=-0.015, bb_delta= 0.009, runs_delta= 0.14),
  "Winters"   =list(k_delta= 0.011, bb_delta=-0.006, runs_delta=-0.08),
  "Gibson"    =list(k_delta=-0.010, bb_delta= 0.005, runs_delta= 0.08),
  "Barrett"   =list(k_delta= 0.008, bb_delta=-0.004, runs_delta=-0.06),
  "Wegner"    =list(k_delta= 0.007, bb_delta=-0.004, runs_delta=-0.05),
  "Eddings"   =list(k_delta=-0.011, bb_delta= 0.007, runs_delta= 0.11),
  "Welke"     =list(k_delta= 0.005, bb_delta=-0.003, runs_delta=-0.04),
  "Miller"    =list(k_delta=-0.008, bb_delta= 0.005, runs_delta= 0.07),
  "West"      =list(k_delta= 0.010, bb_delta=-0.005, runs_delta=-0.07))

PARK_FACTORS <- list(
  "Angel Stadium"               =list(runs=0.99,hr=1.01,hr_L=1.00,hr_R=1.02,dome=FALSE,pull_sens=0.8, altitude=160),
  "Busch Stadium"               =list(runs=0.93,hr=0.84,hr_L=0.82,hr_R=0.86,dome=FALSE,pull_sens=0.7, altitude=465),
  "Chase Field"                 =list(runs=0.95,hr=0.87,hr_L=0.88,hr_R=0.86,dome=TRUE, pull_sens=0.6, altitude=1082),
  "Citi Field"                  =list(runs=0.89,hr=1.05,hr_L=1.08,hr_R=1.02,dome=FALSE,pull_sens=0.9, altitude=15),
  "Citizens Bank Park"          =list(runs=1.06,hr=1.22,hr_L=1.20,hr_R=1.24,dome=FALSE,pull_sens=1.0, altitude=20),
  "Comerica Park"               =list(runs=1.02,hr=0.96,hr_L=0.94,hr_R=0.98,dome=FALSE,pull_sens=0.6, altitude=600),
  "Coors Field"                 =list(runs=1.27,hr=1.21,hr_L=1.22,hr_R=1.20,dome=FALSE,pull_sens=0.7, altitude=5200),
  "Dodger Stadium"              =list(runs=0.92,hr=1.24,hr_L=1.30,hr_R=1.18,dome=FALSE,pull_sens=0.9, altitude=512),
  "Fenway Park"                 =list(runs=1.11,hr=0.97,hr_L=1.15,hr_R=0.82,dome=FALSE,pull_sens=1.3, altitude=20),
  "Globe Life Field"            =list(runs=0.97,hr=0.96,hr_L=0.95,hr_R=0.97,dome=TRUE, pull_sens=0.6, altitude=551),
  "Great American Ball Park"    =list(runs=1.07,hr=1.28,hr_L=1.25,hr_R=1.31,dome=FALSE,pull_sens=1.1, altitude=490),
  "Guaranteed Rate Field"       =list(runs=0.98,hr=1.12,hr_L=1.10,hr_R=1.14,dome=FALSE,pull_sens=0.9, altitude=595),
  "Kauffman Stadium"            =list(runs=1.02,hr=0.84,hr_L=0.83,hr_R=0.85,dome=FALSE,pull_sens=0.6, altitude=750),
  "loanDepot park"              =list(runs=0.90,hr=0.72,hr_L=0.70,hr_R=0.74,dome=TRUE, pull_sens=0.5, altitude=6),
  "American Family Field"       =list(runs=1.05,hr=1.13,hr_L=1.14,hr_R=1.12,dome=TRUE, pull_sens=0.7, altitude=635),
  "Minute Maid Park"            =list(runs=1.03,hr=1.09,hr_L=1.12,hr_R=1.06,dome=TRUE, pull_sens=0.8, altitude=22),
  "Nationals Park"              =list(runs=1.04,hr=1.08,hr_L=1.06,hr_R=1.10,dome=FALSE,pull_sens=0.8, altitude=25),
  "Oracle Park"                 =list(runs=0.93,hr=0.79,hr_L=0.72,hr_R=0.86,dome=FALSE,pull_sens=0.7, altitude=0),
  "Oriole Park at Camden Yards" =list(runs=0.94,hr=0.91,hr_L=0.88,hr_R=0.94,dome=FALSE,pull_sens=0.8, altitude=20),
  "Petco Park"                  =list(runs=0.93,hr=0.97,hr_L=0.96,hr_R=0.98,dome=FALSE,pull_sens=0.7, altitude=17),
  "PNC Park"                    =list(runs=0.97,hr=0.79,hr_L=0.80,hr_R=0.78,dome=FALSE,pull_sens=0.6, altitude=730),
  "Progressive Field"           =list(runs=1.07,hr=0.97,hr_L=0.96,hr_R=0.98,dome=FALSE,pull_sens=0.7, altitude=650),
  "Rogers Centre"               =list(runs=0.96,hr=1.12,hr_L=1.10,hr_R=1.14,dome=TRUE, pull_sens=0.7, altitude=300),
  "T-Mobile Park"               =list(runs=0.94,hr=1.03,hr_L=1.02,hr_R=1.04,dome=TRUE, pull_sens=0.7, altitude=0),
  "Target Field"                =list(runs=0.93,hr=0.86,hr_L=0.85,hr_R=0.87,dome=FALSE,pull_sens=0.6, altitude=830),
  "Truist Park"                 =list(runs=1.08,hr=0.93,hr_L=0.92,hr_R=0.94,dome=FALSE,pull_sens=0.7, altitude=1050),
  "Wrigley Field"               =list(runs=0.99,hr=0.98,hr_L=0.97,hr_R=0.99,dome=FALSE,pull_sens=0.9, altitude=595),
  "Yankee Stadium"              =list(runs=0.98,hr=1.20,hr_L=1.45,hr_R=1.05,dome=FALSE,pull_sens=1.5, altitude=55),
  "Sutter Health Park"          =list(runs=1.18,hr=1.60,hr_L=1.58,hr_R=1.62,dome=FALSE,pull_sens=0.9, altitude=25),
  "George M. Steinbrenner Field"=list(runs=1.02,hr=1.30,hr_L=1.50,hr_R=1.15,dome=FALSE,pull_sens=1.2, altitude=10),
  "Oakland Coliseum"            =list(runs=0.91,hr=0.80,hr_L=0.79,hr_R=0.81,dome=FALSE,pull_sens=0.6, altitude=0),
  "Tropicana Field"             =list(runs=0.96,hr=1.00,hr_L=0.99,hr_R=1.01,dome=TRUE, pull_sens=0.7, altitude=0))

# Regular-season opening dates (first game that counts). 2026 opened with a single
# game on Mar 25; 2025 with the Tokyo Series on Mar 18. Anything earlier is spring
# training or an exhibition and never enters a ledger, a fit or a backfill.
SEASON_START <- list(
  "2027"=as.Date("2027-03-25"),
  "2026"=as.Date("2026-03-25"), "2025"=as.Date("2025-03-18"),
  "2024"=as.Date("2024-03-20"), "2023"=as.Date("2023-03-30"),
  "2022"=as.Date("2022-04-07"))

# Game types that are never projected or learned from: spring training, exhibitions
# and the All-Star game. Regular season (R) and postseason (F/D/L/W) are kept.
MLB_SKIP_GAME_TYPES <- c("S", "E", "A")

mlb_season_start <- function(season) {
  s <- SEASON_START[[as.character(season)]]
  if (is.null(s)) as.Date(paste0(season, "-03-25")) else s
}

# TRUE for ledger rows that belong to the regular season or postseason (drops the
# spring-training and exhibition rows that older versions wrote to the ledger).
mlb_competitive_rows <- function(h) {
  if (is.null(h) || !nrow(h) || !("GameDate" %in% names(h))) return(rep(TRUE, NROW(h)))
  d <- suppressWarnings(as.Date(as.character(h$GameDate)))
  yr <- suppressWarnings(as.integer(format(d, "%Y")))
  st <- rep(as.Date(NA), length(d))
  for (y in unique(yr[!is.na(yr)])) st[which(yr == y)] <- mlb_season_start(y)
  ok <- !is.na(d) & !is.na(st) & d >= st
  if ("GameType" %in% names(h)) ok <- ok & !(as.character(h$GameType) %in% MLB_SKIP_GAME_TYPES)
  ok
}

HOT_COLD_STREAK_WEIGHT <- list(last7=0.50, last14=0.30, season=0.20)

.fetch_cache   <- new.env(hash=TRUE, parent=emptyenv())
.savant_cache  <- new.env(hash=TRUE, parent=emptyenv())
.gamelog_cache <- new.env(hash=TRUE, parent=emptyenv())
.calib_store   <- new.env(hash=TRUE, parent=emptyenv())
.calib_store$log <- list()

LEGEND_TERMS <- list(
  list(abbr="ERA",   full="Earned Run Average",                       cat="Pitching"),
  list(abbr="FIP",   full="Fielding Independent Pitching",            cat="Pitching"),
  list(abbr="xFIP",  full="Expected FIP (normalises HR/FB rate)",     cat="Pitching"),
  list(abbr="SIERA", full="Skill-Interactive ERA",                    cat="Pitching"),
  list(abbr="WHIP",  full="Walks + Hits per Inning Pitched",          cat="Pitching"),
  list(abbr="K%",    full="Strikeout Percentage",                     cat="Pitching"),
  list(abbr="BB%",   full="Walk Percentage (per batter faced)",       cat="Pitching"),
  list(abbr="GB%",   full="Ground Ball Percentage",                   cat="Pitching"),
  list(abbr="FB%",   full="Fly Ball Percentage",                      cat="Pitching"),
  list(abbr="TTO",   full="Times Through Order (3rd TTO penalty)",    cat="Pitching"),
  list(abbr="wOBA",  full="Weighted On-Base Average",                 cat="Hitting"),
  list(abbr="ISO",   full="Isolated Power (SLG minus AVG)",           cat="Hitting"),
  list(abbr="SLG",   full="Slugging Percentage",                      cat="Hitting"),
  list(abbr="OBP",   full="On-Base Percentage",                       cat="Hitting"),
  list(abbr="OPS",   full="On-Base plus Slugging",                    cat="Hitting"),
  list(abbr="BABIP", full="Batting Average on Balls In Play",         cat="Hitting"),
  list(abbr="PA",    full="Plate Appearances",                        cat="Hitting"),
  list(abbr="SB",    full="Stolen Bases",                             cat="Hitting"),
  list(abbr="NRFI",  full="No Run First Inning \u2014 neither team scores in the 1st", cat="First Inning"),
  list(abbr="YRFI",  full="Yes Run First Inning \u2014 at least one run scores",       cat="First Inning"),
  list(abbr="F1",    full="First inning only (projected runs, both halves)",         cat="First Inning"),
  list(abbr="Top/Bot", full="P(scoreless) for the away half / home half",            cat="First Inning"),
  list(abbr="Edge",  full="Points above or below the league NRFI base rate",         cat="First Inning"),
  list(abbr="Log5",  full="Odds-ratio method merging batter and pitcher rates",      cat="First Inning"),
  list(abbr="LU\u2713", full="Lineup confirmed by the club (not estimated)",         cat="First Inning"),
  list(abbr="thinSP", full="Starter under the innings threshold \u2014 rates regressed hard", cat="First Inning"),
  list(abbr="Pyth",  full="Pythagorean Win%",                         cat="Model"),
  list(abbr="O/U",   full="Projected total runs (park and weather included)", cat="Model"),
  list(abbr="HFE",   full="Home field: home team +3% runs, road team -3% (inside the run model)", cat="Model"),
  list(abbr="Conf",  full="Confidence level (High/Med/Low)",          cat="Model"),
  list(abbr="PIT",   full="Point-in-time: inputs use only games before date D", cat="Integrity"),
  list(abbr="No-H2H",full="Batter-vs-pitcher removed (was target leakage)",      cat="Integrity"),
  list(abbr="SC-off",full="Statcast off (season aggregates can't be point-in-time)", cat="Integrity"),
  list(abbr="Spring",full="Spring training, exhibitions and the All-Star game are never projected or learned from", cat="Integrity")
)

scalar <- function(x, default=NULL) {
  if (is.null(x) || length(x) == 0L) return(default)
  v <- x[[1L]]
  if (length(v) == 0L) return(default)
  if (length(v) > 1L)  v <- v[[1L]]
  if (is.na(v))        return(default)
  v
}
`%||%` <- function(a, b) if (is.null(a) || length(a) == 0L) b else a
coerce_numeric <- function(x, default=0.0) {
  v <- suppressWarnings(as.numeric(x)); v[is.na(v)] <- default; v
}
clamp <- function(x, lo, hi) pmax(pmin(x, hi), lo)
clean_player_id <- function(x) {
  if (is.null(x) || length(x) == 0L) return(NA_integer_)
  id <- suppressWarnings(as.integer(as.numeric(x[[1L]])))
  if (is.na(id)) NA_integer_ else id
}
parse_innings_pitched <- function(ip_str) {
  tryCatch({
    s <- as.character(scalar(ip_str, "0"))
    if (grepl("\\.", s)) {
      p <- strsplit(s, "\\.")[[1L]]
      as.numeric(p[1L]) + as.numeric(p[2L]) / 3
    } else as.numeric(s)
  }, error=function(e) 0.0)
}
cache_key <- function(url) {
  k <- gsub("[^A-Za-z0-9]", ".", as.character(url))
  k <- gsub("\\.{2,}", ".", k)
  if (!grepl("^[A-Za-z]", k)) k <- paste0("k.", k)
  k
}
safe_val <- function(x, default=NA_real_) {
  if (is.null(x) || length(x) != 1 || is.na(x)) default else x
}

# ===== POINT-IN-TIME CORE (identical to unit-tested pit_core.R) =====
filter_splits_before <- function(splits, cutoff_date, last_n = NULL) {
  if (!length(splits)) return(list())
  cutoff_date <- as.Date(cutoff_date)
  dates <- suppressWarnings(as.Date(vapply(
    splits, function(s) as.character(scalar(s[["date"]], "0000-01-01")), character(1L))))
  keep   <- !is.na(dates) & dates < cutoff_date
  splits <- splits[keep]; dates <- dates[keep]
  if (!length(splits)) return(list())
  ord    <- order(dates, decreasing = TRUE)
  splits <- splits[ord]
  if (!is.null(last_n) && last_n > 0L && length(splits) > last_n)
    splits <- splits[seq_len(last_n)]
  splits
}
days_rest_before <- function(splits, cutoff_date, default = 5L) {
  pre <- filter_splits_before(splits, cutoff_date)
  if (!length(pre)) return(default)
  last_date <- suppressWarnings(as.Date(scalar(pre[[1L]][["date"]], NA)))
  if (is.na(last_date)) return(default)
  as.integer(as.Date(cutoff_date) - last_date)
}

http_get_json <- function(url, timeout=DEFAULT_TIMEOUT, retries=HTTP_RETRIES,
                          backoff=RETRY_BACKOFF, silent_404=FALSE) {
  if (!is.character(url) || length(url) != 1L || nchar(trimws(url)) == 0L) {
    mlog_debug("  http skip: empty url"); return(NULL)
  }
  key <- cache_key(url)
  if (exists(key, envir=.fetch_cache, inherits=FALSE))
    return(get(key, envir=.fetch_cache, inherits=FALSE))
  cls <- mlb_url_class(url)
  cached <- mlb_disk_read(url, cls)
  if (!is.null(cached)) {
    .mlb_disk$hits <- .mlb_disk$hits + 1L
    assign(key, cached, envir=.fetch_cache); return(cached)
  }
  if (isTRUE(.mlb_disk$dead)) return(mlb_disk_read(url, cls, stale_ok = TRUE))   # offline: last copy
  .mlb_disk$miss <- .mlb_disk$miss + 1L
  last_err <- NULL
  for (attempt in seq_len(retries)) {
    result <- tryCatch({
      resp <- GET(url, httr::timeout(timeout))
      if (status_code(resp) == 404L) {
        if (!silent_404) mlog_debug("  http 404: ", url); return(NULL)
      }
      stop_for_status(resp)
      content(resp, as="parsed", type="application/json", simplifyVector=FALSE)
    }, error=function(e) { last_err <<- e; NULL })
    if (!is.null(result)) {
      .mlb_disk$fail <- 0L
      mlb_disk_write(url, result, cls)
      assign(key, result, envir=.fetch_cache); return(result)
    }
    Sys.sleep(backoff^(attempt - 1L))
  }
  .mlb_disk$fail <- .mlb_disk$fail + 1L
  if (.mlb_disk$fail >= MLB_DEAD_AFTER && !isTRUE(.mlb_disk$dead)) {
    .mlb_disk$dead <- TRUE
    mlog("Network    | the MLB API is not reachable; serving cached data only")
  }
  mlog_http_fail(url)
  mlb_disk_read(url, cls, stale_ok = TRUE)          # last saved copy, or NULL if never fetched
}

http_get_csv <- function(url, timeout=35) {
  key <- paste0("csv.", cache_key(url))
  if (exists(key, envir=.savant_cache, inherits=FALSE))
    return(get(key, envir=.savant_cache, inherits=FALSE))
  cached <- mlb_disk_read(url, "day")
  if (!is.null(cached)) {
    .mlb_disk$hits <- .mlb_disk$hits + 1L
    assign(key, cached, envir=.savant_cache); return(cached)
  }
  if (isTRUE(.mlb_disk$dead)) return(NULL)
  .mlb_disk$miss <- .mlb_disk$miss + 1L
  result <- tryCatch({
    resp <- GET(url, httr::timeout(timeout),
                add_headers("User-Agent"="Mozilla/5.0 (compatible; R/4.x)"))
    if (status_code(resp) != 200) return(NULL)
    raw_text <- content(resp, as="text", encoding="UTF-8")
    if (nchar(raw_text) < 50) return(NULL)
    read.csv(text=raw_text, stringsAsFactors=FALSE)
  }, error=function(e) NULL)
  if (!is.null(result) && nrow(result) > 0) {
    mlb_disk_write(url, result, "day")
    assign(key, result, envir=.savant_cache)
  }
  result
}

clear_cache <- function() {
  rm(list=ls(envir=.fetch_cache),  envir=.fetch_cache)
  rm(list=ls(envir=.savant_cache), envir=.savant_cache)
  # NOTE: .gamelog_cache (season-long player/team logs, rosters, batsides) is NOT
  # cleared \u2014 it's season-to-date and filtered point-in-time at read, so it serves
  # any selected date. Clearing it would refetch hundreds of player logs per date
  # change. Live scores/boxscores live in .fetch_cache and still refresh.
}

api_has_splits <- function(data) {
  if (is.null(data)) return(FALSE)
  stats <- data[["stats"]]
  if (is.null(stats) || length(stats) == 0L) return(FALSE)
  any(vapply(stats, function(g) length(g[["splits"]] %||% list()) > 0L, logical(1L)))
}

resolve_seasons <- function(query_date=Sys.Date()) {
  query_date   <- as.Date(query_date)
  current_year <- as.integer(format(query_date, "%Y"))
  primary_year <- current_year - 1L
  for (y in seq(current_year, 2022L, by=-1L)) {
    start <- SEASON_START[[as.character(y)]]
    if (!is.null(start) && query_date >= start) { primary_year <- y; break }
  }
  primary_start <- SEASON_START[[as.character(primary_year)]]
  days_in <- if (!is.null(primary_start)) as.integer(query_date - primary_start) else 999L
  fallback <- if (days_in < EARLY_SEASON_GAMES * 3) as.character(primary_year - 1L) else NULL
  list(primary=as.character(primary_year), fallback=fallback,
       days_in=days_in, use_prior_only=(days_in < 3))
}

season_blend_weight <- function(days_in) clamp(1 / (1 + exp(-0.08 * (days_in - 30))), 0, 1)

blend_season_df <- function(df_cur, df_prior, weight_cur, join_col="Team") {
  if (is.null(df_prior) || nrow(df_prior) == 0L) return(df_cur)
  if (is.null(df_cur)   || nrow(df_cur)   == 0L) return(df_prior)
  if (weight_cur >= 1) return(df_cur)
  if (weight_cur <= 0) return(df_prior)
  num_cols <- setdiff(names(df_cur)[sapply(df_cur, is.numeric)], join_col)
  merged   <- merge(df_cur, df_prior, by=join_col, suffixes=c("", ".pr"), all=TRUE)
  for (col in num_cols) {
    cv <- merged[[col]]; pv <- merged[[paste0(col, ".pr")]]
    cv[is.na(cv)] <- pv[is.na(cv)]; pv[is.na(pv)] <- cv[is.na(pv)]
    merged[[col]] <- weight_cur * cv + (1 - weight_cur) * pv
  }
  merged[, names(df_cur), drop=FALSE]
}

# Venue names change with sponsorships. Before this map, three home parks had silently
# fallen out of the table (Astros, White Sox, Dodgers -- 243 home games a year), so their
# park factor, roof flag and HR factors all defaulted to neutral.
PARK_ALIASES <- c(
  "Daikin Park"                    = "Minute Maid Park",
  "Rate Field"                     = "Guaranteed Rate Field",
  "UNIQLO Field at Dodger Stadium" = "Dodger Stadium")
PARK_FACTORS[["Estadio Alfredo Harp Helu"]] <-
  list(runs=1.15, hr=1.25, hr_L=1.25, hr_R=1.25, dome=FALSE, pull_sens=0.8, altitude=7350)
PARK_RUN_ELASTICITY <- 0.70   # measured on 2026 games: listed run factors overstate the effect
park_key <- function(venue_name) {
  v <- as.character(venue_name %||% "")
  if (length(v) != 1L || is.na(v)) return("")
  if (!is.null(PARK_FACTORS[[v]])) return(v)
  a <- PARK_ALIASES[v]
  if (!is.na(a)) return(unname(a))
  v
}
get_park_factor <- function(venue_name, stat="runs") {
  pf <- PARK_FACTORS[[park_key(venue_name)]]; if (is.null(pf)) return(1.0)
  val <- pf[[stat]]; if (is.null(val)) 1.0 else as.numeric(val)
}
is_dome <- function(venue_name) {
  pf <- PARK_FACTORS[[park_key(venue_name)]]; isTRUE(pf[["dome"]])
}
altitude_hr_factor <- function(alt_ft) clamp(1.0 + (alt_ft / 5200) * 0.18, 1.0, 1.18)
get_park_hr_factor <- function(venue_name, bat_hand="R", pull_pct=LG_AVG_PULL_PCT) {
  pf <- PARK_FACTORS[[park_key(venue_name)]]; if (is.null(pf)) return(1.0)
  bh  <- toupper(substr(as.character(bat_hand), 1, 1))
  key <- if (bh == "L") "hr_L" else "hr_R"
  base_factor <- as.numeric(pf[[key]] %||% pf[["hr"]] %||% 1.0)
  pull_sens   <- as.numeric(pf[["pull_sens"]] %||% 0.8)
  pull_delta  <- (pull_pct - LG_AVG_PULL_PCT) * pull_sens
  # The listed HR factors are measured at each park, so altitude is already inside
  # them. Multiplying by an altitude factor again counted Coors twice (1.21 x 1.18).
  clamp(base_factor * (1.0 + pull_delta), 0.50, 2.80)
}
get_park_nb_shape <- function(venue_name) {
  pf <- get_park_factor(venue_name, "runs")
  if (!is.na(pf) && pf > 1.10) NB_SHAPE_HIGH_OFFENSE else NB_SHAPE_DEFAULT
}

# The MLB API sends weather as {condition, temp, wind = "8 mph, Out To CF"}. The old
# parser read temperature/windSpeed/windDirection, which do not exist, so every game
# got the neutral default. Effects below were measured on the 2026 regular season
# (2,354 games): runs +0.44%/degF, +0.68%/mph blowing out, -0.45%/mph blowing in;
# home runs +0.86%/degF and -1.2%/mph blowing in (blowing out showed no measurable lift).
WX_RUNS_TEMP <- 0.0044; WX_RUNS_OUT <- 0.0068; WX_RUNS_IN <- 0.0045
WX_HR_TEMP   <- 0.0086; WX_HR_OUT   <- 0.0030; WX_HR_IN   <- 0.0121
parse_mlb_weather <- function(weather) {
  if (!is.list(weather) || length(weather) == 0L) return(NULL)
  temp <- suppressWarnings(as.numeric(scalar(weather[["temp"]] %||% weather[["temperature"]], NA)))
  wind <- tolower(as.character(scalar(weather[["wind"]], "")))
  spd  <- suppressWarnings(as.numeric(sub("^\\s*([0-9]+(\\.[0-9]+)?)\\s*mph.*$", "\\1", wind)))
  if (!is.finite(spd)) spd <- suppressWarnings(as.numeric(scalar(weather[["windSpeed"]], 0)))
  dir  <- trimws(sub("^[^,]*,", "", wind))
  if (!nzchar(dir) || identical(dir, wind))
    dir <- tolower(as.character(scalar(weather[["windDirection"]], "")))
  cond <- tolower(as.character(scalar(weather[["condition"]], "")))
  list(temp = if (is.finite(temp)) temp else 70, spd = if (is.finite(spd)) spd else 0,
       out = grepl("^out", dir), inn = grepl("^in\\b|^in ", dir),
       roof = grepl("roof closed|dome", cond))
}
advanced_weather_adjustment <- function(weather, venue_name=NULL) {
  w <- tryCatch(parse_mlb_weather(weather), error = function(e) NULL)
  roof_closed <- !is.null(w) && isTRUE(w$roof)
  # Parks with a roof are treated as neutral (as in the measurement), and so is any
  # game the API reports as "Roof Closed" or "Dome".
  if ((!is.null(venue_name) && is_dome(venue_name)) || roof_closed)
    return(list(runs=1.0, hr=1.0, dome=TRUE))
  if (is.null(w)) return(list(runs=1.0, hr=1.0, dome=FALSE))
  dt <- w$temp - 70
  out_s <- if (isTRUE(w$out)) w$spd else 0; in_s <- if (isTRUE(w$inn)) w$spd else 0
  runs <- exp(WX_RUNS_TEMP*dt + WX_RUNS_OUT*out_s - WX_RUNS_IN*in_s)
  hr   <- exp(WX_HR_TEMP*dt   + WX_HR_OUT*out_s   - WX_HR_IN*in_s)
  list(runs=clamp(runs, 0.80, 1.25), hr=clamp(hr, 0.65, 1.45), dome=FALSE,
       temp=w$temp, wind=w$spd, out=isTRUE(w$out), inn=isTRUE(w$inn))
}

# Matches the umpire's LAST NAME exactly. The old substring test let a table key match
# any name that merely contained it.
get_umpire_adjustment <- function(umpire_name) {
  none <- list(k_delta=0.0, bb_delta=0.0, runs_delta=0.0)
  if (is.null(umpire_name) || length(umpire_name) != 1L || is.na(umpire_name) ||
      nchar(umpire_name) == 0L) return(none)
  parts <- strsplit(trimws(as.character(umpire_name)), "\\s+")[[1L]]
  last  <- tolower(parts[length(parts)])
  if (last %in% c("jr.", "jr", "sr.", "sr", "ii", "iii") && length(parts) > 1L)
    last <- tolower(parts[length(parts) - 1L])
  hit <- names(UMPIRE_ADJUSTMENTS)[tolower(names(UMPIRE_ADJUSTMENTS)) == last]
  if (length(hit)) UMPIRE_ADJUSTMENTS[[hit[1L]]] else none
}

platoon_key <- function(bat_hand, pitcher_hand) {
  bh <- toupper(substr(as.character(bat_hand), 1, 1))
  ph <- toupper(substr(as.character(pitcher_hand), 1, 1))
  if (bh == "S") return(paste0("S", ph))
  if (bh %in% c("L","R") && ph %in% c("L","R")) paste0(bh, ph) else "RR"
}
platoon_woba_mult   <- function(bh, ph) PLATOON_WOBA_MULT[[platoon_key(bh, ph)]] %||% 1.0
platoon_hr_rate_val <- function(bh, ph) PLATOON_HR_RATE[[platoon_key(bh, ph)]] %||% LG_AVG_HR_PER_PA
effective_bat_hand  <- function(bat_hand, pitcher_hand) {
  bh <- toupper(substr(as.character(bat_hand), 1, 1))
  ph <- toupper(substr(as.character(pitcher_hand), 1, 1))
  if (bh == "S") (if (ph == "R") "L" else "R") else bh
}
player_type <- function(iso) {
  if (is.null(iso) || is.na(iso)) return("balanced")
  if (iso >= ISO_ELITE_THRESHOLD) "power"
  else if (iso >= 0.155) "balanced"
  else "contact"
}
regress_to_mean <- function(observed, pa, lg_avg, type="balanced") {
  rpa <- REGRESS_PA[[type]] %||% 200L
  w   <- pa / (pa + rpa)
  w * observed + (1 - w) * lg_avg
}
blend_value <- function(base_val, recent_val, weight=0.35, recent_n=NULL, min_n=30) {
  if (is.null(recent_val) || length(recent_val) != 1L || !is.finite(recent_val))
    return(base_val)
  eff_weight <- if (!is.null(recent_n) && recent_n < min_n) weight*(recent_n/min_n) else weight
  (1 - eff_weight)*base_val + eff_weight*recent_val
}
streak_blend_hr_rate <- function(rate_season, pa_season, recent_rate=NULL, recent_pa=0) {
  if (!is.null(recent_rate) && recent_pa >= MIN_PA_RECENT) {
    w_r <- clamp(recent_pa / 60, 0, 0.30)
    return((1 - w_r) * rate_season + w_r * recent_rate)
  }
  rate_season
}

ops_win_probability_adjustment <- function(team_ops, opp_ops) {
  if (is.null(team_ops) || is.null(opp_ops)) return(0.0)
  if (is.na(team_ops) || is.na(opp_ops)) return(0.0)
  ops_diff <- team_ops - opp_ops
  clamp(ops_diff * OPS_WIN_WEIGHT * 1.8, -0.18, 0.18)
}
iso_cluster_hr_boost <- function(team_iso, team_slg) {
  iso_boost <- if (!is.null(team_iso) && !is.na(team_iso) && team_iso >= ISO_CLUSTER_THRESHOLD)
    ISO_CLUSTER_HR_BOOST else 1.0
  slg_boost <- if (!is.null(team_slg) && !is.na(team_slg) && team_slg >= SLG_HR_THRESHOLD)
    SLG_HR_CLUSTER_MULT else 1.0
  max(iso_boost, slg_boost)
}
compute_pythag_regression_factor <- function(actual_wpct, pyth_wpct, games_played) {
  if (games_played < 20) return(1.0)
  win_delta <- (actual_wpct - pyth_wpct) * games_played
  if (abs(win_delta) < PYTHAG_REGRESSION_THRESHOLD) return(1.0)
  adj <- -sign(win_delta) * PYTHAG_REGRESSION_STRENGTH *
    clamp((abs(win_delta) - PYTHAG_REGRESSION_THRESHOLD) / 4, 0, 1)
  clamp(1.0 + adj, 0.88, 1.12)
}
compute_babip_luck_adj <- function(season_babip, xbabip=NULL, rolling_games=5) {
  expected_babip <- xbabip %||% 0.296
  delta <- clamp(season_babip - expected_babip, -0.060, 0.060)
  confidence <- clamp(rolling_games / 30, 0.1, 1.0)
  regression_pull <- -delta * 0.40 * confidence
  clamp(1.0 + regression_pull, 0.85, 1.15)
}
compute_lob_adjustment <- function(team_lob_pct) {
  if (is.null(team_lob_pct) || is.na(team_lob_pct)) return(1.0)
  lob <- clamp(team_lob_pct, 0.55, 0.88)
  delta <- lob - LG_AVG_LOB_PCT
  clamp(1.0 - delta * LOB_RUN_SENSITIVITY, 0.75, 1.25)
}
compute_series_modifier <- function(series_wins_home, series_wins_away, series_game_num) {
  if (is.null(series_game_num) || series_game_num <= 1L)
    return(list(home=0.0, away=0.0))
  home_lead <- series_wins_home > series_wins_away
  away_lead <- series_wins_away > series_wins_home
  boost <- SERIES_MOMENTUM_BOOST * min(series_game_num - 1L, 2L)
  list(home = if (home_lead) boost else if (away_lead) -boost else 0.0,
       away = if (away_lead) boost else if (home_lead) -boost else 0.0)
}
apply_extra_inning_adjustment <- function(raw_hwp, h_mean, a_mean) {
  diff <- abs(h_mean - a_mean)
  if (diff >= CLOSE_GAME_THRESHOLD) return(raw_hwp)
  strength <- (1 - diff / CLOSE_GAME_THRESHOLD)
  pull <- EXTRA_INN_WIN_PULL * strength
  if (raw_hwp > 0.5) clamp(raw_hwp - pull, 0.08, 0.92)
  else               clamp(raw_hwp + pull, 0.08, 0.92)
}
blend_first_inning_era <- function(overall_era, first_inning_era=NULL) {
  if (is.null(first_inning_era) || is.na(first_inning_era)) return(overall_era)
  fi <- clamp(first_inning_era, 1.0, 12.0)
  (1 - FIRST_INN_ERA_WEIGHT) * overall_era + FIRST_INN_ERA_WEIGHT * fi
}
compute_bullpen_handedness_adj <- function(bullpen_lhp_pct, opp_lineup_lhp_pct) {
  if (is.null(bullpen_lhp_pct) || is.na(bullpen_lhp_pct)) return(1.0)
  if (is.null(opp_lineup_lhp_pct) || is.na(opp_lineup_lhp_pct)) return(1.0)
  bp  <- clamp(bullpen_lhp_pct, 0.10, 0.65)
  opp <- clamp(opp_lineup_lhp_pct, 0.20, 0.70)
  same_hand_frac <- bp * opp + (1 - bp) * (1 - opp)
  platoon_adv    <- same_hand_frac - 0.50
  clamp(1.0 - platoon_adv * BULLPEN_PLATOON_SENSITIVITY, 0.88, 1.12)
}
calc_woba <- function(bb, hbp, hits, doubles, triples, hr, ab, sf) {
  singles <- pmax(hits - doubles - triples - hr, 0)
  num <- WOBA_WEIGHTS$bb*bb + WOBA_WEIGHTS$hbp*hbp + WOBA_WEIGHTS$single*singles +
    WOBA_WEIGHTS$double*doubles + WOBA_WEIGHTS$triple*triples + WOBA_WEIGHTS$hr*hr
  den <- ab + bb + sf + hbp
  if (den > 0) num/den else LG_AVG_WOBA
}
pythagorean_winpct <- function(rs, ra, exp=1.83) {
  rs <- pmax(rs, 0.1); ra <- pmax(ra, 0.1)
  rs^exp / (rs^exp + ra^exp)
}
iso_power_multiplier <- function(iso) {
  iso <- max(iso, 0)
  if (iso >= ISO_ELITE_THRESHOLD)
    1.18 + 0.36*((iso - ISO_ELITE_THRESHOLD)/0.060)
  else if (iso >= ISO_POWER_THRESHOLD)
    1.0 + 0.18*((iso - ISO_POWER_THRESHOLD)/(ISO_ELITE_THRESHOLD - ISO_POWER_THRESHOLD))
  else max(0.72, 1.0 - 0.28*((ISO_POWER_THRESHOLD - iso)/ISO_POWER_THRESHOLD))
}
barrel_power_multiplier <- function(barrel_pct, hard_hit_pct) {
  b <- clamp(barrel_pct   %||% LG_AVG_BARREL_PCT,  0, 0.25)
  h <- clamp(hard_hit_pct %||% LG_AVG_HARD_HIT_PCT, 0.15, 0.65)
  barrel_comp <- 1.0 + (b - LG_AVG_BARREL_PCT)/LG_AVG_BARREL_PCT * 0.45
  hard_comp   <- 1.0 + (h - LG_AVG_HARD_HIT_PCT)/LG_AVG_HARD_HIT_PCT * 0.20
  clamp(barrel_comp * hard_comp, 0.55, 1.95)
}
pitcher_gb_fb_hr_factor <- function(gb_pct, fb_pct, venue_name=NULL) {
  gb <- clamp(gb_pct %||% LG_AVG_GB_PCT, 0.25, 0.65)
  fb <- clamp(fb_pct %||% LG_AVG_FB_PCT, 0.20, 0.55)
  gb_effect <- 1.0 - (gb - LG_AVG_GB_PCT) * 1.30
  fb_effect <- 1.0 + (fb - LG_AVG_FB_PCT) * 1.55
  base      <- clamp((gb_effect + fb_effect) / 2.0, 0.60, 1.65)
  park_hr   <- get_park_factor(venue_name %||% "Unknown", "hr")
  if (park_hr > 1.10 && fb > LG_AVG_FB_PCT) base <- base * 1.08
  if (park_hr < 0.90 && gb > LG_AVG_GB_PCT) base <- base * 0.94
  clamp(base, 0.55, 1.75)
}
stuff_quality_hr_factor <- function(k_pct, bb_pct) {
  kbb_diff <- clamp(k_pct - bb_pct, -0.10, 0.30)
  delta    <- kbb_diff - (LG_AVG_K_PCT - LG_AVG_BB_PCT)
  clamp(1.0 - delta * KBB_RUN_MODEL_SENSITIVITY, 0.62, 1.38)
}
kbb_starter_multiplier <- function(k_pct, bb_pct, umpire_k_delta=0.0, umpire_bb_delta=0.0) {
  eff_k  <- clamp(k_pct  + umpire_k_delta,  0.08, 0.44)
  eff_bb <- clamp(bb_pct + umpire_bb_delta, 0.02, 0.22)
  kbb    <- if (eff_bb > 0) eff_k / eff_bb else eff_k / 0.02
  lg_kbb <- LG_AVG_K_PCT / LG_AVG_BB_PCT
  ratio  <- kbb / lg_kbb
  clamp(1.0 + (ratio - 1.0) * 0.26, 0.70, 1.42)
}
walk_collapse_era_mult <- function(bb_pct, umpire_bb_delta=0.0) {
  eff_bb <- clamp(bb_pct + umpire_bb_delta, 0.02, 0.22)
  if (eff_bb >= BB_COLLAPSE_THRESHOLD) {
    severity <- clamp((eff_bb - BB_COLLAPSE_THRESHOLD) / 0.05, 0.0, 1.0)
    BB_COLLAPSE_ERA_MULT + severity * 0.18
  } else 1.0
}
pitch_efficiency_factor <- function(pitches_thrown, innings_pitched, days_rest=5) {
  if (is.null(pitches_thrown) || is.null(innings_pitched) ||
      is.na(pitches_thrown)   || is.na(innings_pitched)   || innings_pitched <= 0)
    return(1.0)
  pip     <- pitches_thrown / innings_pitched
  rest_adj <- if (!is.null(days_rest) && !is.na(days_rest) && days_rest < 4) 0.04 else 0.0
  if (pip >= CRITICAL_WORKLOAD_PIP) {
    clamp(PITCH_EFF_ERA_MULT + rest_adj + (pip - CRITICAL_WORKLOAD_PIP) * 0.02, 1.0, 1.40)
  } else if (pip >= HIGH_WORKLOAD_PIP) {
    clamp(1.0 + (pip - HIGH_WORKLOAD_PIP) / (CRITICAL_WORKLOAD_PIP - HIGH_WORKLOAD_PIP) *
            (PITCH_EFF_ERA_MULT - 1.0) * 0.6, 1.0, 1.25)
  } else if (pip < 14.0) {
    clamp(1.0 - (14.0 - pip) * 0.015, 0.88, 1.0)
  } else 1.0
}
compute_siera_proxy <- function(k_pct, bb_pct, gb_pct) {
  k  <- clamp(k_pct  %||% LG_AVG_K_PCT,  0.08, 0.42)
  bb <- clamp(bb_pct %||% LG_AVG_BB_PCT, 0.02, 0.20)
  gb <- clamp(gb_pct %||% LG_AVG_GB_PCT, 0.25, 0.65)
  siera <- 6.145 - 16.986*k + 11.434*bb - 1.858*gb +
    7.653*k*k + 6.664*bb*bb + 3.246*gb*gb - 13.045*k*bb - 3.981*gb*bb + 2.519*gb*k
  clamp(siera, 1.50, 7.50)
}
get_velo_tier_name <- function(avg_velo) {
  avg_velo <- avg_velo %||% 92.0
  for (t in VELO_TIERS) { if (avg_velo >= t$min) return(t$name) }
  "soft"
}
get_velo_hr_factor <- function(avg_velo, batter_iso=0.160, batter_ev=LG_AVG_EXIT_VELO) {
  avg_velo <- avg_velo %||% 92.0
  tier_factor <- 1.0
  for (t in VELO_TIERS) { if (avg_velo >= t$min) { tier_factor <- t$hr_factor; break } }
  ptype <- player_type(batter_iso)
  adj   <- BATTER_VELO_ADJUSTMENT[[ptype]] %||% list(vs_elite=0.86, vs_soft=1.09)
  if (avg_velo >= 97)
    tier_factor <- clamp(adj$vs_elite + (batter_ev - LG_AVG_EXIT_VELO)*0.004, 0.68, 1.05)
  else if (avg_velo >= 94)
    tier_factor <- clamp(0.84 + (batter_ev - LG_AVG_EXIT_VELO)*0.003, 0.74, 1.05)
  else if (avg_velo < 88)
    tier_factor <- clamp(adj$vs_soft + (batter_ev - LG_AVG_EXIT_VELO)*0.002, 0.95, 1.38)
  clamp(tier_factor, 0.62, 1.42)
}
get_arsenal_hr_factor <- function(fb_pct, breaking_pct=NULL, offspeed_pct=NULL) {
  fb_pct   <- clamp(fb_pct %||% 0.55, 0.20, 0.85)
  if (fb_pct >= 0.65) return(ARSENAL_HR_FACTORS$fb_heavy)
  breaking <- breaking_pct %||% (1 - fb_pct)*0.55
  offspeed  <- offspeed_pct %||% (1 - fb_pct)*0.45
  if (!is.null(breaking_pct) && breaking >= 0.45) return(ARSENAL_HR_FACTORS$breaking)
  if (!is.null(offspeed_pct) && offspeed  >= 0.35) return(ARSENAL_HR_FACTORS$offspeed)
  if (fb_pct >= 0.50) return(ARSENAL_HR_FACTORS$fb_balanced)
  ARSENAL_HR_FACTORS$mixed
}
get_tto_multiplier <- function(lineup_slot, starter_avg_ip) {
  avg_ip       <- clamp(starter_avg_ip %||% STARTER_INNINGS_DEFAULT, 3.0, 8.0)
  estimated_tto <- clamp((avg_ip / 3.0) * (lineup_slot / 9.0) + 1.0, 1.0, 3.0)
  if (estimated_tto >= 2.5) return(TTO_HR_MULTIPLIERS[3])
  if (estimated_tto >= 1.5) return(TTO_HR_MULTIPLIERS[2])
  TTO_HR_MULTIPLIERS[1]
}
hitter_count_hr_factor <- function(pitcher_bb_pct, umpire_bb_delta=0.0) {
  effective_bb <- clamp(pitcher_bb_pct + umpire_bb_delta, 0.02, 0.22)
  delta        <- clamp(effective_bb - LG_AVG_BB_PCT, -0.06, 0.12)
  clamp(1.0 + delta * 3.0, 0.80, 1.42)
}
pitcher_home_away_factor <- function(pitcher_home_era, pitcher_away_era, is_home_pitcher) {
  if (is.null(pitcher_home_era) || is.null(pitcher_away_era)) return(1.0)
  if (is.na(pitcher_home_era)   || is.na(pitcher_away_era))   return(1.0)
  if (pitcher_home_era <= 0     || pitcher_away_era <= 0)      return(1.0)
  ratio <- if (isTRUE(is_home_pitcher)) pitcher_home_era / pitcher_away_era
  else pitcher_away_era / pitcher_home_era
  clamp(ratio, 0.80, 1.25)
}
compute_bullpen_fatigue <- function(team, recent_pitching_df) {
  rp <- recent_pitching_df[recent_pitching_df$Team == team, , drop=FALSE]
  if (nrow(rp) == 0) return(1.0)
  bull_ip       <- rp$BullpenIP[1] %||% 0
  games         <- max(rp$Games[1] %||% 1, 1)
  bull_ip_per_g <- bull_ip / games
  fatigue_ratio <- bull_ip_per_g / RELIEVER_INNINGS_GAME
  clamp(1.0 + (fatigue_ratio - 1.0) * 0.15, 0.86, 1.22)
}
compute_rolling_momentum <- function(team, recent_pitching_df, recent_batting_df) {
  rp <- recent_pitching_df[recent_pitching_df$Team == team, , drop=FALSE]
  rb <- recent_batting_df[recent_batting_df$Team   == team, , drop=FALSE]
  if (nrow(rp) == 0 || nrow(rb) == 0) return(0.0)
  rs <- if ("wOBA" %in% names(rb)) rb$wOBA[1]*12 else LG_AVG_RUNS_PER_GAME
  ra <- rp$RunsAllowed[1] / max(rp$InningsPitched[1] / 9, 1)
  pythagorean_winpct(rs, ra) - 0.500
}

# Calibration left as identity under strict mode (log never populated).
compute_platt_params <- function() {
  log <- .calib_store$log; n <- length(log)
  if (n < 30L) return(list(a=1.0, b=0.0))
  preds   <- vapply(log, `[[`, numeric(1L), "pred")
  actuals <- vapply(log, `[[`, numeric(1L), "actual")
  preds   <- clamp(preds, 1e-6, 1 - 1e-6)
  logits  <- log(preds / (1 - preds))
  tryCatch({
    fit <- glm(actuals ~ logits, family=binomial())
    list(a=coef(fit)[["logits"]], b=coef(fit)[["(Intercept)"]])
  }, error=function(e) list(a=1.0, b=0.0))
}
apply_calibration <- function(raw_prob, platt) {
  logit <- log(clamp(raw_prob, 1e-6, 1-1e-6) / (1-clamp(raw_prob, 1e-6, 1-1e-6)))
  clamp(1 / (1 + exp(-(platt$a * logit + platt$b))), 0.05, 0.95)
}
log_prediction <- function(pred_home_win_prob, actual_home_win) {
  if (!is.numeric(pred_home_win_prob) || !is.numeric(actual_home_win)) return(invisible(NULL))
  .calib_store$log[[length(.calib_store$log) + 1L]] <-
    list(pred=pred_home_win_prob, actual=actual_home_win)
}

bayesian_matchup_hr_rate <- function(career_hr, career_pa, platoon_hr_rate, arsenal_factor,
                                     velo_factor, tto_factor, park_factor=1.0,
                                     count_leverage_factor=1.0, pitcher_home_away_f=1.0,
                                     sp_iso_mult=1.0) {
  prior_rate <- platoon_hr_rate * arsenal_factor * velo_factor * tto_factor *
    park_factor * count_leverage_factor * pitcher_home_away_f * sp_iso_mult
  prior_rate   <- clamp(prior_rate, 0.004, 0.120)
  prior_weight <- MIN_PA_BAYES_PRIOR
  career_pa    <- max(career_pa %||% 0, 0)
  career_hr    <- max(career_hr %||% 0, 0)
  posterior_pa <- career_pa + prior_weight
  posterior_hr <- career_hr + prior_rate * prior_weight
  credibility  <- clamp(career_pa / (career_pa + prior_weight), 0, 1)
  list(rate=clamp(posterior_hr/posterior_pa, 0.003, 0.140),
       credibility=credibility, prior_rate=prior_rate)
}
bayesian_matchup_woba <- function(career_woba, career_pa, platoon_woba,
                                  arsenal_woba_factor=1.0, sp_woba_mult=1.0) {
  prior_woba   <- platoon_woba * arsenal_woba_factor * sp_woba_mult
  prior_weight <- 150L
  career_pa    <- max(career_pa %||% 0, 0)
  if (career_pa < 8 || is.null(career_woba) || is.na(career_woba))
    return(list(woba=prior_woba, credibility=0))
  posterior_pa   <- career_pa + prior_weight
  posterior_woba <- (career_woba*career_pa + prior_woba*prior_weight) / posterior_pa
  credibility    <- clamp(career_pa / (career_pa + prior_weight), 0, 1)
  list(woba=clamp(posterior_woba, 0.180, 0.550), credibility=credibility)
}

classify_sp_tier <- function(sp_era, sp_kpct, sp_bbpct, sp_whiff_pct=NULL,
                             sp_k9=NULL, sp_recent_era=NULL) {
  eff_era <- if (!is.null(sp_recent_era) && !is.na(sp_recent_era) && sp_recent_era > 0) {
    0.35 * sp_era + 0.65 * sp_recent_era
  } else sp_era
  whiff <- sp_whiff_pct %||% LG_AVG_WHIFF_PCT
  kbb   <- if (sp_bbpct > 0) sp_kpct / sp_bbpct else sp_kpct / 0.02
  dom   <- (0.40 * (LG_AVG_ERA - eff_era) / LG_AVG_ERA) +
    (0.25 * (sp_kpct - LG_AVG_K_PCT) / LG_AVG_K_PCT) +
    (0.20 * (LG_AVG_BB_PCT - sp_bbpct) / LG_AVG_BB_PCT) +
    (0.15 * (whiff - LG_AVG_WHIFF_PCT) / LG_AVG_WHIFF_PCT)
  tier <- if (eff_era <= SP_ERA_ELITE_THRESHOLD && kbb >= 3.5)     "elite"
  else if (eff_era <= SP_ERA_GOOD_THRESHOLD && kbb >= 2.5)       "good"
  else if (eff_era >= SP_ERA_STRUGGLING_THRESHOLD)               "struggling"
  else if (eff_era >= 5.5 || kbb < 1.5)                         "below_avg"
  else if (eff_era >= 4.50)                                      "average_low"
  else                                                            "average_high"
  list(tier=tier, dom_score=dom, eff_era=eff_era, kbb=kbb)
}
sp_batting_adjustment <- function(sp_tier_result, sp_kpct, sp_bbpct,
                                  sp_avg_velo, sp_whiff_pct=NULL,
                                  sp_fb_arsenal=NULL, umpire_k_delta=0.0,
                                  umpire_bb_delta=0.0) {
  tier  <- sp_tier_result$tier
  whiff <- sp_whiff_pct %||% LG_AVG_WHIFF_PCT
  eff_k <- clamp(sp_kpct + umpire_k_delta, 0.08, 0.44)
  velo_tier_name <- "avg"
  for (t in VELO_TIERS) { if (sp_avg_velo >= t$min) { velo_tier_name <- t$name; break } }
  ev_suppress <- SP_VELO_SUPPRESSION[[velo_tier_name]] %||% 1.0
  iso_mult <- switch(tier, elite=SP_ISO_SUPPRESSION_ELITE, good=SP_ISO_SUPPRESSION_GOOD,
                     average_high=1.00, average_low=1.05,
                     below_avg=1.10, struggling=SP_ISO_BOOST_STRUGGLING, 1.00)
  woba_mult <- switch(tier, elite=SP_WOBA_SUPPRESSION_ELITE, good=0.92,
                      average_high=1.00, average_low=1.04,
                      below_avg=1.08, struggling=SP_WOBA_BOOST_STRUGGLING, 1.00)
  k_inflation     <- clamp(1.0 + (eff_k - LG_AVG_K_PCT) * SP_BATAVG_SENSITIVITY, 0.72, 1.38)
  bb_deflation    <- clamp(1.0 - (sp_bbpct - LG_AVG_BB_PCT) * 2.8, 0.72, 1.32)
  contact_quality <- clamp(1.0 - (whiff - LG_AVG_WHIFF_PCT) * 2.0, 0.75, 1.25)
  arsenal_hr_factor <- if (!is.null(sp_fb_arsenal)) get_arsenal_hr_factor(sp_fb_arsenal) else 1.0
  bb_collapse_flag <- sp_bbpct >= BB_COLLAPSE_THRESHOLD
  bb_collapse_mult <- if (bb_collapse_flag) 1.16 else 1.0
  list(iso_mult=clamp(iso_mult, 0.58, 1.55), woba_mult=clamp(woba_mult, 0.72, 1.38),
       k_inflation=k_inflation, bb_deflation=bb_deflation,
       contact_quality=contact_quality, ev_suppress=ev_suppress,
       arsenal_hr_factor=arsenal_hr_factor, bb_collapse_flag=bb_collapse_flag,
       bb_collapse_mult=bb_collapse_mult, tier=tier, dom_score=sp_tier_result$dom_score)
}
apply_sp_to_team_batting <- function(team_iso, team_woba, team_bbpct, team_kpct,
                                     team_barrel_pct, sp_adj) {
  list(
    adj_iso        = clamp(team_iso    * sp_adj$iso_mult,      0.04, 0.35),
    adj_woba       = clamp(team_woba   * sp_adj$woba_mult,     0.20, 0.50),
    adj_bbpct      = clamp(team_bbpct  * sp_adj$bb_deflation,  0.03, 0.22),
    adj_kpct       = clamp(team_kpct   * sp_adj$k_inflation,   0.12, 0.42),
    adj_barrel_pct = clamp(team_barrel_pct * sp_adj$contact_quality, 0.02, 0.20),
    bb_collapse_flag = sp_adj$bb_collapse_flag,
    bb_collapse_mult = sp_adj$bb_collapse_mult)
}
apply_sp_to_lineup_woba <- function(lineup_woba, sp_adj) {
  clamp(lineup_woba * sp_adj$woba_mult * sp_adj$contact_quality, 0.180, 0.520)
}

# ===== Statcast (Savant) \u2014 season aggregates; used only if USE_STATCAST =====
fetch_savant_batter_metrics <- function(season="2026") {
  key <- paste0("savant_bat_", season)
  if (exists(key, envir=.savant_cache, inherits=FALSE))
    return(get(key, envir=.savant_cache, inherits=FALSE))
  url <- sprintf("%s/leaderboard/statcast?type=batter&year=%s&position=&team=&min=50&csv=true",
                 SAVANT_BASE, season)
  df <- tryCatch(http_get_csv(url, timeout=40), error=function(e) NULL)
  if (is.null(df) || nrow(df) == 0) return(NULL)
  cnames <- tolower(names(df)); names(df) <- cnames
  result <- tryCatch({
    id_col      <- if ("player_id" %in% cnames) "player_id" else if ("batter" %in% cnames) "batter" else NULL
    barrel_col  <- if ("barrel_batted_rate" %in% cnames) "barrel_batted_rate" else if ("brl_percent" %in% cnames) "brl_percent" else if ("barrel_rate" %in% cnames) "barrel_rate" else NULL
    hardhit_col <- if ("hard_hit_percent" %in% cnames) "hard_hit_percent" else if ("hard_hit_rate" %in% cnames) "hard_hit_rate" else NULL
    pull_col    <- if ("pull_percent" %in% cnames) "pull_percent" else NULL
    sprint_col  <- if ("sprint_speed" %in% cnames) "sprint_speed" else NULL
    xwoba_col   <- if ("xwoba" %in% cnames) "xwoba" else if ("est_woba" %in% cnames) "est_woba" else NULL
    ev_col      <- if ("avg_hit_speed" %in% cnames) "avg_hit_speed" else if ("exit_velocity_avg" %in% cnames) "exit_velocity_avg" else NULL
    la_col      <- if ("avg_hit_angle" %in% cnames) "avg_hit_angle" else if ("launch_angle_avg" %in% cnames) "launch_angle_avg" else NULL
    whiff_col   <- if ("whiff_percent" %in% cnames) "whiff_percent" else NULL
    hr_fb_col   <- if ("hr_flyballs" %in% cnames) "hr_flyballs" else NULL
    babip_col   <- if ("babip" %in% cnames) "babip" else NULL
    xbabip_col  <- if ("est_ba" %in% cnames) "est_ba" else NULL
    slg_col     <- if ("slg" %in% cnames) "slg" else NULL
    ops_col     <- if ("ops" %in% cnames) "ops" else NULL
    if (is.null(id_col)) return(NULL)
    out <- data.frame(SavantID=coerce_numeric(df[[id_col]]))
    out$BarrelPct   <- if (!is.null(barrel_col))  coerce_numeric(df[[barrel_col]])/100  else LG_AVG_BARREL_PCT
    out$HardHitPct  <- if (!is.null(hardhit_col)) coerce_numeric(df[[hardhit_col]])/100 else LG_AVG_HARD_HIT_PCT
    out$PullPct     <- if (!is.null(pull_col))    coerce_numeric(df[[pull_col]])/100    else LG_AVG_PULL_PCT
    out$SprintSpeed <- if (!is.null(sprint_col))  coerce_numeric(df[[sprint_col]])      else LG_AVG_SPRINT_SPEED
    out$xwOBA_sv    <- if (!is.null(xwoba_col))   coerce_numeric(df[[xwoba_col]])       else NA_real_
    out$AvgEV       <- if (!is.null(ev_col))      coerce_numeric(df[[ev_col]])          else LG_AVG_EXIT_VELO
    out$AvgLA       <- if (!is.null(la_col))      coerce_numeric(df[[la_col]])          else LG_AVG_LAUNCH_ANGLE
    out$WhiffPct    <- if (!is.null(whiff_col))   coerce_numeric(df[[whiff_col]])/100   else LG_AVG_WHIFF_PCT
    out$HR_FB_Rate  <- if (!is.null(hr_fb_col))   coerce_numeric(df[[hr_fb_col]])/100   else NA_real_
    out$BABIP       <- if (!is.null(babip_col))   coerce_numeric(df[[babip_col]])       else 0.296
    out$xBABIP      <- if (!is.null(xbabip_col))  coerce_numeric(df[[xbabip_col]])      else NA_real_
    out$SLG_sv      <- if (!is.null(slg_col))     coerce_numeric(df[[slg_col]])         else NA_real_
    out$OPS_sv      <- if (!is.null(ops_col))     coerce_numeric(df[[ops_col]])         else NA_real_
    out[out$SavantID > 0, ]
  }, error=function(e) NULL)
  if (!is.null(result) && nrow(result) > 0) assign(key, result, envir=.savant_cache)
  result
}
fetch_savant_pitcher_metrics <- function(season="2026") {
  key <- paste0("savant_pit_", season)
  if (exists(key, envir=.savant_cache, inherits=FALSE))
    return(get(key, envir=.savant_cache, inherits=FALSE))
  url <- sprintf("%s/leaderboard/statcast?type=pitcher&year=%s&position=&team=&min=20&csv=true",
                 SAVANT_BASE, season)
  df <- tryCatch(http_get_csv(url, timeout=40), error=function(e) NULL)
  if (is.null(df) || nrow(df) == 0) return(NULL)
  cnames <- tolower(names(df)); names(df) <- cnames
  result <- tryCatch({
    id_col      <- if ("player_id" %in% cnames) "player_id" else if ("pitcher" %in% cnames) "pitcher" else NULL
    gb_col      <- if ("gb_percent" %in% cnames) "gb_percent" else NULL
    fb_col      <- if ("fb_percent" %in% cnames) "fb_percent" else NULL
    kbb_col     <- if ("k_percent" %in% cnames) "k_percent" else NULL
    bb_col      <- if ("bb_percent" %in% cnames) "bb_percent" else NULL
    brl_col     <- if ("barrel_batted_rate" %in% cnames) "barrel_batted_rate" else if ("brl_percent" %in% cnames) "brl_percent" else NULL
    xera_col    <- if ("xera" %in% cnames) "xera" else NULL
    velo_col    <- if ("avg_speed" %in% cnames) "avg_speed" else if ("effective_speed" %in% cnames) "effective_speed" else if ("ff_avg_speed" %in% cnames) "ff_avg_speed" else NULL
    ff_pct_col  <- if ("ff_pct" %in% cnames) "ff_pct" else if ("four_seam_percent" %in% cnames) "four_seam_percent" else NULL
    sl_pct_col  <- if ("sl_pct" %in% cnames) "sl_pct" else if ("slider_percent" %in% cnames) "slider_percent" else NULL
    cu_pct_col  <- if ("cu_pct" %in% cnames) "cu_pct" else if ("curveball_percent" %in% cnames) "curveball_percent" else NULL
    ch_pct_col  <- if ("ch_pct" %in% cnames) "ch_pct" else if ("changeup_percent" %in% cnames) "changeup_percent" else NULL
    whiff_col   <- if ("whiff_percent" %in% cnames) "whiff_percent" else NULL
    hr_fb_col   <- if ("hr_flyballs" %in% cnames) "hr_flyballs" else NULL
    home_era_col<- if ("home_era" %in% cnames) "home_era" else NULL
    away_era_col<- if ("away_era" %in% cnames) "away_era" else NULL
    pip_col     <- if ("p_ip" %in% cnames) "p_ip" else if ("pitches_per_ip" %in% cnames) "pitches_per_ip" else NULL
    lob_col     <- if ("lob_percent" %in% cnames) "lob_percent" else if ("stranded_percent" %in% cnames) "stranded_percent" else NULL
    fi_era_col  <- if ("first_inning_era" %in% cnames) "first_inning_era" else NULL
    hand_col    <- if ("p_throws" %in% cnames) "p_throws" else NULL
    whip_col    <- if ("whip" %in% cnames) "whip" else NULL
    if (is.null(id_col)) return(NULL)
    out <- data.frame(SavantID=coerce_numeric(df[[id_col]]))
    out$GBPct         <- if (!is.null(gb_col))  coerce_numeric(df[[gb_col]])/100  else LG_AVG_GB_PCT
    out$FBPct         <- if (!is.null(fb_col))  coerce_numeric(df[[fb_col]])/100  else LG_AVG_FB_PCT
    out$KPct_sv       <- if (!is.null(kbb_col)) coerce_numeric(df[[kbb_col]])/100 else LG_AVG_K_PCT
    out$BBPct_sv      <- if (!is.null(bb_col))  coerce_numeric(df[[bb_col]])/100  else LG_AVG_BB_PCT
    out$BrlPctAllowed <- if (!is.null(brl_col)) coerce_numeric(df[[brl_col]])/100 else LG_AVG_BARREL_PCT
    out$xERA          <- if (!is.null(xera_col)) coerce_numeric(df[[xera_col]])   else NA_real_
    out$AvgVelo       <- if (!is.null(velo_col)) coerce_numeric(df[[velo_col]])   else 92.0
    out$FBPct_arsenal <- if (!is.null(ff_pct_col)) coerce_numeric(df[[ff_pct_col]])/100 else out$FBPct
    out$BreakingPct   <- if (!is.null(sl_pct_col) && !is.null(cu_pct_col))
      (coerce_numeric(df[[sl_pct_col]]) + coerce_numeric(df[[cu_pct_col]]))/100
    else if (!is.null(sl_pct_col)) coerce_numeric(df[[sl_pct_col]])/100 else NA_real_
    out$OffspeedPct   <- if (!is.null(ch_pct_col)) coerce_numeric(df[[ch_pct_col]])/100 else NA_real_
    out$WhiffPct      <- if (!is.null(whiff_col))  coerce_numeric(df[[whiff_col]])/100  else LG_AVG_WHIFF_PCT
    out$HR_FB_Rate_allowed <- if (!is.null(hr_fb_col)) coerce_numeric(df[[hr_fb_col]])/100 else NA_real_
    out$HomeERA       <- if (!is.null(home_era_col)) coerce_numeric(df[[home_era_col]]) else NA_real_
    out$AwayERA       <- if (!is.null(away_era_col)) coerce_numeric(df[[away_era_col]]) else NA_real_
    out$PitchesPerIP  <- if (!is.null(pip_col))  coerce_numeric(df[[pip_col]])    else NA_real_
    out$LOB_Pct       <- if (!is.null(lob_col))  coerce_numeric(df[[lob_col]])/100  else NA_real_
    out$FirstInnERA   <- if (!is.null(fi_era_col)) coerce_numeric(df[[fi_era_col]]) else NA_real_
    out$PitchHand_sv  <- if (!is.null(hand_col))  as.character(df[[hand_col]])      else NA_character_
    out$WHIP_sv       <- if (!is.null(whip_col))  coerce_numeric(df[[whip_col]])    else NA_real_
    out[out$SavantID > 0, ]
  }, error=function(e) NULL)
  if (!is.null(result) && nrow(result) > 0) assign(key, result, envir=.savant_cache)
  result
}
get_batter_statcast  <- function(player_id, savant_bat_df) {
  if (is.null(savant_bat_df) || nrow(savant_bat_df) == 0) return(NULL)
  row <- savant_bat_df[savant_bat_df$SavantID == as.numeric(player_id), , drop=FALSE]
  if (nrow(row) == 0) return(NULL); row[1, ]
}
get_pitcher_statcast <- function(player_id, savant_pit_df) {
  if (is.null(savant_pit_df) || nrow(savant_pit_df) == 0) return(NULL)
  row <- savant_pit_df[savant_pit_df$SavantID == as.numeric(player_id), , drop=FALSE]
  if (nrow(row) == 0) return(NULL); row[1, ]
}

fetch_mlb_schedule <- function(date_str=NULL) {
  if (is.null(date_str)) date_str <- format(Sys.Date(), "%Y-%m-%d")
  url <- sprintf("%s/schedule?sportId=1&date=%s&hydrate=team,probablePitcher(note),linescore,game,stats,venue,weather,broadcasts,officials",
                 MLB_API_BASE, date_str)
  data <- http_get_json(url)
  empty_s <- data.frame(
    GameID=integer(), Date=character(), HomeTeam=character(), AwayTeam=character(),
    HomeTeamID=integer(), AwayTeamID=integer(),
    HomePitcher=character(), HomePitcherID=integer(), HomePitcherHand=character(),
    AwayPitcher=character(), AwayPitcherID=integer(), AwayPitcherHand=character(),
    Venue=character(), Umpire=character(), GameStatus=character(),
    ActualWinner=character(), HomeScore=numeric(), AwayScore=numeric(),
    SeriesGameNum=integer(), SeriesHomeWins=integer(), SeriesAwayWins=integer(),
    GameType=character(), StartUTC=character(), stringsAsFactors=FALSE)
  if (is.null(data) || is.null(data[["dates"]]) || length(data[["dates"]]) == 0L)
    return(empty_s)
  rows <- list(); w_list <- list()
  tryCatch({
    for (date_info in data[["dates"]])
      for (g in (date_info[["games"]] %||% list())) {
        gtype <- as.character(scalar(g[["gameType"]], "R"))
        if (gtype %in% MLB_SKIP_GAME_TYPES) next      # spring training / exhibition / All-Star
        ht   <- as.character(scalar(g[["teams"]][["home"]][["team"]][["name"]], "Unknown"))
        at   <- as.character(scalar(g[["teams"]][["away"]][["team"]][["name"]], "Unknown"))
        htid <- clean_player_id(g[["teams"]][["home"]][["team"]][["id"]])
        atid <- clean_player_id(g[["teams"]][["away"]][["team"]][["id"]])
        vn   <- as.character(scalar(g[["venue"]][["name"]], "Unknown"))
        wx   <- g[["weather"]] %||% list()
        gs   <- as.character(scalar(g[["status"]][["detailedState"]], "Scheduled"))
        hs   <- coerce_numeric(scalar(g[["teams"]][["home"]][["score"]], 0))
        as_  <- coerce_numeric(scalar(g[["teams"]][["away"]][["score"]], 0))
        ser_num   <- coerce_numeric(scalar(g[["seriesGameNumber"]], 1))
        ser_h_win <- coerce_numeric(scalar(g[["teams"]][["home"]][["seriesNumber"]], 0))
        ser_a_win <- coerce_numeric(scalar(g[["teams"]][["away"]][["seriesNumber"]], 0))
        umpire_name <- NA_character_
        for (off in (g[["officials"]] %||% list()))
          if (grepl("plate|home plate|HP", scalar(off[["officialType"]], ""), ignore.case=TRUE))
            umpire_name <- as.character(scalar(off[["official"]][["fullName"]], NA_character_))
        aw <- NA_character_
        if (gs %in% c("Final","Game Over","Completed Early"))
          aw <- if (hs > as_) ht else if (as_ > hs) at else "Tie"
        hpid    <- clean_player_id(g[["teams"]][["home"]][["probablePitcher"]][["id"]])
        apid    <- clean_player_id(g[["teams"]][["away"]][["probablePitcher"]][["id"]])
        hp_hand <- as.character(scalar(g[["teams"]][["home"]][["probablePitcher"]][["pitchHand"]][["code"]], "R"))
        ap_hand <- as.character(scalar(g[["teams"]][["away"]][["probablePitcher"]][["pitchHand"]][["code"]], "R"))
        rows[[length(rows)+1L]] <- data.frame(
          GameID=coerce_numeric(scalar(g[["gamePk"]], NA)),
          Date=date_str, HomeTeam=ht, AwayTeam=at,
          HomeTeamID=htid %||% NA_integer_, AwayTeamID=atid %||% NA_integer_,
          HomePitcher=as.character(scalar(g[["teams"]][["home"]][["probablePitcher"]][["fullName"]], "TBD")),
          HomePitcherID=hpid, HomePitcherHand=hp_hand,
          AwayPitcher=as.character(scalar(g[["teams"]][["away"]][["probablePitcher"]][["fullName"]], "TBD")),
          AwayPitcherID=apid, AwayPitcherHand=ap_hand,
          Venue=vn, Umpire=umpire_name, GameStatus=gs, ActualWinner=aw,
          HomeScore=hs, AwayScore=as_,
          SeriesGameNum=as.integer(ser_num), SeriesHomeWins=as.integer(ser_h_win),
          SeriesAwayWins=as.integer(ser_a_win), GameType=gtype,
          StartUTC=as.character(scalar(g[["gameDate"]], NA_character_)), stringsAsFactors=FALSE)
        w_list[[length(w_list)+1L]] <- wx
      }
  }, error=function(e) mlog("Schedule   | fetch failed: ", conditionMessage(e)))
  if (!length(rows)) return(empty_s)
  df <- bind_rows(rows); df$Weather <- w_list; df
}

# ===== POINT-IN-TIME GAME-LOG FETCHERS / BUILDERS =====
fetch_team_gamelog_raw <- function(season, group) {
  key <- paste0("tgl_", group, "_", season)
  if (exists(key, envir=.gamelog_cache, inherits=FALSE))
    return(get(key, envir=.gamelog_cache, inherits=FALSE))
  url  <- sprintf("%s/teams/stats?season=%s&stats=gameLog&group=%s&sportIds=1&limit=100000",
                  MLB_API_BASE, season, group)
  data <- http_get_json(url)
  splits <- if (api_has_splits(data))
    unlist(lapply(data[["stats"]], function(g) g[["splits"]] %||% list()), recursive=FALSE)
  else list()
  assign(key, splits, envir=.gamelog_cache); splits
}
fetch_player_gamelog_raw <- function(season) {
  key <- paste0("pgl_", season)
  if (exists(key, envir=.gamelog_cache, inherits=FALSE))
    return(get(key, envir=.gamelog_cache, inherits=FALSE))
  url  <- sprintf("%s/stats?stats=gameLog&group=hitting&sportId=1&season=%s&limit=100000&hydrate=person",
                  MLB_API_BASE, season)
  data <- http_get_json(url)
  splits <- if (api_has_splits(data))
    unlist(lapply(data[["stats"]], function(g) g[["splits"]] %||% list()), recursive=FALSE)
  else list()
  assign(key, splits, envir=.gamelog_cache); splits
}

.agg_team_pitching <- function(sps) {
  a <- list(g=0,w=0,l=0,r=0,hr=0,so=0,bb=0,ibb=0,h=0,ip=0,hbp=0,bf=0,ao=0,go=0)
  for (sp in sps) {
    st  <- sp[["stat"]] %||% list()
    a$g  <- a$g  + 1
    a$w  <- a$w  + coerce_numeric(scalar(st[["wins"]],       0))
    a$l  <- a$l  + coerce_numeric(scalar(st[["losses"]],     0))
    a$r  <- a$r  + coerce_numeric(scalar(st[["runs"]],       0))
    a$hr <- a$hr + coerce_numeric(scalar(st[["homeRuns"]],   0))
    a$so <- a$so + coerce_numeric(scalar(st[["strikeOuts"]], 0))
    a$bb <- a$bb + coerce_numeric(scalar(st[["baseOnBalls"]],0))
    a$ibb<- a$ibb+ coerce_numeric(scalar(st[["intentionalWalks"]],0))
    a$h  <- a$h  + coerce_numeric(scalar(st[["hits"]],       0))
    a$ip <- a$ip + parse_innings_pitched(scalar(st[["inningsPitched"]],"0"))
    a$hbp<- a$hbp+ coerce_numeric(scalar(st[["hitByPitch"]], 0))
    a$bf <- a$bf + coerce_numeric(scalar(st[["battersFaced"]],0))
    a$ao <- a$ao + coerce_numeric(scalar(st[["airOuts"]],    0))
    a$go <- a$go + coerce_numeric(scalar(st[["groundOuts"]], 0))
  }
  a
}
# Team pitching staff. RA9 is kept in the ERA column (it is what the run model and the
# league baselines use). FIP/xFIP are on the same runs-per-9 scale because
# FIP_CONSTANT is re-derived from the league each run. xFIP used to estimate fly balls
# as 0.35 x strikeouts, which made it a second strikeout stat; it now uses air outs.
# PenSkill is the staff's FIP regressed with 200 IP of league average -- on the 2026
# season it predicted as well as a true starter/reliever split, at no extra API cost.
PEN_PRIOR_IP <- 200
.build_pitching_row <- function(tn, a) {
  ip  <- a$ip; bf <- if (a$bf>0) a$bf else ip*4.3
  era  <- if (ip>0) 9*a$r/ip else LG_AVG_ERA
  fipn <- 13*a$hr + 3*(a$bb - a$ibb + a$hbp) - 2*a$so
  fip  <- if (ip>0) fipn/ip + FIP_CONSTANT else LG_AVG_FIP
  xfip <- if (ip>0) (13*LG_HR_PER_FBP*(a$ao + a$hr) + 3*(a$bb - a$ibb + a$hbp) - 2*a$so)/ip + FIP_CONSTANT else LG_AVG_FIP
  pen  <- (fipn + (LG_AVG_ERA - FIP_CONSTANT) * PEN_PRIOR_IP) / (ip + PEN_PRIOR_IP) + FIP_CONSTANT
  whip <- if (ip>0) (a$h+a$bb)/ip else 1.30
  kpct <- if (bf>0) a$so/bf else LG_AVG_K_PCT
  bbpct<- if (bf>0) a$bb/bf else LG_AVG_BB_PCT
  avg_starter_ip <- LG_IP_PER_START
  siera          <- compute_siera_proxy(kpct, bbpct, if ((a$go + a$ao) > 0) a$go/(a$go + a$ao) else LG_AVG_GB_PCT)
  data.frame(Team=tn, Games=a$g, Wins=a$w, Losses=a$l,
             RunsAllowed=a$r, HomeRunsAllowed=a$hr,
             ERA=era, FIP=fip, WHIP=whip, xFIP=xfip, SIERA=siera, PenSkill=pen,
             Strikeouts=a$so, Walks=a$bb, IntWalks=a$ibb, InningsPitched=ip, Hits=a$h, HitByPitch=a$hbp,
             AirOuts=a$ao, GroundOuts=a$go, BattersFaced=bf,
             StarterERA=era, BullpenERA=pen, BullpenIP=ip*(1-avg_starter_ip/9),
             KPct=kpct, BBPct=bbpct, AvgStarterIP=avg_starter_ip, stringsAsFactors=FALSE)
}
build_pitching_df <- function(season, cutoff_date, last_n=NULL) {
  splits <- fetch_team_gamelog_raw(season, "pitching")
  if (!length(splits)) return(data.frame())
  by_team <- split(splits, vapply(splits,
                                  function(s) as.character(scalar(s[["team"]][["name"]],"Unknown")), character(1L)))
  rows <- list()
  for (tn in names(by_team)) {
    sps <- filter_splits_before(by_team[[tn]], cutoff_date, last_n=last_n)
    if (!length(sps)) next
    rows[[length(rows)+1L]] <- .build_pitching_row(tn, .agg_team_pitching(sps))
  }
  if (!length(rows)) return(data.frame()); bind_rows(rows)
}
.agg_team_batting <- function(sps) {
  a <- list(g=length(sps),hr=0,ab=0,pa=0,h=0,d=0,t=0,bb=0,hbp=0,sf=0,so=0,sb=0,r=0)
  fmap <- c(homeRuns="hr",atBats="ab",plateAppearances="pa",hits="h",doubles="d",
            triples="t",baseOnBalls="bb",hitByPitch="hbp",sacFlies="sf",
            strikeOuts="so",stolenBases="sb",runs="r")
  for (sp in sps) {
    st <- sp[["stat"]] %||% list()
    for (fld in names(fmap)) a[[fmap[fld]]] <- a[[fmap[fld]]] + coerce_numeric(scalar(st[[fld]],0))
  }
  a
}
.make_batting_row <- function(tn, a) {
  singles <- pmax(a$h-a$d-a$t-a$hr, 0); tb_val <- singles+2*a$d+3*a$t+4*a$hr
  slg  <- if (a$ab>0) tb_val/a$ab else 0
  obp  <- if (a$pa>0) (a$h+a$bb+a$hbp)/a$pa else 0
  iso  <- slg - if (a$ab>0) a$h/a$ab else 0
  ops  <- obp + slg
  woba <- calc_woba(a$bb,a$hbp,a$h,a$d,a$t,a$hr,a$ab,a$sf)
  babip <- if ((a$ab - a$so - a$hr + a$sf) > 0) (a$h - a$hr) / (a$ab - a$so - a$hr + a$sf) else 0.296
  data.frame(Team=tn, Games=a$g, HomeRuns=a$hr, AtBats=a$ab, PlateAppearances=a$pa,
             wOBA=woba, xwOBA=woba*0.98, SLG=slg, OPS=ops, OBP=obp, Hits=a$h,
             Doubles=a$d, Triples=a$t, BaseOnBalls=a$bb, HitByPitch=a$hbp, SacFlies=a$sf,
             ISO=iso, BBPct=if(a$pa>0) a$bb/a$pa else LG_AVG_BB_PCT,
             KPct=if(a$pa>0) a$so/a$pa else LG_AVG_K_PCT,
             StolenBases=a$sb, BABIP=babip, Runs=a$r %||% NA_real_, stringsAsFactors=FALSE)
}
build_team_batting_df <- function(season, cutoff_date, last_n=NULL) {
  splits <- fetch_team_gamelog_raw(season, "hitting")
  if (!length(splits)) return(data.frame())
  by_team <- split(splits, vapply(splits,
                                  function(s) as.character(scalar(s[["team"]][["name"]],"Unknown")), character(1L)))
  rows <- list()
  for (tn in names(by_team)) {
    sps <- filter_splits_before(by_team[[tn]], cutoff_date, last_n=last_n)
    if (!length(sps)) next
    a <- .agg_team_batting(sps); a$g <- length(sps)
    rows[[length(rows)+1L]] <- .make_batting_row(tn, a)
  }
  if (!length(rows)) return(data.frame()); bind_rows(rows)
}
build_records_from_pitching <- function(pitching_df_std) {
  recs <- list()
  if (is.null(pitching_df_std) || nrow(pitching_df_std) == 0) return(recs)
  for (i in seq_len(nrow(pitching_df_std))) {
    tn <- pitching_df_std$Team[i]
    recs[[tn]] <- list(wins=pitching_df_std$Wins[i] %||% 0,
                       losses=pitching_df_std$Losses[i] %||% 0, run_diff=0)
  }
  recs
}
lookup_record <- function(team_name, records) {
  if (is.null(records) || length(records) == 0L) return(NULL)
  if (!is.null(records[[team_name]])) return(records[[team_name]])
  last_word <- function(s) tail(strsplit(trimws(s), "\\s+")[[1L]], 1L)
  lw <- last_word(team_name)
  for (k in names(records)) if (last_word(k) == lw) return(records[[k]])
  for (k in names(records))
    if (grepl(team_name, k, fixed=TRUE) || grepl(k, team_name, fixed=TRUE)) return(records[[k]])
  NULL
}

.process_player_splits <- function(pid, sps, savant_bat_df=NULL) {
  tn   <- as.character(scalar(sps[[1L]][["team"]][["name"]], "Unknown"))
  pnam <- as.character(scalar(sps[[1L]][["player"]][["fullName"]],"Unknown"))
  bh   <- as.character(scalar(sps[[1L]][["player"]][["batSide"]][["code"]],"R"))
  slot <- coerce_numeric(scalar(sps[[1L]][["battingOrder"]],500))
  slot <- max(1L, min(9L, as.integer(slot/100)))
  a <- list(g=length(sps),hr=0,ab=0,pa=0,h=0,d=0,t=0,bb=0,hbp=0,sf=0,so=0)
  fmap <- c(homeRuns="hr",atBats="ab",plateAppearances="pa",hits="h",doubles="d",
            triples="t",baseOnBalls="bb",hitByPitch="hbp",sacFlies="sf",strikeOuts="so")
  for (sp in sps) {
    st <- sp[["stat"]] %||% list()
    for (fld in names(fmap)) a[[fmap[fld]]] <- a[[fmap[fld]]] + coerce_numeric(scalar(st[[fld]],0))
  }
  singles  <- pmax(a$h-a$d-a$t-a$hr, 0); tb_val <- singles+2*a$d+3*a$t+4*a$hr
  slg      <- if (a$ab>0) tb_val/a$ab else 0
  obp      <- if (a$pa>0) (a$h+a$bb+a$hbp)/a$pa else 0
  iso      <- slg - if (a$ab>0) a$h/a$ab else 0
  ops      <- obp + slg
  woba     <- calc_woba(a$bb,a$hbp,a$h,a$d,a$t,a$hr,a$ab,a$sf)
  hr_rate  <- if (a$pa >= MIN_PA_SEASON) a$hr/a$pa else LG_AVG_HR_PER_PA
  pk_ll    <- platoon_key(bh,"L"); pk_lr <- platoon_key(bh,"R")
  hr_rate_L<- hr_rate*(PLATOON_HR_RATE[[pk_ll]]%||%LG_AVG_HR_PER_PA)/LG_AVG_HR_PER_PA
  hr_rate_R<- hr_rate*(PLATOON_HR_RATE[[pk_lr]]%||%LG_AVG_HR_PER_PA)/LG_AVG_HR_PER_PA
  woba_vs_L<- woba*(PLATOON_WOBA_MULT[[pk_ll]]%||%1.0)
  woba_vs_R<- woba*(PLATOON_WOBA_MULT[[pk_lr]]%||%1.0)
  sc <- get_batter_statcast(pid, savant_bat_df)
  barrel_pct   <- if (!is.null(sc)) sc$BarrelPct   else LG_AVG_BARREL_PCT
  hard_hit_pct <- if (!is.null(sc)) sc$HardHitPct  else LG_AVG_HARD_HIT_PCT
  pull_pct     <- if (!is.null(sc)) sc$PullPct     else LG_AVG_PULL_PCT
  sprint_speed <- if (!is.null(sc)) sc$SprintSpeed else LG_AVG_SPRINT_SPEED
  xwoba_sv     <- if (!is.null(sc) && !is.na(sc$xwOBA_sv %||% NA_real_)) sc$xwOBA_sv else woba*0.98
  avg_ev       <- if (!is.null(sc) && !is.na(sc$AvgEV %||% NA_real_)) sc$AvgEV else LG_AVG_EXIT_VELO
  avg_la       <- if (!is.null(sc) && !is.na(sc$AvgLA %||% NA_real_)) sc$AvgLA else LG_AVG_LAUNCH_ANGLE
  whiff_pct    <- if (!is.null(sc) && !is.na(sc$WhiffPct %||% NA_real_)) sc$WhiffPct else LG_AVG_WHIFF_PCT
  hr_fb_rate   <- if (!is.null(sc) && !is.na(sc$HR_FB_Rate %||% NA_real_)) sc$HR_FB_Rate else NA_real_
  babip_sv     <- if (!is.null(sc) && !is.na(sc$BABIP %||% NA_real_)) sc$BABIP else 0.296
  xbabip_sv    <- if (!is.null(sc) && !is.na(sc$xBABIP %||% NA_real_)) sc$xBABIP else NA_real_
  slg_sv       <- if (!is.null(sc) && !is.na(sc$SLG_sv %||% NA_real_)) sc$SLG_sv else slg
  ops_sv       <- if (!is.null(sc) && !is.na(sc$OPS_sv %||% NA_real_)) sc$OPS_sv else ops
  last_date <- as.character(scalar(sps[[1L]][["date"]], NA_character_))   # splits are newest-first
  data.frame(PlayerID=as.integer(pid), PlayerName=pnam, Team=tn, BatHand=bh,
             LineupSlot=slot, Games=a$g, LastGameDate=last_date,
             PAperG=if (a$g > 0) a$pa / a$g else 0,
             HomeRuns=a$hr, AtBats=a$ab, PlateAppearances=a$pa,
             wOBA=woba, xwOBA=xwoba_sv, wOBA_L=woba_vs_L, wOBA_R=woba_vs_R,
             SLG=slg_sv, OPS=ops_sv, OBP=obp, ISO=iso,
             HRRate=hr_rate, HRRate_L=hr_rate_L, HRRate_R=hr_rate_R,
             Hits=a$h, Doubles=a$d, Triples=a$t, BaseOnBalls=a$bb, HitByPitch=a$hbp, SacFlies=a$sf,
             StrikeOuts=a$so, KPct=if (a$pa > 0) a$so/a$pa else LG_AVG_K_PCT,
             BarrelPct=barrel_pct, HardHitPct=hard_hit_pct, PullPct=pull_pct, SprintSpeed=sprint_speed,
             AvgEV=avg_ev, AvgLA=avg_la, WhiffPct=whiff_pct, HR_FB_Rate=hr_fb_rate,
             BABIP=babip_sv, xBABIP=xbabip_sv, stringsAsFactors=FALSE)
}
# ===== Player batting: fetch hitting game logs PER PLAYER (league-wide call returned empty) =====
`%or%` <- function(a, b) if (is.null(a) || length(a) == 0L || is.na(a)) b else a
ROSTER_TYPE <- "active"   # "active" = current roster; switch to "fullSeason" for fuller coverage

fetch_player_gamelog_one <- function(pid, season = "2026") {
  pid <- clean_player_id(pid); if (is.na(pid)) return(list())
  key <- paste0("pglone_", pid, "_", season)
  if (exists(key, envir = .gamelog_cache, inherits = FALSE))
    return(get(key, envir = .gamelog_cache, inherits = FALSE))
  url  <- sprintf("%s/people/%d/stats?stats=gameLog&group=hitting&season=%s&limit=100000",
                  MLB_API_BASE, pid, season)
  data <- http_get_json(url)
  sp <- if (api_has_splits(data))
    unlist(lapply(data[["stats"]], function(g) g[["splits"]] %||% list()), recursive = FALSE) else list()
  assign(key, sp, envir = .gamelog_cache); sp
}

fetch_team_hitter_ids <- function(team_id, season = "2026", roster_type = ROSTER_TYPE) {
  tid <- clean_player_id(team_id); if (is.na(tid)) return(integer())
  key <- paste0("roster_", roster_type, "_", tid, "_", season)
  if (exists(key, envir = .gamelog_cache, inherits = FALSE))
    return(get(key, envir = .gamelog_cache, inherits = FALSE))
  url  <- sprintf("%s/teams/%d/roster?rosterType=%s&season=%s", MLB_API_BASE, tid, roster_type, season)
  data <- http_get_json(url)
  ids <- integer()
  for (p in (data[["roster"]] %||% list())) {
    pos <- as.character(scalar(p[["position"]][["abbreviation"]], ""))
    if (pos == "P") next
    id <- clean_player_id(p[["person"]][["id"]])
    if (!is.na(id)) ids <- c(ids, id)
  }
  ids <- unique(ids)
  assign(key, ids, envir = .gamelog_cache); ids
}

fetch_batside_map <- function(pids) {
  pids <- unique(stats::na.omit(as.integer(pids))); out <- list(); need <- character()
  for (id in pids) {
    k <- paste0("bs_", id)
    if (exists(k, envir = .gamelog_cache, inherits = FALSE))
      out[[as.character(id)]] <- get(k, envir = .gamelog_cache, inherits = FALSE)
    else need <- c(need, as.character(id))
  }
  if (length(need)) for (chunk in split(need, ceiling(seq_along(need) / 100))) {
    url  <- sprintf("%s/people?personIds=%s", MLB_API_BASE, paste(chunk, collapse = ","))
    data <- http_get_json(url)
    for (p in (data[["people"]] %||% list())) {
      id <- clean_player_id(p[["id"]]); bs <- as.character(scalar(p[["batSide"]][["code"]], "R"))
      if (!is.na(id)) { assign(paste0("bs_", id), bs, envir = .gamelog_cache)
        out[[as.character(id)]] <- bs }
    }
  }
  out
}

build_player_batting_df <- function(season, cutoff_date, last_n = NULL,
                                    savant_bat_df = NULL, team_ids = NULL) {
  cutoff_date <- as.Date(cutoff_date)
  if (is.null(team_ids)) {
    sched <- fetch_mlb_schedule(format(cutoff_date, "%Y-%m-%d"))
    team_ids <- unique(stats::na.omit(c(sched$HomeTeamID, sched$AwayTeamID)))
  }
  if (!length(team_ids)) return(data.frame())
  # A past slate uses everyone who was on the roster during the season (each player's
  # team is then taken from his own game log as of that date); today's slate uses the
  # active roster. Using today's roster for past dates put later acquisitions into
  # old lineups and dropped players who had since left.
  rt <- if (cutoff_date < mlb_today() - 1) "fullSeason" else ROSTER_TYPE
  hitter_ids <- unique(unlist(lapply(team_ids, fetch_team_hitter_ids, season = season, roster_type = rt)))
  if (!length(hitter_ids)) return(data.frame())
  bs_map <- fetch_batside_map(hitter_ids)
  rows <- list()
  for (pid in hitter_ids) {
    sps_all <- fetch_player_gamelog_one(pid, season)
    if (!length(sps_all)) next
    bs <- bs_map[[as.character(pid)]] %or% "R"
    sps_all <- lapply(sps_all, function(s) {
      if (is.null(s[["player"]])) s[["player"]] <- list()
      s[["player"]][["batSide"]] <- list(code = bs); s
    })
    sps <- filter_splits_before(sps_all, cutoff_date, last_n = last_n)
    if (!length(sps)) next
    rows[[length(rows) + 1L]] <- .process_player_splits(as.character(pid), sps, savant_bat_df)
  }
  if (!length(rows)) return(data.frame())
  bind_rows(rows)
}

# League per-inning rates used to regress pitchers (refreshed point-in-time in
# refresh_league_baselines; the defaults are the 2026 regular-season values).
LG_K_PER_IP      <- 0.944
LG_BBHBP_PER_IP  <- 0.405
LG_HR_PER_IP     <- 0.128
LG_HR_PER_FBP    <- 0.111   # HR / (air outs + HR)
LG_BF_PER_START  <- 21.6
LG_IP_PER_START  <- 5.3

# Starter skill on the runs-allowed-per-9 scale, as validated on the 2026 season
# (walk-forward, 2,354 games): 40% an xFIP-style estimate (K, BB+HBP and fly balls
# at a league HR rate) regressed with 90 IP of league average, 60% runs allowed per 9
# regressed with 30 IP. Early in a season the regression target is last season's
# numbers (half-weighted, capped) rather than the league average.
SP_FIP_PRIOR_IP  <- 90
SP_RA_PRIOR_IP   <- 30
SP_W_XFIP        <- 0.40
SP_PREV_IP_CAP   <- 150
SP_PREV_WEIGHT   <- 0.50

.pitch_agg <- function(sps) {
  a <- list(ip=0,hr=0,so=0,bb=0,ibb=0,hbp=0,bf=0,r=0,g=length(sps),h=0,pc=0,ao=0,go=0,
            gs=0,gs_ip=0,gs_bf=0,gs_pc=0)
  for (sp in sps) {
    st <- sp[["stat"]] %||% list()
    ip <- parse_innings_pitched(scalar(st[["inningsPitched"]], "0"))
    bf <- coerce_numeric(scalar(st[["battersFaced"]], 0))
    a$ip  <- a$ip  + ip
    a$hr  <- a$hr  + coerce_numeric(scalar(st[["homeRuns"]], 0))
    a$so  <- a$so  + coerce_numeric(scalar(st[["strikeOuts"]], 0))
    a$bb  <- a$bb  + coerce_numeric(scalar(st[["baseOnBalls"]], 0))
    a$ibb <- a$ibb + coerce_numeric(scalar(st[["intentionalWalks"]], 0))
    a$hbp <- a$hbp + coerce_numeric(scalar(st[["hitByPitch"]], 0))
    a$bf  <- a$bf  + bf
    a$r   <- a$r   + coerce_numeric(scalar(st[["runs"]], 0))
    a$h   <- a$h   + coerce_numeric(scalar(st[["hits"]], 0))
    a$pc  <- a$pc  + coerce_numeric(scalar(st[["numberOfPitches"]], 0))
    a$ao  <- a$ao  + coerce_numeric(scalar(st[["airOuts"]], 0))
    a$go  <- a$go  + coerce_numeric(scalar(st[["groundOuts"]], 0))
    if (coerce_numeric(scalar(st[["gamesStarted"]], 0)) >= 1) {
      a$gs <- a$gs + 1; a$gs_ip <- a$gs_ip + ip; a$gs_bf <- a$gs_bf + bf
      a$gs_pc <- a$gs_pc + coerce_numeric(scalar(st[["numberOfPitches"]], 0))
    }
  }
  if (a$bf == 0) a$bf <- a$ip * 4.3
  a
}

# Per-inning rates a pitcher is regressed toward: league average, pulled toward his
# previous season when he has one.
.pitch_target <- function(prev) {
  lg <- list(k = LG_K_PER_IP, bb = LG_BBHBP_PER_IP, hr = LG_HR_PER_IP,
             fbp = (LG_HR_PER_IP / max(LG_HR_PER_FBP, 0.02)), ra = LG_AVG_ERA / 9)
  if (is.null(prev) || prev$ip <= 0) return(lg)
  w <- SP_PREV_WEIGHT * min(prev$ip, SP_PREV_IP_CAP)
  mix <- function(x, l) (x + l * SP_FIP_PRIOR_IP) / (prev$ip + SP_FIP_PRIOR_IP)
  pr <- list(k = mix(prev$so, lg$k), bb = mix(prev$bb - prev$ibb + prev$hbp, lg$bb),
             hr = mix(prev$hr, lg$hr), fbp = mix(prev$ao + prev$hr, lg$fbp),
             ra = (prev$r + lg$ra * SP_RA_PRIOR_IP) / (prev$ip + SP_RA_PRIOR_IP))
  f <- w / (w + SP_FIP_PRIOR_IP)
  lapply(stats::setNames(names(lg), names(lg)), function(k) f * pr[[k]] + (1 - f) * lg[[k]])
}

pitcher_skill_ra9 <- function(a, target) {
  ip <- a$ip
  k   <- (a$so + target$k * SP_FIP_PRIOR_IP) / (ip + SP_FIP_PRIOR_IP)
  bb  <- (a$bb - a$ibb + a$hbp + target$bb * SP_FIP_PRIOR_IP) / (ip + SP_FIP_PRIOR_IP)
  fbp <- (a$ao + a$hr + target$fbp * SP_FIP_PRIOR_IP) / (ip + SP_FIP_PRIOR_IP)
  hr  <- (a$hr + target$hr * SP_FIP_PRIOR_IP) / (ip + SP_FIP_PRIOR_IP)
  xfip <- 13 * LG_HR_PER_FBP * fbp + 3 * bb - 2 * k + FIP_CONSTANT
  fip  <- 13 * hr + 3 * bb - 2 * k + FIP_CONSTANT
  ra9  <- 9 * (a$r + target$ra * SP_RA_PRIOR_IP) / (ip + SP_RA_PRIOR_IP)
  list(skill = SP_W_XFIP * xfip + (1 - SP_W_XFIP) * ra9, xfip = xfip, fip = fip, ra9 = ra9)
}

fetch_pitcher_gamelog <- function(pid, season) {
  key <- paste0("pitlog_", pid, "_", season)
  if (exists(key, envir = .gamelog_cache, inherits = FALSE))
    return(get(key, envir = .gamelog_cache, inherits = FALSE))
  url_g  <- sprintf("%s/people/%d/stats?stats=gameLog&group=pitching&season=%s&limit=100000",
                    MLB_API_BASE, pid, season)
  data_g <- http_get_json(url_g)
  sp <- unlist(lapply(data_g[["stats"]] %||% list(),
                      function(g) g[["splits"]] %||% list()), recursive=FALSE)
  sp <- Filter(function(s) !(as.character(scalar(s[["gameType"]], "R")) %in% MLB_SKIP_GAME_TYPES), sp %||% list())
  assign(key, sp, envir = .gamelog_cache); sp
}

# Per-starter point-in-time stats: season-to-date (and last season as a prior), all < D.
fetch_pitcher_pit <- function(pitcher_id, cutoff_date, season="2026",
                              n_starts=N_RECENT_STARTS, savant_pit_df=NULL) {
  pid <- clean_player_id(pitcher_id); if (is.na(pid)) return(NULL)
  pd  <- http_get_json(sprintf("%s/people/%d", MLB_API_BASE, pid))
  pitch_hand <- "R"
  if (!is.null(pd)) {
    ppl <- pd[["people"]]
    if (!is.null(ppl) && length(ppl) > 0)
      pitch_hand <- as.character(scalar(ppl[[1L]][["pitchHand"]][["code"]], "R"))
  }
  sc_pit <- if (USE_STATCAST) get_pitcher_statcast(pid, savant_pit_df) else NULL
  avg_velo      <- if (!is.null(sc_pit) && !is.na(sc_pit$AvgVelo %||% NA_real_)) sc_pit$AvgVelo else 92.0
  fb_arsenal    <- if (!is.null(sc_pit) && !is.na(sc_pit$FBPct_arsenal %||% NA_real_)) sc_pit$FBPct_arsenal else 0.55
  breaking_pct  <- if (!is.null(sc_pit) && !is.na(sc_pit$BreakingPct %||% NA_real_)) sc_pit$BreakingPct else NULL
  offspeed_pct  <- if (!is.null(sc_pit) && !is.na(sc_pit$OffspeedPct %||% NA_real_)) sc_pit$OffspeedPct else NULL
  whiff_pit     <- if (!is.null(sc_pit) && !is.na(sc_pit$WhiffPct %||% NA_real_)) sc_pit$WhiffPct else LG_AVG_WHIFF_PCT
  hr_fb_allowed <- if (!is.null(sc_pit) && !is.na(sc_pit$HR_FB_Rate_allowed %||% NA_real_)) sc_pit$HR_FB_Rate_allowed else NA_real_
  home_era_sc   <- if (!is.null(sc_pit) && !is.na(sc_pit$HomeERA %||% NA_real_)) sc_pit$HomeERA else NA_real_
  away_era_sc   <- if (!is.null(sc_pit) && !is.na(sc_pit$AwayERA %||% NA_real_)) sc_pit$AwayERA else NA_real_
  lob_pct       <- if (!is.null(sc_pit) && !is.na(sc_pit$LOB_Pct %||% NA_real_)) sc_pit$LOB_Pct else NA_real_
  first_inn_era <- if (!is.null(sc_pit) && !is.na(sc_pit$FirstInnERA %||% NA_real_)) sc_pit$FirstInnERA else NA_real_
  hand_sv       <- if (!is.null(sc_pit) && !is.na(sc_pit$PitchHand_sv %||% NA_character_)) sc_pit$PitchHand_sv else pitch_hand

  splits_all <- fetch_pitcher_gamelog(pid, season)
  std_sps <- filter_splits_before(splits_all, cutoff_date)
  a <- .pitch_agg(std_sps)

  # previous season as the regression target (a finished season: always leak-free).
  # Only looked up while this season's sample is still small.
  prev <- NULL
  if (a$ip < 60) {
    prev_sps <- tryCatch(fetch_pitcher_gamelog(pid, as.character(as.integer(season) - 1L)),
                         error = function(e) list())
    if (length(prev_sps)) prev <- .pitch_agg(prev_sps)
  }
  target <- .pitch_target(prev)
  sk <- pitcher_skill_ra9(a, target)

  ip <- a$ip
  bf <- a$bf
  kpct  <- (a$so + LG_AVG_K_PCT * 70) / (bf + 70)                       # K% stabilises fast
  bbpct <- (a$bb + LG_AVG_BB_PCT * 170) / (bf + 170)
  whip  <- if (ip > 0) ((a$h + a$bb) + 1.30 * 20) / (ip + 20) else 1.30
  hr9   <- 9 * (a$hr + target$hr * SP_FIP_PRIOR_IP) / (ip + SP_FIP_PRIOR_IP)
  gb_pct <- if ((a$go + a$ao) > 0) clamp((a$go + LG_AVG_GB_PCT * 60) / (a$go + a$ao + 60), 0.25, 0.65) else LG_AVG_GB_PCT
  fb_pct <- clamp(1 - gb_pct - 0.21, 0.20, 0.55)
  pip   <- if (ip > 0 && a$pc > 0) (a$pc + LG_AVG_PITCHES_PER_IP * 10) / (ip + 10) else LG_AVG_PITCHES_PER_IP
  # starts only: expected length of THIS outing
  prior_gs <- 10
  start_ip <- clamp((a$gs_ip + LG_IP_PER_START * prior_gs) / (a$gs + prior_gs), 3.0, 7.5)
  start_bf <- (a$gs_bf + LG_BF_PER_START * ifelse(a$gs == 0, 0.7, 1) * 3) / (a$gs + 3)

  # last few outings, reported for context (RecentERA) and the SP-tier label only
  rec_sps <- filter_splits_before(splits_all, cutoff_date, last_n=n_starts)
  ra <- .pitch_agg(rec_sps)
  recent_era <- if (ra$ip >= MIN_IP_PITCHER) 9 * ra$r / ra$ip else NULL
  days_rest <- days_rest_before(splits_all, cutoff_date, default = NA_integer_)

  list(
    PitcherID=pid, PitchHand=pitch_hand,
    ERA=clamp(sk$ra9, 0.50, 12.0),                 # regressed runs allowed per 9
    FIP=clamp(sk$fip, 0.50, 12.0),
    xFIP=clamp(sk$xfip, 0.50, 12.0),
    SIERA=clamp(compute_siera_proxy(kpct, bbpct, gb_pct), 0.50, 12.0),
    SkillRA9=clamp(sk$skill, 1.50, 9.00),
    WHIP=clamp(whip, 0.70, 2.50),
    HR9=clamp(hr9, 0.0, 4.0),
    KPct=kpct, BBPct=bbpct,
    PitchesPerIP=clamp(pip, 10.0, 24.0),
    RecentERA=recent_era, RecentIP=ra$ip, RecentStarts=ra$g,
    SeasonERA=if (ip > 0) 9 * a$r / ip else LG_AVG_ERA,
    GBPct=gb_pct, FBPct=fb_pct, AvgVelo=avg_velo,
    FBPct_arsenal=fb_arsenal, BreakingPct=breaking_pct, OffspeedPct=offspeed_pct,
    WhiffPct=whiff_pit, HR_FB_Rate_allowed=hr_fb_allowed,
    HomeERA=home_era_sc, AwayERA=away_era_sc,
    DaysRest=days_rest,
    AvgIPPerStart=start_ip, StartBF=start_bf, GamesStarted=a$gs,
    InningsPitched=ip, SeasonBF=bf, SeasonK=a$so, SeasonBB=a$bb,
    RawKPct=if (bf > 0) a$so / bf else NA_real_, RawBBPct=if (bf > 0) a$bb / bf else NA_real_,
    RawWHIP=if (ip > 0) (a$h + a$bb) / ip else NA_real_, RawHR9=if (ip > 0) 9 * a$hr / ip else NA_real_,
    LOB_Pct=lob_pct, FirstInnERA=first_inn_era, PitchHand_sv=hand_sv)
}

fetch_all_pitcher_stats <- function(pitcher_ids, cutoff_date, season="2026", savant_pit_df=NULL) {
  ids <- unique(pitcher_ids[!is.na(pitcher_ids)])
  if (!length(ids)) return(list())
  res <- lapply(ids, function(pid)
    tryCatch(fetch_pitcher_pit(pid, cutoff_date, season=season, savant_pit_df=savant_pit_df),
             error=function(e) NULL))
  names(res) <- as.character(ids); res
}

fetch_confirmed_lineup <- function(game_id) {
  if (is.null(game_id) || is.na(game_id)) return(NULL)
  gid_int <- tryCatch(as.integer(game_id), error=function(e) NA_integer_)
  if (is.na(gid_int)) return(NULL)
  # The club's posted lineup appears in the boxscore's battingOrder (a few hours before
  # first pitch). The old /game/{pk}/lineups path does not exist, and its 404 was
  # silenced, so confirmed lineups were never actually used.
  data <- http_get_json(sprintf("%s/game/%d/boxscore", MLB_API_BASE, gid_int), silent_404=TRUE)
  if (is.null(data)) return(NULL)
  tryCatch({
    result <- list(); side_of <- character()
    for (side in c("home","away")) {
      # The STARTING lineup: each player's battingOrder code is slot*100 for the man
      # who started in that slot (substitutes are slot*100+1, +2, ...). The team-level
      # battingOrder list shows whoever ENDED the game in each slot -- in a finished
      # box score that can be a pinch hitter or even a reliever -- so it is only the
      # fallback.
      st <- list()
      for (pl in (data[["teams"]][[side]][["players"]] %||% list())) {
        code <- suppressWarnings(as.integer(scalar(pl[["battingOrder"]], NA)))
        if (is.na(code) || code %% 100L != 0L) next
        pid <- clean_player_id(pl[["person"]][["id"]]); slot <- code %/% 100L
        if (!is.na(pid) && slot >= 1L && slot <= 9L) st[[as.character(pid)]] <- slot
      }
      if (length(st) < 9L) {
        bo <- data[["teams"]][[side]][["battingOrder"]] %||% list()
        if (length(bo) < 9L) next                     # not posted yet (or incomplete)
        st <- list(); slot <- 1L
        for (b in bo[seq_len(9L)]) {
          pid <- clean_player_id(b)
          if (!is.na(pid)) st[[as.character(pid)]] <- slot
          slot <- slot + 1L
        }
      }
      for (k in names(st)) { result[[k]] <- st[[k]]; side_of[k] <- side }
    }
    if (!length(result)) return(NULL)
    attr(result, "side") <- side_of                   # which club each id bats for
    result
  }, error=function(e) NULL)
}

fetch_game_boxscore <- function(game_id) {
  if (is.null(game_id) || is.na(game_id)) return(NULL)
  data <- http_get_json(sprintf("%s/schedule?gamePk=%d&hydrate=linescore", MLB_API_BASE, as.integer(game_id)))
  if (is.null(data) || !length(data[["dates"]])) return(NULL)   # unreachable: keep the schedule's status
  tryCatch({
    g  <- data[["dates"]][[1L]][["games"]][[1L]]
    if (is.null(g)) return(NULL)
    gs <- as.character(scalar(g[["status"]][["detailedState"]],"Scheduled"))
    hs <- coerce_numeric(scalar(g[["teams"]][["home"]][["score"]],0))
    as_<- coerce_numeric(scalar(g[["teams"]][["away"]][["score"]],0))
    aw <- if (gs %in% c("Final","Game Over","Completed Early"))
      if (hs > as_) "Home" else if (as_ > hs) "Away" else "Tie" else NA_character_
    list(GameStatus=gs, HomeScore=hs, AwayScore=as_, ActualWinner=aw,
         InningsCompleted=coerce_numeric(scalar(g[["linescore"]][["currentInning"]],9)))
  }, error=function(e) NULL)
}

fetch_game_player_stats <- function(game_id) {
  if (is.null(game_id) || is.na(game_id)) return(data.frame())
  data <- http_get_json(sprintf("%s/game/%d/boxscore", MLB_API_BASE, as.integer(game_id)))
  rows <- list()
  tryCatch({
    for (tt in c("home","away")) {
      td <- data[["teams"]][[tt]] %||% list()
      tn <- as.character(scalar(td[["team"]][["name"]],"Unknown"))
      for (pid_str in names(td[["players"]] %||% list())) {
        pdata <- td[["players"]][[pid_str]]
        pid   <- clean_player_id(sub("^ID","",pid_str)); if (is.na(pid)) next
        bat   <- pdata[["stats"]][["batting"]] %||% list()
        ab    <- coerce_numeric(scalar(bat[["atBats"]],0))
        pa    <- coerce_numeric(scalar(bat[["plateAppearances"]], ab))
        if (ab > 0 || pa > 0) rows[[length(rows)+1L]] <- data.frame(
          PlayerID=pid, PlayerName=as.character(scalar(pdata[["person"]][["fullName"]],"Unknown")),
          Team=tn, HomeRuns=coerce_numeric(scalar(bat[["homeRuns"]],0)),
          Hits=coerce_numeric(scalar(bat[["hits"]],0)), GameID=game_id, stringsAsFactors=FALSE)
      }
    }
  }, error=function(e) mlog_debug("  boxscore fetch failed: ", conditionMessage(e)))
  if (!length(rows)) return(data.frame()); bind_rows(rows)
}

fetch_game_sp_ks <- function(game_id) {
  if (is.null(game_id) || is.na(game_id)) return(NULL)
  data <- http_get_json(sprintf("%s/game/%d/boxscore", MLB_API_BASE, as.integer(game_id)), silent_404=TRUE)
  if (is.null(data)) return(NULL)
  tryCatch({
    result <- list()
    for (tt in c("home","away")) {
      td       <- data[["teams"]][[tt]] %||% list()
      pitchers <- td[["pitchers"]] %||% list()
      if (length(pitchers) == 0) next
      pid_num  <- tryCatch(as.integer(pitchers[[1]]), error=function(e) NA_integer_)
      if (is.na(pid_num)) next
      pdata    <- td[["players"]][[paste0("ID", pid_num)]] %||% list()
      pstat    <- pdata[["stats"]][["pitching"]] %||% list()
      ip       <- parse_innings_pitched(scalar(pstat[["inningsPitched"]], "0"))
      if (ip < 2.0) next
      result[[tt]] <- list(name=as.character(scalar(pdata[["person"]][["fullName"]], "Unknown")),
                           k=coerce_numeric(scalar(pstat[["strikeOuts"]], 0)), ip=ip)
    }
    if (length(result) == 0) NULL else result
  }, error=function(e) NULL)
}

compute_team_ratings <- function(pitching_df, team_batting_df, team_records=NULL) {
  PYTH_REG_PRIOR <- 40   # v7: games-prior for regressing Pythagorean toward .500 (feeds win-pick d_pyth)
  teams   <- union(pitching_df$Team, team_batting_df$Team)
  ratings <- setNames(rep(0.500, length(teams)), teams)
  pyth_wpcts <- setNames(rep(0.500, length(teams)), teams)
  for (tn in teams) {
    tb <- team_batting_df[team_batting_df$Team == tn, , drop=FALSE]
    tp <- pitching_df[pitching_df$Team         == tn, , drop=FALSE]
    if (nrow(tb) == 0 || nrow(tp) == 0) next
    g         <- max(tb$Games[1], 1)
    xwoba_val <- if ("xwOBA" %in% names(tb)) tb$xwOBA[1] else tb$wOBA[1]
    ops_val   <- if ("OPS" %in% names(tb)) tb$OPS[1] %||% 0.720 else 0.720
    bb_bonus  <- ((tb$BBPct[1] %||% LG_AVG_BB_PCT) - LG_AVG_BB_PCT)*7
    k_penalty <- ((tb$KPct[1]  %||% LG_AVG_K_PCT)  - LG_AVG_K_PCT)*(-4)
    sb_bonus  <- ((tb$StolenBases[1] %||% 0)/g - LG_AVG_SB_PER_G)*0.15
    babip_adj <- if ("BABIP" %in% names(tb))
      compute_babip_luck_adj(tb$BABIP[1], xbabip=NULL, rolling_games=min(g, 30)) else 1.0
    ops_adj <- clamp((ops_val - 0.720) * OPS_RUN_TRANSLATION * 0.45, -0.4, 0.4)
    rs  <- (xwoba_val*12 + (tb$ISO[1]%||%0.150)*6 + bb_bonus + k_penalty + sb_bonus + ops_adj) * babip_adj
    siera_val     <- if ("SIERA" %in% names(tp)) tp$SIERA[1] %||% LG_AVG_FIP else LG_AVG_FIP
    fip_adj       <- tp$FIP[1] %||% LG_AVG_FIP
    xfip_adj      <- tp$xFIP[1] %||% LG_AVG_FIP
    composite_pit <- SIERA_W_SIERA*siera_val + SIERA_W_XFIP*xfip_adj + (1 - SIERA_W_SIERA - SIERA_W_XFIP)*fip_adj
    whip_run_adj  <- if ("WHIP" %in% names(tp)) clamp((tp$WHIP[1] - 1.30) * 0.45, -0.5, 0.5) else 0.0
    ra  <- (tp$RunsAllowed[1] / max(tp$InningsPitched[1]/9, 1) * (composite_pit/LG_AVG_FIP)) + whip_run_adj
    pyth_r <- pythagorean_winpct(max(rs, 0.5), max(ra, 0.5))
    # v7: regress raw Pythagorean toward .500 by sample size before it feeds the
    # win-pick's dominant d_pyth feature. A regressed estimate predicts FUTURE games
    # better than the raw one; the more games seen, the less it's pulled to the mean.
    pyth_wpcts[[tn]] <- (pyth_r * g + 0.500 * PYTH_REG_PRIOR) / (g + PYTH_REG_PRIOR)
    rec <- if (!is.null(team_records)) lookup_record(tn, team_records) else NULL
    if (!is.null(rec) && (rec$wins + rec$losses) >= 20) {
      actual_wpct  <- rec$wins / (rec$wins + rec$losses)
      games_played <- rec$wins + rec$losses
      rec_weight   <- clamp(games_played / 162, 0, 0.45)
      blended_wpct <- (1 - rec_weight)*pyth_r + rec_weight*actual_wpct
      pyth_reg_f   <- compute_pythag_regression_factor(actual_wpct, pyth_r, games_played)
      ratings[[tn]] <- clamp(blended_wpct * pyth_reg_f, 0.25, 0.80)
    } else ratings[[tn]] <- pyth_r
  }
  list(ratings=ratings, pyth_wpcts=pyth_wpcts)
}

# NOTE: H2H removed. The pitcher_id arg is retained for signature
# compatibility but no batter-vs-pitcher lookup is performed; the
# Bayesian wOBA prior carries the matchup with zero H2H credibility.
compute_lineup_matchup_score <- function(player_df, team_name, pitcher_hand,
                                         pitcher_id, pitcher_ps, sp_adj, season="2026") {
  tb <- player_df[player_df$Team == team_name &
                    !is.na(player_df$PlateAppearances) &
                    player_df$PlateAppearances >= MIN_PA_SEASON, , drop=FALSE]
  if (nrow(tb) == 0) return(list(woba=LG_AVG_WOBA, score=0.0, n_matchups=0,
                                 lineup_lhp_pct=0.40, team_ops=0.720, team_slg=0.420))
  arsenal_f      <- if (!is.null(pitcher_ps))
    get_arsenal_hr_factor(pitcher_ps$FBPct_arsenal, pitcher_ps$BreakingPct, pitcher_ps$OffspeedPct) else 1.0
  arsenal_woba_f <- clamp(1.0 + (arsenal_f - 1.0)*0.4, 0.88, 1.12)
  slot_wobas <- numeric(9); slot_ops <- numeric(9); slot_slg <- numeric(9)
  for (slot in 1:9) {
    candidates <- tb[!is.na(tb$LineupSlot) & tb$LineupSlot == slot, , drop=FALSE]
    if (nrow(candidates) == 0) {
      sv <- tb$LineupSlot; sv[is.na(sv)] <- 5L
      candidates <- tb[order(abs(sv - slot)), , drop=FALSE]
    }
    if (nrow(candidates) == 0) {
      slot_wobas[slot] <- LG_AVG_WOBA; slot_ops[slot] <- 0.720; slot_slg[slot] <- 0.420; next
    }
    pl        <- candidates[1, ]; bh <- as.character(pl$BatHand %||% "R")
    platoon_w <- platoon_woba_mult(bh, pitcher_hand)
    base_woba <- pl$xwOBA %||% pl$wOBA %||% LG_AVG_WOBA
    # H2H removed -> prior only (career_pa = 0)
    bay <- bayesian_matchup_woba(NULL, 0, base_woba * platoon_w, arsenal_woba_f,
                                 sp_woba_mult=sp_adj$woba_mult * sp_adj$contact_quality)
    slot_wobas[slot] <- bay$woba
    slot_ops[slot]   <- pl$OPS %||% 0.720
    slot_slg[slot]   <- pl$SLG %||% 0.420
  }
  weighted_woba <- sum(slot_wobas * LINEUP_PA_BY_SLOT) / sum(LINEUP_PA_BY_SLOT)
  weighted_ops  <- sum(slot_ops   * LINEUP_PA_BY_SLOT) / sum(LINEUP_PA_BY_SLOT)
  weighted_slg  <- sum(slot_slg   * LINEUP_PA_BY_SLOT) / sum(LINEUP_PA_BY_SLOT)
  lhp_count <- sum(tb$BatHand == "L" | tb$BatHand == "S", na.rm=TRUE)
  lineup_lhp_pct <- if (nrow(tb) > 0) lhp_count / nrow(tb) else 0.40
  list(woba=weighted_woba, score=(weighted_woba - LG_AVG_WOBA)*20.0,
       n_matchups=nrow(tb), lineup_lhp_pct=lineup_lhp_pct,
       team_ops=weighted_ops, team_slg=weighted_slg)
}

# ===== RUN MODEL (v10) =====================================================
# Replaces the old additive "Monte Carlo" run estimate, which (a) moved runs the
# wrong way for the opposing pitcher (a bad starter or bullpen LOWERED the offense's
# projected runs), (b) counted lineup wOBA, K%, ISO and the umpire several times over,
# and (c) simulated runs with too little spread (negative-binomial size 8), which is
# why it put 87% on games the favourite won 52% of the time.
#
# Expected runs for a team = league runs/game x its offense index x the opposing
# staff's run-prevention index x park x weather x home/away. Each index is a
# regressed, point-in-time rate:
#   offense  = half wOBA-implied runs (wOBA regressed with 3,000 PA toward last
#              season's level) and half actual runs/game (regressed with 100 games)
#   pitching = expected starter innings x starter skill (xFIP/RA9 blend, see
#              fetch_pitcher_pit) + the rest of the game x the staff's regressed FIP
# Win probability is then EXACT under two independent negative binomials (size 4,
# which matches the spread of real MLB scores), with ties -- extra innings -- split
# by relative scoring strength instead of being handed to the road team.
# Validated walk-forward on the 2026 season (tuned Apr-Jun, tested Jul-Sep):
#   test accuracy 57.5% and Brier 0.2426, against 55.9% and 0.2447 for the old model.
RUN_OFF_PRIOR_PA  <- 3000
RUN_RPG_PRIOR_G   <- 100
RUN_W_ACTUAL_RS   <- 0.50
RUN_HFA           <- 0.03     # home +3% runs, road -3%
RUN_NB_SIZE       <- 4
RUN_SHORT_REST    <- 0.06     # starter on <= 3 days' rest allows 6% more runs
RUN_WOBA_SCALE    <- 1.20
RUN_LINEUP_W      <- 0.50     # share of a confirmed lineup's edge over the team norm
RUN_LINEUP_CAP    <- 0.04

mlb_offense_index <- function(tb_cur, tb_prev, lg_prev_woba = NA_real_, lineup_woba = NA_real_) {
  lg_rpg <- LG_AVG_RUNS_PER_GAME; lg_w <- LG_AVG_WOBA
  pa  <- if (!is.null(tb_cur)) as.numeric(tb_cur$PlateAppearances %||% 0) else 0
  g   <- if (!is.null(tb_cur)) as.numeric(tb_cur$Games %||% 0) else 0
  w   <- if (!is.null(tb_cur)) as.numeric(tb_cur$wOBA %||% lg_w) else lg_w
  rs  <- if (!is.null(tb_cur) && "Runs" %in% names(tb_cur)) as.numeric(tb_cur$Runs) else lg_rpg * g
  if (!is.finite(pa)) pa <- 0; if (!is.finite(g)) g <- 0; if (!is.finite(w)) w <- lg_w
  if (!is.finite(rs)) rs <- lg_rpg * g
  prior <- lg_w
  if (!is.null(tb_prev) && is.finite(as.numeric(tb_prev$wOBA %||% NA)) && is.finite(lg_prev_woba))
    prior <- lg_w + (as.numeric(tb_prev$wOBA) - lg_prev_woba)
  wreg <- (w * pa + prior * RUN_OFF_PRIOR_PA) / (pa + RUN_OFF_PRIOR_PA)
  off_woba <- lg_rpg + (wreg - lg_w) / RUN_WOBA_SCALE * LG_PA_PER_GAME
  off_rs   <- (rs + lg_rpg * RUN_RPG_PRIOR_G) / (g + RUN_RPG_PRIOR_G)
  idx <- ((1 - RUN_W_ACTUAL_RS) * off_woba + RUN_W_ACTUAL_RS * off_rs) / lg_rpg
  if (is.finite(lineup_woba)) {
    edge <- (lineup_woba - wreg) / RUN_WOBA_SCALE * LG_PA_PER_GAME / lg_rpg
    idx <- idx * (1 + clamp(RUN_LINEUP_W * edge, -RUN_LINEUP_CAP, RUN_LINEUP_CAP))
  }
  clamp(idx, 0.60, 1.50)
}

mlb_pitching_index <- function(sp, staff) {
  lg <- LG_AVG_ERA
  pen <- if (!is.null(staff) && is.finite(as.numeric(staff$PenSkill %||% NA))) as.numeric(staff$PenSkill) else lg
  if (is.null(sp)) { sk <- pen; sip <- LG_IP_PER_START }
  else {
    sk  <- as.numeric(sp$SkillRA9 %||% lg); if (!is.finite(sk)) sk <- lg
    sip <- as.numeric(sp$AvgIPPerStart %||% LG_IP_PER_START); if (!is.finite(sip)) sip <- LG_IP_PER_START
    rest <- suppressWarnings(as.numeric(sp$DaysRest %||% NA))
    if (is.finite(rest) && rest <= 3) sk <- sk * (1 + RUN_SHORT_REST)
  }
  share <- clamp(sip, 3, 7.5) / 9
  list(idx = clamp((share * sk + (1 - share) * pen) / lg, 0.55, 1.70), sp = sk, pen = pen, sip = sip)
}

mlb_win_prob <- function(mu_h, mu_a, size = RUN_NB_SIZE, maxr = 30L) {
  r  <- 0:maxr
  dh <- stats::dnbinom(r, size = size, mu = mu_h); da <- stats::dnbinom(r, size = size, mu = mu_a)
  ca <- cumsum(da)
  p_gt  <- sum(dh[-1] * ca[-length(ca)])
  p_tie <- sum(dh * da)
  tilt  <- mu_h^1.8 / (mu_h^1.8 + mu_a^1.8)
  clamp(p_gt + p_tie * (0.5 + 0.5 * (tilt - 0.5)), 0.03, 0.97)
}

mlb_game_model <- function(off_h, off_a, pit_h, pit_a, park_runs = 1, weather_runs = 1) {
  env <- (park_runs %||% 1)^PARK_RUN_ELASTICITY * (weather_runs %||% 1)
  mu_h <- LG_AVG_RUNS_PER_GAME * off_h * pit_a$idx * env * (1 + RUN_HFA)
  mu_a <- LG_AVG_RUNS_PER_GAME * off_a * pit_h$idx * env * (1 - RUN_HFA)
  list(mu_h = mu_h, mu_a = mu_a, hwp = mlb_win_prob(mu_h, mu_a))
}

# Confirmed-lineup wOBA (slot-weighted), each hitter regressed 200 PA toward his team.
lineup_woba_from_confirmed <- function(player_df, team, confirmed, team_woba, side = NULL) {
  if (is.null(confirmed) || !length(confirmed) || is.null(player_df) || !nrow(player_df)) return(NA_real_)
  if (!is.finite(team_woba)) return(NA_real_)
  ids <- suppressWarnings(as.integer(names(confirmed))); slots <- unlist(confirmed, use.names = FALSE)
  tb <- player_df[player_df$Team == team, , drop = FALSE]
  if (!nrow(tb)) return(NA_real_)
  sd_ <- attr(confirmed, "side")
  if (!is.null(side) && !is.null(sd_) && length(sd_) == length(ids)) {
    # this club's nine, including anyone not yet in the batting frames (a player
    # activated today has no row there): he counts at the team's own rate
    mine <- sd_ == side & slots >= 1 & slots <= 9
    if (sum(mine) < 9) return(NA_real_)
    j <- match(ids[mine], tb$PlayerID); sl <- slots[mine]
    if (sum(!is.na(j)) < 7) return(NA_real_)          # mostly unknown: no adjustment
    pa <- ifelse(is.na(j), 0, tb$PlateAppearances[j]); w <- ifelse(is.na(j), team_woba, tb$wOBA[j])
  } else {
    j <- match(ids, tb$PlayerID); keep <- !is.na(j) & slots >= 1 & slots <= 9
    if (sum(keep) < 9) return(NA_real_)
    pa <- tb$PlateAppearances[j[keep]]; w <- tb$wOBA[j[keep]]; sl <- slots[keep]
  }
  pa[!is.finite(pa)] <- 0; w[!is.finite(w)] <- team_woba
  reg <- (w * pa + team_woba * 200) / (pa + 200)
  wt <- LINEUP_PA_BY_SLOT[sl]
  sum(reg * wt) / sum(wt)
}

# ===== EMPIRICAL (data-weighted) WIN PROBABILITY =====================
# Replaces the MC-blend + WHIP-gate + Platt heuristics for the WIN pick with a
# calibrated logistic on the 3 features that carried the signal in the 891-game
# backtest: starter-WHIP diff, staff-K% diff, season-Pythagorean diff.
# (Cross-validated accuracy ~56.6% vs the old model's 52.1% and always-home 52.75%.)
#
# Features are HOME-minus-AWAY, computed from SEASON-to-date frames so they match
# the backtest_games.csv columns the coefficients were fit on:
#   d_whip = skillERA(home) - skillERA(away)   [mean of SIERA/xFIP/FIP; starter PIT if IP>MIN_IP_SEASON else season; v7 -- was raw WHIP]
#   d_kpct = staffK%(home)     - staffK%(away)        [pitching_df_season$KPct]
#   d_pyth = pyth_wpct(home)   - pyth_wpct(away)       [team_ratings$pyth_wpcts]
#
# >>> THE DEFAULT COEFFICIENTS BELOW WERE FIT IN-SAMPLE ON 2026-03-23..05-30. For an
# >>> honest test, REFIT on an earlier window and evaluate on a later one you did NOT
# >>> fit on (use refit_winprob.R). Coefs evaluated on their own fit window read high.
USE_EMPIRICAL_WINPROB <- TRUE
EMP_WINPROB_COEF <- c(intercept = 0.1346, d_whip = -0.10, d_kpct = 0, d_pyth = 1.4679)  # d_whip rescaled for skill-ERA units (v7)
EMP_CONF_HIGH <- 0.60    # raised from 0.575: OOS, 0.575-0.60 picks won only ~52%; 0.60+ wins ~60%
EMP_CONF_MED  <- 0.535   # pick-prob >= this -> "Medium"

# === ADAPTIVE WIN MODEL (self-refitting, recency-weighted, leakage-safe) ========
# v10: the pick starts from the run model's probability (validated to be calibrated:
# a logistic fit of results on it returns slope 1.03, intercept ~0) and the adaptive
# layer may re-weight it and the Pythagorean gap as THIS model version's own graded
# games accumulate. Rows written by older model versions are never used to fit it --
# their probabilities came from a different engine.
#
# LEAKAGE RULE (enforced): weights used to predict games on date D are fit ONLY on
# games final BEFORE D (awm_fit(..., as_of = D)). A game never trains on itself.
MLB_MODEL_VER         <- "mlb-runs-v10"
AWM_HISTORY_PATH      <- "predictions_ledger.csv"  # picks on record, frozen at first pitch (auto-written)
# What the CURRENT model says about every game, point-in-time, graded as results come
# in. This -- not the pick ledger -- is what the adaptive layer and the calibration
# learn from. The ledger keeps the pick that was on file at first pitch (so an older
# model's picks stay on record), which means after a model upgrade it holds no games
# the new model predicted and the learning layer would sit idle for a season. The
# memory is keyed by game AND model version, backfilled for any date it is missing,
# and follows the same freeze-at-first-pitch rule as the ledger.
AWM_MEMORY_PATH       <- "mlb_model_memory.csv"
AWM_HALF_LIFE_DEFAULT <- 60     # fallback forgetting speed until the model selects its own
AWM_PRIOR_STRENGTH    <- 800    # ~graded games needed before the data outvotes the prior
AWM_MIN_ROWS          <- 150    # below this many graded rows the prior is used as is
AWM_PRIOR_COEF <- c(`(Intercept)` = 0.0, z_run = 1.0, D_pyth = 0.0)
FINAL_CAL_MIN_GAMES   <- 300

awm_logit <- function(p) { p <- pmax(pmin(p, 0.98), 0.02); log(p / (1 - p)) }
awm_half_life_label <- function(hl) {
  hl <- suppressWarnings(as.numeric(hl))
  if (!length(hl) || !is.finite(hl)) "half-life ?" else if (hl >= 1e5) "every game weighted equally" else sprintf("half-life %g d", hl)
}

awm_load <- function(path = AWM_HISTORY_PATH) {
  if (!file.exists(path)) return(NULL)
  h <- tryCatch(read.csv(path, stringsAsFactors = FALSE), error = function(e) NULL)
  if (is.null(h) || !nrow(h)) return(NULL)
  # read.csv turns a GameType column holding only "F" (wild card) into logical FALSE
  if ("GameType" %in% names(h)) {
    g <- h$GameType
    if (is.logical(g)) g <- ifelse(is.na(g), NA_character_, ifelse(g, "T", "F"))
    g <- as.character(g); g[g %in% "FALSE"] <- "F"; g[g %in% "TRUE"] <- "T"
    h$GameType <- g
  }
  h
}

# Training rows for the adaptive layer and the calibration: the model memory, plus
# any current-version rows in the pick ledger the memory lacks (e.g. the memory file
# was deleted). Each game appears once.
awm_training_history <- function() {
  m <- awm_load(AWM_MEMORY_PATH)
  l <- awm_load(AWM_HISTORY_PATH)
  if (!is.null(l) && all(c("ModelVer", "GameID") %in% names(l))) {
    l <- l[l$ModelVer %in% MLB_MODEL_VER, , drop = FALSE]
    if (!is.null(m) && nrow(m) && all(c("ModelVer", "GameID") %in% names(m)))
      l <- l[!(paste(l$GameID, l$ModelVer) %in% paste(m$GameID, m$ModelVer)), , drop = FALSE]
    if (nrow(l)) m <- if (is.null(m) || !nrow(m)) l else .ledger_bind(m, l[, intersect(names(l), names(m)), drop = FALSE])
  }
  if (is.null(m) || !nrow(m)) NULL else m
}

# Graded rows written by the CURRENT model version, strictly before a date.
awm_version_rows <- function(history, as_of_date) {
  if (is.null(history) || !nrow(history)) return(NULL)
  need <- c("HomeWon", "GameDate", "RunHomeWP", "D_pyth", "ModelVer")
  if (!all(need %in% names(history))) return(NULL)
  h <- history[!is.na(history$HomeWon) & history$ModelVer %in% MLB_MODEL_VER, , drop = FALSE]
  h <- h[mlb_competitive_rows(h), , drop = FALSE]
  h <- h[as.Date(h$GameDate) < as.Date(as_of_date), , drop = FALSE]          # <<< LEAKAGE GUARD
  h$RunHomeWP <- suppressWarnings(as.numeric(h$RunHomeWP))
  h$D_pyth    <- suppressWarnings(as.numeric(h$D_pyth))
  h$home_win  <- as.integer(h$HomeWon)
  h <- h[stats::complete.cases(h[, c("home_win", "RunHomeWP", "D_pyth")]), , drop = FALSE]
  if (!nrow(h)) return(NULL)
  h$z_run <- awm_logit(h$RunHomeWP / 100)
  h
}

# Re-fit the adaptive layer as of a date, recent games weighted more, shrunk to the prior.
awm_fit <- function(history, as_of_date, half_life = AWM_HALF_LIFE_DEFAULT) {
  prior <- AWM_PRIOR_COEF
  h <- awm_version_rows(history, as_of_date)
  if (is.null(h) || nrow(h) < AWM_MIN_ROWS) return(list(coef = prior, n = NROW(h), w_data = 0))
  asof <- as.Date(as_of_date)
  wts <- 0.5 ^ (as.numeric(asof - as.Date(h$GameDate)) / half_life)   # recency weights
  fit <- tryCatch(suppressWarnings(glm(home_win ~ z_run + D_pyth, data = h,
                                       family = binomial(), weights = wts)), error = function(e) NULL)
  if (is.null(fit) || !all(is.finite(coef(fit)[names(prior)])))
    return(list(coef = prior, n = nrow(h), w_data = 0))
  cf <- coef(fit)[names(prior)]; names(cf) <- names(prior)
  n_eff  <- sum(wts)
  w_data <- n_eff / (n_eff + AWM_PRIOR_STRENGTH)            # shrink to prior when thin
  list(coef = w_data * cf + (1 - w_data) * prior, n = nrow(h), w_data = w_data)
}

awm_predict_home <- function(coef, run_hwp, d_pyth) {
  x <- c(`(Intercept)` = 1, z_run = awm_logit(run_hwp), D_pyth = d_pyth %||% 0)
  x[!is.finite(x)] <- 0
  pmax(pmin(plogis(sum(coef[names(x)] * x, na.rm = TRUE)), 0.95), 0.05)
}

# ---------------------------------------------------------------------------
# FINAL-STAGE CALIBRATION (v8)
# The learning layer's probabilities run a little hot toward home (it says 57%
# when home really wins ~54%). This learns that bias from the model's own past
# results and gently deflates the final number so a stated 57% MEANS 57%.
#
# Key discipline: it always trains on the RAW model probability (RawHomeWP, or
# HomeWinProb for older rows logged before v8), never on an already-calibrated
# number -- so it can't chase its own tail over time. It is fit point-in-time
# (only games final BEFORE the slate date) with recent games weighted more, and
# falls back to "do nothing" until there are enough games to fit it honestly.
fit_final_calibration <- function(history, as_of_date, half_life = 60, min_games = FINAL_CAL_MIN_GAMES) {
  ident <- list(a = 1, b = 0, ok = FALSE, n = 0)
  if (is.null(history) || !nrow(history)) return(ident)
  if (!all(c("RawHomeWP", "HomeWon", "GameDate", "ModelVer") %in% names(history))) return(ident)
  # v10: only this model version's own raw probabilities, regular season/postseason only
  h <- history[!is.na(history$HomeWon) & history$ModelVer %in% MLB_MODEL_VER, , drop = FALSE]
  h <- h[mlb_competitive_rows(h), , drop = FALSE]
  asof <- as.Date(as_of_date)
  h <- h[as.Date(h$GameDate) < asof, , drop = FALSE]                 # <<< point-in-time, no leakage
  if (!nrow(h)) return(ident)
  p  <- suppressWarnings(as.numeric(h$RawHomeWP)) / 100
  y  <- as.integer(as.logical(h$HomeWon))
  gd <- as.Date(h$GameDate)
  ok <- is.finite(p) & p > 0.02 & p < 0.98 & !is.na(y)
  p <- p[ok]; y <- y[ok]; gd <- gd[ok]
  if (length(p) < min_games) return(ident)
  z   <- qlogis(p)
  wts <- 0.5 ^ (as.numeric(asof - gd) / half_life)                  # recency-weighted, like the learner
  fit <- tryCatch(suppressWarnings(glm(y ~ z, family = binomial(), weights = wts)),
                  error = function(e) NULL)
  if (is.null(fit) || any(!is.finite(coef(fit)))) return(ident)
  w <- sum(wts) / (sum(wts) + 600)                                    # shrink toward "no change"
  list(a = w * unname(coef(fit)[["z"]]) + (1 - w), b = w * unname(coef(fit)[["(Intercept)"]]),
       ok = TRUE, n = length(p))
}

apply_final_calibration <- function(hwp, cal) {
  if (is.null(cal) || !isTRUE(cal$ok)) return(hwp)
  z <- qlogis(pmin(pmax(hwp, 0.02), 0.98))
  pmin(pmax(plogis(cal$a * z + cal$b), 0.05), 0.95)
}

# TRUE / "TRUE" / "True" / "T" -> TRUE (a ledger saved by another program may
# store its flags as text).
.is_true <- function(x) {
  if (is.logical(x)) return(x %in% TRUE)
  toupper(trimws(as.character(x))) %in% c("TRUE", "T")
}

# TRUE for each row whose game is under way (or already graded), tolerant of a
# frame that is missing any one of the status columns -- `NULL %in% TRUE` is
# logical(0), and OR-ing that against a real vector silently collapses the whole
# result to length zero.
.started_flag <- function(df, cols = c("IsLive", "IsFinal"), graded = NULL) {
  n <- nrow(df); out <- rep(FALSE, n)
  for (cc in cols) if (cc %in% names(df)) out <- out | .is_true(df[[cc]])
  if (!is.null(graded) && graded %in% names(df)) out <- out | !is.na(df[[graded]])
  out
}

# Stack a ledger read back from CSV on top of freshly computed rows. A column can
# come back from disk as a different type than the live one (all-blank -> logical,
# a hand-edited file -> character), and dplyr refuses to combine those, which
# used to make the append fail silently. Mismatches are resolved here instead:
# an all-NA column adopts the other side's type, numbers/logicals mix freely, and
# anything else is combined as text (read.csv re-types it on the next load).
.ledger_bind <- function(old, new) {
  for (cc in intersect(names(old), names(new))) {
    a <- old[[cc]]; b <- new[[cc]]
    if (identical(class(a), class(b))) next
    num_like <- function(x) is.numeric(x) || is.logical(x)
    if (num_like(a) && num_like(b)) next
    if (all(is.na(a))) { old[[cc]] <- b[rep(NA_integer_, length(a))]; next }
    if (all(is.na(b))) { new[[cc]] <- a[rep(NA_integer_, length(b))]; next }
    old[[cc]] <- as.character(a); new[[cc]] <- as.character(b)
  }
  dplyr::bind_rows(old, new)
}

# Grow the model's memory with this run's games.
#
# WRITE-ONCE AT FIRST PITCH (v9). This used to dedup with fromLast=TRUE -- "keep
# newest" -- so re-opening an old slate REWROTE that slate's stored rows using
# today's weights. The ledger is the model's training set, so rewriting it moved
# every downstream fit and made yesterday's forecast a moving target.
#
# The rule now:
#   * game not started  -> the row is refreshed. The pick SHOULD still improve as
#                          lineups are confirmed and a TBD starter is named.
#   * game started      -> the row is frozen. Nothing about the prediction is ever
#     (live or final)      written again; only the result is filled in, and the
#                          win/loss is scored against the pick that was on file.
# So a pick is fixed at first pitch, which is the only version of it you could
# actually have acted on.
awm_append <- function(rows, path = AWM_HISTORY_PATH) {
  if (is.null(rows) || !nrow(rows)) return(invisible(FALSE))
  rows$Started <- .started_flag(rows, graded = "HomeWon")
  cols <- intersect(c("GameDate","GameID","Matchup","ProjectedWinner","WinProbNum",
                      "Confidence","HomeWinProb",
                      "MCHomeWP","RawHomeWP","RunHomeWP","EmpHomeWP","D_whip","D_kpct","D_pyth",
                      "C_whip","C_kpct","C_pyth","C_run","D_mw","D_mk","D_mp",
                      "ProjHomeRuns","ProjAwayRuns","ModelVer","GameType",
                      "Started","HomeWon","IsCorrect","Venue","Umpire"), names(rows))
  new <- rows[, cols, drop = FALSE]
  old <- awm_load(path)
  if (is.null(old) || !nrow(old) || !("GameID" %in% names(old)))
    return(tryCatch({ csv_replace(new, path); invisible(TRUE) },
                    error = function(e) invisible(FALSE)))
  for (cc in setdiff(cols, names(old))) old[[cc]] <- NA          # legacy ledgers
  if (!("Started" %in% names(old))) old$Started <- !is.na(old$HomeWon)
  started_old <- .is_true(old$Started) | !is.na(old$HomeWon)
  idx <- match(as.character(new$GameID), as.character(old$GameID))
  for (k in which(!is.na(idx))) {
    o <- idx[k]
    if (started_old[o]) {
      # frozen row: fill in the result only, and score the pick that is ON FILE
      if (is.na(old$HomeWon[o]) && !is.na(new$HomeWon[k])) {
        old$HomeWon[o]  <- new$HomeWon[k]
        old$Started[o]  <- TRUE
        mtc  <- as.character(old$Matchup[o] %||% "")
        home <- sub("^.* @ ", "", mtc); away <- sub(" @ .*$", "", mtc)
        win  <- if (isTRUE(as.integer(old$HomeWon[o]) == 1L)) home else away
        pick <- as.character(old$ProjectedWinner[o])
        old$IsCorrect[o] <- if (is.na(pick) || !nzchar(mtc)) new$IsCorrect[k] else (pick == win)
      }
    } else {
      for (cc in cols) old[[cc]][o] <- new[[cc]][k]              # pre-game: refresh
    }
  }
  comb <- .ledger_bind(old, new[is.na(idx), , drop = FALSE])
  comb <- comb[!duplicated(comb$GameID, fromLast = FALSE), , drop = FALSE]
  tryCatch({ csv_replace(comb, path); invisible(TRUE) },
           error = function(e) invisible(FALSE))
}

# Record the current model's own numbers in the model memory (see AWM_MEMORY_PATH).
# `rows` must be the projection BEFORE locked picks are swapped in. Same first-pitch
# rule as awm_append(): refreshed until the game starts, then frozen with only the
# result filled in. Keyed by game + model version, so a later model can keep its
# own record next to this one.
AWM_MEMORY_COLS <- c("GameDate", "GameID", "Matchup", "GameType", "ModelVer", "ProjectedWinner",
                     "WinProbNum", "Confidence", "HomeWinProb", "RawHomeWP", "RunHomeWP", "D_pyth",
                     "C_run", "C_pyth", "ProjHomeRuns", "ProjAwayRuns", "Started", "HomeWon",
                     "IsCorrect", "Venue")
awm_memory_append <- function(rows, path = AWM_MEMORY_PATH) {
  if (is.null(rows) || !nrow(rows)) return(invisible(FALSE))
  rows$Started <- .started_flag(rows, graded = "HomeWon")
  if (!("ModelVer" %in% names(rows))) rows$ModelVer <- MLB_MODEL_VER
  new <- rows[, intersect(AWM_MEMORY_COLS, names(rows)), drop = FALSE]
  new <- new[!is.na(new$GameID), , drop = FALSE]
  if (!nrow(new)) return(invisible(FALSE))
  old <- awm_load(path)
  if (is.null(old) || !nrow(old) || !all(c("GameID", "ModelVer") %in% names(old)))
    return(tryCatch({ csv_replace(new, path); invisible(TRUE) },
                    error = function(e) invisible(FALSE)))
  for (cc in setdiff(names(new), names(old))) old[[cc]] <- NA
  started_old <- .is_true(old$Started) | !is.na(old$HomeWon)
  idx <- match(paste(new$GameID, new$ModelVer), paste(old$GameID, old$ModelVer))
  for (k in which(!is.na(idx))) {
    o <- idx[k]
    if (started_old[o]) {
      if (is.na(old$HomeWon[o]) && !is.na(new$HomeWon[k])) {
        old$HomeWon[o] <- new$HomeWon[k]; old$Started[o] <- TRUE
        mtc  <- as.character(old$Matchup[o] %||% "")
        win  <- if (isTRUE(as.integer(old$HomeWon[o]) == 1L)) sub("^.* @ ", "", mtc) else sub(" @ .*$", "", mtc)
        pick <- as.character(old$ProjectedWinner[o])
        old$IsCorrect[o] <- if (is.na(pick) || !nzchar(mtc)) new$IsCorrect[k] else (pick == win)
      }
    } else {
      for (cc in names(new)) old[[cc]][o] <- new[[cc]][k]
    }
  }
  comb <- .ledger_bind(old, new[is.na(idx), , drop = FALSE])
  comb <- comb[!duplicated(paste(comb$GameID, comb$ModelVer)), , drop = FALSE]
  tryCatch({ csv_replace(comb, path); invisible(TRUE) },
           error = function(e) invisible(FALSE))
}

# ---------------------------------------------------------------------------
# LOCKED HISTORY (v9)
# The guarantee the ledger cannot give on its own: a slate you have already
# forecast displays the pick you actually made, not a fresh re-derivation of it.
# Any game already in the ledger has its pick, probability and confidence read
# back out of the ledger, and the win/loss is re-scored against THAT pick. So a
# past date's record is fixed the moment it is first graded, no matter what the
# model has learned since. Games not yet in the ledger (today's slate, or a date
# first opened after this version) are computed live and then locked on write.
awm_apply_locked <- function(df, history = NULL) {
  if (is.null(df) || !nrow(df)) return(df)
  df$Locked <- FALSE
  if (is.null(history) || !nrow(history)) return(df)
  if (!all(c("GameID", "ProjectedWinner") %in% names(history))) return(df)
  idx <- match(as.character(df$GameID), as.character(history$GameID))
  stored_pick <- rep(NA_character_, nrow(df))
  stored_pick[!is.na(idx)] <- as.character(history$ProjectedWinner[idx[!is.na(idx)]])
  stored_started <- rep(FALSE, nrow(df))
  if ("Started" %in% names(history))
    stored_started[!is.na(idx)] <- .is_true(history$Started[idx[!is.na(idx)]])
  if ("HomeWon" %in% names(history))
    stored_started[!is.na(idx)] <- stored_started[!is.na(idx)] |
    !is.na(history$HomeWon[idx[!is.na(idx)]])
  # A stored pick is authoritative once the game is under way -- either it was
  # already frozen, or this run is the first to see first pitch. Before that the
  # pick is allowed to keep improving as lineups firm up.
  started_now <- .started_flag(df, graded = "HomeWon")
  hit <- !is.na(stored_pick) & nzchar(stored_pick) & stored_pick != "NA" &
    (stored_started | started_now)
  if (!any(hit)) return(df)
  hrow <- history[idx[hit], , drop = FALSE]
  home_team <- sub("^.* @ ", "", df$Matchup[hit])
  df$ProjectedWinner[hit] <- stored_pick[hit]
  if ("Confidence" %in% names(hrow)) {
    cf <- as.character(hrow$Confidence)
    ok <- !is.na(cf) & nzchar(cf); df$Confidence[hit][ok] <- cf[ok]
  }
  if ("HomeWinProb" %in% names(hrow)) {
    hw <- suppressWarnings(as.numeric(hrow$HomeWinProb))
    ok <- is.finite(hw)
    if (any(ok)) {
      df$HomeWinProb[hit][ok] <- hw[ok]
      wp <- ifelse(stored_pick[hit][ok] == home_team[ok], hw[ok], 100 - hw[ok])
      df$WinProbNum[hit][ok] <- round(wp, 1)
      df$WinProb[hit][ok]    <- paste0(round(wp, 1), "%")
      df$StrengthPct[hit][ok] <- round(pmax(hw[ok], 100 - hw[ok]))
    }
  }
  if ("RawHomeWP" %in% names(hrow)) {
    rw <- suppressWarnings(as.numeric(hrow$RawHomeWP))
    ok <- is.finite(rw); df$RawHomeWP[hit][ok] <- rw[ok]
  }
  df$FinalPick[hit] <- df$ProjectedWinner[hit]
  # the pick on file keeps the version of the model that made it (none on a legacy row),
  # so an older model's pick is never written back labelled as this model's
  if ("ModelVer" %in% names(df))
    df$ModelVer[hit] <- if ("ModelVer" %in% names(hrow)) as.character(hrow$ModelVer) else NA_character_
  # re-score the stored pick against the result this run actually observed
  winner <- ifelse(df$IsFinal[hit] & !is.na(df$HomeWon[hit]),
                   ifelse(df$HomeWon[hit] == 1L, home_team,
                          sub(" @ .*$", "", df$Matchup[hit])), NA_character_)
  df$IsCorrect[hit] <- ifelse(is.na(winner), NA, df$ProjectedWinner[hit] == winner)
  df$Locked[hit] <- TRUE
  df
}

# Pick the forgetting half-life the model should use, by held-out accuracy. No guessing.
awm_select_half_life <- function(history, as_of_date,
                                 candidates = c(25, 45, 60, 90, 1e6),
                                 min_train = 300) {
  h <- awm_version_rows(history, as_of_date)
  if (is.null(h) || nrow(h) < min_train + 100) return(AWM_HALF_LIFE_DEFAULT)
  h <- h[order(h$GameDate), ]
  dts <- sort(unique(h$GameDate)); cutd <- dts[ceiling(0.70 * length(dts))]
  tr <- h[h$GameDate <= cutd, , drop = FALSE]; te <- h[h$GameDate > cutd, , drop = FALSE]
  if (nrow(te) < 60) return(AWM_HALF_LIFE_DEFAULT)
  asof <- as.Date(cutd) + 1
  score <- sapply(candidates, function(hl) {
    w <- 0.5 ^ (as.numeric(asof - as.Date(tr$GameDate)) / hl)
    fit <- tryCatch(suppressWarnings(glm(home_win ~ z_run + D_pyth,
                                         data = tr, family = binomial(), weights = w)), error = function(e) NULL)
    if (is.null(fit)) return(Inf)
    p <- tryCatch(predict(fit, newdata = te, type = "response"), error = function(e) NULL)
    if (is.null(p) || any(!is.finite(p))) return(Inf)
    mean((p - te$home_win)^2)                       # Brier on held-out tail
  })
  best <- candidates[which.min(score)]
  if (!length(best) || !is.finite(best)) AWM_HALF_LIFE_DEFAULT else best
}

# One call site for the game model (the slate view and the backfill both use it).
run_game_projection <- function(dat, slate_date, half_life = NULL) {
  project_game_outcomes(dat$schedule_df, dat$pitching_df, dat$team_batting_df,
                        dat$recent_pitching_df, dat$recent_team_batting_df,
                        dat$player_batting_df, dat$team_ratings, dat$team_records,
                        dat$pitcher_stats_dict, pitching_df_season = dat$pitching_df_season,
                        season = dat$season, slate_date = as.Date(slate_date),
                        half_life = half_life,
                        team_batting_cur = dat$team_batting_cur,
                        team_batting_prev = dat$team_batting_prev,
                        lg_prev_woba = dat$lg_prev_woba %||% NA_real_)
}

# Fill in any missing past dates so the model's memory is current. Replaces the old
# separate "sweep" script -- the model now backfills itself. Point-in-time + resilient.
awm_catch_up <- function(end_date = Sys.Date() - 1, recent_games = 15L, on_progress = NULL) {
  end_date <- as.Date(end_date); h <- awm_load(); m <- awm_load(AWM_MEMORY_PATH)
  # A date counts as done only when BOTH the pick ledger and the current model's
  # memory have it -- after a model upgrade the ledger is full but the memory is
  # not, and this is what fills it.
  led_have <- if (!is.null(h) && "GameDate" %in% names(h))
    unique(as.character(as.Date(h$GameDate))) else character(0)
  mem_have <- if (!is.null(m) && all(c("GameDate", "ModelVer") %in% names(m)))
    unique(as.character(as.Date(m$GameDate[m$ModelVer %in% MLB_MODEL_VER]))) else character(0)
  have <- intersect(led_have, mem_have)
  season_floor <- mlb_season_start(format(end_date, "%Y"))   # regular season only (v10)
  # HOLE HEALING (v9). This used to resume at max(recorded) + 1, so a date that
  # errored mid-backfill -- a network blip, a 500 from the stats API -- was stepped
  # over once and then never revisited, leaving a permanent gap in the training
  # set. It now walks the whole season and skips dates already on file, which the
  # NRFI backfill has always done. A recorded date costs a loop iteration, not a
  # fetch, and a genuine off-day costs one small schedule call.
  from <- season_floor
  if (from > end_date) return(invisible(0L))
  dates <- seq(from, end_date, by = "day"); done <- 0L; healed <- 0L
  for (k in seq_along(dates)) {
    ds <- format(dates[k], "%Y-%m-%d")
    if (ds %in% have) next
    # cheap probe: league-wide off-days have no schedule, so don't build the
    # full point-in-time frames just to discover there is nothing to grade.
    if (isTRUE(tryCatch(nrow(fetch_mlb_schedule(ds)) == 0L, error = function(e) FALSE))) next
    if (length(have) && dates[k] < max(as.Date(have))) healed <- healed + 1L
    if (!is.null(on_progress)) on_progress(k / length(dates), ds)
    tryCatch(with_quiet_log({          # one line per DAY of backfill was the console spam
      dat <- prepare_data(recent_games = recent_games, date_str = ds)
      run_game_projection(dat, dates[k], half_life = AWM_HALF_LIFE_DEFAULT)  # fixed during backfill (fast)
      done <- done + 1L
    }), error = function(e) NULL)
    Sys.sleep(0.2)
  }
  if (done > 0L)
    mlog(sprintf("Memory     | backfilled %d day(s) of results, %s to %s%s",
                 done, format(dates[1L], "%b %d"), format(dates[length(dates)], "%b %d"),
                 if (healed > 0L) sprintf(" (%d gap(s) healed)", healed) else ""))
  invisible(done)
}

# What's working / what busted, straight from memory. Replaces the old "analyze" script.
compute_model_diagnostics <- function(history, memory = NULL) {
  graded <- function(x) {
    if (is.null(x) || !nrow(x) || !all(c("HomeWon", "IsCorrect") %in% names(x))) return(NULL)
    x <- x[!is.na(x$HomeWon) & !is.na(x$IsCorrect), , drop = FALSE]
    x <- x[mlb_competitive_rows(x), , drop = FALSE]               # no spring-training rows
    if (nrow(x)) x else NULL
  }
  score <- function(x) {
    p <- pmin(pmax(suppressWarnings(as.numeric(x$HomeWinProb)) / 100, 1e-4), 1 - 1e-4)
    y <- as.integer(x$HomeWon)
    list(n = nrow(x), overall = round(100 * mean(.is_true(x$IsCorrect)), 1),
         brier = round(mean((p - y)^2, na.rm = TRUE), 4),
         logloss = round(-mean(y * log(p) + (1 - y) * log(1 - p), na.rm = TRUE), 4))
  }
  H <- graded(history)
  # Picks on record: everything in the ledger, whichever model made the pick.
  record <- if (!is.null(H)) score(H) else NULL
  # The model that is running: its own point-in-time record in the model memory,
  # falling back to its rows in the ledger, then to the ledger as a whole.
  M <- graded(memory)
  if (!is.null(M) && "ModelVer" %in% names(M)) M <- M[M$ModelVer %in% MLB_MODEL_VER, , drop = FALSE]
  L <- if (!is.null(M) && nrow(M) >= 20) M else H
  if (is.null(L) || !nrow(L)) return(NULL)
  cur <- if ("ModelVer" %in% names(L)) L$ModelVer %in% MLB_MODEL_VER else rep(FALSE, nrow(L))
  if (sum(cur) >= 20) L <- L[cur, , drop = FALSE]                 # judge the model that is running
  L$IsCorrect <- .is_true(L$IsCorrect)
  for (cc in c("HomeWinProb","C_whip","C_kpct","C_pyth","C_run"))
    if (cc %in% names(L)) L[[cc]] <- suppressWarnings(as.numeric(L[[cc]]))
  L$home_win <- as.integer(L$HomeWon); L$correct <- as.logical(L$IsCorrect)
  p <- pmin(pmax(L$HomeWinProb / 100, 1e-4), 1 - 1e-4)
  brier <- round(mean((p - L$home_win)^2, na.rm = TRUE), 4)
  logloss <- round(-mean(L$home_win * log(p) + (1 - L$home_win) * log(1 - p), na.rm = TRUE), 4)
  by_tier <- tryCatch(aggregate(correct ~ Confidence, L, function(x) round(100*mean(x),1)),
                      error = function(e) NULL)
  cols <- if ("C_run" %in% names(L) && any(is.finite(L$C_run)))
    c(RunModel="C_run", Pyth="C_pyth") else c(WHIP="C_whip", StaffK="C_kpct", Pyth="C_pyth")
  attrib <- tryCatch({
    do.call(rbind, lapply(names(cols), function(nm) {
      cc <- L[[cols[[nm]]]]; used <- is.finite(cc) & abs(cc) > 1e-6
      data.frame(metric = nm, games = sum(used, na.rm=TRUE),
                 right_pct = round(100*mean(sign(cc[used])==sign(L$home_win[used]-0.5), na.rm=TRUE),1))
    }))
  }, error = function(e) NULL)
  busted <- tryCatch({
    miss <- L[!L$correct, , drop=FALSE]
    if (!nrow(miss)) NULL else {
      cul <- sapply(seq_len(nrow(miss)), function(i){
        cc <- vapply(cols, function(k) as.numeric(miss[[k]][i]), 0); cc[!is.finite(cc)] <- 0
        cw <- if (miss$home_win[i]==0) cc else -cc; names(which.max(cw))
      })
      tb <- sort(table(cul), decreasing=TRUE)
      data.frame(metric=names(tb), pct_of_losses=round(100*as.numeric(tb)/nrow(miss),1))
    }
  }, error = function(e) NULL)
  cal <- tryCatch({
    pk  <- 100 * pmax(p, 1 - p)
    hit <- ifelse(p >= 0.5, L$home_win, 1 - L$home_win)
    b <- cut(pk, breaks = c(50, 53, 56, 60, 65, 100), include.lowest = TRUE,
             labels = c("50-53%", "53-56%", "56-60%", "60-65%", "65%+"))
    a <- aggregate(cbind(predicted = pk, actual = 100 * hit) ~ b, data.frame(b, pk, hit),
                   function(x) round(mean(x), 1))
    names(a)[1] <- "bucket"
    a$n <- as.numeric(table(b)[as.character(a$bucket)]); a
  }, error = function(e) NULL)
  list(n = nrow(L), overall = round(100*mean(L$correct),1), brier = brier, logloss = logloss,
       version = if (sum(cur) >= 20) MLB_MODEL_VER else "earlier versions",
       from_memory = !is.null(M) && nrow(M) >= 20,
       record = record,
       by_tier = by_tier, attrib = attrib, busted = busted, cal = cal)
}
# =================================================================================

# Empirical home-run model (replaces the old multiplicative lambda). Logistic on 5
# point-in-time features, refit on 2026 games; OOS-calibrated, top-pick lift ~2.2x.
HR_COEF <- c(intercept = -4.4637, batter_hr_rate = 11.3268, batter_iso = 0.9468,
             opp_hr9 = 0.2195, park_hr = 0.4274, platoon = 1.1974)

empirical_home_winprob <- function(hps, aps, psn_h, psn_a, pyth_wpcts, ht, at) {
  # PITCHER SIGNAL UPGRADE (v7): the starter-matchup feature now uses a skill-based
  # run-prevention estimate -- the mean of whichever of SIERA / xFIP / FIP are
  # available -- instead of raw WHIP. WHIP is largely BABIP/defense-driven and noisy;
  # SIERA/xFIP/FIP estimate the pitcher's OWN talent (K, BB, batted-ball) and predict
  # how the start actually goes far better. It rides in the existing 'd_whip' feature
  # slot, so the adaptive layer, ledger, and calibration are untouched -- only the
  # signal feeding the slot is cleaner. Lower = better pitcher (same sign as WHIP).
  skill_era <- function(ps, psn) {
    pick <- function(o) { if (is.null(o)) return(NA_real_)
      v <- c(o$SIERA %||% NA_real_, o$xFIP %||% NA_real_, o$FIP %||% NA_real_)
      v <- v[is.finite(v)]; if (length(v)) mean(v) else NA_real_ }
    val <- if (!is.null(ps) && ((ps$InningsPitched %||% 0) > MIN_IP_SEASON)) pick(ps) else NA_real_
    if (!is.finite(val)) val <- pick(psn)
    if (!is.finite(val)) val <- LG_AVG_FIP
    val
  }
  d_whip <- skill_era(hps, psn_h) - skill_era(aps, psn_a)   # home - away skill-ERA (slot name kept)
  kp <- function(psn) if (!is.null(psn)) (psn$KPct %||% LG_AVG_K_PCT) else LG_AVG_K_PCT
  d_kpct <- kp(psn_h) - kp(psn_a)
  pw <- function(t) { v <- if (!is.null(pyth_wpcts)) pyth_wpcts[[t]] else NULL
  if (is.null(v) || is.na(v)) 0.5 else as.numeric(v) }
  d_pyth <- pw(ht) - pw(at)
  c_whip <- EMP_WINPROB_COEF[["d_whip"]] * d_whip   # signed push toward HOME, in log-odds
  c_kpct <- EMP_WINPROB_COEF[["d_kpct"]] * d_kpct
  c_pyth <- EMP_WINPROB_COEF[["d_pyth"]] * d_pyth
  z <- EMP_WINPROB_COEF[["intercept"]] + c_whip + c_kpct + c_pyth
  # Return the prob AND the decomposition so every pick is auditable.
  list(hwp = clamp(plogis(z), 0.05, 0.95),
       d_whip = d_whip, d_kpct = d_kpct, d_pyth = d_pyth,
       c_whip = c_whip, c_kpct = c_kpct, c_pyth = c_pyth)
}
# =====================================================================

# ============================================================================
#  TEAM-SPECIFIC OFFENSE: RUN CONVERSION  ("do they leave guys on base?")
#  ---------------------------------------------------------------------------
#  Measures, for EACH team, how many runs they actually score vs how many their
#  hitting says they should. Uses only games BEFORE the date being predicted,
#  and trusts each team's own number more as they play more games. Nothing here
#  is hand-set -- it reads the box scores and recomputes every run, so it sharpens
#  on its own as the season goes. Output: one number per team, e.g.
#     0.94 -> scores ~6% FEWER runs than its bats predict (strands runners)
#     1.06 -> scores ~6% MORE  (sequences well). Plugs into mc_run_estimate().
# ============================================================================
WOBA_TO_RUNS_SCALE <- 1.20          # standard wOBA scale (runs per wOBA pt * PA)
RUNCONV_REGRESS_G  <- 40L           # "trust dial": fewer games -> lean on league avg
RUNCONV_CLAMP      <- c(0.88, 1.12) # safety rail: no team quirk swings > +-12%

.expected_runs_from_woba <- function(woba, pa, lg_woba = LG_AVG_WOBA,
                                     lg_rpg = LG_AVG_RUNS_PER_GAME, pa_per_game = 38) {
  runs_above_avg_per_pa <- (woba - lg_woba) / WOBA_TO_RUNS_SCALE
  (lg_rpg / pa_per_game + runs_above_avg_per_pa) * pa
}

build_team_run_conversion <- function(season, cutoff_date, last_n = NULL) {
  empty <- data.frame(Team = character(), Games = integer(), ActualRPG = numeric(),
                      ExpRPG = numeric(), RunConv = numeric(), stringsAsFactors = FALSE)
  splits <- tryCatch(fetch_team_gamelog_raw(season, "hitting"), error = function(e) NULL)
  if (is.null(splits) || !length(splits)) return(empty)
  by_team <- split(splits, vapply(splits,
                                  function(s) as.character(scalar(s[["team"]][["name"]], "Unknown")),
                                  character(1L)))
  tmp <- list()
  for (tn in names(by_team)) {
    sps <- filter_splits_before(by_team[[tn]], cutoff_date, last_n = last_n)
    g <- length(sps); if (g < 5L) next
    acc <- list(R = 0, pa = 0, ab = 0, h = 0, d = 0, t = 0,
                hr = 0, bb = 0, hbp = 0, sf = 0)
    for (sp in sps) {
      st <- sp[["stat"]] %||% list()
      acc$R   <- acc$R   + coerce_numeric(scalar(st[["runs"]], 0))
      acc$pa  <- acc$pa  + coerce_numeric(scalar(st[["plateAppearances"]], 0))
      acc$ab  <- acc$ab  + coerce_numeric(scalar(st[["atBats"]], 0))
      acc$h   <- acc$h   + coerce_numeric(scalar(st[["hits"]], 0))
      acc$d   <- acc$d   + coerce_numeric(scalar(st[["doubles"]], 0))
      acc$t   <- acc$t   + coerce_numeric(scalar(st[["triples"]], 0))
      acc$hr  <- acc$hr  + coerce_numeric(scalar(st[["homeRuns"]], 0))
      acc$bb  <- acc$bb  + coerce_numeric(scalar(st[["baseOnBalls"]], 0))
      acc$hbp <- acc$hbp + coerce_numeric(scalar(st[["hitByPitch"]], 0))
      acc$sf  <- acc$sf  + coerce_numeric(scalar(st[["sacFlies"]], 0))
    }
    if (acc$pa < 50) next
    woba     <- calc_woba(acc$bb, acc$hbp, acc$h, acc$d, acc$t, acc$hr, acc$ab, acc$sf)
    exp_runs <- .expected_runs_from_woba(woba, acc$pa)
    if (!is.finite(exp_runs) || exp_runs <= 0) next
    tmp[[tn]] <- list(g = g, R = acc$R, exp = exp_runs, ratio = acc$R / exp_runs)
  }
  if (!length(tmp)) return(empty)
  lg_ratio <- mean(vapply(tmp, function(x) x$ratio, numeric(1)))
  if (!is.finite(lg_ratio) || lg_ratio <= 0) lg_ratio <- 1.0
  rows <- lapply(names(tmp), function(tn) {
    x   <- tmp[[tn]]
    rel <- x$ratio / lg_ratio
    w   <- x$g / (x$g + RUNCONV_REGRESS_G)
    conv <- clamp(w * rel + (1 - w) * 1.0, RUNCONV_CLAMP[1], RUNCONV_CLAMP[2])
    data.frame(Team = tn, Games = x$g,
               ActualRPG = round(x$R / x$g, 2),
               ExpRPG    = round(x$exp / x$g, 2),
               RunConv   = round(conv, 3), stringsAsFactors = FALSE)
  })
  out <- bind_rows(rows)
  out[order(out$RunConv), ]
}

team_run_conv <- function(team_name, runconv_df) {
  if (is.null(runconv_df) || !nrow(runconv_df)) return(1.0)
  r <- runconv_df[runconv_df$Team == team_name, , drop = FALSE]
  if (!nrow(r)) return(1.0)
  v <- as.numeric(r$RunConv[1]); if (is.na(v)) 1.0 else v
}

# ----------------------------------------------------------------------------
#  MATCHUP EDGES as LEARNED win-model features (walks, contact, power).
#  For each game we compute home-lineup-vs-away-starter and away-lineup-vs-home-
#  starter using the matchup (log5) formula, centered so 0 = league-neutral, then
#  take home-minus-away. These are NOT given a weight by hand -- they are fed to
#  the adaptive win model (awm_*), which learns from actual wins how much each one
#  matters, exactly like it already does for WHIP and Pythagorean.
# ----------------------------------------------------------------------------
matchup_win_features <- function(h_bb, h_k, h_iso, a_bb, a_k, a_iso,
                                 hp_bb, hp_k, hp_fb, ap_bb, ap_k, ap_fb,
                                 lg_bb, lg_k, lg_iso, lg_fb = LG_AVG_FB_PCT) {
  l5 <- function(b, p, l) if (is.na(b) || is.na(p) || is.na(l) || l <= 0) NA_real_ else (b * p) / l
  ctr <- function(rate, lg) { if (is.na(rate) || is.na(lg) || lg <= 0) 0 else (rate / lg) - 1 }
  powr <- function(iso, fb) clamp(iso / lg_iso, 0.4, 2.0) * clamp((fb %||% lg_fb) / lg_fb, 0.6, 1.6) - 1
  # home lineup vs away starter
  h_mw <-  ctr(l5(h_bb, ap_bb, lg_bb), lg_bb)
  h_mk <- -ctr(l5(h_k,  ap_k,  lg_k ), lg_k )      # fewer strikeouts = good for hitters
  h_mp <-  powr(h_iso, ap_fb)
  # away lineup vs home starter
  a_mw <-  ctr(l5(a_bb, hp_bb, lg_bb), lg_bb)
  a_mk <- -ctr(l5(a_k,  hp_k,  lg_k ), lg_k )
  a_mp <-  powr(a_iso, hp_fb)
  list(D_mw = clamp(h_mw - a_mw, -0.6, 0.6),
       D_mk = clamp(h_mk - a_mk, -0.6, 0.6),
       D_mp = clamp(h_mp - a_mp, -0.6, 0.6))
}
# ============================================================================

# ============================================================================
# VEGAS ODDS INTEGRATION -- REMOVED (v9)
# The bet365 moneyline scrape (sportsbookreview __NEXT_DATA__) was pulled out on
# purpose. It was the single least reliable input in the file: the page shape
# changes without notice, so in practice the fetch failed far more often than it
# succeeded, and every failure printed a line to the console while contributing
# nothing to the pick. Worse, when it DID succeed it silently overrode the model
# on non-High-confidence disagreements, which meant the same slate could produce
# a different pick purely because a scrape happened to work that minute.
# The pick is now, and only, the model's own calibrated probability.
# ============================================================================

project_game_outcomes <- function(schedule_df, pitching_df, team_batting_df,
                                  recent_pitching_df, recent_team_batting_df,
                                  player_batting_df, team_ratings_obj, team_records,
                                  pitcher_stats_dict, pitching_df_season=NULL, season="2026",
                                  slate_date=Sys.Date(), half_life=NULL,
                                  team_batting_cur=NULL, team_batting_prev=NULL,
                                  lg_prev_woba=NA_real_) {
  if (nrow(schedule_df) == 0) return(data.frame())
  rows <- list()
  # Re-fit the adaptive layer from accumulated results of THIS model version (the
  # model memory), as of this slate's date (only games final BEFORE it -> no leakage).
  .hist <- awm_load()                 # pick ledger: locked picks
  .mem  <- awm_training_history()     # model memory: what this model said, point-in-time
  .hl <- if (!is.null(half_life)) half_life else
    tryCatch(awm_select_half_life(.mem, slate_date), error = function(e) AWM_HALF_LIFE_DEFAULT)
  if (is.null(.hl) || !is.finite(.hl)) .hl <- AWM_HALF_LIFE_DEFAULT
  awm_state <- tryCatch(awm_fit(.mem, as_of_date = slate_date, half_life = .hl),
                        error = function(e) list(coef = AWM_PRIOR_COEF, n = 0, w_data = 0))
  awm_state$half_life <- .hl
  mlog(sprintf("Win model  | learned weights: run model %.3f, Pythagorean gap %.3f (fit on %s graded %s games, %.0f%% data, %s)",
               awm_state$coef[["z_run"]], awm_state$coef[["D_pyth"]], format(as.integer(awm_state$n %||% 0L), big.mark = ","),
               MLB_MODEL_VER, 100 * (awm_state$w_data %||% 0), awm_half_life_label(.hl)))
  final_calib <- tryCatch(fit_final_calibration(.mem, slate_date),
                          error = function(e) list(a = 1, b = 0, ok = FALSE, n = 0))
  if (isTRUE(final_calib$ok))
    mlog(sprintf("Win model  | calibration a=%.3f b=%.3f  (fit on %d graded games before %s)",
                 final_calib$a, final_calib$b, final_calib$n, as.character(slate_date)))
  else
    mlog(sprintf("Win model  | calibration off (needs %d graded %s games before %s) -> run model as is",
                 FINAL_CAL_MIN_GAMES, MLB_MODEL_VER, as.character(slate_date)))
  .skipped <- list()   # collected per-game failures -> one summary line, not N warnings
  pit_season <- pitching_df_season %||% pitching_df
  tb_cur  <- team_batting_cur %||% team_batting_df
  get1  <- function(df, team) {
    if (is.null(df) || !nrow(df)) return(NULL)
    r <- df[df$Team==team,,drop=FALSE]; if (nrow(r)==0) NULL else r[1L,] }
  for (i in seq_len(nrow(schedule_df))) {
    tryCatch({
      g   <- schedule_df[i, ]; ht <- g$HomeTeam; at <- g$AwayTeam; gid <- g$GameID
      bs  <- fetch_game_boxscore(gid)
      hs  <- g$HomeScore; as_ <- g$AwayScore; aw <- g$ActualWinner; gs <- g$GameStatus
      if (!is.null(bs)) {
        hs <- bs$HomeScore; as_ <- bs$AwayScore; gs <- bs$GameStatus
        aw <- if (!is.na(bs$ActualWinner %||% NA_character_) && bs$ActualWinner == "Home") ht
        else if (!is.na(bs$ActualWinner %||% NA_character_) && bs$ActualWinner == "Away") at
        else bs$ActualWinner
      }
      hp <- get1(pit_season, ht); ap <- get1(pit_season, at)
      hb <- get1(tb_cur, ht);     ab_ <- get1(tb_cur, at)
      hps <- pitcher_stats_dict[[as.character(g$HomePitcherID)]]
      aps <- pitcher_stats_dict[[as.character(g$AwayPitcherID)]]
      # ---- run model ----
      conf_lu <- tryCatch(fetch_confirmed_lineup(gid), error = function(e) NULL)
      h_lw <- lineup_woba_from_confirmed(player_batting_df, ht, conf_lu, as.numeric(hb$wOBA %||% LG_AVG_WOBA), side = "home")
      a_lw <- lineup_woba_from_confirmed(player_batting_df, at, conf_lu, as.numeric(ab_$wOBA %||% LG_AVG_WOBA), side = "away")
      off_h <- mlb_offense_index(hb, get1(team_batting_prev, ht), lg_prev_woba, h_lw)
      off_a <- mlb_offense_index(ab_, get1(team_batting_prev, at), lg_prev_woba, a_lw)
      pit_h <- mlb_pitching_index(hps, hp); pit_a <- mlb_pitching_index(aps, ap)
      wx <- if ("Weather" %in% names(g)) g$Weather[[1L]] else list()
      wa <- advanced_weather_adjustment(wx, g$Venue)
      pr <- get_park_factor(g$Venue, "runs")
      gm <- mlb_game_model(off_h, off_a, pit_h, pit_a, pr, wa$runs)
      run_hwp <- gm$hwp
      # ---- starter labels (display only) ----
      sp_lbl <- function(ps) {
        if (is.null(ps)) return("SP-TBD")
        t <- classify_sp_tier(ps$ERA %||% LG_AVG_ERA, ps$KPct %||% LG_AVG_K_PCT,
                              ps$BBPct %||% LG_AVG_BB_PCT, ps$WhiffPct %||% LG_AVG_WHIFF_PCT,
                              sp_recent_era = NULL)
        paste0("SP-", t$tier)
      }
      home_sp_lbl <- sp_lbl(hps); away_sp_lbl <- sp_lbl(aps)
      # ---- context features kept in the ledger (and D_pyth feeds the adaptive layer) ----
      pyw   <- if (is.list(team_ratings_obj)) team_ratings_obj$pyth_wpcts else NULL
      emp <- empirical_home_winprob(hps, aps, hp, ap, pyw, ht, at)
      emp_hwp <- emp$hwp
      cf <- awm_state$coef
      raw_awm_hwp <- awm_predict_home(cf, run_hwp, emp$d_pyth)
      cal_hwp     <- apply_final_calibration(raw_awm_hwp, final_calib)
      cal_awp <- 1 - cal_hwp
      pk <- max(cal_hwp, cal_awp)
      conf_lbl <- if (pk >= EMP_CONF_HIGH) "High" else if (pk >= EMP_CONF_MED) "Medium" else "Low"
      pw <- if (cal_hwp >= 0.5) ht else at    # the pick IS the model, with no market override
      pick_pct <- round(pk * 100)
      ser_mod <- compute_series_modifier(g$SeriesHomeWins %||% 0L, g$SeriesAwayWins %||% 0L, g$SeriesGameNum %||% 1L)
      ser_g_num <- g$SeriesGameNum %||% 1L
      ser_label <- if (!is.null(ser_mod) && (abs(ser_mod$home) > 0 || abs(ser_mod$away) > 0)) paste0("G", ser_g_num) else ""
      is_final <- gs %in% c("Final","Game Over","Completed Early")
      is_live  <- grepl("Progress|Live", gs, ignore.case=TRUE)
      correct_pred <- if (is_final && !is.na(aw %||% NA_character_) && aw != "Tie") (pw == aw) else NA
      home_won     <- if (is_final && !is.na(aw %||% NA_character_) && aw != "Tie") as.integer(aw == ht) else NA_integer_
      actual_score_str <- if (is_final && !is.na(aw %||% NA_character_) && aw != "Tie") {
        ws <- if (ht == aw) hs else as_; ls <- if (ht == aw) as_ else hs; paste0(aw," ",ws,"-",ls)
      } else if (is_live) paste0("Live: ", hs, "-", as_) else "\u2014"
      win_prob_num <- if (pw == ht) round(cal_hwp*100,1) else round(cal_awp*100,1)
      h_wh <- as.numeric(hps$WHIP %||% hp$WHIP %||% 1.30); a_wh <- as.numeric(aps$WHIP %||% ap$WHIP %||% 1.30)
      h_ops <- as.numeric(hb$OPS %||% 0.720); a_ops <- as.numeric(ab_$OPS %||% 0.720)
      rows[[length(rows)+1L]] <- data.frame(
        GameID=gid, Matchup=paste0(at," @ ",ht), ProjectedWinner=pw, WinProb=paste0(win_prob_num,"%"),
        WinProbNum=win_prob_num, HomeWinProb=round(cal_hwp*100,1), RawHomeWP=round(raw_awm_hwp*100,1), Confidence=conf_lbl,
        WHIPSignal="", LOBSignal="", OPSSignal="", SeriesGame=ser_label,
        HomeSP=home_sp_lbl, AwaySP=away_sp_lbl, HomeWHIP=round(h_wh,3), AwayWHIP=round(a_wh,3),
        HomeOPS=round(h_ops,3), AwayOPS=round(a_ops,3), Total=round(gm$mu_h + gm$mu_a,1),
        ProjHomeRuns=round(gm$mu_h,2), ProjAwayRuns=round(gm$mu_a,2),
        ActualResult=actual_score_str, IsCorrect=correct_pred, IsLive=is_live, IsFinal=is_final,
        GameDate=as.character(slate_date), HomeWon=home_won, GameType=g$GameType %||% "R",
        MCHomeWP=round(run_hwp*100,1), RunHomeWP=round(run_hwp*100,1), EmpHomeWP=round(emp_hwp*100,1),
        D_whip=round(emp$d_whip,4), D_kpct=round(emp$d_kpct,4), D_pyth=round(emp$d_pyth,4),
        D_mw=0, D_mk=0, D_mp=0,
        C_whip=NA_real_, C_kpct=NA_real_,
        C_pyth=round(cf[["D_pyth"]] * emp$d_pyth,4), C_run=round(cf[["z_run"]] * awm_logit(run_hwp),4),
        CoefWhip=NA_real_, CoefKpct=NA_real_,
        CoefPyth=round(cf[["D_pyth"]],4), CoefMC=round(cf[["z_run"]],4),
        LearnGames=awm_state$n, LearnWeight=round(awm_state$w_data,3),
        LearnHalfLife=awm_state$half_life, ModelVer=MLB_MODEL_VER,
        FinalPick=pw, Strength="MODEL", StrengthPct=pick_pct,
        Venue=g$Venue %||% NA_character_, Umpire=g$Umpire %||% NA_character_,
        stringsAsFactors=FALSE)
    }, error = function(e) {
      .skipped[[length(.skipped) + 1L]] <<- paste0(schedule_df$AwayTeam[i] %||% "?", " @ ",
                                                   schedule_df$HomeTeam[i] %||% "?", ": ",
                                                   conditionMessage(e))
    })
  }
  if (length(.skipped))
    mlog(sprintf("Win model  | %d game(s) skipped: %s", length(.skipped),
                 paste(utils::head(unlist(.skipped), 3L), collapse = "; ")))
  if (!length(rows)) return(data.frame())
  df <- bind_rows(rows)
  # The model's own numbers go to its memory first, before any locked pick replaces them.
  tryCatch(awm_memory_append(df), error = function(e) NULL)
  # Any game already recorded in the ledger shows the pick it was recorded WITH.
  df <- tryCatch(awm_apply_locked(df, .hist), error = function(e) df)
  n_lock <- sum(df$Locked %in% TRUE)
  if (n_lock > 0)
    mlog(sprintf("Win model  | %d of %d games served from locked history (picks frozen at first pitch)",
                 n_lock, nrow(df)))
  tryCatch(awm_append(df), error = function(e) NULL)
  df[order(match(df$Confidence, c("High","Medium","Low")), -as.numeric(df$WinProbNum)), ]
}

# ============================================================================
# FIRST-INNING RUN MODEL (NRFI / YRFI)                                    v1.0
# ============================================================================
# WHY A SEPARATE ENGINE: the rest of this file projects a whole GAME, where a
# negative-binomial on expected runs is fine. The first inning is a different
# object -- it is ONE half-inning of exactly 3 outs, the batting order is KNOWN
# (slots 1-2-3 are guaranteed to hit), the pitcher is a starter at his first
# time through, and there is no bullpen, no pinch-hitting and no lineup
# uncertainty. A runs-per-game model cannot express "did at least one run cross
# before the third out", so this builds the half-inning explicitly.
#
# HOW IT WORKS
#   1. Per-batter outcome rates (K / BB+HBP / 1B / 2B / 3B / HR / GB out / air
#      out) are built for each of the first 9 lineup slots.
#   2. Batter rate x pitcher rate are combined with the odds-ratio (Log5)
#      method against the league rate -- the standard way to merge a hitter's
#      and a pitcher's true-talent rates. Both sides are first regressed to the
#      league mean using per-stat stabilisation points, so a 12-PA hitter or a
#      2-start pitcher does not swing the number.
#   3. An EXACT dynamic program walks the half-inning over the 24 base-out
#      states, tracking two masses in parallel: total probability (for expected
#      runs) and still-scoreless probability (for P(no run)). No simulation
#      noise -- the answer is exact given the inputs.
#   4. Both halves are combined with a small positive correlation term (shared
#      park / weather / umpire / ball make the two halves not independent).
#
# THE ONE THING PEOPLE GET WRONG: "the 1st is the highest-scoring inning" is
# TRUE (~0.54 R/half vs ~0.49 league-wide) but it is MOSTLY the batting order,
# not cold pitchers. Slots 1-2-3 are the best hitters on the roster and they
# are guaranteed to bat. Because this model puts the actual top of the order in
# the box, that effect is already counted -- so the residual "pitcher not warm"
# bump is SMALL (see FIRST_INN_WARMUP_MULT), and it is partly cancelled by the
# first-time-through-order bonus the pitcher gets (FIRST_INN_TTO1_MULT). Adding
# a big first-inning multiplier on top of an explicit top-of-order lineup is
# double-counting and is why a lot of public NRFI models run too low.

NRFI_LEDGER_PATH        <- "nrfi_ledger.csv"  # self-measurement memory (auto-written)

# League anchors. These are only STARTING points -- refresh_nrfi_baselines()
# overwrites them from the model's own graded results once enough pile up.
NRFI_LG_HALF_SCORELESS  <- 0.728   # P(a half-inning ends 0-0), league-wide
NRFI_LG_BASE            <- 0.530   # P(no run in the 1st), league-wide
NRFI_ANCHOR_WEIGHT      <- 0.45    # shrink each half toward the league anchor (v10: was 0.18;
                                   # on 2026 games even a sound starter/offense model beat the
                                   # base rate by only 0.001 Brier -- first innings are mostly noise)
NRFI_HALF_CORRELATION   <- 0.045   # residual correlation between the two halves
NRFI_MIN_GAMES_CAL      <- 250L    # graded games before calibration switches on
# 250 is not arbitrary. Measured on simulated slates at ~15 games/day: at 120
# graded games the fitted curve still moves a projection +/-15 points on noise
# alone and under-corrects a known bias; by 250 (~17 slate days) the spread is
# down to about +/-3 points. Below this the model reports its raw number, which
# is the safer error.
NRFI_CAL_HALF_LIFE      <- 45      # recency half-life for calibration, in days

FIRST_INN_WARMUP_MULT   <- 1.025   # RESIDUAL cold-pitcher effect (lineup already modelled)
FIRST_INN_TTO1_MULT     <- 0.985   # 1st time through the order favours the pitcher
NRFI_RUN_ELASTICITY     <- 1.75    # a +10% run park moves EVENT rates only ~+5.7%
NRFI_MAX_BATTERS        <- 15L     # DP depth; truncation error < 1e-5
NRFI_LG_HBP             <- 0.011   # HBP per PA (folded in with walks)
NRFI_LG_ROE             <- 0.012   # reached-on-error per PA (folded in with singles)
NRFI_BF_PER_IP_BASE     <- 3.0     # BF/IP ~= 3 + WHIP + adj
NRFI_BF_PER_IP_ADJ      <- -0.08   # HBP/ROE add BF, DPs and caught stealings remove them

# League per-PA outcome shares. Used as the Log5 pivot and as the fallback
# batter/pitcher when a player has no usable data.
NRFI_LG_RATES <- list(k = 0.225, bb = 0.094, s = 0.145, d = 0.045, t = 0.004, hr = 0.030)

# Stabilisation points (PA for hitters, batters-faced for pitchers): the number
# of observations at which the stat is half player, half league. Standard
# reliability values -- K% settles fast, HR and hit rates never really do.
NRFI_STAB_BAT <- c(k = 60, bb = 120, s = 290, d = 160, t = 300, hr = 170)
NRFI_STAB_PIT <- c(k = 70, bb = 170, s = 320, d = 220, t = 350, hr = 500)

# Baserunner advancement. Every one of these is a tunable, not a magic number.
NRFI_ADV <- list(
  p_r1_scores_on_2b = 0.42,   # 1st -> home on a double
  p_r2_scores_on_1b = 0.60,   # 2nd -> home on a single
  p_r1_to_3rd_on_1b = 0.28,   # 1st -> 3rd on a single
  p_gidp            = 0.115,  # double play, given runner on 1st and < 2 outs
  p_r3_scores_on_gb = 0.44,   # 3rd -> home on an infield ground out
  p_r3_scores_on_fc = 0.30,   # 3rd -> home when the play is a force elsewhere
  p_r2_to_3_on_gb   = 0.35,
  p_r3_scores_on_fb = 0.34,   # sacrifice fly
  p_r2_to_3_on_fb   = 0.12,
  # Runners also move WITHOUT a plate appearance -- steals, wild pitches, passed
  # balls, balks. Leaving these out is why a pure batter-by-batter model returns
  # too few one-run innings: it has no way to turn a runner on 1st into a runner
  # on 2nd, which is the single most common way a lone single becomes a run.
  p_steal_1to2      = 0.075,  # per PA, given runner on 1st and 2nd open
  p_steal_2to3      = 0.030,  # per PA, given runner on 2nd and 3rd open
  p_wp_scores_r3    = 0.020)  # per PA, runner on 3rd scores on a wild pitch/PB

# base-state encoding: 1=empty 2=1B 3=2B 4=3B 5=1&2 6=1&3 7=2&3 8=loaded
NRFI_BASES <- list(c(0,0,0), c(1,0,0), c(0,1,0), c(0,0,1),
                   c(1,1,0), c(1,0,1), c(0,1,1), c(1,1,1))
NRFI_BIDX  <- local({
  m <- integer(8)
  for (i in seq_along(NRFI_BASES)) { b <- NRFI_BASES[[i]]; m[b[1]*4 + b[2]*2 + b[3] + 1L] <- i }
  m
})
nrfi_bi <- function(r1, r2, r3) NRFI_BIDX[r1*4 + r2*2 + r3 + 1L]

# Odds-ratio (Log5): merge a batter rate and a pitcher rate against the league.
nrfi_log5 <- function(pb, pp, pl) {
  pb <- clamp(pb, 1e-4, 0.9); pp <- clamp(pp, 1e-4, 0.9); pl <- clamp(pl, 1e-4, 0.9)
  o <- (pb/(1-pb)) * (pp/(1-pp)) / (pl/(1-pl))
  if (!is.finite(o) || o <= 0) return(pb)
  o/(1+o)
}
# Regress an observed rate toward league using a stabilisation point.
nrfi_shrink <- function(obs, n, lg, stab) {
  if (is.null(obs) || !is.finite(obs) || is.null(n) || !is.finite(n) || n <= 0) return(lg)
  (obs*n + lg*stab) / (n + stab)
}

# ---- per-batter outcome vector vs THIS starter -----------------------------
# Returns c(k, bb, s, d, t, hr, gb_out, air_out), summing to 1.
nrfi_batter_vector <- function(pl, pit, bat_hand, pitch_hand, env_mult = 1.0,
                               ump_k = 0.0, ump_bb = 0.0) {
  L <- NRFI_LG_RATES
  # ---- batter side (season-to-date, point-in-time upstream) ----
  if (is.null(pl) || !is.data.frame(pl) || nrow(pl) == 0) {
    b <- L; pa <- 0
  } else {
    pa  <- suppressWarnings(as.numeric(pl$PlateAppearances[1])); if (!is.finite(pa)) pa <- 0
    gv  <- function(col) {
      if (!(col %in% names(pl))) return(NA_real_)            # column absent -> use league
      v <- suppressWarnings(as.numeric(pl[[col]][1] %||% NA)); if (is.finite(v)) v else 0
    }
    h   <- gv("Hits"); d2 <- gv("Doubles"); t3 <- gv("Triples"); hr <- gv("HomeRuns")
    bb  <- gv("BaseOnBalls") + gv("HitByPitch")
    so  <- gv("StrikeOuts")
    s1  <- max(h - d2 - t3 - hr, 0)
    raw <- if (pa > 0) list(k = so/pa, bb = bb/pa, s = s1/pa, d = d2/pa, t = t3/pa, hr = hr/pa) else L
    # a stat with a missing source column regresses fully to league, not to zero
    b   <- lapply(names(L), function(nm) {
      v <- raw[[nm]]
      if (is.null(v) || !is.finite(v)) L[[nm]]
      else nrfi_shrink(v, pa, L[[nm]], NRFI_STAB_BAT[[nm]])
    })
    names(b) <- names(L)
  }
  # platoon: reuse the file's existing platoon tables so this stays consistent
  pw <- platoon_woba_mult(bat_hand %||% "R", pitch_hand %||% "R")
  b$s <- b$s * pw^0.60; b$d <- b$d * pw^0.90; b$t <- b$t * pw^0.90
  b$bb <- b$bb * pw^0.45
  b$hr <- b$hr * (platoon_hr_rate_val(bat_hand %||% "R", pitch_hand %||% "R") / LG_AVG_HR_PER_PA)
  b$k  <- b$k * (1/pw)^0.50
  
  # ---- pitcher side, converted to per-batter-faced rates ----
  if (is.null(pit)) {
    p <- L; bf <- 0; gb_share <- 0.53
  } else {
    ip   <- suppressWarnings(as.numeric(pit$InningsPitched %||% 0)); if (!is.finite(ip)) ip <- 0
    # v10: season-to-date RAW rates (the regressed ones would be shrunk twice below)
    rawv <- function(a, b, d) { v <- suppressWarnings(as.numeric(a %||% NA)); if (!is.finite(v)) v <- suppressWarnings(as.numeric(b %||% d)); if (!is.finite(v)) d else v }
    whip <- clamp(rawv(pit$RawWHIP, pit$WHIP, 1.30), 0.70, 2.50)
    bfip <- NRFI_BF_PER_IP_BASE + whip + NRFI_BF_PER_IP_ADJ
    bf   <- ip * bfip
    k_p  <- clamp(rawv(pit$RawKPct, pit$KPct, L$k), 0.05, 0.45)
    bb_w <- clamp(rawv(pit$RawBBPct, pit$BBPct, 0.083), 0.01, 0.25)  # WALKS ONLY
    bb_p <- bb_w + NRFI_LG_HBP                               # walks + HBP, for the Log5 rate
    hr9  <- clamp(rawv(pit$RawHR9, pit$HR9, 1.20), 0.0, 4.0)
    hr_p <- hr9 / (9 * bfip)
    # WHIP counts walks and hits only -- back out hits with the WALK rate, not
    # walks+HBP, or the pitcher gets credited with ~0.015 fewer hits per batter.
    h_ip <- max(whip - bb_w*bfip, 0.20)
    h_bf <- h_ip / bfip
    nonhr <- max(h_bf - hr_p, 0.02)
    gbp   <- clamp(suppressWarnings(as.numeric(pit$GBPct %||% LG_AVG_GB_PCT)), 0.25, 0.65)
    fbp   <- clamp(suppressWarnings(as.numeric(pit$FBPct %||% LG_AVG_FB_PCT)), 0.20, 0.55)
    # fly-ball pitchers give up proportionally more extra-base hits
    xbh_tilt <- clamp(1 + (fbp - LG_AVG_FB_PCT)*1.2 - (gbp - LG_AVG_GB_PCT)*0.8, 0.80, 1.25)
    lg_nonhr <- L$s + L$d + L$t
    d_share <- (L$d/lg_nonhr) * xbh_tilt
    t_share <- (L$t/lg_nonhr) * xbh_tilt
    s_share <- max(1 - d_share - t_share, 0.50)
    p <- list(k = k_p, bb = bb_p, s = nonhr*s_share, d = nonhr*d_share,
              t = nonhr*t_share, hr = hr_p)
    p <- lapply(names(L), function(nm) nrfi_shrink(p[[nm]], bf, L[[nm]], NRFI_STAB_PIT[[nm]]))
    names(p) <- names(L)
    gb_share <- clamp(gbp / (gbp + fbp), 0.35, 0.72)
  }
  
  # ---- combine ----
  out <- setNames(numeric(6), names(L))
  for (nm in names(L)) out[[nm]] <- nrfi_log5(b[[nm]], p[[nm]], L[[nm]])
  # first-inning context: cold pitcher (up) vs 1st time through the order (down)
  ctx <- FIRST_INN_WARMUP_MULT * FIRST_INN_TTO1_MULT * env_mult
  for (nm in c("bb","s","d","t","hr")) out[[nm]] <- out[[nm]] * ctx
  out[["k"]]  <- clamp(out[["k"]]  + ump_k,  0.02, 0.60)
  out[["bb"]] <- clamp(out[["bb"]] + ump_bb, 0.005, 0.35)
  out[["s"]]  <- out[["s"]] + NRFI_LG_ROE                    # reached-on-error
  
  tot <- sum(out)
  if (tot > 0.95) out <- out * (0.95/tot)
  inplay <- max(1 - sum(out), 0.02)
  c(as.numeric(out[c("k","bb","s","d","t","hr")]),
    inplay*gb_share, inplay*(1-gb_share))
}

# ---- exact half-inning dynamic program ------------------------------------
# Two masses evolve together over the 24 base-out states: M = all paths (gives
# expected runs), Z = paths with zero runs so far (gives P(scoreless)).
nrfi_half_inning <- function(batters, adv = NRFI_ADV, max_bat = NRFI_MAX_BATTERS) {
  Z <- matrix(0, 3, 8); M <- matrix(0, 3, 8)
  Z[1,1] <- 1; M[1,1] <- 1
  p_scoreless <- 0; exp_runs <- 0
  nb_avail <- length(batters)
  
  for (bi in seq_len(max_bat)) {
    pv <- batters[[((bi - 1L) %% nb_avail) + 1L]]
    k <- pv[1]; bb <- pv[2]; s <- pv[3]; d <- pv[4]; t <- pv[5]; hr <- pv[6]
    gb <- pv[7]; fb <- pv[8]
    Zn <- matrix(0, 3, 8); Mn <- matrix(0, 3, 8); z_done <- 0
    
    # --- free advances before the pitch: steals, wild pitches, passed balls ---
    Zs <- matrix(0, 3, 8); Ms <- matrix(0, 3, 8)
    for (o in 0:2) for (bidx in 1:8) {
      mz <- Z[o+1, bidx]; mm <- M[o+1, bidx]
      if (mz <= 0 && mm <= 0) next
      st <- NRFI_BASES[[bidx]]; r1 <- st[1]; r2 <- st[2]; r3 <- st[3]
      spl <- list(); addp <- function(runs, nbi, p)
        if (p > 0) spl[[length(spl)+1L]] <<- list(r = runs, b = nbi, p = p)
      p12 <- if (r1 == 1 && r2 == 0) adv$p_steal_1to2 else 0
      p23 <- if (r2 == 1 && r3 == 0) adv$p_steal_2to3 else 0
      pwp <- if (r3 == 1) adv$p_wp_scores_r3 else 0
      for (s12 in 0:1) for (s23 in 0:1) for (wp in 0:1) {
        pp <- (if (s12) p12 else 1 - p12) * (if (s23) p23 else 1 - p23) * (if (wp) pwp else 1 - pwp)
        if (pp <= 0) next
        n1 <- r1; n2 <- r2; n3 <- r3
        if (s23 == 1) { n2 <- 0; n3 <- 1 }
        if (s12 == 1) { n1 <- 0; n2 <- 1 }
        rr <- 0
        if (wp == 1 && r3 == 1) { rr <- 1; if (s23 == 1) n3 <- 1 else n3 <- 0 }
        addp(rr, nrfi_bi(n1, n2, n3), pp)
      }
      for (sp in spl) {
        if (mm > 0) {
          exp_runs <- exp_runs + mm * sp$p * sp$r
          Ms[o+1, sp$b] <- Ms[o+1, sp$b] + mm * sp$p
        }
        if (mz > 0 && sp$r == 0) Zs[o+1, sp$b] <- Zs[o+1, sp$b] + mz * sp$p
      }
    }
    Z <- Zs; M <- Ms
    
    for (o in 0:2) for (bidx in 1:8) {
      mz <- Z[o+1, bidx]; mm <- M[o+1, bidx]
      if (mz <= 0 && mm <= 0) next
      st <- NRFI_BASES[[bidx]]; r1 <- st[1]; r2 <- st[2]; r3 <- st[3]
      nrun <- r1 + r2 + r3
      
      tr_r <- numeric(0); tr_o <- integer(0); tr_b <- integer(0); tr_p <- numeric(0)
      T <- function(runs, no, nbi, p) {
        if (p <= 0) return(invisible(NULL))
        tr_r <<- c(tr_r, runs); tr_o <<- c(tr_o, no); tr_b <<- c(tr_b, nbi); tr_p <<- c(tr_p, p)
      }
      
      T(nrun + 1, o, 1L, hr)                                    # home run
      T(nrun,     o, nrfi_bi(0,0,1), t)                         # triple
      
      if (d > 0) {                                              # double
        br <- r2 + r3
        if (r1 == 1) {
          T(br + 1, o, nrfi_bi(0,1,0), d * adv$p_r1_scores_on_2b)
          T(br,     o, nrfi_bi(0,1,1), d * (1 - adv$p_r1_scores_on_2b))
        } else T(br, o, nrfi_bi(0,1,0), d)
      }
      
      if (s > 0) {                                              # single
        if (r2 == 1) {
          for (sc2 in 0:1) {
            p2 <- if (sc2 == 1) adv$p_r2_scores_on_1b else 1 - adv$p_r2_scores_on_1b
            ra <- r3 + sc2; third <- 1 - sc2
            if (r1 == 1) {
              if (third == 1) T(ra, o, nrfi_bi(1,1,1), s * p2)
              else {
                T(ra, o, nrfi_bi(1,0,1), s * p2 * adv$p_r1_to_3rd_on_1b)
                T(ra, o, nrfi_bi(1,1,0), s * p2 * (1 - adv$p_r1_to_3rd_on_1b))
              }
            } else T(ra, o, nrfi_bi(1,0,third), s * p2)
          }
        } else if (r1 == 1) {
          T(r3, o, nrfi_bi(1,0,1), s * adv$p_r1_to_3rd_on_1b)
          T(r3, o, nrfi_bi(1,1,0), s * (1 - adv$p_r1_to_3rd_on_1b))
        } else T(r3, o, nrfi_bi(1,0,0), s)
      }
      
      if (bb > 0) {                                             # walk / HBP: force only
        if (r1 == 0)      T(0, o, nrfi_bi(1, r2, r3), bb)
        else if (r2 == 0) T(0, o, nrfi_bi(1, 1, r3),  bb)
        else if (r3 == 0) T(0, o, nrfi_bi(1, 1, 1),   bb)
        else              T(1, o, nrfi_bi(1, 1, 1),   bb)
      }
      
      if (k > 0) T(0, o + 1L, bidx, k)                          # strikeout
      
      if (gb > 0) {                                             # ground ball
        if (o < 2 && r1 == 1) {
          pdp <- adv$p_gidp
          if (o + 2L >= 3L) T(0, 3L, 1L, gb * pdp)              # DP ends inning: no run
          else T(r3, o + 2L, nrfi_bi(0, 0, r2), gb * pdp)
          rest <- gb * (1 - pdp)
          if (o + 1L >= 3L) T(0, 3L, 1L, rest)
          else {                                                # force out, batter safe at 1st
            psc <- r3 * adv$p_r3_scores_on_fc
            T(1, o + 1L, nrfi_bi(1, r2, 0),  rest * psc)
            T(0, o + 1L, nrfi_bi(1, r2, r3), rest * (1 - psc))
          }
        } else if (o + 1L >= 3L) T(0, 3L, 1L, gb)
        else {
          ps3 <- if (r3 == 1) adv$p_r3_scores_on_gb else 0
          for (sc3 in 0:1) {
            p3 <- if (sc3 == 1) ps3 else 1 - ps3
            if (p3 <= 0) next
            ta <- if (r3 == 1 && sc3 == 0) 1 else 0
            if (r2 == 1 && ta == 0) {
              T(sc3, o + 1L, nrfi_bi(r1,0,1), gb * p3 * adv$p_r2_to_3_on_gb)
              T(sc3, o + 1L, nrfi_bi(r1,1,0), gb * p3 * (1 - adv$p_r2_to_3_on_gb))
            } else T(sc3, o + 1L, nrfi_bi(r1, r2, ta), gb * p3)
          }
        }
      }
      
      if (fb > 0) {                                             # air out / sac fly
        if (o + 1L >= 3L) T(0, 3L, 1L, fb)
        else {
          ps3 <- if (r3 == 1) adv$p_r3_scores_on_fb else 0
          for (sc3 in 0:1) {
            p3 <- if (sc3 == 1) ps3 else 1 - ps3
            if (p3 <= 0) next
            ta <- if (r3 == 1 && sc3 == 0) 1 else 0
            if (r2 == 1 && ta == 0) {
              T(sc3, o + 1L, nrfi_bi(r1,0,1), fb * p3 * adv$p_r2_to_3_on_fb)
              T(sc3, o + 1L, nrfi_bi(r1,1,0), fb * p3 * (1 - adv$p_r2_to_3_on_fb))
            } else T(sc3, o + 1L, nrfi_bi(r1, r2, ta), fb * p3)
          }
        }
      }
      
      if (length(tr_p)) for (j in seq_along(tr_p)) {
        if (mm > 0) {
          exp_runs <- exp_runs + mm * tr_p[j] * tr_r[j]
          if (tr_o[j] < 3L) Mn[tr_o[j]+1L, tr_b[j]] <- Mn[tr_o[j]+1L, tr_b[j]] + mm * tr_p[j]
        }
        if (mz > 0 && tr_r[j] == 0) {
          if (tr_o[j] >= 3L) z_done <- z_done + mz * tr_p[j]
          else Zn[tr_o[j]+1L, tr_b[j]] <- Zn[tr_o[j]+1L, tr_b[j]] + mz * tr_p[j]
        }
      }
    }
    p_scoreless <- p_scoreless + z_done
    Z <- Zn; M <- Mn
    if (sum(Z) < 1e-10 && sum(M) < 1e-7) break
  }
  list(p_scoreless = clamp(p_scoreless, 0.30, 0.95), exp_runs = exp_runs)
}

# ---- who actually bats ----------------------------------------------------
# Confirmed lineup if the club has posted it; otherwise the most common slot
# occupants from the point-in-time player frame (same fallback the wOBA lineup
# scorer uses, so the two views of a team agree).
nrfi_lineup_rows <- function(player_df, team_name, confirmed = NULL, n = 9L) {
  tb <- player_df[player_df$Team == team_name &
                    !is.na(player_df$PlateAppearances) &
                    player_df$PlateAppearances >= MIN_PA_RECENT, , drop = FALSE]
  if (nrow(tb) == 0) return(list(rows = rep(list(NULL), n), confirmed = FALSE, n_avail = 0L))
  used <- integer(0); out <- vector("list", n); got_conf <- FALSE
  if (!is.null(confirmed) && length(confirmed)) {
    ids <- suppressWarnings(as.integer(names(confirmed)))
    slots <- unlist(confirmed, use.names = FALSE)
    ord <- order(slots)
    for (k in ord) {
      sl <- slots[k]; if (is.na(sl) || sl < 1 || sl > n) next
      if (!is.null(out[[sl]])) next
      r <- tb[tb$PlayerID == ids[k], , drop = FALSE]
      if (nrow(r)) { out[[sl]] <- r[1, , drop = FALSE]; used <- c(used, ids[k]); got_conf <- TRUE }
    }
  }
  for (sl in seq_len(n)) {
    if (!is.null(out[[sl]])) next
    cand <- tb[!(tb$PlayerID %in% used) & !is.na(tb$LineupSlot) & tb$LineupSlot == sl, , drop = FALSE]
    if (nrow(cand) == 0) {
      pool <- tb[!(tb$PlayerID %in% used), , drop = FALSE]
      if (nrow(pool) == 0) next
      sv <- pool$LineupSlot; sv[is.na(sv)] <- 5L
      cand <- pool[order(abs(sv - sl), -pool$PlateAppearances), , drop = FALSE]
    } else if (nrow(cand) > 1) cand <- cand[order(-cand$PlateAppearances), , drop = FALSE]
    out[[sl]] <- cand[1, , drop = FALSE]; used <- c(used, cand$PlayerID[1])
  }
  list(rows = out, confirmed = got_conf, n_avail = nrow(tb))
}

# ---- grading: did anyone score in the 1st? --------------------------------
fetch_first_inning_result <- function(game_id) {
  if (is.null(game_id) || is.na(game_id)) return(NULL)
  gid <- tryCatch(as.integer(game_id), error = function(e) NA_integer_)
  if (is.na(gid)) return(NULL)
  d <- http_get_json(sprintf("%s/game/%d/linescore", MLB_API_BASE, gid), silent_404 = TRUE)
  if (is.null(d)) return(NULL)
  tryCatch({
    inns <- d[["innings"]] %||% list()
    if (!length(inns)) return(NULL)
    cur  <- coerce_numeric(scalar(d[["currentInning"]], 0))
    i1   <- inns[[1L]]
    ar   <- coerce_numeric(scalar(i1[["away"]][["runs"]], NA))
    hr_  <- coerce_numeric(scalar(i1[["home"]][["runs"]], NA))
    # only grade once the 1st is actually complete
    done <- (is.finite(cur) && cur > 1) || length(inns) > 1
    if (!done || !is.finite(ar) || !is.finite(hr_)) return(NULL)
    list(away_runs = ar, home_runs = hr_, runs = ar + hr_, nrfi = as.integer((ar + hr_) == 0))
  }, error = function(e) NULL)
}

# ---- ledger + point-in-time calibration (same discipline as the win model) --
nrfi_ledger_load <- function(path = NRFI_LEDGER_PATH) {
  if (!file.exists(path)) return(NULL)
  h <- tryCatch(read.csv(path, stringsAsFactors = FALSE), error = function(e) NULL)
  if (is.null(h) || !nrow(h)) return(NULL)
  h
}

# Same first-pitch rule as awm_append(): a first inning that has not started yet
# is refreshed (confirmed lineups genuinely improve it), one that has started is
# frozen and only ever has its result written in.
# What this model has actually done, over every first inning it has ever called.
#
# Shown on the page on purpose. A pick displayed with a confidence badge and no record
# invites more trust than it has earned, and over 1,825 graded innings this one has not
# separated itself from a coin toss: a Wilson interval that still contains 50% is the
# honest way to say so, and it will stop saying so the moment that stops being true.
nrfi_track_record <- function() {
  h <- tryCatch(nrfi_ledger_load(), error = function(e) NULL)
  if (is.null(h) || !nrow(h) || !("IsCorrect" %in% names(h))) return(NULL)
  h <- h[mlb_competitive_rows(h), , drop = FALSE]
  h <- h[!is.na(h$IsCorrect), , drop = FALSE]
  n <- nrow(h); if (n < 200) return(NULL)
  k <- sum(h$IsCorrect %in% TRUE)
  p <- k / n; z <- 1.96; d <- 1 + z^2 / n
  lo <- (p + z^2/(2*n) - z*sqrt(p*(1-p)/n + z^2/(4*n^2))) / d
  hi <- (p + z^2/(2*n) + z*sqrt(p*(1-p)/n + z^2/(4*n^2))) / d
  sprintf("Measured record: %d of %d correct, %.1f%% (95%% interval %.1f-%.1f%%). %s",
          k, n, 100*p, 100*lo, 100*hi,
          if (lo > 0.5) "Ahead of a coin toss." else
            "That interval still includes 50%, so this has not yet shown an edge over a coin toss \u2014 treat it as a readout, not a recommendation.")
}

nrfi_ledger_append <- function(rows, path = NRFI_LEDGER_PATH) {
  if (is.null(rows) || !nrow(rows)) return(invisible(FALSE))
  rows$Started <- .started_flag(rows, cols = "Started", graded = "ActualNRFI")
  cols <- intersect(c("GameDate","GameID","Matchup","Pick","NRFIProbNum","RawNRFI","TopScoreless",
                      "BotScoreless","F1Runs","Confidence","Started","ActualNRFI","ActualF1Runs",
                      "IsCorrect","Venue","Umpire","HomeSP","AwaySP"), names(rows))
  new <- rows[, cols, drop = FALSE]
  old <- nrfi_ledger_load(path)
  if (is.null(old) || !nrow(old) || !("GameID" %in% names(old)))
    return(tryCatch({ csv_replace(new, path); invisible(TRUE) },
                    error = function(e) invisible(FALSE)))
  for (cc in setdiff(cols, names(old))) old[[cc]] <- NA              # legacy ledgers
  if (!("Started" %in% names(old))) old$Started <- !is.na(old$ActualNRFI)
  started_old <- .is_true(old$Started) | !is.na(old$ActualNRFI)
  idx <- match(as.character(new$GameID), as.character(old$GameID))
  for (k in which(!is.na(idx))) {
    o <- idx[k]
    if (started_old[o]) {
      if (is.na(old$ActualNRFI[o]) && !is.na(new$ActualNRFI[k])) {
        old$ActualNRFI[o]   <- new$ActualNRFI[k]
        old$ActualF1Runs[o] <- new$ActualF1Runs[k]
        old$Started[o]      <- TRUE
        pick <- as.character(old$Pick[o])
        old$IsCorrect[o] <- if (is.na(pick)) new$IsCorrect[k]
        else ((pick == "NRFI") == (as.integer(old$ActualNRFI[o]) == 1L))
      }
    } else {
      for (cc in cols) old[[cc]][o] <- new[[cc]][k]                  # pre-game: refresh
    }
  }
  comb <- .ledger_bind(old, new[is.na(idx), , drop = FALSE])
  comb <- comb[!duplicated(comb$GameID, fromLast = FALSE), , drop = FALSE]
  tryCatch({ csv_replace(comb, path); invisible(TRUE) },
           error = function(e) invisible(FALSE))
}

# Same locked-history rule as the win model: a first inning that has already been
# graded and stored shows the call it was stored with, re-scored against the result.
nrfi_apply_locked <- function(df, history = NULL) {
  if (is.null(df) || !nrow(df)) return(df)
  df$Locked <- FALSE
  if (is.null(history) || !nrow(history)) return(df)
  if (!all(c("GameID", "Pick") %in% names(history))) return(df)
  idx <- match(as.character(df$GameID), as.character(history$GameID))
  stored <- rep(NA_character_, nrow(df))
  stored[!is.na(idx)] <- as.character(history$Pick[idx[!is.na(idx)]])
  stored_started <- rep(FALSE, nrow(df))
  ok <- !is.na(idx)
  if ("Started" %in% names(history)) stored_started[ok] <- .is_true(history$Started[idx[ok]])
  if ("ActualNRFI" %in% names(history))
    stored_started[ok] <- stored_started[ok] | !is.na(history$ActualNRFI[idx[ok]])
  started_now <- .started_flag(df, cols = "Started", graded = "ActualNRFI")
  hit <- !is.na(stored) & stored %in% c("NRFI", "YRFI") & (stored_started | started_now)
  if (!any(hit)) return(df)
  hrow <- history[idx[hit], , drop = FALSE]
  df$Pick[hit] <- stored[hit]
  if ("NRFIProbNum" %in% names(hrow)) {
    pn <- suppressWarnings(as.numeric(hrow$NRFIProbNum)); ok <- is.finite(pn)
    if (any(ok)) {
      df$NRFIProbNum[hit][ok] <- pn[ok]
      df$NRFIProb[hit][ok]    <- paste0(round(pn[ok], 1), "%")
      df$YRFIProb[hit][ok]    <- paste0(round(100 - pn[ok], 1), "%")
      df$Edge[hit][ok]        <- round(pn[ok] - NRFI_LG_BASE * 100, 1)
    }
  }
  if ("Confidence" %in% names(hrow)) {
    cf <- as.character(hrow$Confidence); ok <- !is.na(cf) & nzchar(cf)
    df$Confidence[hit][ok] <- cf[ok]
  }
  act <- suppressWarnings(as.integer(df$ActualNRFI[hit]))
  df$IsCorrect[hit] <- ifelse(is.na(act), NA, (df$Pick[hit] == "NRFI") == (act == 1L))
  df$Locked[hit] <- TRUE
  df
}

# Learn the model's own bias from graded games BEFORE the slate date. Never
# trains on a game it is predicting -- same leakage guard as the win model.
nrfi_fit_calibration <- function(history, as_of_date, half_life = NRFI_CAL_HALF_LIFE,
                                 min_games = NRFI_MIN_GAMES_CAL) {
  ident <- list(a = 1, b = 0, ok = FALSE, n = 0)
  if (is.null(history) || !nrow(history)) return(ident)
  if (!all(c("RawNRFI","ActualNRFI","GameDate") %in% names(history))) return(ident)
  h <- history[!is.na(history$ActualNRFI), , drop = FALSE]
  h <- h[mlb_competitive_rows(h), , drop = FALSE]
  asof <- as.Date(as_of_date)
  h <- h[as.Date(h$GameDate) < asof, , drop = FALSE]           # <<< LEAKAGE GUARD
  if (!nrow(h)) return(ident)
  p  <- suppressWarnings(as.numeric(h$RawNRFI)) / 100
  y  <- as.integer(suppressWarnings(as.numeric(h$ActualNRFI)))
  gd <- as.Date(h$GameDate)
  ok <- is.finite(p) & p > 0.02 & p < 0.98 & !is.na(y)
  p <- p[ok]; y <- y[ok]; gd <- gd[ok]
  if (length(p) < min_games) return(ident)
  z   <- qlogis(p)
  wts <- 0.5 ^ (as.numeric(asof - gd) / half_life)
  fit <- tryCatch(suppressWarnings(glm(y ~ z, family = binomial(), weights = wts)),
                  error = function(e) NULL)
  if (is.null(fit) || any(!is.finite(coef(fit)))) return(ident)
  list(a = unname(coef(fit)[["z"]]), b = unname(coef(fit)[["(Intercept)"]]),
       ok = TRUE, n = length(p))
}

nrfi_apply_calibration <- function(p, cal) {
  if (is.null(cal) || !isTRUE(cal$ok)) return(p)
  z <- qlogis(clamp(p, 0.02, 0.98))
  clamp(plogis(cal$a * z + cal$b), 0.12, 0.88)
}

# Re-measure the league base rate from the model's own graded history.
refresh_nrfi_baselines <- function(history, as_of_date = NULL) {
  if (is.null(history) || !"ActualNRFI" %in% names(history)) return(invisible(FALSE))
  # LEAKAGE FIX (v9): same problem as HOME_FIELD_EDGE -- NRFI_LG_BASE was measured
  # over the whole ledger, so first innings that had not happened yet moved the
  # anchor (and the confidence edge) for a slate already in the past.
  if (!is.null(as_of_date) && "GameDate" %in% names(history)) {
    keep <- suppressWarnings(as.Date(history$GameDate) < as.Date(as_of_date))
    keep[is.na(keep)] <- FALSE
    history <- history[keep, , drop = FALSE]
    if (!nrow(history)) return(invisible(FALSE))
  }
  history <- history[mlb_competitive_rows(history), , drop = FALSE]
  a <- suppressWarnings(as.numeric(history$ActualNRFI)); a <- a[!is.na(a)]
  if (length(a) >= 250) {
    NRFI_LG_BASE           <<- clamp(mean(a), 0.44, 0.62)
    NRFI_LG_HALF_SCORELESS <<- clamp(sqrt(NRFI_LG_BASE), 0.65, 0.80)
  }
  invisible(TRUE)
}

# Backfill the first-inning ledger from past slates, so calibration has enough
# graded innings to switch on without the user clicking through dates one at a
# time. Mirrors awm_catch_up(): walks days, skips dates already recorded, and
# leans on .gamelog_cache (NOT cleared between dates) so the expensive per-player
# game logs are fetched once for the whole run rather than once per date.
#
# Unlike the win backfill this defaults to a bounded RECENT window rather than
# the whole season: the calibration is recency-weighted anyway (45-day half-life),
# so the last ~45 days carry nearly all the signal and cost a fraction of the time.
# Raise max_days if you want a deeper history.
nrfi_catch_up <- function(end_date = Sys.Date() - 1, recent_games = 15L,
                          max_days = 45L, on_progress = NULL) {
  end_date <- as.Date(end_date); h <- nrfi_ledger_load()
  have <- if (!is.null(h) && "GameDate" %in% names(h))
    unique(as.character(as.Date(h$GameDate))) else character(0)
  season_floor <- mlb_season_start(format(end_date, "%Y"))   # regular season only (v10)
  # Deliberate divergence from awm_catch_up(): that one resumes at last_recorded+1,
  # so a date that errored mid-backfill (network blip) is stepped over and never
  # retried. Here the window is fixed and already-recorded dates are skipped by the
  # `have` test below, so any hole heals itself on the next run at no extra cost --
  # skipping a recorded date is a loop iteration, not a fetch.
  from <- max(season_floor, end_date - max_days + 1)
  if (from > end_date) return(invisible(0L))
  dates <- seq(from, end_date, by = "day"); done <- 0L
  for (k in seq_along(dates)) {
    ds <- format(dates[k], "%Y-%m-%d")
    if (ds %in% have) next
    if (isTRUE(tryCatch(nrow(fetch_mlb_schedule(ds)) == 0L, error = function(e) FALSE))) next
    if (!is.null(on_progress)) on_progress(k / length(dates), ds)
    tryCatch(with_quiet_log({
      dat <- prepare_data(recent_games = recent_games, date_str = ds)
      project_first_inning(dat$schedule_df, dat$player_batting_df, dat$pitching_df,
                           dat$pitcher_stats_dict, team_batting_df = dat$team_batting_df,
                           season = dat$season, slate_date = dates[k])
      done <- done + 1L
    }), error = function(e) NULL)
    Sys.sleep(0.2)
  }
  if (done > 0L)
    mlog(sprintf("Memory     | backfilled %d day(s) of first innings", done))
  invisible(done)
}

# ============================================================================
# MAIN: one row per game, ranked by confidence that NO run scores in the 1st
# ============================================================================
project_first_inning <- function(schedule_df, player_batting_df, pitching_df,
                                 pitcher_stats_dict, team_batting_df = NULL,
                                 season = "2026", slate_date = Sys.Date()) {
  if (is.null(schedule_df) || nrow(schedule_df) == 0) return(data.frame())
  
  # Team running game: a leadoff man who steals turns a single into a runner in
  # scoring position without a hit, which is a real first-inning run source.
  team_adv <- function(team) {
    a <- NRFI_ADV
    if (is.null(team_batting_df) || !nrow(team_batting_df)) return(a)
    r <- team_batting_df[team_batting_df$Team == team, , drop = FALSE]
    if (!nrow(r)) return(a)
    sb <- suppressWarnings(as.numeric(r$StolenBases[1] %||% NA))
    gm <- suppressWarnings(as.numeric(r$Games[1] %||% NA))
    if (!is.finite(sb) || !is.finite(gm) || gm < 5 || LG_AVG_SB_PER_G <= 0) return(a)
    f <- clamp((sb/gm) / LG_AVG_SB_PER_G, 0.50, 1.80)
    a$p_steal_1to2 <- a$p_steal_1to2 * f
    a$p_steal_2to3 <- a$p_steal_2to3 * f
    a
  }
  hist <- nrfi_ledger_load()
  tryCatch(refresh_nrfi_baselines(hist, as_of_date = slate_date), error = function(e) NULL)
  cal <- tryCatch(nrfi_fit_calibration(hist, slate_date),
                  error = function(e) list(a = 1, b = 0, ok = FALSE, n = 0))
  if (isTRUE(cal$ok))
    mlog(sprintf("NRFI model | calibration a=%.3f b=%.3f  (fit on %d graded 1st innings before %s)",
                 cal$a, cal$b, cal$n, as.character(slate_date)))
  else
    mlog(sprintf("NRFI model | calibration off (needs %d graded 1st innings before %s) -> raw model",
                 NRFI_MIN_GAMES_CAL, as.character(slate_date)))
  
  rows <- list(); .nrfi_skipped <- list()
  for (i in seq_len(nrow(schedule_df))) {
    tryCatch({
      g <- schedule_df[i, ]; ht <- g$HomeTeam; at <- g$AwayTeam; gid <- g$GameID
      hps <- pitcher_stats_dict[[as.character(g$HomePitcherID)]]
      aps <- pitcher_stats_dict[[as.character(g$AwayPitcherID)]]
      
      # shared environment: park, weather, umpire -- scaled from run space into
      # event space, because a +10% run park is not a +10% on-base park.
      wx  <- if ("Weather" %in% names(g)) g$Weather[[1L]] else list()
      wa  <- advanced_weather_adjustment(wx, g$Venue)
      pr  <- get_park_factor(g$Venue, "runs")
      ump <- get_umpire_adjustment(g$Umpire %||% NA_character_)
      run_env  <- clamp(pr * wa$runs * (1 + (ump$runs_delta %||% 0)/LG_AVG_RUNS_PER_GAME), 0.75, 1.35)
      env_mult <- 1 + (run_env - 1)/NRFI_RUN_ELASTICITY
      
      conf_lu <- tryCatch(fetch_confirmed_lineup(gid), error = function(e) NULL)
      h_lu <- nrfi_lineup_rows(player_batting_df, ht, conf_lu)
      a_lu <- nrfi_lineup_rows(player_batting_df, at, conf_lu)
      
      mk_side <- function(lu, pit, phand) {
        lapply(lu$rows, function(r)
          nrfi_batter_vector(r, pit, if (is.null(r)) "R" else (r$BatHand[1] %||% "R"),
                             phand, env_mult, ump$k_delta %||% 0, ump$bb_delta %||% 0))
      }
      top <- nrfi_half_inning(mk_side(a_lu, hps, g$HomePitcherHand %||% "R"), adv = team_adv(at))
      bot <- nrfi_half_inning(mk_side(h_lu, aps, g$AwayPitcherHand %||% "R"), adv = team_adv(ht))
      
      # shrink each half toward the measured league anchor, then join the halves
      # with a small positive correlation (shared park/weather/umpire/ball).
      shr <- function(p) (1 - NRFI_ANCHOR_WEIGHT)*p + NRFI_ANCHOR_WEIGHT*NRFI_LG_HALF_SCORELESS
      pt <- clamp(shr(top$p_scoreless), 0.35, 0.94)
      pb <- clamp(shr(bot$p_scoreless), 0.35, 0.94)
      rho <- NRFI_HALF_CORRELATION
      raw_nrfi <- clamp(pt*pb + rho*sqrt(pt*(1-pt)*pb*(1-pb)), 0.15, 0.90)
      nrfi <- nrfi_apply_calibration(raw_nrfi, cal)
      f1_runs <- top$exp_runs + bot$exp_runs
      
      # ---- confidence: edge off the league base rate, gated on data quality --
      h_ip <- suppressWarnings(as.numeric(hps$InningsPitched %||% 0))
      a_ip <- suppressWarnings(as.numeric(aps$InningsPitched %||% 0))
      if (!is.finite(h_ip)) h_ip <- 0; if (!is.finite(a_ip)) a_ip <- 0
      sp_ok   <- (h_ip >= MIN_IP_SEASON) && (a_ip >= MIN_IP_SEASON)
      lu_ok   <- (h_lu$n_avail >= 8) && (a_lu$n_avail >= 8)
      tbd     <- is.na(g$HomePitcherID %||% NA) || is.na(g$AwayPitcherID %||% NA)
      lu_conf <- isTRUE(h_lu$confirmed) || isTRUE(a_lu$confirmed)
      edge    <- (nrfi - NRFI_LG_BASE) * 100
      dq      <- sum(c(sp_ok, lu_ok, !tbd, lu_conf))
      conf_lbl <- if (tbd || !lu_ok) "Low"
      else if (abs(edge) >= 6 && dq >= 3) "High"
      else if (abs(edge) >= 3 && dq >= 2) "Medium" else "Low"
      
      flags <- character(0)
      if (lu_conf) flags <- c(flags, "LU\u2713")
      if (tbd)     flags <- c(flags, "SP-TBD")
      if (!sp_ok)  flags <- c(flags, "thinSP")
      if (run_env >= 1.10) flags <- c(flags, "ENV+") else if (run_env <= 0.92) flags <- c(flags, "ENV-")
      
      # ---- grade, if the 1st is already in the books ----
      fr <- tryCatch(fetch_first_inning_result(gid), error = function(e) NULL)
      act_nrfi <- if (is.null(fr)) NA_integer_ else fr$nrfi
      act_runs <- if (is.null(fr)) NA_real_    else fr$runs
      pick_no  <- nrfi >= 0.50
      correct  <- if (is.na(act_nrfi)) NA else (pick_no == (act_nrfi == 1L))
      res_str  <- if (is.na(act_nrfi)) "\u2014"
      else if (act_nrfi == 1L) "NRFI (0 runs)"
      else sprintf("YRFI (%s%d run%s)", if (fr$away_runs > 0 && fr$home_runs > 0) "" else
        (if (fr$away_runs > 0) "away " else "home "), as.integer(act_runs),
        if (act_runs == 1) "" else "s")
      
      rows[[length(rows)+1L]] <- data.frame(
        GameID = gid, GameDate = as.character(slate_date),
        Matchup = paste0(at, " @ ", ht),
        Starters = paste0(g$AwayPitcher %||% "TBD", " vs ", g$HomePitcher %||% "TBD"),
        NRFIProb = paste0(round(nrfi*100, 1), "%"), NRFIProbNum = round(nrfi*100, 1),
        YRFIProb = paste0(round((1-nrfi)*100, 1), "%"),
        RawNRFI = round(raw_nrfi*100, 1),
        TopScoreless = round(pt*100, 1), BotScoreless = round(pb*100, 1),
        F1Runs = round(f1_runs, 2),
        Pick = if (pick_no) "NRFI" else "YRFI",
        Started = !is.na(act_nrfi) ||
          isTRUE(grepl("Progress|Live|Final|Game Over|Completed",
                       g$GameStatus %||% "", ignore.case = TRUE)),
        Edge = round(edge, 1), Confidence = conf_lbl,
        Flags = paste(flags, collapse = " "),
        HomeSP = g$HomePitcher %||% "TBD", AwaySP = g$AwayPitcher %||% "TBD",
        Venue = g$Venue %||% NA_character_, Umpire = g$Umpire %||% NA_character_,
        ActualNRFI = act_nrfi, ActualF1Runs = act_runs,
        Result = res_str, IsCorrect = correct,
        stringsAsFactors = FALSE)
    }, error = function(e) {
      .nrfi_skipped[[length(.nrfi_skipped) + 1L]] <<- conditionMessage(e)
    })
  }
  if (length(.nrfi_skipped))
    mlog(sprintf("NRFI model | %d game(s) skipped: %s", length(.nrfi_skipped),
                 paste(utils::head(unlist(.nrfi_skipped), 3L), collapse = "; ")))
  if (!length(rows)) return(data.frame())
  df <- bind_rows(rows)
  df <- tryCatch(nrfi_apply_locked(df, hist), error = function(e) df)
  tryCatch(nrfi_ledger_append(df), error = function(e) NULL)
  # ranked by confidence that NO run scores -- highest NRFI probability first
  df[order(-df$NRFIProbNum), , drop = FALSE]
}

project_home_run_hitters <- function(schedule_df, player_batting_df, pitching_df,
                                     recent_player_batting_df, recent_pitching_df,
                                     pitcher_stats_dict, top_n_per_game=3, season="2026") {
  if (nrow(schedule_df) == 0 || nrow(player_batting_df) == 0) return(data.frame())
  rows <- list(); .hr_skipped <- 0L
  for (i in seq_len(nrow(schedule_df))) {
    tryCatch({
      g   <- schedule_df[i, ]; ht <- g$HomeTeam; at <- g$AwayTeam; gid <- g$GameID
      bs  <- fetch_game_boxscore(gid); gs <- g$GameStatus; innings_done <- 0
      if (!is.null(bs)) { gs <- bs$GameStatus; innings_done <- bs$InningsCompleted %||% 0 }
      ast <- data.frame()
      if (!is.null(gs) && !is.na(gs) && gs != "Scheduled")
        ast <- tryCatch(fetch_game_player_stats(gid), error=function(e) data.frame())
      wx  <- if ("Weather" %in% names(g)) g$Weather[[1L]] else list()
      wa  <- advanced_weather_adjustment(wx, g$Venue)
      ump_adj <- get_umpire_adjustment(g$Umpire %||% NA_character_)
      innings_remaining <- if (!is.null(gs) && !is.na(gs) && grepl("Progress|Live", gs, ignore.case=TRUE))
        max(9 - innings_done, 0) / 9 else 1.0
      hps <- pitcher_stats_dict[[as.character(g$HomePitcherID)]]
      aps <- pitcher_stats_dict[[as.character(g$AwayPitcherID)]]
      confirmed_lineup <- tryCatch(fetch_confirmed_lineup(gid), error=function(e) NULL)
      for (pair in list(
        list(batting_team=ht, opp_ps=aps, opp_hand=g$AwayPitcherHand, opp_pid=g$AwayPitcherID,
             opp_name=g$AwayPitcher, opp_team=at, venue=g$Venue, is_home_pitcher=FALSE),
        list(batting_team=at, opp_ps=hps, opp_hand=g$HomePitcherHand, opp_pid=g$HomePitcherID,
             opp_name=g$HomePitcher, opp_team=ht, venue=g$Venue, is_home_pitcher=TRUE))) {
        team <- pair$batting_team; opp_ps <- pair$opp_ps; opp_hand <- pair$opp_hand
        opp_pid <- pair$opp_pid; opp_name <- pair$opp_name; venue <- pair$venue
        is_home_p <- pair$is_home_pitcher; opp_team <- pair$opp_team
        tb <- player_batting_df[player_batting_df$Team == team & !is.na(player_batting_df$PlateAppearances) &
                                  player_batting_df$PlateAppearances >= MIN_PA_SEASON, , drop=FALSE]
        if (nrow(tb) == 0)
          tb <- player_batting_df[player_batting_df$Team == team & !is.na(player_batting_df$PlateAppearances) &
                                    player_batting_df$PlateAppearances > 0, , drop=FALSE]
        if (nrow(tb) == 0) next
        # v10: only hitters who will actually bat. With a posted lineup, exactly those
        # nine; otherwise everyday players (3.2+ PA per game) who played in the last 5
        # days. Bench bats used to be ranked here and then graded "No HR" when they sat.
        in_lineup <- FALSE
        if (!is.null(confirmed_lineup) && length(confirmed_lineup) > 0) {
          conf_ids <- suppressWarnings(as.integer(names(confirmed_lineup)))
          # the posted nine; a starter with no batting row yet (activated today) just isn't ranked
          if (sum(tb$PlayerID %in% conf_ids) >= 7) {
            tb <- tb[tb$PlayerID %in% conf_ids, , drop = FALSE]; in_lineup <- TRUE
          }
          for (j in seq_len(nrow(tb))) {
            slot_val <- confirmed_lineup[[as.character(tb$PlayerID[j])]]
            if (!is.null(slot_val) && !is.na(slot_val)) tb$LineupSlot[j] <- as.integer(slot_val)
          }
        }
        if (!in_lineup && "LastGameDate" %in% names(tb)) {
          recent_ok <- !is.na(tb$LastGameDate) &
            suppressWarnings(as.Date(tb$LastGameDate)) >= (as.Date(g$Date %||% Sys.Date()) - 5)
          regular <- recent_ok & (tb$PAperG %||% 0) >= 3.2
          if (sum(regular) >= 6) tb <- tb[regular, , drop = FALSE]
          else if (sum(recent_ok) >= 6) tb <- tb[recent_ok, , drop = FALSE]
        }
        trb <- recent_player_batting_df[recent_player_batting_df$Team == team, , drop=FALSE]
        sp_era_for_tier <- opp_ps$ERA %||% LG_AVG_ERA; sp_kpct <- opp_ps$KPct %||% LG_AVG_K_PCT
        sp_bbpct <- opp_ps$BBPct %||% LG_AVG_BB_PCT; sp_whiff <- opp_ps$WhiffPct %||% LG_AVG_WHIFF_PCT
        sp_recent_era <- opp_ps$RecentERA
        sp_tier <- classify_sp_tier(sp_era_for_tier, sp_kpct, sp_bbpct, sp_whiff, sp_recent_era=sp_recent_era)
        sp_adj  <- sp_batting_adjustment(sp_tier, sp_kpct, sp_bbpct, opp_ps$AvgVelo %||% 92.0, sp_whiff,
                                         opp_ps$FBPct_arsenal %||% 0.55, ump_adj$k_delta, ump_adj$bb_delta)
        opp_era_recent <- opp_ps$RecentERA %||% opp_ps$ERA %||% LG_AVG_ERA
        pitcher_vuln   <- clamp(opp_era_recent / LG_AVG_ERA, 0.40, 2.20)
        is_struggling  <- !is.null(opp_ps$RecentERA) && opp_ps$RecentERA > 7.0 && (opp_ps$RecentIP %||% 0) >= MIN_IP_PITCHER
        is_sharp       <- !is.null(opp_ps$RecentERA) && opp_ps$RecentERA < 2.5 && (opp_ps$RecentIP %||% 0) >= MIN_IP_PITCHER
        if (is_struggling) pitcher_vuln <- pitcher_vuln * 1.18
        if (is_sharp)      pitcher_vuln <- pitcher_vuln * 0.85
        gb_fb_factor   <- pitcher_gb_fb_hr_factor(opp_ps$GBPct, opp_ps$FBPct, venue)
        stuff_factor   <- stuff_quality_hr_factor(opp_ps$KPct %||% LG_AVG_K_PCT, opp_ps$BBPct %||% LG_AVG_BB_PCT)
        xfip_factor    <- clamp(1+(opp_ps$xFIP-LG_AVG_FIP)/LG_AVG_FIP*0.55, 0.72, 1.38)
        siera_factor   <- if (!is.null(opp_ps$SIERA) && !is.na(opp_ps$SIERA %||% NA_real_))
          clamp(1+(opp_ps$SIERA-LG_AVG_FIP)/LG_AVG_FIP*0.52, 0.72, 1.38) else xfip_factor
        arsenal_factor <- get_arsenal_hr_factor(opp_ps$FBPct_arsenal %||% 0.55, opp_ps$BreakingPct, opp_ps$OffspeedPct)
        pitcher_avg_ip <- opp_ps$AvgIPPerStart %||% STARTER_INNINGS_DEFAULT
        pitcher_bb_pct <- opp_ps$BBPct %||% LG_AVG_BB_PCT
        home_away_f    <- pitcher_home_away_factor(opp_ps$HomeERA, opp_ps$AwayERA, is_home_p)
        hr_fb_allowed_f <- 1.0
        if (!is.null(opp_ps$HR_FB_Rate_allowed) && !is.na(opp_ps$HR_FB_Rate_allowed %||% NA_real_))
          hr_fb_allowed_f <- clamp(opp_ps$HR_FB_Rate_allowed / 0.135, 0.60, 1.85)
        whip_hr_factor <- if (!is.null(opp_ps$WHIP) && !is.na(opp_ps$WHIP %||% NA_real_))
          clamp(1.0 + (opp_ps$WHIP - 1.30) * WHIP_WIN_CORRELATION * 0.25, 0.78, 1.38) else 1.0
        count_lev_f <- hitter_count_hr_factor(pitcher_bb_pct, ump_adj$bb_delta)
        pip_val    <- opp_ps$PitchesPerIP %||% LG_AVG_PITCHES_PER_IP
        pip_hr_factor <- clamp(1.0 + (pip_val - LG_AVG_PITCHES_PER_IP)/LG_AVG_PITCHES_PER_IP*0.08, 0.90, 1.15)
        bb_hr_boost <- if (sp_adj$bb_collapse_flag) 1.12 else 1.00
        combined_pitcher_vuln <- pitcher_vuln * gb_fb_factor * stuff_factor *
          (SIERA_W_SIERA*siera_factor + (1 - SIERA_W_SIERA)*xfip_factor) *
          arsenal_factor * hr_fb_allowed_f * home_away_f * pip_hr_factor *
          whip_hr_factor * sp_adj$iso_mult * bb_hr_boost
        opp_hr9_feat <- 1.1
        ohr <- pitching_df[pitching_df$Team == opp_team, , drop=FALSE]
        if (nrow(ohr) > 0 && safe_val(ohr$InningsPitched[1], 0) > 0)
          opp_hr9_feat <- ohr$HomeRunsAllowed[1] / ohr$InningsPitched[1] * 9
        n_players <- nrow(tb)
        tb$HRProb <- rep(NA_real_, n_players); tb$H2H_PA_val <- rep(0L, n_players); tb$H2H_HR_val <- rep(0L, n_players)
        for (j in seq_len(n_players)) {
          pl <- tb[j, ]; pid <- pl$PlayerID; bh <- as.character(pl$BatHand %||% "R")
          eff_hand <- effective_bat_hand(bh, opp_hand)
          player_iso <- safe_val(pl$ISO, 0.150); adj_iso <- clamp(player_iso * sp_adj$iso_mult, 0.04, 0.35)
          player_ev  <- safe_val(pl$AvgEV, LG_AVG_EXIT_VELO); adj_ev <- player_ev * sp_adj$ev_suppress
          player_la  <- safe_val(pl$AvgLA, LG_AVG_LAUNCH_ANGLE); ptype <- player_type(adj_iso)
          platoon_k  <- platoon_key(bh, opp_hand)
          platoon_base <- PLATOON_HR_RATE[[platoon_k]] %||% LG_AVG_HR_PER_PA
          platoon_base_adj <- platoon_base * sp_adj$iso_mult
          hand_hr_rate <- if (opp_hand == "L") { v <- pl$HRRate_L; if (is.null(v)||length(v)!=1||is.na(v)) pl$HRRate else v }
          else { v <- pl$HRRate_R; if (is.null(v)||length(v)!=1||is.na(v)) pl$HRRate else v }
          if (is.null(hand_hr_rate)||length(hand_hr_rate)!=1||is.na(hand_hr_rate)) hand_hr_rate <- LG_AVG_HR_PER_PA
          pa_val <- safe_val(pl$PlateAppearances, 0)
          season_hr_rate <- regress_to_mean(hand_hr_rate, pa_val, platoon_base_adj, type=ptype)
          rpl <- trb[!is.na(trb$PlayerID) & trb$PlayerID == pid, , drop=FALSE]
          recent_rate <- if (nrow(rpl) > 0 && !is.na(rpl$PlateAppearances[1]) && rpl$PlateAppearances[1] >= MIN_PA_RECENT) rpl$HRRate[1] else NULL
          recent_pa   <- if (nrow(rpl) > 0 && !is.na(rpl$PlateAppearances[1])) rpl$PlateAppearances[1] else 0
          player_hr_rate <- streak_blend_hr_rate(season_hr_rate, pa_val, recent_rate, recent_pa)
          batter_babip_adj <- if ("BABIP" %in% names(pl))
            compute_babip_luck_adj(pl$BABIP %||% 0.296, pl$xBABIP, rolling_games=min(pa_val/4, 30)) else 1.0
          player_hr_rate <- player_hr_rate * batter_babip_adj
          player_slg <- safe_val(pl$SLG, 0.420)
          cluster_mult <- iso_cluster_hr_boost(adj_iso, player_slg)
          player_hr_rate <- player_hr_rate * cluster_mult
          pitcher_velo <- opp_ps$AvgVelo %||% 92.0
          velo_f  <- get_velo_hr_factor(pitcher_velo, adj_iso, adj_ev)
          slot_raw <- tb$LineupSlot[j]
          slot <- if (is.null(slot_raw)||length(slot_raw)!=1||is.na(slot_raw)) 5L else max(1L, min(9L, as.integer(slot_raw)))
          tto_f    <- get_tto_multiplier(slot, pitcher_avg_ip)
          pull_pct_val <- safe_val(pl$PullPct, LG_AVG_PULL_PCT)
          park_hr  <- get_park_hr_factor(venue, eff_hand, pull_pct_val)
          iso_mult <- iso_power_multiplier(adj_iso)
          bp <- safe_val(pl$BarrelPct, LG_AVG_BARREL_PCT); hh <- safe_val(pl$HardHitPct, LG_AVG_HARD_HIT_PCT)
          adj_bp <- clamp(bp * sp_adj$contact_quality, 0.02, 0.25)
          barrel_mult <- barrel_power_multiplier(adj_bp, hh)
          la_bonus    <- clamp(1.0 + (player_la - LG_AVG_LAUNCH_ANGLE)*0.022, 0.76, 1.35)
          hr_fb_batter_f <- 1.0; hr_fb_val <- pl$HR_FB_Rate
          if (!is.null(hr_fb_val) && length(hr_fb_val)==1 && !is.na(hr_fb_val) && hr_fb_val>0)
            hr_fb_batter_f <- clamp(hr_fb_val / 0.135, 0.50, 2.25)
          # H2H REMOVED (target leakage): no batter-vs-pitcher lookups.
          combined_pa <- 0L; combined_hr <- 0L
          tb$H2H_PA_val[j] <- combined_pa; tb$H2H_HR_val[j] <- combined_hr
          bay <- bayesian_matchup_hr_rate(career_hr=combined_hr, career_pa=combined_pa,
                                          platoon_hr_rate=platoon_base_adj, arsenal_factor=arsenal_factor, velo_factor=velo_f,
                                          tto_factor=tto_f, park_factor=park_hr, count_leverage_factor=count_lev_f,
                                          pitcher_home_away_f=home_away_f, sp_iso_mult=sp_adj$iso_mult)
          z_hr <- HR_COEF[["intercept"]] +
            HR_COEF[["batter_hr_rate"]] * safe_val(pl$HRRate, LG_AVG_HR_PER_PA) +
            HR_COEF[["batter_iso"]]     * safe_val(pl$ISO, 0.140) +
            HR_COEF[["opp_hr9"]]        * opp_hr9_feat +
            HR_COEF[["park_hr"]]        * park_hr +
            HR_COEF[["platoon"]]        * (platoon_base / LG_AVG_HR_PER_PA) +
            log(clamp(wa$hr %||% 1, 0.65, 1.45))     # v10: temperature / wind (was always neutral)
          tb$HRProb[j] <- clamp(1 / (1 + exp(-z_hr)), 0.002, 0.60)
        }
        tb <- tb[!is.na(tb$HRProb), , drop=FALSE]
        if (nrow(tb) == 0) next
        top <- tb[order(-tb$HRProb), , drop=FALSE][seq_len(min(top_n_per_game, nrow(tb))), , drop=FALSE]
        for (j in seq_len(nrow(top))) {
          pl <- top[j, ]; result_note <- "\u2014"; is_final_hr <- FALSE; correct_hr <- NA
          if (nrow(ast) > 0 && "PlayerID" %in% names(ast)) {
            gs_check <- gs %||% ""; is_final_hr <- gs_check %in% c("Final","Game Over","Completed Early")
            if (is_final_hr) {
              pa <- ast[!is.na(ast$PlayerID) & ast$PlayerID == pl$PlayerID, , drop=FALSE]
              if (nrow(pa) == 0) {
                result_note <- "DNP"; correct_hr <- NA            # did not bat: not a miss
              } else {
                result_note <- if (!is.na(pa$HomeRuns[1]) && pa$HomeRuns[1] > 0) "\u2713 Hit HR" else "\u2717 No HR"
                correct_hr  <- grepl("\u2713", result_note)
              }
            }
          }
          rows[[length(rows)+1L]] <- data.frame(
            GameID=gid, PlayerID=pl$PlayerID,
            Player=pl$PlayerName, Team=team, Matchup=paste0(at," @ ",ht), OppPitcher=opp_name,
            SPTier=sp_tier$tier, HRProb=paste0(round(pl$HRProb*100,1),"%"), HRProbNum=round(pl$HRProb*100,1),
            Result=result_note, IsCorrect=correct_hr, stringsAsFactors=FALSE)
        }
      }
    }, error = function(e) { .hr_skipped <<- .hr_skipped + 1L })
  }
  if (.hr_skipped > 0L) mlog(sprintf("HR model   | %d game(s) skipped", .hr_skipped))
  if (!length(rows)) return(data.frame())
  df <- bind_rows(rows); df$HRProbNum <- as.numeric(df$HRProbNum); df <- df[order(-df$HRProbNum), ]; df
}

# STRIKEOUT PROJECTION (v10). Validated on 4,523 starts from the 2026 season:
# mean absolute error 1.81 K (was 1.93), correlation with actual 0.44 (was 0.38).
# Changes: the opponent's BATTING strikeout rate (the old code used the opponent's
# PITCHING staff K%), a log5 merge of pitcher and lineup rates, and batters faced
# from the pitcher's own starts (not innings over all appearances x 4.3). A pitcher
# with no starts yet is expected to face 30% fewer batters (openers, call-ups).
K_PRIOR_BF     <- 120
K_OPP_PRIOR_PA <- 600
K_SCALE        <- 0.98
K_NB_SIZE      <- 15
k_log5 <- function(b, p, l) { o <- (b/(1-b))*(p/(1-p))/(l/(1-l)); o/(1+o) }
project_pitcher_strikeouts <- function(schedule_df, pitcher_stats_dict, pitching_df,
                                       season="2026", allow_completed=FALSE, team_batting_df=NULL) {
  if (nrow(schedule_df) == 0) return(data.frame())
  rows <- list()
  lgk <- LG_AVG_K_PCT
  for (i in seq_len(nrow(schedule_df))) {
    tryCatch({
      g <- schedule_df[i, ]
      is_done <- isTRUE(g$GameStatus %in% c("Final","Game Over","Completed Early"))
      if (is_done && !allow_completed) next
      sp_ks <- if (is_done) tryCatch(fetch_game_sp_ks(g$GameID), error=function(e) NULL) else NULL
      for (side in list(
        list(sp_id=g$HomePitcherID, sp_name=g$HomePitcher, opp_team=g$AwayTeam, is_home=TRUE),
        list(sp_id=g$AwayPitcherID, sp_name=g$AwayPitcher, opp_team=g$HomeTeam, is_home=FALSE))) {
        sp_name <- as.character(side$sp_name %||% "TBD")
        if (sp_name == "TBD" || is.na(side$sp_id)) next
        ps  <- pitcher_stats_dict[[as.character(side$sp_id)]]
        bfk <- if (!is.null(ps)) c(ps$SeasonK %||% 0, ps$SeasonBF %||% 0) else c(0, 0)
        pk  <- (bfk[1] + lgk * K_PRIOR_BF) / (bfk[2] + K_PRIOR_BF)
        opp <- if (!is.null(team_batting_df) && nrow(team_batting_df))
          team_batting_df[team_batting_df$Team == side$opp_team, , drop = FALSE] else data.frame()
        ok_k  <- if (nrow(opp)) as.numeric(opp$KPct[1]) * as.numeric(opp$PlateAppearances[1]) else 0
        ok_pa <- if (nrow(opp)) as.numeric(opp$PlateAppearances[1]) else 0
        if (!is.finite(ok_k) || !is.finite(ok_pa)) { ok_k <- 0; ok_pa <- 0 }
        opk <- (ok_k + lgk * K_OPP_PRIOR_PA) / (ok_pa + K_OPP_PRIOR_PA)
        k_rate <- k_log5(clamp(pk, 0.05, 0.45), clamp(opk, 0.10, 0.40), clamp(lgk, 0.15, 0.30))
        exp_bf <- if (!is.null(ps)) as.numeric(ps$StartBF %||% (LG_BF_PER_START * 0.7)) else LG_BF_PER_START * 0.7
        exp_k  <- clamp(k_rate * exp_bf * K_SCALE, 0.5, 14.0)
        line   <- floor(exp_k) + 0.5
        p_over <- 1 - stats::pnbinom(floor(line), size = K_NB_SIZE, mu = exp_k)
        pick   <- if (p_over >= 0.5) "Over" else "Under"
        sp_side_key <- if (isTRUE(side$is_home)) "home" else "away"
        sp_actual   <- if (!is.null(sp_ks)) sp_ks[[sp_side_key]] else NULL
        result_str  <- "\u2014"; is_correct_k <- NA
        if (!is.null(sp_actual)) {
          actual_k <- sp_actual$k
          prop_hit <- if (pick == "Over") actual_k > line else actual_k < line
          result_str   <- if (prop_hit) paste0("\u2713 ", actual_k, " K") else paste0("\u2717 ", actual_k, " K")
          is_correct_k <- prop_hit
        }
        rows[[length(rows)+1L]] <- data.frame(
          GameID=g$GameID, PitcherID=as.integer(side$sp_id), Side=sp_side_key,
          Matchup=paste0(g$AwayTeam," @ ",g$HomeTeam), SP=sp_name, ExpK=round(exp_k,1),
          ExpKNum=round(exp_k,2), Line=line, POver=round(100*p_over), Pick=pick,
          Result=result_str, IsCorrect=is_correct_k, stringsAsFactors=FALSE)
      }
    }, error=function(e) NULL)
  }
  if (!length(rows)) return(data.frame())
  df <- bind_rows(rows); df[order(-df$ExpKNum), ]
}

# ===== SELF-MEASURING LEAGUE BASELINES =====
# Recomputes the league-average constants from the season-to-date data each run and
# updates them in place, so nothing here is a hardcoded guess. (Statcast-only metrics
# -- barrel%, exit velo, sprint speed, whiff% -- stay as fallbacks because USE_STATCAST
# is off and they aren't in these frames; they only matter if you turn Statcast on.)
refresh_league_baselines <- function(tbat_s, pitch_s, history = NULL, as_of_date = NULL) {
  # LEAKAGE FIX (v9): the ledger passed in here contains EVERY game the model has
  # ever graded, including games on/after the slate being predicted. Cut it to games
  # strictly BEFORE the slate date, and (v10) to regular-season/postseason rows only.
  if (!is.null(history) && !is.null(as_of_date) && "GameDate" %in% names(history)) {
    keep <- suppressWarnings(as.Date(history$GameDate) < as.Date(as_of_date))
    keep[is.na(keep)] <- FALSE
    keep <- keep & mlb_competitive_rows(history)
    history <- history[keep, , drop = FALSE]
    if (!nrow(history)) history <- NULL
  }
  numc <- function(df, col) if (!is.null(df) && col %in% names(df)) suppressWarnings(as.numeric(df[[col]])) else NA_real_
  tot  <- function(x) sum(x, na.rm = TRUE)
  if (!is.null(tbat_s) && nrow(tbat_s)) {
    PA <- numc(tbat_s, "PlateAppearances"); G <- numc(tbat_s, "Games")
    if (tot(PA) > 2000) {
      LG_AVG_K_PCT     <<- tot(numc(tbat_s,"KPct")  * PA) / tot(PA)    # = total K  / total PA
      LG_AVG_BB_PCT    <<- tot(numc(tbat_s,"BBPct") * PA) / tot(PA)    # = total BB / total PA
      LG_AVG_HR_PER_PA <<- tot(numc(tbat_s,"HomeRuns")) / tot(PA)
      LG_AVG_WOBA      <<- tot(numc(tbat_s,"wOBA")  * PA) / tot(PA)
      LG_AVG_XWOBA     <<- tot(numc(tbat_s,"xwOBA") * PA) / tot(PA)
      if (tot(G) > 0) LG_PA_PER_GAME <<- tot(PA) / tot(G)
    }
    if (tot(G) > 0) LG_AVG_SB_PER_G <<- tot(numc(tbat_s,"StolenBases")) / tot(G)
  }
  if (!is.null(pitch_s) && nrow(pitch_s)) {
    IP <- numc(pitch_s,"InningsPitched"); G <- numc(pitch_s,"Games")
    if (tot(IP) > 300) {
      hr <- tot(numc(pitch_s,"HomeRunsAllowed")); k <- tot(numc(pitch_s,"Strikeouts"))
      bb <- tot(numc(pitch_s,"Walks")) - tot(numc(pitch_s,"IntWalks")) + tot(numc(pitch_s,"HitByPitch"))
      ao <- tot(numc(pitch_s,"AirOuts"))
      LG_AVG_ERA      <<- 9 * tot(numc(pitch_s,"RunsAllowed")) / tot(IP)   # runs (not earned) per 9
      FIP_CONSTANT    <<- LG_AVG_ERA - (13*hr + 3*bb - 2*k) / tot(IP)      # FIP on the RA9 scale
      LG_AVG_FIP      <<- LG_AVG_ERA
      LG_K_PER_IP     <<- k / tot(IP)
      LG_BBHBP_PER_IP <<- bb / tot(IP)
      LG_HR_PER_IP    <<- hr / tot(IP)
      if (ao + hr > 0) LG_HR_PER_FBP <<- hr / (ao + hr)
    }
    if (tot(G) > 0) LG_AVG_RUNS_PER_GAME <<- tot(numc(pitch_s,"RunsAllowed")) / tot(G)
  }
  # Home-field edge is measured from the model's own resolved games, not assumed.
  if (!is.null(history) && "HomeWon" %in% names(history)) {
    hw <- suppressWarnings(as.numeric(history$HomeWon)); hw <- hw[!is.na(hw)]
    if (length(hw) >= 200) HOME_FIELD_EDGE <<- clamp(mean(hw) - 0.5, 0.0, 0.08)
  }
  invisible(TRUE)
}
LG_PA_PER_GAME <- 37.7

# ===== POINT-IN-TIME data assembly (cutoff = analysis date D) =====
prepare_data <- function(recent_games=15, date_str=NULL) {
  if (is.null(date_str)) date_str <- format(Sys.Date(), "%Y-%m-%d")
  D       <- as.Date(date_str)
  seasons <- resolve_seasons(D)
  pri <- seasons$primary; fb <- seasons$fallback
  prev_season <- as.character(as.integer(pri) - 1L)
  w   <- season_blend_weight(seasons$days_in)

  savant_bat <- if (USE_STATCAST) tryCatch(fetch_savant_batter_metrics(pri), error=function(e) NULL) else NULL
  savant_pit <- if (USE_STATCAST) tryCatch(fetch_savant_pitcher_metrics(pri), error=function(e) NULL) else NULL

  sched   <- fetch_mlb_schedule(date_str)
  # All current-season aggregates cut STRICTLY before D.
  pitch_cur <- build_pitching_df(pri, D)
  tbat_cur  <- build_team_batting_df(pri, D)
  # Last season in full (a finished season precedes D, so this is leak-free). It is
  # the run model's offensive prior all season and the league baseline in April.
  tbat_prev  <- tryCatch(build_team_batting_df(prev_season, D), error = function(e) data.frame())
  pitch_prev <- tryCatch(build_pitching_df(prev_season, D), error = function(e) data.frame())
  lg_prev_woba <- if (nrow(tbat_prev)) sum(tbat_prev$wOBA * tbat_prev$PlateAppearances) /
    sum(tbat_prev$PlateAppearances) else NA_real_
  # League averages are MEASURED point-in-time (current season once it has enough
  # games, last season before that), and BEFORE anything that depends on them.
  enough <- nrow(tbat_cur) && sum(tbat_cur$PlateAppearances, na.rm = TRUE) > 20000
  tryCatch(refresh_league_baselines(if (enough) tbat_cur else tbat_prev,
                                    if (enough) pitch_cur else pitch_prev,
                                    awm_load(), as_of_date = D), error = function(e) NULL)
  pitch_cur <- build_pitching_df(pri, D)          # rebuilt: FIP/xFIP/PenSkill use the fresh constants
  pitch_s <- pitch_cur
  pitch_r <- build_pitching_df(pri, D, last_n=recent_games)
  tbat_s  <- tbat_cur
  tbat_r  <- build_team_batting_df(pri, D, last_n=recent_games)
  pbat_s  <- build_player_batting_df(pri, D, savant_bat_df=savant_bat)
  pbat_r  <- build_player_batting_df(pri, D, last_n=recent_games, savant_bat_df=savant_bat)
  records <- build_records_from_pitching(pitch_s)

  if (!is.null(fb) && w < 1) {
    savant_bat_fb <- if (USE_STATCAST) tryCatch(fetch_savant_batter_metrics(fb), error=function(e) NULL) else NULL
    savant_pit_fb <- if (USE_STATCAST) tryCatch(fetch_savant_pitcher_metrics(fb), error=function(e) NULL) else NULL
    # Prior season fully precedes D, so cutoff=D keeps all of it (leak-free).
    pitch_s <- blend_season_df(pitch_s, build_pitching_df(fb, D), w)
    pitch_r <- blend_season_df(pitch_r, build_pitching_df(fb, D, last_n=recent_games), w)
    tbat_s  <- blend_season_df(tbat_s,  build_team_batting_df(fb, D), w)
    tbat_r  <- blend_season_df(tbat_r,  build_team_batting_df(fb, D, last_n=recent_games), w)
    if (nrow(pbat_s) == 0) pbat_s <- build_player_batting_df(fb, D, savant_bat_df=savant_bat_fb)
    if (nrow(pbat_r) == 0) pbat_r <- build_player_batting_df(fb, D, last_n=recent_games, savant_bat_df=savant_bat_fb)
    if (length(records) == 0) records <- build_records_from_pitching(build_pitching_df(fb, D))
    if (is.null(savant_pit)) savant_pit <- savant_pit_fb
  }

  pids  <- unique(na.omit(c(sched$HomePitcherID, sched$AwayPitcherID)))
  pdict <- fetch_all_pitcher_stats(pids, cutoff_date=D, season=pri, savant_pit_df=savant_pit)
  ratings_obj <- compute_team_ratings(pitch_s, tbat_s, records)

  list(schedule_df=sched,
       pitching_df=if(nrow(pitch_r)>0) pitch_r else pitch_s,
       pitching_df_season=pitch_cur, pitching_df_blend=pitch_s, recent_pitching_df=pitch_r,
       team_batting_df=tbat_s, recent_team_batting_df=tbat_r,
       team_batting_cur=tbat_cur, team_batting_prev=tbat_prev, lg_prev_woba=lg_prev_woba,
       player_batting_df=pbat_s, recent_player_batting_df=pbat_r,
       pitcher_stats_dict=pdict, team_ratings=ratings_obj, team_records=records,
       season_info=seasons, season=pri, savant_bat=savant_bat, savant_pit=savant_pit)
}

compute_accuracy_summary <- function(proj_df) {
  if (is.null(proj_df) || nrow(proj_df) == 0) return(NULL)
  finished <- proj_df[!is.na(proj_df$IsCorrect), , drop=FALSE]
  if (nrow(finished) == 0) return(NULL)
  total   <- nrow(finished); correct <- sum(finished$IsCorrect, na.rm=TRUE)
  brier <- NA_real_
  if (all(c("HomeWinProb", "HomeWon") %in% names(finished))) {
    p <- suppressWarnings(as.numeric(finished$HomeWinProb)) / 100
    y <- suppressWarnings(as.numeric(finished$HomeWon))
    ok <- is.finite(p) & is.finite(y)
    if (any(ok)) brier <- round(mean((p[ok] - y[ok])^2), 3)
  }
  list(total=total, correct=correct, pct=round(correct/total*100, 1), brier=brier)
}


# ==================== NFL / NCAAF ====================

CACHE_DIR    <- "nfl_cache"
CACHE_VER    <- 7
LEDGER_DIR   <- "nfl_ledger"
LEDGER_FILE  <- file.path(LEDGER_DIR, "predictions.rds")
MODEL_VER    <- "epa-pd-qb-v2"      # v2: adds the starting-QB-change term (see qb_change_flags)

LOAD_SEASONS <- 2014:2026
PICK_SEASONS <- 2019:2026

TZ_ET             <- "America/New_York"
FINAL_AFTER_H     <- 4
SCHED_REFRESH_MIN <- 60
PBP_REFRESH_MIN   <- 30
AVAIL_REFRESH_MIN <- 20
AVAIL_IDLE_MIN    <- 24 * 60
CFB_REFRESH_MIN   <- 30
POLL_MIN          <- 15
INJ_OUT           <- c("Out", "Doubtful")
FAR_FUTURE        <- as.POSIXct("2100-01-01", tz = "America/New_York")

TEAM_FIX <- c(STL = "LA", SD = "LAC", OAK = "LV", LAR = "LA", JAC = "JAX", WSH = "WAS")
fix_team <- function(x) { i <- !is.na(x) & x %in% names(TEAM_FIX); x[i] <- TEAM_FIX[x[i]]; x }

K_SHRINK     <- 900
PRIOR_W      <- 0.35
ADJ_PASSES   <- 1
FORM_G       <- 3
PD_FROM_WEEK <- 5
PD_K         <- 4
PD_PRIOR_W   <- 0.2

dir.create(CACHE_DIR, showWarnings = FALSE)
dir.create(LEDGER_DIR, showWarnings = FALSE)

now_et <- function() {
  x <- getOption("nfl.now")
  x <- if (is.null(x)) Sys.time() else as.POSIXct(x)
  attr(x, "tzone") <- TZ_ET
  x
}

# What day it is in the east -- which is not what as.Date() says.
#
# as.Date() on a time ignores its time zone and reads it in UTC, so from 8pm eastern
# onwards the plain conversion is already tomorrow. Every schedule here is dated
# eastern, so that one-line difference was enough to point the whole evening at the
# next day's slate: games that had just been played showed no winner, because the day
# on screen was a day that had not happened yet.
today_et <- function() as.Date(format(now_et(), "%Y-%m-%d"))

# the eastern day a moment falls on, for the same reason
day_et <- function(x) as.Date(format(x, "%Y-%m-%d"))

# ---- picks frozen when the game starts -------------------------------------------
#
# Baseball, pro football and college football each write their pick to a ledger the
# moment a game starts, and read it back for ever after, so the record on the page is
# the pick as it actually stood. Hockey and basketball computed theirs the same way --
# ratings from earlier dates only, calibration from earlier seasons only, so nothing
# ever leaked -- but never wrote them down, which meant every rebuild recomputed
# history. Nothing was wrong with it; it just was not nailed down. This gives the last
# two leagues the same memory as the rest, and all five now behave identically.

game_empty_ledger <- function() data.frame(
  game_id = character(0), season = integer(0),
  kickoff = as.POSIXct(character(0), tz = TZ_ET),
  rd = numeric(0), pred = numeric(0), conf = numeric(0),
  model_ver = character(0), locked_at = as.POSIXct(character(0), tz = TZ_ET),
  stringsAsFactors = FALSE)

game_read_ledger <- function(path) {
  if (!file.exists(path)) return(game_empty_ledger())
  L <- try(readRDS(path), silent = TRUE)
  if (inherits(L, "try-error") || !is.data.frame(L)) return(game_empty_ledger())
  L
}

# Append-only. A pick already on the ledger is never rewritten, by anything.
game_append_ledger <- function(path, new) {
  L <- game_read_ledger(path)
  new <- new[!new$game_id %in% L$game_id, , drop = FALSE]
  if (!nrow(new)) return(invisible(L))
  L <- dplyr::bind_rows(L, new)
  dir.create(dirname(path), recursive = TRUE, showWarnings = FALSE)
  tmp <- paste0(path, ".tmp")
  ok <- tryCatch({ saveRDS(L, tmp); file.rename(tmp, path) }, error = function(e) FALSE)
  if (!isTRUE(ok)) unlink(tmp)
  invisible(L)
}

# One row per game in g, in g's order: the frozen pick where there is one, otherwise a
# fresh pick computed with nothing later than pmin(start, now) -- and written to the
# ledger only once the game has actually started, so a pick can never be stored using
# anything that happened during or after the game it is predicting.
# Writes down what actually happened, once per game.
#
# The pick stays untouchable: pred, conf, kickoff, model_ver and locked_at are never
# rewritten, and a row that already carries a result is left alone. Without this the
# only trace of a settled pick was the day page it appeared on, and those age out after
# two weeks -- so a season's record quietly disappeared as the window moved.
game_grade_ledger <- function(path, game_id, home_score, away_score) {
  L <- game_read_ledger(path)
  if (!nrow(L) || !length(game_id) || !("pred" %in% names(L))) return(invisible(FALSE))
  for (cl in c("home_score", "away_score")) if (!(cl %in% names(L))) L[[cl]] <- NA_real_
  if (!("won" %in% names(L))) L$won <- NA
  if (!("settled_at" %in% names(L))) L$settled_at <- as.POSIXct(NA, tz = TZ_ET)
  r <- data.frame(gid = as.character(game_id),
                  hs = suppressWarnings(as.numeric(home_score)),
                  aw = suppressWarnings(as.numeric(away_score)),
                  stringsAsFactors = FALSE)
  r <- r[!is.na(r$hs) & !is.na(r$aw) & !duplicated(r$gid), , drop = FALSE]
  if (!nrow(r)) return(invisible(FALSE))
  j <- match(as.character(L$game_id), r$gid)
  need <- !is.na(j) & is.na(L$home_score)
  if (!any(need)) return(invisible(FALSE))
  hs <- r$hs[j[need]]; aw <- r$aw[j[need]]
  L$home_score[need] <- hs
  L$away_score[need] <- aw
  L$won[need]        <- ifelse(hs == aw, NA, (L$pred[need] > 0) == (hs > aw))
  L$settled_at[need] <- Sys.time()
  dir.create(dirname(path), recursive = TRUE, showWarnings = FALSE)
  tmp <- paste0(path, ".tmp")
  ok <- tryCatch({ saveRDS(L, tmp); file.rename(tmp, path) }, error = function(e) FALSE)
  if (!isTRUE(ok)) unlink(tmp)
  invisible(isTRUE(ok))
}

# Every settled game a league knows about, not just the slate on screen. A day page only
# covers a fortnight, so without this pass any pick older than the window would keep its
# result for ever unwritten.
game_grade_history <- function(path, sch) {
  if (is.null(sch) || !nrow(sch)) return(invisible(FALSE))
  ok <- sch$has_score %in% TRUE & !is.na(sch$home_score) & !is.na(sch$away_score)
  if (!("final_at" %in% names(sch))) ok <- ok & FALSE
  else ok <- ok & !is.na(sch$final_at) & sch$final_at <= now_et()
  i <- which(ok)
  if (!length(i)) return(invisible(FALSE))
  game_grade_ledger(path, sch$game_id[i], sch$home_score[i], sch$away_score[i])
}

# ---- player props: what was offered, and whether it happened --------------------
#
# Separate from the game ledgers because a prop is one player in one game, and because
# only settled rows are written. The probability a board shows is computed from games
# before kickoff and nothing else, so for a game that is over it is identical to what
# was on screen beforehand -- which means recording at settlement captures the pick as
# it stood without needing to write it twice.
#
# p_raw is the model's own number, before any recalibration. Calibrating on an already
# calibrated number would chase its own tail.
# A text ledger rather than a compressed one, deliberately. This grows by tens of
# thousands of rows a season and is committed as it does; git stores an appended text file
# as a small delta against the previous version, and a gzipped binary as a whole new blob
# every time. The other ledgers in this project are csv for the same reason.
PROP_LEDGER <- file.path(LEDGER_DIR, "player_props_graded.csv")
PROP_TFMT   <- "%Y-%m-%d %H:%M:%S"

prop_empty <- function() data.frame(
  league = character(0), market = character(0), game_id = character(0),
  pid = character(0), pname = character(0),
  kickoff = as.POSIXct(character(0), tz = TZ_ET),
  p_raw = numeric(0), hit = integer(0),
  model_ver = character(0), settled_at = as.POSIXct(character(0), tz = TZ_ET),
  stringsAsFactors = FALSE)

prop_read <- function(path = PROP_LEDGER) {
  if (!file.exists(path)) return(prop_empty())
  L <- try(utils::read.csv(path, stringsAsFactors = FALSE,
                           colClasses = c(game_id = "character", pid = "character")),
           silent = TRUE)
  if (inherits(L, "try-error") || !is.data.frame(L) || !nrow(L)) return(prop_empty())
  for (cl in c("kickoff", "settled_at"))
    if (cl %in% names(L))
      L[[cl]] <- as.POSIXct(as.character(L[[cl]]), format = PROP_TFMT, tz = TZ_ET)
  L
}

# Append-only, one row per player per game per market. A row already written is never
# revisited, so a later run cannot talk itself into a different answer.
prop_record <- function(league, market, game_id, pid, pname, kickoff, p_raw, hit,
                        model_ver = NA_character_, path = PROP_LEDGER) {
  n <- length(pid)
  if (!n) return(invisible(FALSE))
  keep <- !is.na(hit) & !is.na(p_raw) & !is.na(game_id) & !is.na(pid)
  if (!any(keep)) return(invisible(FALSE))
  new <- data.frame(
    league = as.character(league), market = as.character(market),
    game_id = as.character(game_id)[keep], pid = as.character(pid)[keep],
    pname = as.character(pname)[keep],
    kickoff = rep(as.POSIXct(NA, tz = TZ_ET), sum(keep)),
    p_raw = as.numeric(p_raw)[keep], hit = as.integer(hit)[keep],
    model_ver = as.character(model_ver), settled_at = Sys.time(),
    stringsAsFactors = FALSE)
  if (length(kickoff) == n) new$kickoff <- kickoff[keep]
  else if (length(kickoff) == 1L) new$kickoff <- rep(kickoff, sum(keep))
  L <- prop_read(path)
  k <- function(d) paste(d$league, d$market, d$game_id, d$pid)
  new <- new[!(k(new) %in% k(L)) & !duplicated(k(new)), , drop = FALSE]
  if (!nrow(new)) return(invisible(FALSE))
  L <- dplyr::bind_rows(L, new)
  L <- L[order(L$kickoff, L$league, L$market, L$game_id, L$pid), , drop = FALSE]
  W <- L
  for (cl in c("kickoff", "settled_at"))
    W[[cl]] <- format(W[[cl]], PROP_TFMT)
  dir.create(dirname(path), recursive = TRUE, showWarnings = FALSE)
  tmp <- paste0(path, ".tmp")
  ok <- tryCatch({
    utils::write.csv(W, tmp, row.names = FALSE, na = "")
    file.rename(tmp, path)
  }, error = function(e) FALSE)
  if (!isTRUE(ok)) unlink(tmp)
  invisible(isTRUE(ok))
}

PROP_CAL_MIN <- 300L   # graded props before a correction is trusted at all
PROP_CAL_HL  <- 60     # days of half-life, so this season's scoring environment counts most

# The correction a board's own record says it needs.
#
# Same shape as the baseball calibration already in this file: a logistic fit of what
# happened on what was said, weighted toward recent games, with an identity fallback. It
# is measured only on props that had already settled before the slate being built, so a
# week is never corrected using its own results.
prop_calib <- function(league, market, asof, min_n = PROP_CAL_MIN, half_life = PROP_CAL_HL) {
  ident <- list(ok = FALSE, a = 1, b = 0, n = 0L)
  if (is.null(asof) || !is.finite(as.numeric(asof))) return(ident)
  L <- prop_read()
  if (!nrow(L)) return(ident)
  h <- L[L$league == league & L$market == market &
         !is.na(L$hit) & !is.na(L$p_raw) & !is.na(L$kickoff) & L$kickoff < asof, , drop = FALSE]
  if (nrow(h) < min_n) return(ident)
  z <- stats::qlogis(clamp(h$p_raw, 0.002, 0.998))
  wts <- 0.5 ^ (as.numeric(difftime(asof, h$kickoff, units = "days")) / half_life)
  fit <- tryCatch(suppressWarnings(stats::glm(h$hit ~ z, family = stats::binomial(),
                                              weights = wts)), error = function(e) NULL)
  if (is.null(fit) || any(!is.finite(stats::coef(fit)))) return(ident)
  a <- unname(stats::coef(fit)[2]); b <- unname(stats::coef(fit)[1])
  # a negative slope would turn the board upside down: that is a broken fit, not a finding
  if (!is.finite(a) || a <= 0) return(ident)
  list(ok = TRUE, a = a, b = b, n = nrow(h))
}

prop_apply <- function(p, cal) {
  if (is.null(cal) || !isTRUE(cal$ok)) return(p)
  clamp(stats::plogis(cal$a * stats::qlogis(clamp(p, 0.002, 0.998)) + cal$b), 0.002, 0.95)
}

# every settled game on this slate, handed to the grader above
game_grade_slate <- function(path, g, done) {
  i <- which(done %in% TRUE)
  if (!length(i)) return(invisible(FALSE))
  game_grade_ledger(path, g$game_id[i], g$home_score[i], g$away_score[i])
}

game_settle <- function(path, model_ver, predict_fn, g, now) {
  if (!nrow(g)) return(NULL)
  L <- game_read_ledger(path)
  out <- list()
  Lg <- L[L$game_id %in% g$game_id, , drop = FALSE]
  if (nrow(Lg)) { Lg$locked <- TRUE; out[[1]] <- Lg }
  todo <- g[!g$game_id %in% Lg$game_id, , drop = FALSE]
  if (nrow(todo)) {
    cut <- as.POSIXct(pmin(as.numeric(todo$ko), as.numeric(now)),
                      origin = "1970-01-01", tz = TZ_ET)
    for (u in unique(as.numeric(cut))) {
      gi <- todo[as.numeric(cut) == u, , drop = FALSE]
      x <- predict_fn(gi, as.POSIXct(u, origin = "1970-01-01", tz = TZ_ET))
      if (is.null(x) || !nrow(x)) next
      x$kickoff   <- gi$ko[match(x$game_id, gi$game_id)]
      x$model_ver <- model_ver
      x$locked_at <- now
      x$locked    <- !is.na(x$kickoff) & now >= x$kickoff
      out[[length(out) + 1L]] <- x
      lk <- x[x$locked, , drop = FALSE]
      if (nrow(lk))
        game_append_ledger(path,
          lk[, intersect(names(game_empty_ledger()), names(lk)), drop = FALSE])
    }
  }
  if (!length(out)) return(NULL)
  r <- dplyr::bind_rows(out)
  r$locked[is.na(r$locked)] <- FALSE
  r[match(g$game_id, r$game_id), , drop = FALSE]
}

NICK <- c(ARI="Cardinals", ATL="Falcons", BAL="Ravens", BUF="Bills",
  CAR="Panthers", CHI="Bears", CIN="Bengals", CLE="Browns", DAL="Cowboys",
  DEN="Broncos", DET="Lions", GB="Packers", HOU="Texans", IND="Colts",
  JAX="Jaguars", JAC="Jaguars", KC="Chiefs", LA="Rams", LAR="Rams",
  LAC="Chargers", SD="Chargers", LV="Raiders", OAK="Raiders", MIA="Dolphins",
  MIN="Vikings", NE="Patriots", NO="Saints", NYG="Giants", NYJ="Jets",
  PHI="Eagles", PIT="Steelers", SEA="Seahawks", SF="49ers", STL="Rams",
  TB="Buccaneers", TEN="Titans", WAS="Commanders", WSH="Commanders")
FULL <- c(ARI="Arizona Cardinals", ATL="Atlanta Falcons", BAL="Baltimore Ravens",
  BUF="Buffalo Bills", CAR="Carolina Panthers", CHI="Chicago Bears",
  CIN="Cincinnati Bengals", CLE="Cleveland Browns", DAL="Dallas Cowboys",
  DEN="Denver Broncos", DET="Detroit Lions", GB="Green Bay Packers",
  HOU="Houston Texans", IND="Indianapolis Colts", JAX="Jacksonville Jaguars",
  JAC="Jacksonville Jaguars", KC="Kansas City Chiefs", LA="Los Angeles Rams",
  LAR="Los Angeles Rams", LAC="Los Angeles Chargers", SD="Los Angeles Chargers",
  LV="Las Vegas Raiders", OAK="Las Vegas Raiders", MIA="Miami Dolphins",
  MIN="Minnesota Vikings", NE="New England Patriots", NO="New Orleans Saints",
  NYG="New York Giants", NYJ="New York Jets", PHI="Philadelphia Eagles",
  PIT="Pittsburgh Steelers", SEA="Seattle Seahawks", SF="San Francisco 49ers",
  STL="Los Angeles Rams", TB="Tampa Bay Buccaneers", TEN="Tennessee Titans",
  WAS="Washington Commanders", WSH="Washington Commanders")
FALLBACK_COL <- c(ARI="#97233F", ATL="#A71930", BAL="#241773", BUF="#00338D",
  CAR="#0085CA", CHI="#0B162A", CIN="#FB4F14", CLE="#311D00", DAL="#041E42",
  DEN="#FB4F14", DET="#0076B6", GB="#203731", HOU="#03202F", IND="#002C5F",
  JAX="#006778", KC="#E31837", LA="#003594", LAC="#0080C6", LV="#101820",
  MIA="#008E97", MIN="#4F2683", NE="#002244", NO="#A08A58", NYG="#0B2265",
  NYJ="#125740", PHI="#004C54", PIT="#B8A400", SEA="#002244", SF="#AA0000",
  TB="#D50A0A", TEN="#0C2340", WAS="#5A1414")
nick <- function(x) ifelse(is.na(NICK[x]), x, NICK[x])
full <- function(x) ifelse(is.na(FULL[x]), x, FULL[x])

mix_white <- function(hex, p) {
  v <- grDevices::col2rgb(hex)[, 1]
  grDevices::rgb(v[1] + (255 - v[1]) * p, v[2] + (255 - v[2]) * p,
                 v[3] + (255 - v[3]) * p, maxColorValue = 255)
}
CONF_RAMP <- grDevices::colorRamp(c("#aab4c0", "#2c6fbb"))
conf_col <- function(p) {
  x <- pmin(pmax((p - 0.5) / 0.30, 0), 1)
  m <- CONF_RAMP(ifelse(is.na(x), 0, x))
  grDevices::rgb(m[, 1], m[, 2], m[, 3], maxColorValue = 255)
}

PBP_REQ <- c("game_id", "season", "week", "posteam", "defteam", "epa", "vegas_wp",
             "play_type", "success", "down", "yards_gained", "yardline_100",
             "sack", "interception", "fumble_lost", "qb_dropback",
             "passer_player_name")

PLR_REQ <- c("game_id", "season", "week", "posteam", "defteam", "play_type",
             "pass_attempt", "rush_attempt", "complete_pass", "air_yards",
             "yardline_100", "receiving_yards", "receiving_yards", "touchdown",
             "receiver_player_id", "receiver_player_name",
             "rusher_player_id", "rusher_player_name",
             "pass_touchdown", "rush_touchdown")
PLR_SEASONS  <- 2019:2026
PLR_MIN_OPP  <- 1.0
PLR_BLEND_G  <- 4
PLR_RECENT_WEEKS <- 3

pbp_file   <- function(y) file.path(CACHE_DIR, sprintf("pbp_v%d_%d.rds", CACHE_VER, y))
plr_file   <- function(y) file.path(CACHE_DIR, sprintf("plr_v%d_%d.rds", CACHE_VER, y))
ros_file   <- function()  file.path(CACHE_DIR, sprintf("ros_v%d.rds", CACHE_VER))
inj_file   <- function()  file.path(CACHE_DIR, sprintf("inj_v%d.rds", CACHE_VER))
pbp_miss   <- function(y) file.path(CACHE_DIR, sprintf("pbp_v%d_%d.miss", CACHE_VER, y))
sched_file <- function()  file.path(CACHE_DIR, sprintf("schedules_v%d.rds", CACHE_VER))
teams_file <- function()  file.path(CACHE_DIR, sprintf("teams_v%d.rds", CACHE_VER))
fit_file   <- function(s) file.path(CACHE_DIR, sprintf("fit_v%d_%s_%d.rds", CACHE_VER, MODEL_VER, s))
age_min    <- function(f) if (file.exists(f))
  as.numeric(difftime(Sys.time(), file.mtime(f), units = "mins")) else Inf

cleanup_old_caches <- function() {
  f <- list.files(CACHE_DIR, pattern = "^(pbp|plr|ros|schedules|fit|teams)_v[0-9]+_?", full.names = TRUE)
  v <- suppressWarnings(as.integer(sub("^(pbp|plr|ros|schedules|fit|teams)_v([0-9]+).*$", "\\2", basename(f))))
  old <- f[!is.na(v) & v != CACHE_VER]
  # model fits saved under an earlier model version are never read again (player fits
  # used to run ~50 MB apiece), so they go too instead of piling up in every deployment
  m <- list.files(CACHE_DIR, pattern = "^p?fit_v[0-9]+_.*[.]rds$", full.names = TRUE)
  b <- basename(m)
  cur <- ifelse(startsWith(b, "pfit_"),
                startsWith(b, sprintf("pfit_v%d_%s_%s_", CACHE_VER, MODEL_VER, PLR_VER)),
                startsWith(b, sprintf("fit_v%d_%s_", CACHE_VER, MODEL_VER)))
  old <- union(old, m[!cur])
  if (length(old)) unlink(old)
}

# A fitted lm/glm keeps its training data and, through its formula, the whole environment
# it was fitted in -- each saved player model came to ~50 MB on disk and over 150 MB in
# memory for every visitor who opened the NFL tab. Prediction needs only the
# coefficients, terms, family and pivot, so the rest is dropped (predictions unchanged).
slim_fit <- function(m) {
  if (!inherits(m, "lm")) return(m)
  for (k in c("fitted.values", "effects", "linear.predictors", "weights", "prior.weights",
              "y", "model", "data")) m[[k]] <- NULL
  m$qr$qr <- NULL
  attr(m$terms, ".Environment") <- globalenv()
  if (!is.null(m$formula)) environment(m$formula) <- globalenv()
  m
}
slim_fits <- function(m, parts) {
  for (p in intersect(parts, names(m))) {
    if (inherits(m[[p]], "lm")) m[[p]] <- slim_fit(m[[p]])
    else if (is.list(m[[p]])) m[[p]] <- lapply(m[[p]], slim_fit)
  }
  m$slim <- TRUE
  m
}

download_pbp_season <- function(y) {
  d <- try(nflreadr::load_pbp(y), silent = TRUE)
  if (inherits(d, "try-error") || is.null(d) || nrow(d) == 0) return(NULL)
  d <- as.data.frame(d)
  gone <- setdiff(c(PBP_REQ, "season_type"), names(d))
  if (length(gone))
    stop("nflreadr returned play-by-play without: ", paste(gone, collapse = ", "),
         ". Try install.packages('nflreadr').")
  d <- d[d$season_type == "REG" & d$play_type %in% c("pass", "run") &
           !is.na(d$posteam) & !is.na(d$defteam) & !is.na(d$epa), ]
  d$posteam <- fix_team(d$posteam); d$defteam <- fix_team(d$defteam)
  d[, PBP_REQ, drop = FALSE]
}

build_player_game <- function(d) {
  d <- d[d$play_type %in% c("pass", "run") & !is.na(d$posteam), ]
  d$posteam <- fix_team(d$posteam); d$defteam <- fix_team(d$defteam)
  d$rz <- as.integer(!is.na(d$yardline_100) & d$yardline_100 <= 20)
  d$i10 <- as.integer(!is.na(d$yardline_100) & d$yardline_100 <= 10)
  d$i5 <- as.integer(!is.na(d$yardline_100) & d$yardline_100 <= 5)
  z <- function(x) ifelse(is.na(x), 0, x)
  key <- c("game_id", "season", "week", "posteam", "defteam", "pid", "pname")

  r <- d[!is.na(d$receiver_player_id) & z(d$pass_attempt) == 1, ]
  rg <- if (nrow(r) == 0) NULL else {
    r$pid <- r$receiver_player_id; r$pname <- r$receiver_player_name
    r %>% group_by(across(all_of(key))) %>%
      summarise(tgt = dplyr::n(), rec = sum(z(complete_pass)),
                recyds = sum(z(receiving_yards)), ay = sum(z(air_yards)),
                rz_tgt = sum(rz), i10_tgt = sum(i10), i5_tgt = sum(i5),
                rec_td = sum(z(pass_touchdown)), .groups = "drop") %>% as.data.frame()
  }
  u <- d[!is.na(d$rusher_player_id) & z(d$rush_attempt) == 1, ]
  ug <- if (nrow(u) == 0) NULL else {
    u$pid <- u$rusher_player_id; u$pname <- u$rusher_player_name
    u %>% group_by(across(all_of(key))) %>%
      summarise(car = dplyr::n(), rz_car = sum(rz), i10_car = sum(i10),
                i5_car = sum(i5), rush_td = sum(z(rush_touchdown)), .groups = "drop") %>%
      as.data.frame()
  }
  if (is.null(rg) && is.null(ug)) return(NULL)
  p <- if (is.null(ug)) rg else if (is.null(rg)) ug else
    merge(rg, ug, by = key, all = TRUE)
  num <- setdiff(names(p), key)
  for (c in num) p[[c]] <- z(p[[c]])
  for (c in c("tgt","rec","recyds","ay","rz_tgt","i10_tgt","i5_tgt","rec_td",
              "car","rz_car","i10_car","i5_car","rush_td"))
    if (!c %in% names(p)) p[[c]] <- 0

  t <- d %>% group_by(game_id, posteam) %>%
    summarise(t_tgt = sum(z(pass_attempt)), t_car = sum(z(rush_attempt)),
              t_plays = dplyr::n(), t_rz = sum(rz), t_i5 = sum(i5),
              t_td = sum(z(touchdown)), .groups = "drop") %>% as.data.frame()
  p <- merge(p, t, by = c("game_id", "posteam"), all.x = TRUE)
  p$td <- as.integer((p$rec_td + p$rush_td) > 0)
  p$opp_n <- p$tgt + p$car
  p$touch <- p$rec + p$car
  p$rz_opp <- p$rz_tgt + p$rz_car
  p$i10_opp <- p$i10_tgt + p$i10_car
  p$i5_opp <- p$i5_tgt + p$i5_car
  p
}

download_player_season <- function(y) {
  d <- try(nflreadr::load_pbp(y), silent = TRUE)
  if (inherits(d, "try-error") || is.null(d) || nrow(d) == 0) return(NULL)
  d <- as.data.frame(d)
  if (!all(c("receiver_player_id", "rusher_player_id") %in% names(d))) return(NULL)
  d <- d[d$season_type == "REG", ]
  keep <- intersect(unique(PLR_REQ), names(d))
  build_player_game(d[, keep, drop = FALSE])
}

download_rosters <- function() {
  r <- try(nflreadr::load_rosters_weekly(PLR_SEASONS), silent = TRUE)
  if (inherits(r, "try-error") || is.null(r) || nrow(r) == 0) return(NULL)
  r <- as.data.frame(r)
  need <- c("season", "week", "team", "position", "gsis_id", "status")
  if (!all(need %in% names(r))) return(NULL)
  r <- r[!is.na(r$gsis_id) & r$gsis_id != "", need]
  r$team <- fix_team(r$team)
  r
}

download_injuries <- function() {
  r <- try(nflreadr::load_injuries(PLR_SEASONS), silent = TRUE)
  if (inherits(r, "try-error") || is.null(r) || nrow(r) == 0) return(NULL)
  r <- as.data.frame(r)
  need <- c("season", "week", "team", "gsis_id", "report_status")
  if (!all(need %in% names(r))) return(NULL)
  if ("season_type" %in% names(r)) {
    kt <- is.na(r$season_type) | r$season_type == "REG"
    r <- r[kt, , drop = FALSE]
  }
  if (!"practice_status" %in% names(r)) r$practice_status <- NA_character_
  r <- r[!is.na(r$gsis_id) & r$gsis_id != "", c(need, "practice_status")]
  r$team <- fix_team(r$team)
  r$report_status   <- trimws(as.character(r$report_status))
  r$practice_status <- trimws(as.character(r$practice_status))
  r <- r[!duplicated(paste(r$season, r$week, r$gsis_id)), ]
  r
}

download_sched <- function() {
  s <- as.data.frame(nflreadr::load_schedules())
  s <- s[s$game_type == "REG", ]
  s$home_team <- fix_team(s$home_team); s$away_team <- fix_team(s$away_team)
  s
}

add_kickoff <- function(s) {
  gt <- ifelse(is.na(s$gametime) | s$gametime == "", "13:00", s$gametime)
  s$ko <- as.POSIXct(paste(s$gameday, gt), tz = TZ_ET, format = "%Y-%m-%d %H:%M")
  s$final_at  <- s$ko + FINAL_AFTER_H * 3600
  s$has_score <- !is.na(s$home_score) & !is.na(s$away_score)
  s
}

team_palette <- function() {
  f <- teams_file()
  t <- if (file.exists(f)) try(readRDS(f), silent = TRUE) else NULL
  if (is.null(t) || inherits(t, "try-error")) {
    t <- try(as.data.frame(nflreadr::load_teams()), silent = TRUE)
    if (inherits(t, "try-error") || !is.data.frame(t)) t <- data.frame()
    try(saveRDS(t, f), silent = TRUE)
  }
  col <- FALLBACK_COL
  logo <- setNames(rep(NA_character_, length(col)), names(col))
  if (is.data.frame(t) && nrow(t) > 0 && all(c("team_abbr", "team_color") %in% names(t))) {
    ab <- fix_team(t$team_abbr)
    ok <- !is.na(ab) & !is.na(t$team_color) & t$team_color != ""
    col[ab[ok]] <- t$team_color[ok]
    if ("team_logo_espn" %in% names(t)) {
      lk <- !is.na(ab) & !is.na(t$team_logo_espn) & t$team_logo_espn != ""
      logo[ab[lk]] <- t$team_logo_espn[lk]
    }
  }
  list(col = col, logo = logo)
}

sync_data <- function(force = FALSE) {
  now <- now_et(); sf <- sched_file()
  if (force || age_min(sf) > SCHED_REFRESH_MIN) {
    s <- try(download_sched(), silent = TRUE)
    if (!inherits(s, "try-error") && is.data.frame(s) && nrow(s) > 0) saveRDS(s, sf)
  }
  if (!file.exists(sf)) stop("Could not load the NFL schedule. Check your connection.")
  sch <- add_kickoff(readRDS(sf))
  for (y in LOAD_SEASONS) {
    f <- pbp_file(y)
    active <- any(sch$season == y & abs(as.numeric(difftime(sch$ko, now, units = "days"))) <= 10,
                  na.rm = TRUE)
    if (file.exists(f)) {
      if (!active || (!force && age_min(f) < PBP_REFRESH_MIN)) next
      final_ids <- sch$game_id[sch$season == y & sch$has_score & sch$final_at <= now &
                                 sch$final_at >= now - 7 * 86400]
      if (!force && all(final_ids %in% unique(readRDS(f)$game_id))) next
    } else if (!force && age_min(pbp_miss(y)) < PBP_REFRESH_MIN) next
    p <- download_pbp_season(y)
    if (is.null(p)) { file.create(pbp_miss(y)); next }
    saveRDS(p, f)
    if (y %in% PLR_SEASONS) {
      q <- download_player_season(y)
      if (!is.null(q)) saveRDS(q, plr_file(y))
    }
  }
  for (y in PLR_SEASONS) {
    if (file.exists(plr_file(y)) || !file.exists(pbp_file(y))) next
    q <- download_player_season(y)
    if (!is.null(q)) saveRDS(q, plr_file(y))
  }
  soon <- any(!is.na(sch$ko) &
              abs(as.numeric(difftime(sch$ko, now, units = "days"))) <= 4, na.rm = TRUE)
  amin <- if (soon) AVAIL_REFRESH_MIN else AVAIL_IDLE_MIN
  rf <- ros_file()
  if (force || age_min(rf) > amin) {
    r <- download_rosters()
    if (!is.null(r)) saveRDS(r, rf)
  }
  qf <- inj_file()
  if (force || age_min(qf) > amin) {
    q <- download_injuries()
    if (!is.null(q)) saveRDS(q, qf)
  }
  files <- c(sf, rf, qf, vapply(LOAD_SEASONS, pbp_file, ""),
             vapply(PLR_SEASONS, plr_file, ""))
  files <- files[file.exists(files)]
  paste(files, as.numeric(file.mtime(files)), collapse = "|")
}

build_team_weeks <- function(p) {
  p <- p[!(!is.na(p$vegas_wp) & (p$vegas_wp > 0.90 | p$vegas_wp < 0.10)), ]
  p$is_pass <- as.integer(p$play_type == "pass")
  p$expl <- as.integer(ifelse(p$is_pass == 1, p$yards_gained >= 15, p$yards_gained >= 10))
  p$tov <- pmin(1, ifelse(is.na(p$interception), 0, p$interception) +
                   ifelse(is.na(p$fumble_lost), 0, p$fumble_lost))
  p$early <- p$down %in% c(1, 2)
  p$rz <- !is.na(p$yardline_100) & p$yardline_100 <= 20

  base <- function(key, pre) {
    d <- p; d$tm__ <- d[[key]]
    f <- d %>% group_by(season, week, tm__) %>%
      summarise(epa = mean(epa), n = dplyr::n(),
                sr = mean(success, na.rm = TRUE), expl = mean(expl, na.rm = TRUE),
                to = mean(tov, na.rm = TRUE), sack = mean(sack, na.rm = TRUE),
                .groups = "drop")
    addsub <- function(f, mask, nm) {
      dd <- d[which(mask), , drop = FALSE]
      if (nrow(dd) == 0) { f[[nm]] <- NA_real_; return(f) }
      r <- dd %>% group_by(season, week, tm__) %>%
        summarise(v__ = mean(epa), .groups = "drop")
      f <- left_join(f, r, by = c("season", "week", "tm__"))
      names(f)[names(f) == "v__"] <- nm; f
    }
    f <- addsub(f, d$is_pass == 1, "pepa"); f <- addsub(f, d$is_pass == 0, "repa")
    f <- addsub(f, d$early, "eepa");        f <- addsub(f, d$rz, "rzepa")
    names(f)[names(f) == "tm__"] <- "team"
    j <- !names(f) %in% c("season", "week", "team")
    names(f)[j] <- paste0(pre, names(f)[j]); as.data.frame(f)
  }
  off <- base("posteam", "o_"); def <- base("defteam", "d_")
  qb <- p %>%
    filter(qb_dropback == 1, !is.na(passer_player_name), !is.na(epa)) %>%
    group_by(season, week, team = posteam, qb = passer_player_name) %>%
    summarise(db = dplyr::n(), qepa = mean(epa), .groups = "drop") %>%
    group_by(season, week, team) %>%
    slice_max(db, n = 1, with_ties = FALSE) %>% ungroup() %>% as.data.frame()
  off %>% inner_join(def, by = c("season", "week", "team")) %>%
    left_join(qb, by = c("season", "week", "team")) %>% as.data.frame()
}

sched_long <- function(sch) {
  mk <- function(team, opp) data.frame(
    season = sch$season, week = sch$week, team = team, opp = opp, game_id = sch$game_id,
    ko = sch$ko, final_at = sch$final_at, has_score = sch$has_score, stringsAsFactors = FALSE)
  rbind(mk(sch$home_team, sch$away_team), mk(sch$away_team, sch$home_team))
}

build_pd_long <- function(sch) {
  g <- sch[sch$has_score, ]
  mk <- function(team, pdg) data.frame(season = g$season, week = g$week, team = team,
    pdg = pdg, final_at = g$final_at, stringsAsFactors = FALSE)
  rbind(mk(g$home_team, g$home_score - g$away_score),
        mk(g$away_team, g$away_score - g$home_score))
}

# Starting-QB change. nflverse lists each game's starting QB (and, for the coming
# week, the expected starter). A team whose QB differs from its previous game's
# starter is flagged. Walk-forward over 2017-2025 this was the single most useful
# addition to the EPA model: about 2.9 points of margin, Brier 0.2227 -> 0.2213.
qb_change_flags <- function(sch) {
  sch$h_qbchg <- 0L; sch$a_qbchg <- 0L
  if (!all(c("home_qb_id", "away_qb_id") %in% names(sch))) return(sch)
  L <- rbind(
    data.frame(i = seq_len(nrow(sch)), team = sch$home_team, ko = as.numeric(sch$ko),
               qb = as.character(sch$home_qb_id), side = "h", stringsAsFactors = FALSE),
    data.frame(i = seq_len(nrow(sch)), team = sch$away_team, ko = as.numeric(sch$ko),
               qb = as.character(sch$away_qb_id), side = "a", stringsAsFactors = FALSE))
  L <- L[order(L$team, L$ko), ]
  L$prev <- stats::ave(L$qb, L$team, FUN = function(v) c(NA_character_, utils::head(v, -1)))
  L$chg  <- as.integer(!is.na(L$qb) & L$qb != "" & !is.na(L$prev) & L$prev != "" & L$qb != L$prev)
  h <- L[L$side == "h", ]; a <- L[L$side == "a", ]
  sch$h_qbchg[h$i] <- h$chg; sch$a_qbchg[a$i] <- a$chg
  sch
}

load_all <- function() {
  sch <- qb_change_flags(add_kickoff(readRDS(sched_file())))
  pbp <- dplyr::bind_rows(lapply(LOAD_SEASONS, function(y) {
    f <- pbp_file(y); if (file.exists(f)) readRDS(f) else NULL
  }))
  if (nrow(pbp) == 0) stop("No play-by-play could be loaded. Check your connection.")
  tw <- build_team_weeks(pbp)
  tw <- dplyr::left_join(tw, sched_long(sch), by = c("season", "week", "team"))
  game_grade_history(LEDGER_FILE, sch)
  pal <- team_palette()
  plr <- dplyr::bind_rows(lapply(PLR_SEASONS, function(y) {
    f <- plr_file(y); if (file.exists(f)) readRDS(f) else NULL
  }))
  if (nrow(plr) > 0) {
    k <- sch[, c("game_id", "ko", "final_at", "has_score")]
    plr <- merge(plr, k, by = "game_id", all.x = TRUE)
    plr <- plr[!is.na(plr$ko), ]
    plr <- tryCatch(plr_add_qb_starts(plr, sch), error = function(e) plr)
    plr <- plr[order(plr$pid, plr$ko), ]
  }
  rf <- ros_file()
  ros <- if (file.exists(rf)) readRDS(rf) else NULL
  qf <- inj_file()
  inj <- if (file.exists(qf)) readRDS(qf) else NULL
  list(sch = sch, tw = tw, pdl = build_pd_long(sch), pbp_ids = unique(pbp$game_id),
       teams = sort(unique(c(sch$home_team, sch$away_team))),
       col = pal$col, logo = pal$logo, plr = plr, ros = ros, inj = inj,
       pos = player_positions(ros))
}

player_positions <- function(ros) {
  if (is.null(ros) || nrow(ros) == 0) return(character(0))
  r <- ros[!is.na(ros$position) & ros$position != "", ]
  if (nrow(r) == 0) return(character(0))
  m <- tapply(r$position, r$gsis_id, function(x) names(sort(table(x), decreasing = TRUE))[1])
  v <- as.character(m); names(v) <- names(m)
  v[v %in% c("FB")] <- "RB"
  v
}

# The player table is built from carries and targets, so a starting quarterback who never
# ran or caught the ball has no row for that game (about one start in six). Left that way
# the touchdown model would see only a QB's games with a carry and overrate pocket
# passers, so each such start is added as a game with no touches and no touchdown.
plr_add_qb_starts <- function(plr, sch) {
  if (!all(c("home_qb_id", "away_qb_id") %in% names(sch))) return(plr)
  g <- sch[sch$has_score %in% TRUE & sch$game_id %in% plr$game_id, , drop = FALSE]
  if (nrow(g) == 0) return(plr)
  qn <- function(v) if (v %in% names(g)) as.character(g[[v]]) else rep(NA_character_, nrow(g))
  S <- rbind(
    data.frame(game_id = g$game_id, posteam = g$home_team, pid = as.character(g$home_qb_id),
               nm = qn("home_qb_name"), stringsAsFactors = FALSE),
    data.frame(game_id = g$game_id, posteam = g$away_team, pid = as.character(g$away_qb_id),
               nm = qn("away_qb_name"), stringsAsFactors = FALSE))
  S <- S[!is.na(S$pid) & S$pid != "", , drop = FALSE]
  S <- S[!paste(S$game_id, S$pid) %in% paste(plr$game_id, plr$pid), , drop = FALSE]
  tm <- plr[!duplicated(plr[, c("game_id", "posteam")]), , drop = FALSE]
  j <- match(paste(S$game_id, S$posteam), paste(tm$game_id, tm$posteam))
  S <- S[!is.na(j), , drop = FALSE]; j <- j[!is.na(j)]
  if (nrow(S) == 0) return(plr)
  z <- tm[j, , drop = FALSE]
  game <- c("game_id", "season", "week", "posteam", "defteam", "ko", "final_at", "has_score")
  for (c in setdiff(names(z), c(game, grep("^t_", names(z), value = TRUE))))
    if (is.numeric(z[[c]])) z[[c]][] <- 0L
  z$pid <- S$pid
  last <- plr[!duplicated(plr$pid, fromLast = TRUE), c("pid", "pname")]
  nm <- last$pname[match(S$pid, last$pid)]
  z$pname <- ifelse(is.na(nm), ifelse(is.na(S$nm), S$pid, sub("^(\\S)\\S*\\s+", "\\1.", S$nm, perl = TRUE)), nm)
  rbind(plr, z[, names(plr), drop = FALSE])
}

# Each team's starting quarterback for the given games: the one nflverse lists for that
# game (the expected starter beforehand, the actual one afterwards), else the team's most
# recently listed starter.
qb_starters <- function(sch, gids) {
  if (!all(c("home_qb_id", "away_qb_id") %in% names(sch))) return(NULL)
  L <- rbind(
    data.frame(game_id = sch$game_id, team = sch$home_team, ko = as.numeric(sch$ko),
               qb = as.character(sch$home_qb_id), stringsAsFactors = FALSE),
    data.frame(game_id = sch$game_id, team = sch$away_team, ko = as.numeric(sch$ko),
               qb = as.character(sch$away_qb_id), stringsAsFactors = FALSE))
  L$qb[!is.na(L$qb) & L$qb == ""] <- NA_character_
  W <- L[L$game_id %in% gids, , drop = FALSE]
  K <- L[!is.na(L$qb) & !is.na(L$ko), , drop = FALSE]
  K <- K[order(K$ko), , drop = FALSE]
  for (i in which(is.na(W$qb) & !is.na(W$ko))) {
    k <- which(K$team == W$team[i] & K$ko <= W$ko[i])
    if (length(k)) W$qb[i] <- K$qb[k[length(k)]]
  }
  W
}

# Marks each team's starting QB (qb_start) and drops its other quarterbacks: a backup's
# chance "if he plays" is no use for a bet, since he usually doesn't.
keep_qb_starter <- function(x, sch) {
  x$qb_start <- rep(FALSE, nrow(x))
  if (nrow(x) == 0 || !any(x$pos == "QB")) return(x)
  qs <- qb_starters(sch, unique(x$game_id))
  if (is.null(qs)) return(x)
  st <- qs$qb[match(paste(x$game_id, x$team_now), paste(qs$game_id, qs$team))]
  x$qb_start <- x$pos == "QB" & !is.na(st) & x$pid == st
  x[x$pos != "QB" | is.na(st) | x$qb_start, , drop = FALSE]
}

wmean_by <- function(idx, x, w, nt) {
  num <- rep(0, nt); den <- rep(0, nt)
  sn <- tapply(x * w, idx, sum); sd_ <- tapply(w, idx, sum)
  num[as.integer(names(sn))]  <- as.numeric(sn)
  den[as.integer(names(sd_))] <- as.numeric(sd_)
  ifelse(den > 0, num / den, 0)
}
wsum_by <- function(idx, w, nt) {
  out <- rep(0, nt); s <- tapply(w, idx, sum)
  out[as.integer(names(s))] <- as.numeric(s); out
}

finished_by <- function(df, season_, cutoff)
  which(df$season == season_ & (df$has_score %in% TRUE) &
          !is.na(df$final_at) & df$final_at <= cutoff)

rate_teams <- function(tw, season_, cutoff, teams,
                       k = K_SHRINK, carry = NULL, prior_w = PRIOR_W,
                       iters = ADJ_PASSES) {
  nt <- length(teams)
  zero <- setNames(rep(0, nt), teams)
  h <- tw[finished_by(tw, season_, cutoff), ]
  h <- h[!is.na(h$opp), ]
  if (nrow(h) == 0) return(if (is.null(carry)) zero else carry)
  ti <- match(h$team, teams); oi <- match(h$opp, teams)
  ok <- !is.na(ti) & !is.na(oi) & !is.na(h$o_epa) & !is.na(h$d_epa)
  h <- h[ok, ]; ti <- ti[ok]; oi <- oi[ok]
  if (nrow(h) == 0) return(if (is.null(carry)) zero else carry)
  off <- rep(0, nt); dff <- rep(0, nt)
  for (i in seq_len(iters)) {
    no <- wmean_by(ti, h$o_epa - dff[oi], h$o_n, nt)
    nd <- wmean_by(ti, h$d_epa - off[oi], h$d_n, nt)
    off <- no - mean(no); dff <- nd - mean(nd)
  }
  n <- wsum_by(ti, h$o_n, nt) + wsum_by(ti, h$d_n, nt)
  r <- (off - dff) * (n / (n + k))
  if (!is.null(carry)) {
    r <- (1 - prior_w) * r + prior_w * carry
    unplayed <- setdiff(teams, unique(h$team))
    if (length(unplayed)) { j <- match(unplayed, teams); r[j] <- carry[j] }
  }
  setNames(r, teams)
}

pd_rating <- function(pdl, season_, cutoff, teams, k = PD_K, prior_w = PD_PRIOR_W) {
  prev <- pdl[pdl$season == season_ - 1, ]
  cur  <- pdl[which(pdl$season == season_ & pdl$final_at <= cutoff), ]
  pm <- if (nrow(prev)) tapply(prev$pdg, prev$team, mean) else numeric(0)
  cm <- if (nrow(cur))  tapply(cur$pdg,  cur$team,  mean) else numeric(0)
  cn <- if (nrow(cur))  tapply(cur$pdg,  cur$team,  length) else numeric(0)
  out <- setNames(numeric(length(teams)), teams)
  for (t in teams) {
    p <- if (t %in% names(pm)) as.numeric(pm[[t]]) else 0
    if (t %in% names(cm)) {
      n <- as.numeric(cn[[t]])
      out[[t]] <- (1 - prior_w) * as.numeric(cm[[t]]) * (n / (n + k)) + prior_w * p
    } else out[[t]] <- p
  }
  out
}

pd_to_date <- function(pdl, season_, cutoff, team) {
  d <- pdl[which(pdl$season == season_ & pdl$final_at <= cutoff & pdl$team == team), ]
  if (nrow(d) == 0) return(c(NA_real_, 0))
  c(mean(d$pdg), nrow(d))
}

FORM_METS <- c("o_epa","o_pepa","o_repa","o_eepa","o_rzepa","o_sr","o_expl","o_to","o_sack",
               "d_epa","d_pepa","d_repa","d_eepa","d_rzepa","d_sr","d_expl","d_to","d_sack",
               "qepa")

team_form <- function(tw, season_, cutoff, teams) {
  wcol <- function(m) if (startsWith(m, "d_")) "d_n" else "o_n"
  cur  <- tw[finished_by(tw, season_, cutoff), ]
  prio <- tw[tw$season == season_ - 1, ]
  agg <- function(df) {
    if (is.null(df) || nrow(df) == 0) return(NULL)
    out <- data.frame(team = sort(unique(df$team)), stringsAsFactors = FALSE)
    for (m in FORM_METS) {
      if (!m %in% names(df)) { out[[m]] <- NA_real_; next }
      x <- df[[m]]; w <- df[[wcol(m)]]
      keep <- !is.na(x) & !is.na(w) & w > 0
      if (!any(keep)) { out[[m]] <- NA_real_; next }
      num <- tapply((x * w)[keep], df$team[keep], sum)
      den <- tapply(w[keep], df$team[keep], sum)
      v <- setNames(rep(NA_real_, nrow(out)), out$team)
      common <- intersect(names(num), out$team)
      if (length(common)) v[common] <- as.numeric(num[common]) / as.numeric(den[common])
      out[[m]] <- as.numeric(v[out$team])
    }
    tab <- table(df$team)
    out$games <- as.numeric(tab[out$team]); out$games[is.na(out$games)] <- 0
    out
  }
  A <- agg(cur); B <- agg(prio)
  nres <- length(teams)
  res <- data.frame(team = teams, stringsAsFactors = FALSE)
  ia <- if (!is.null(A)) match(res$team, A$team) else rep(NA_integer_, nres)
  ib <- if (!is.null(B)) match(res$team, B$team) else rep(NA_integer_, nres)
  gp <- if (!is.null(A)) ifelse(is.na(ia), 0, A$games[ia]) else rep(0, nres)
  gp[is.na(gp)] <- 0; res$games <- gp
  w <- gp / (gp + FORM_G)
  for (m in FORM_METS) {
    a <- if (!is.null(A) && m %in% names(A)) A[[m]][ia] else rep(NA_real_, nres)
    b <- if (!is.null(B) && m %in% names(B)) B[[m]][ib] else rep(NA_real_, nres)
    a <- as.numeric(a); b <- as.numeric(b)
    fa <- ifelse(is.na(a), b, a); fb <- ifelse(is.na(b), a, b)
    res[[m]] <- ifelse(is.na(fa) & is.na(fb), NA_real_,
                       w * ifelse(is.na(fa), 0, fa) + (1 - w) * ifelse(is.na(fb), 0, fb))
  }
  cols <- c("season", "week", "team", "qb")
  qsrc <- rbind(
    if (nrow(cur)  > 0 && all(cols %in% names(cur)))  cur[, cols]  else NULL,
    if (nrow(prio) > 0 && all(cols %in% names(prio))) prio[, cols] else NULL)
  if (!is.null(qsrc) && nrow(qsrc) > 0) {
    qsrc <- qsrc[!is.na(qsrc$qb), ]
    qsrc <- qsrc[order(qsrc$season, qsrc$week, decreasing = TRUE), ]
    res$qb <- qsrc$qb[match(res$team, qsrc$team)]
  } else res$qb <- NA_character_
  res
}

rank_desc <- function(x) rank(-x, na.last = "keep", ties.method = "min")
rank_asc  <- function(x) rank( x, na.last = "keep", ties.method = "min")
ord <- function(i) {
  if (length(i) == 0 || is.na(i)) return("")
  i <- as.integer(i)
  if (i %% 100 %in% 11:13) return(paste0(i, "th"))
  paste0(i, c("th","st","nd","rd","th","th","th","th","th","th")[(i %% 10) + 1])
}
fmt <- function(x, d = 3)
  if (length(x) == 0 || is.na(x)) "\u2014" else sprintf(paste0("%+.", d, "f"), x)
pct <- function(x)
  if (length(x) == 0 || is.na(x)) "\u2014" else sprintf("%.1f%%", 100 * x)
num0 <- function(x) if (length(x) == 0 || is.na(x)) 0L else as.integer(round(x))
chr  <- function(x) if (length(x) == 0 || is.na(x)) "\u2014" else as.character(x)

inclusion_groups <- function(tw, pdl, s, cutoffs) {
  fa <- sort(unique(as.numeric(c(tw$final_at[finished_by(tw, s, FAR_FUTURE)],
                                 pdl$final_at[pdl$season == s]))))
  findInterval(as.numeric(cutoffs), fa)
}

fit_history <- function(tw, sch, pdl, teams, season_) {
  cf <- fit_file(season_)
  if (file.exists(cf)) {
    m <- try(readRDS(cf), silent = TRUE)
    if (!inherits(m, "try-error") && is.list(m) && !is.null(m$f_early)) {
      if (!isTRUE(m$slim)) { m <- slim_fits(m, c("f_early", "f_late", "cal")); try(saveRDS(m, cf), silent = TRUE) }
      return(m)
    }
  }
  hist <- sort(unique(sch$season[sch$season < season_ & sch$has_score]))
  hist <- hist[hist > min(tw$season)]
  if (length(hist) == 0) return(NULL)
  rows <- list()
  for (s in hist) {
    prev <- rate_teams(tw, s - 1, FAR_FUTURE, teams, carry = NULL)
    gs <- sch[sch$season == s & sch$has_score, ]
    grp <- inclusion_groups(tw, pdl, s, gs$ko)
    for (k in unique(grp)) {
      ix <- which(grp == k); cut <- gs$ko[ix[1]]
      R <- rate_teams(tw, s, cut, teams, carry = prev)
      P <- pd_rating(pdl, s, cut, teams)
      g <- gs[ix, ]
      rows[[length(rows) + 1]] <- data.frame(
        week   = g$week,
        diff   = as.numeric(R[g$home_team]) - as.numeric(R[g$away_team]),
        pdd    = as.numeric(P[g$home_team]) - as.numeric(P[g$away_team]),
        qbd    = as.numeric(g$a_qbchg %||% 0) - as.numeric(g$h_qbchg %||% 0),
        margin = g$home_score - g$away_score, stringsAsFactors = FALSE)
    }
  }
  d <- dplyr::bind_rows(rows)
  d <- d[!is.na(d$diff) & !is.na(d$pdd) & !is.na(d$margin), ]
  if (nrow(d) < 100) return(NULL)
  if (!"qbd" %in% names(d)) d$qbd <- 0
  d$qbd[is.na(d$qbd)] <- 0
  f_early <- lm(margin ~ diff + qbd, data = d)
  dl <- d[d$week >= PD_FROM_WEEK, ]
  f_late <- if (nrow(dl) >= 100) lm(margin ~ diff + pdd + qbd, data = dl) else NULL
  d$pred <- project(list(f_early = f_early, f_late = f_late), d$week, d$diff, d$pdd, d$qbd)
  d <- d[d$margin != 0, ]
  d$hit <- as.integer((d$pred > 0) == (d$margin > 0))
  d$am  <- abs(d$pred)
  cal <- glm(hit ~ am, data = d, family = binomial())
  m <- slim_fits(list(f_early = f_early, f_late = f_late, cal = cal, hist = d, seasons = hist),
                 c("f_early", "f_late", "cal"))
  try(saveRDS(m, cf), silent = TRUE)
  m
}

project <- function(m, week, ediff, pdd, qbd = 0) {
  nd <- data.frame(diff = as.numeric(ediff), pdd = as.numeric(pdd),
                   qbd = rep_len(as.numeric(qbd), length(ediff)))
  nd$qbd[is.na(nd$qbd)] <- 0
  out <- as.numeric(predict(m$f_early, newdata = nd))
  if (!is.null(m$f_late) && nrow(nd) > 0) {
    late <- rep_len(week >= PD_FROM_WEEK, nrow(nd))
    if (any(late))
      out[late] <- as.numeric(predict(m$f_late, newdata = nd[late, , drop = FALSE]))
  }
  out
}

conf_of <- function(m, pred) {
  p <- try(as.numeric(predict(m$cal, newdata = data.frame(am = abs(pred)),
                              type = "response")), silent = TRUE)
  if (inherits(p, "try-error")) return(rep(NA_real_, length(pred)))
  pmin(pmax(p, 0.5), 0.95)
}

PLR_SEA <- c("opp_n","touch","rz_opp","i10_opp","i5_opp","td","recyds","tgt","car","ay",
             "tgt_sh","car_sh","rz_sh","i5_sh")

plr_derive <- function(p) {
  sf <- function(a, b) ifelse(is.na(b) | b == 0, NA_real_, a / b)
  p$tgt_sh <- sf(p$tgt, p$t_tgt); p$car_sh <- sf(p$car, p$t_car)
  p$rz_sh  <- sf(p$rz_opp, p$t_rz); p$i5_sh <- sf(p$i5_opp, p$t_i5)
  p
}

plr_history <- function(plr, pos, cutoff) {
  if (is.null(plr) || nrow(plr) == 0) return(NULL)
  h <- plr[!is.na(plr$final_at) & plr$final_at <= cutoff & (plr$has_score %in% TRUE), ]
  if (nrow(h) == 0) return(NULL)
  h <- plr_derive(h)
  h$pos <- ifelse(is.na(pos[h$pid]), "OTH", pos[h$pid])
  h[order(h$pid, h$ko), ]
}

.PLR_MEMO <- new.env(parent = emptyenv())

memo_states <- function(h, cutoff) {
  k <- paste0("s", as.numeric(cutoff), "_", nrow(h))
  if (!is.null(.PLR_MEMO[[k]])) return(.PLR_MEMO[[k]])
  v <- plr_week_states(h, unique(h$season))
  if (length(ls(.PLR_MEMO)) > 8) rm(list = ls(.PLR_MEMO), envir = .PLR_MEMO)
  assign(k, v, envir = .PLR_MEMO)
  v
}

memo_history <- function(plr, pos, cutoff) {
  k <- paste0("h", as.numeric(cutoff))
  if (!is.null(.PLR_MEMO[[k]])) return(.PLR_MEMO[[k]])
  v <- plr_history(plr, pos, cutoff)
  assign(k, v, envir = .PLR_MEMO)
  v
}

plr_week_states <- function(h, seasons) {
  h <- h[order(h$pid, h$season, h$week), ]
  key <- paste(h$pid, h$season)
  n_after <- stats::ave(rep(1, nrow(h)), key, FUN = cumsum)
  st <- data.frame(pid = h$pid, season = h$season,
                   valid_from = h$week + 1L, gp_season = n_after,
                   pos = h$pos, pname = h$pname, team_last = h$posteam,
                   stringsAsFactors = FALSE)
  for (c in PLR_SEA) {
    v <- ifelse(is.na(h[[c]]), 0, h[[c]])
    st[[paste0("cur_", c)]] <- stats::ave(v, key, FUN = cumsum) / n_after
  }
  ids <- unique(paste(h$pid, h$season))
  init <- data.frame(pid = sub(" .*$", "", ids), season = as.integer(sub("^.* ", "", ids)),
                     valid_from = 1L, gp_season = 0, stringsAsFactors = FALSE)
  init$pos <- h$pos[match(paste(init$pid, init$season), key)]
  init$pname <- h$pname[match(paste(init$pid, init$season), key)]
  init$team_last <- h$posteam[match(paste(init$pid, init$season), key)]
  for (c in PLR_SEA) init[[paste0("cur_", c)]] <- NA_real_
  st <- rbind(init[, names(st)], st)

  ps <- h %>% group_by(pid, season) %>%
    summarise(across(all_of(PLR_SEA), ~mean(.x, na.rm = TRUE)),
              .groups = "drop") %>% as.data.frame()
  ps$season <- ps$season + 1
  names(ps)[names(ps) %in% PLR_SEA] <- paste0("pri_", PLR_SEA)
  carry_ids <- setdiff(unique(paste(ps$pid, ps$season)), unique(paste(st$pid, st$season)))
  if (length(carry_ids)) {
    ext <- data.frame(pid = sub(" .*$", "", carry_ids),
                      season = as.integer(sub("^.* ", "", carry_ids)),
                      valid_from = 1L, gp_season = 0, stringsAsFactors = FALSE)
    lastseen <- h[!duplicated(h$pid, fromLast = TRUE), ]
    j <- match(ext$pid, lastseen$pid)
    ext$pos <- lastseen$pos[j]; ext$pname <- lastseen$pname[j]
    ext$team_last <- lastseen$posteam[j]
    for (c in PLR_SEA) ext[[paste0("cur_", c)]] <- NA_real_
    st <- rbind(st, ext[, names(st)])
  }
  grid <- expand.grid(week = 1:22, ids = unique(paste(st$pid, st$season)),
                      stringsAsFactors = FALSE)
  grid$pid <- sub(" .*$", "", grid$ids)
  grid$season <- as.integer(sub("^.* ", "", grid$ids))
  grid$ids <- NULL
  st <- st[order(st$pid, st$season, st$valid_from), ]
  g <- merge(grid, st, by.x = c("pid", "season", "week"),
             by.y = c("pid", "season", "valid_from"), all.x = TRUE)
  g <- g[order(g$pid, g$season, g$week), ]
  k2 <- paste(g$pid, g$season)
  carry <- c("gp_season", "pos", "pname", "team_last", paste0("cur_", PLR_SEA))
  for (c in carry) {
    g[[c]] <- unlist(lapply(split(g[[c]], k2), function(z) {
      good <- which(!is.na(z))
      if (!length(good)) return(z)
      idx <- cummax(ifelse(seq_along(z) %in% good, seq_along(z), 0L))
      z[ifelse(idx == 0, NA_integer_, idx)]
    }), use.names = FALSE)
  }
  g <- merge(g, ps, by = c("pid", "season"), all.x = TRUE)
  g$pos[is.na(g$pos)] <- "OTH"
  g$gp_season[is.na(g$gp_season)] <- 0
  pm <- lapply(PLR_SEA, function(c) tapply(h[[c]], h$pos, function(x) mean(x, na.rm = TRUE)))
  names(pm) <- PLR_SEA
  w <- g$gp_season / (g$gp_season + PLR_BLEND_G)
  for (c in PLR_SEA) {
    a <- g[[paste0("cur_", c)]]; b <- g[[paste0("pri_", c)]]
    pmv <- as.numeric(pm[[c]][g$pos]); pmv[is.na(pmv)] <- 0
    b <- ifelse(is.na(b), pmv, b); a <- ifelse(is.na(a), b, a)
    g[[paste0("f_", c)]] <- ifelse(g$gp_season > 0, w * a + (1 - w) * b, b)
  }
  g[, c("pid", "season", "week", "pos", "pname", "team_last", "gp_season",
        grep("^f_", names(g), value = TRUE))]
}

plr_features <- function(h, season_, week_ = NULL, cutoff = NULL) {
  st <- if (is.null(cutoff)) plr_week_states(h, unique(h$season)) else memo_states(h, cutoff)
  wk <- week_
  if (is.null(wk)) {
    seen <- h$week[h$season == season_ & !is.na(h$week)]
    wk <- if (length(seen)) max(seen) + 1 else 1
  }
  if (!is.finite(wk)) wk <- 1
  o <- st[st$season == season_ & st$week == wk, ]
  if (nrow(o) == 0) {
    o <- st[st$season == season_, ]
    o <- o[o$week == max(o$week), ]
  }
  o
}

plr_team_ctx <- function(h, season_) {
  tg <- h[!duplicated(h[, c("game_id", "posteam")]), ]
  cur <- tg[tg$season == season_, ]; pri <- tg[tg$season == season_ - 1, ]
  cols <- c("t_tgt", "t_car", "t_rz", "t_i5", "t_plays", "t_td")
  agg <- function(df) {
    if (nrow(df) == 0) return(NULL)
    o <- data.frame(team = sort(unique(df$posteam)), stringsAsFactors = FALSE)
    for (c in cols) o[[c]] <- as.numeric(tapply(df[[c]], df$posteam, mean)[o$team])
    o$gp <- as.numeric(table(df$posteam)[o$team]); o
  }
  A <- agg(cur); B <- agg(pri)
  teams <- sort(unique(tg$posteam))
  o <- data.frame(team = teams, stringsAsFactors = FALSE)
  ia <- if (is.null(A)) rep(NA_integer_, length(teams)) else match(teams, A$team)
  ib <- if (is.null(B)) rep(NA_integer_, length(teams)) else match(teams, B$team)
  gp <- if (is.null(A)) rep(0, length(teams)) else ifelse(is.na(ia), 0, A$gp[ia])
  gp[is.na(gp)] <- 0
  w <- gp / (gp + 3)
  for (c in cols) {
    a <- if (is.null(A)) rep(NA_real_, length(teams)) else as.numeric(A[[c]][ia])
    b <- if (is.null(B)) rep(NA_real_, length(teams)) else as.numeric(B[[c]][ib])
    lg <- mean(tg[[c]], na.rm = TRUE)
    b <- ifelse(is.na(b), lg, b); a <- ifelse(is.na(a), b, a)
    o[[paste0("off_", c)]] <- ifelse(gp > 0, w * a + (1 - w) * b, b)
  }
  o
}

plr_design <- function(d) {
  d$is_QB <- as.integer(d$pos == "QB")
  d$is_RB <- as.integer(d$pos == "RB")
  d$is_TE <- as.integer(d$pos == "TE")
  nz <- function(x, alt) ifelse(is.na(x) | !is.finite(x), alt, x)
  d$exp_tgt <- nz(d$f_tgt_sh * d$off_t_tgt, d$f_tgt)
  d$exp_car <- nz(d$f_car_sh * d$off_t_car, d$f_car)
  d$exp_i5  <- nz(d$f_i5_sh * d$off_t_i5, d$f_i5_opp)
  d$exp_rz  <- nz(d$f_rz_sh * d$off_t_rz, d$f_rz_opp)
  d$f_ypt   <- nz(d$f_recyds / d$f_tgt, 8)
  d$f_adot  <- nz(d$f_ay / d$f_tgt, 8)
  d$proj    <- d$exp_tgt * d$f_ypt
  d$qb_car  <- d$is_QB * d$exp_car
  d$qb_i5   <- d$is_QB * d$exp_i5
  d$qb_td   <- d$is_QB * nz(d$f_td, 0)
  d
}

# Anytime-TD markets pay on a quarterback's rushing touchdowns too, so each team's
# starting QB is in the touchdown model (v2; v1 left QBs out, which hid the likes of Josh
# Allen and Jalen Hurts). A QB gets his own terms for carries, goal-line carries and his
# rate of games with a touchdown: a sneak at the 1 scores far more often than a scramble,
# and some offenses simply hand their QB the goal-line work. Walk-forward on 2023-25
# (fit on prior seasons only, every start counted): QB log loss 0.426 against 0.458 for
# a flat rate, calibrated within a few points in every band (games above 45%: 55.5%
# predicted, 55.8% scored); the other positions are unchanged.
PLR_TD_POS <- c("QB", "RB", "WR", "TE")
PLR_VER    <- "td-qb-v2"
TD_COLS <- c("is_QB", "is_RB", "is_TE", "f_opp_n", "f_touch", "exp_tgt", "exp_car", "qb_car", "qb_i5",
             "qb_td", "implied")
RY_COLS <- c("is_RB", "is_TE", "f_tgt", "f_recyds", "f_ypt", "f_adot", "exp_tgt",
             "f_tgt_sh", "proj", "off_t_tgt", "implied")
RY_LINES <- c(40, 60, 80)
PLR_HALFLIFE <- 1
RY_RIDGE <- 5

plr_avail <- function(ros, inj, season_, week_, pid, team) {
  n <- length(pid)
  keep <- rep(TRUE, n)
  wk <- rep_len(as.integer(week_), n)
  if (!is.null(ros) && nrow(ros) > 0) {
    r <- ros[ros$season <= season_, , drop = FALSE]
    cur <- r[r$season == season_, , drop = FALSE]
    stc <- rep(NA_character_, n); cov <- rep(FALSE, n)
    if (nrow(cur) > 0) {
      stc <- cur$status[match(paste(wk, pid), paste(cur$week, cur$gsis_id))]
      cov <- paste(wk, team) %in% paste(cur$week, cur$team)
    }
    stp <- rep(NA_character_, n)
    if (nrow(r) > 0) {
      r <- r[order(r$season, r$week), ]
      r$status[r$status == "INA"] <- "ACT"
      for (u in unique(wk)) {
        p <- r[r$season < season_ | r$week < u, , drop = FALSE]
        if (nrow(p) == 0) next
        p <- p[!duplicated(p$gsis_id, fromLast = TRUE), ]
        i <- which(wk == u)
        stp[i] <- p$status[match(pid[i], p$gsis_id)]
      }
    }
    st <- ifelse(cov, stc, stp)
    known <- cov | !is.na(stp)
    keep <- !known | (!is.na(st) & st == "ACT")
  }
  if (!is.null(inj) && nrow(inj) > 0) {
    q <- inj[inj$season == season_, , drop = FALSE]
    if (nrow(q) > 0) {
      j <- match(paste(wk, pid), paste(q$week, q$gsis_id))
      keep <- keep & !(!is.na(j) & q$report_status[j] %in% INJ_OUT)
    }
  }
  keep
}

plr_flag <- function(inj, season_, week_, pid) {
  n <- length(pid)
  tag <- rep("", n)
  if (is.null(inj) || nrow(inj) == 0) return(tag)
  q <- inj[inj$season == season_, , drop = FALSE]
  if (nrow(q) == 0) return(tag)
  wk <- rep_len(as.integer(week_), n)
  j <- match(paste(wk, pid), paste(q$week, q$gsis_id))
  ok <- !is.na(j)
  rs <- ifelse(ok, q$report_status[j], NA_character_)
  ps <- if ("practice_status" %in% names(q)) ifelse(ok, q$practice_status[j], NA_character_)
        else rep(NA_character_, n)
  dnp <- !is.na(ps) & grepl("^Did Not", ps)
  tag[!is.na(rs) & rs == "Questionable"] <- "Q"
  tag[!is.na(rs) & rs == "Questionable" & dnp] <- "Q-DNP"
  tag
}

plr_eligible <- function(st, ros, season_, week_, teams_needed) {
  r <- ros[ros$season == season_ & ros$week <= week_, , drop = FALSE]
  if (nrow(r) > 0) {
    r <- r[order(r$week), ]
    r <- r[!duplicated(r$gsis_id, fromLast = TRUE), ]
    r <- r[r$status %in% c("ACT", "RES", "INA", "DEV"), c("gsis_id", "team")]
  }
  o <- st[st$season == season_ & st$week == week_, , drop = FALSE]
  if (nrow(o) == 0) return(NULL)
  j <- if (nrow(r) > 0) match(o$pid, r$gsis_id) else rep(NA_integer_, nrow(o))
  o$team_now <- ifelse(is.na(j), o$team_last, r$team[j])
  o <- o[!is.na(o$team_now) & o$pos %in% PLR_TD_POS, ]
  o <- o[o$f_opp_n >= PLR_MIN_OPP, ]
  if (!is.null(teams_needed)) o <- o[o$team_now %in% teams_needed, ]
  o
}

plr_training <- function(h, ros, sch, cutoff = NULL) {
  st <- if (is.null(cutoff)) plr_week_states(h, unique(h$season)) else memo_states(h, cutoff)
  gm <- h[!duplicated(h[, c("game_id", "posteam")]),
          c("game_id", "season", "week", "posteam", "defteam")]
  rows <- list()
  for (se in sort(unique(h$season))) {
    gs <- gm[gm$season == se, ]
    for (wk in sort(unique(gs$week))) {
      gw <- gs[gs$week == wk, ]
      el <- plr_eligible(st, ros, se, wk, unique(gw$posteam))
      if (is.null(el) || nrow(el) == 0) next
      # v2: team volume context as it stood BEFORE this week (it used to average the
      # whole season, so training rows saw their own game and every later one).
      tc <- plr_team_ctx(h[h$season < se | (h$season == se & h$week < wk), ], se)
      gj <- gw[, c("game_id", "posteam", "defteam")]
      x <- keep_qb_starter(merge(el, gj, by.x = "team_now", by.y = "posteam"), sch)
      if (nrow(x) == 0) next
      x <- merge(x, tc, by.x = "team_now", by.y = "team", all.x = TRUE)
      x$posteam <- x$team_now
      rows[[length(rows) + 1]] <- x
    }
  }
  d <- dplyr::bind_rows(rows)
  if (nrow(d) == 0) return(NULL)
  act <- h[, c("game_id", "pid", "td", "recyds")]
  act$key <- paste(act$game_id, act$pid)
  d$key <- paste(d$game_id, d$pid)
  j <- match(d$key, act$key)
  d$td <- ifelse(is.na(j), 0L, act$td[j])
  d$recyds <- ifelse(is.na(j), 0, act$recyds[j])
  d$played <- !is.na(j)
  mk <- sch[, c("game_id", "home_team", "away_team", "spread_line", "total_line")]
  d <- merge(d, mk, by = "game_id", all.x = TRUE)
  d$spread <- ifelse(d$posteam == d$home_team, d$spread_line, -d$spread_line)
  d$implied <- (d$total_line / 2) + (d$spread / 2)
  d <- d[!is.na(d$implied), ]
  plr_design(d)
}

ridge_fit <- function(X, y, w, lambda) {
  mu <- colMeans(X); sdv <- apply(X, 2, stats::sd); sdv[sdv == 0 | is.na(sdv)] <- 1
  Z <- scale(X, center = mu, scale = sdv)
  Z[!is.finite(Z)] <- 0
  W <- w / mean(w)
  ym <- sum(W * y) / sum(W)
  A <- crossprod(Z * W, Z) + diag(lambda, ncol(Z))
  b <- solve(A, crossprod(Z * W, y - ym))
  list(mu = mu, sd = sdv, b = as.numeric(b), int = ym)
}

ridge_predict <- function(m, X) {
  Z <- scale(X, center = m$mu, scale = m$sd)
  Z[!is.finite(Z)] <- 0
  as.numeric(m$int + Z %*% m$b)
}

plr_weights <- function(season_vec, target_season) {
  0.5 ^ ((target_season - 1 - season_vec) / PLR_HALFLIFE)
}

fit_player_models <- function(d, target_season) {
  if ("played" %in% names(d)) d <- d[d$played %in% TRUE, ]
  keep_t <- stats::complete.cases(d[, c("td", TD_COLS)]) &
            !is.na(d$f_opp_n) & d$f_opp_n >= PLR_MIN_OPP
  keep_r <- stats::complete.cases(d[, c("recyds", RY_COLS)]) &
            !is.na(d$f_tgt) & d$f_tgt >= PLR_MIN_OPP & d$pos %in% c("RB", "WR", "TE")
  dt <- d[keep_t, ]; dr <- d[keep_r, ]
  if (nrow(dt) < 400 || nrow(dr) < 400) return(NULL)
  ft <- dt[, c("td", TD_COLS)]
  wt <- plr_weights(dt$season, target_season)
  mt <- suppressWarnings(glm(stats::as.formula(paste("td ~", paste(TD_COLS, collapse = " + "))),
                             data = ft, family = binomial(), weights = wt))
  wr <- plr_weights(dr$season, target_season)
  Xr <- as.matrix(dr[, RY_COLS]); Xr[!is.finite(Xr)] <- 0
  mr <- ridge_fit(Xr, dr$recyds, wr, RY_RIDGE)
  cf <- rep(NA_real_, nrow(dr))
  for (s2 in unique(dr$season)) {
    k <- dr$season == s2
    if (sum(!k) < 300) { cf[k] <- pmax(ridge_predict(mr, Xr[k, , drop = FALSE]), 0); next }
    mk <- ridge_fit(Xr[!k, , drop = FALSE], dr$recyds[!k], wr[!k], RY_RIDGE)
    cf[k] <- pmax(ridge_predict(mk, Xr[k, , drop = FALSE]), 0)
  }
  lg <- lapply(RY_LINES, function(l) {
    df <- data.frame(o = as.integer(dr$recyds > l), lp = log1p(cf))
    suppressWarnings(glm(o ~ lp, data = df, family = binomial(), weights = wr))
  })
  names(lg) <- paste0("o", RY_LINES)
  slim_fits(list(td = mt, ry = mr, over = lg, n_td = nrow(dt), n_ry = nrow(dr), season = target_season),
            c("td", "over"))
}

project_players <- function(d, m, s, g, cutoff) {
  if (is.null(m) || nrow(g) == 0) return(NULL)
  h <- memo_history(d$plr, d$pos, cutoff)
  if (is.null(h)) return(NULL)
  f <- plr_features(h, s, cutoff = cutoff); tc <- plr_team_ctx(h, s)
  if (is.null(f)) return(NULL)
  ros <- d$ros
  tm <- f$team_last
  if (!is.null(ros) && nrow(ros) > 0) {
    r <- ros[ros$season == s & ros$week <= max(g$week), ]
    if (nrow(r) > 0) {
      r <- r[order(r$week), ]; r <- r[!duplicated(r$gsis_id, fromLast = TRUE), ]
      r <- r[r$status %in% c("ACT", "RES", "INA", "DEV"), ]
      j <- match(f$pid, r$gsis_id)
      tm <- ifelse(is.na(j), NA_character_, r$team[j])
    }
  }
  f$team_now <- ifelse(is.na(tm), f$team_last, tm)
  f <- f[!is.na(f$team_now) & f$pos %in% PLR_TD_POS, ]
  if (nrow(f) == 0) return(NULL)
  f$week <- NULL
  L <- rbind(
    data.frame(game_id = g$game_id, team = g$home_team, oppt = g$away_team, home = 1L,
               spread = g$spread_line, total_line = g$total_line, ko = g$ko,
               week = g$week, stringsAsFactors = FALSE),
    data.frame(game_id = g$game_id, team = g$away_team, oppt = g$home_team, home = 0L,
               spread = -g$spread_line, total_line = g$total_line, ko = g$ko,
               week = g$week, stringsAsFactors = FALSE))
  x <- merge(f, L, by.x = "team_now", by.y = "team")
  if (nrow(x) == 0) return(NULL)
  x <- merge(x, tc, by.x = "team_now", by.y = "team", all.x = TRUE)
  x$implied <- (x$total_line / 2) + (x$spread / 2)
  x$season <- s
  x <- plr_design(x)
  x <- x[!is.na(x$implied), ]
  if (nrow(x) == 0) return(NULL)
  wkey <- paste(h$season, h$week)
  mx <- tapply(as.numeric(h$ko), wkey, max)
  top <- names(sort(mx, decreasing = TRUE))
  top <- top[seq_len(min(PLR_RECENT_WEEKS, length(top)))]
  recent <- unique(h$pid[wkey %in% top])
  x$gp_recent <- as.integer(x$pid %in% recent)
  x <- keep_qb_starter(x, d$sch)
  x <- x[x$f_opp_n >= PLR_MIN_OPP & (x$gp_recent == 1 | x$qb_start), ]
  if (nrow(x) == 0) return(NULL)
  x <- x[plr_avail(ros, d$inj, s, x$week, x$pid, x$team_now), ]
  if (nrow(x) == 0) return(NULL)
  x$inj_tag <- plr_flag(d$inj, s, x$week, x$pid)
  x$p_td <- as.numeric(predict(m$td, newdata = x, type = "response"))
  Xr <- as.matrix(x[, RY_COLS]); Xr[!is.finite(Xr)] <- 0
  x$p_ry <- pmax(ridge_predict(m$ry, Xr), 0)
  for (l in RY_LINES) {
    nm <- paste0("o", l)
    x[[nm]] <- as.numeric(predict(m$over[[nm]],
                 newdata = data.frame(lp = log1p(x$p_ry)), type = "response"))
  }
  x
}

CFB_VER      <- 1
CFB_SEASONS  <- 2014:2026
CFB_PICK     <- 2016:2026
CFB_MODEL    <- "cfb-epa-prior-v2"
CFB_LEDGER   <- file.path(LEDGER_DIR, "cfb_predictions.rds")
CFB_LAM      <- 5
CFB_PW       <- 40
CFB_PW_G     <- 3
CFB_RHO      <- 0.9
CFB_END_LAM  <- 25
CFB_MAX_WEEK <- 16
CFB_TBD_UTC  <- "19:00"
CFB_PRIOR_X  <- c("last_rating", "tal_z", "R_scr", "I_scr", "I_dv")
CFB_REL      <- "https://github.com/sportsdataverse/sportsdataverse-data/releases/download"

cfb_dir  <- file.path(CACHE_DIR, "cfb")
dir.create(cfb_dir, showWarnings = FALSE, recursive = TRUE)
cfb_path <- function(k, y = NULL, ext = "rds")
  file.path(cfb_dir, if (is.null(y)) sprintf("%s_v%d.%s", k, CFB_VER, ext)
            else sprintf("%s_v%d_%d.%s", k, CFB_VER, y, ext))

cfb_fetch <- function(tag, file, dest) {
  if (file.exists(dest) && file.size(dest) > 512) return(TRUE)
  ms <- paste0(dest, ".miss")
  if (age_min(ms) < SDV_MISS_MIN) return(FALSE)
  u <- sprintf("%s/%s/%s", CFB_REL, tag, file)
  tmp <- paste0(dest, ".part")
  ok <- suppressWarnings(try(
    utils::download.file(u, tmp, mode = "wb", quiet = TRUE), silent = TRUE))
  if (inherits(ok, "try-error") || !file.exists(tmp) || file.size(tmp) < 512) {
    unlink(tmp)
    try(file.create(ms), silent = TRUE)
    return(FALSE)
  }
  unlink(ms)
  file.rename(tmp, dest)
  TRUE
}

cfb_rds <- function(tag, file, dest) {
  if (!cfb_fetch(tag, file, dest)) return(NULL)
  d <- try(readRDS(dest), silent = TRUE)
  if (inherits(d, "try-error")) { unlink(dest); return(NULL) }
  as.data.frame(d)
}

# Recruiting files are parquet, read with nanoparquet. One reader only: a deployment
# installs every package the code names, and naming arrow as a fallback made it a
# requirement too (rsconnect stops if any named package is missing locally).
cfb_parquet <- function(f) {
  if (!file.exists(f) || !requireNamespace("nanoparquet", quietly = TRUE)) return(NULL)
  as.data.frame(try(nanoparquet::read_parquet(f), silent = TRUE))
}

cfb_have_talent <- function() requireNamespace("nanoparquet", quietly = TRUE)

cfb_sync <- function(force = FALSE) {
  now <- now_et()
  for (y in CFB_SEASONS) {
    sf <- cfb_path("sch", y)
    stale <- force || (y >= 2026 && age_min(sf) > CFB_REFRESH_MIN)
    if (stale) unlink(sf)
    cfb_fetch("cfb_schedules", sprintf("cfb_schedules_%d.rds", y), sf)
    af <- cfb_path("adv", y)
    if (stale) unlink(af)
    cfb_fetch("espn_cfb_adv_team", sprintf("adv_team_%d.rds", y), af)
    cfb_fetch("espn_cfb_teams", sprintf("cfb_teams_%d.rds", y), cfb_path("team", y))
    rf <- cfb_path("ros", y)
    if (force || (y >= 2026 && age_min(rf) > 24 * 60)) unlink(rf)
    cfb_fetch("espn_cfb_rosters", sprintf("cfb_rosters_%d.rds", y), rf)
    bf <- cfb_path("box", y)
    if (stale) unlink(bf)
    cfb_fetch("espn_cfb_player_box", sprintf("player_box_%d.rds", y), bf)
    if (cfb_have_talent())
      cfb_fetch("cfb_team_talent", sprintf("cfb_team_talent_%d.parquet", y),
                cfb_path("tal", y, "parquet"))
  }
  f <- vapply(CFB_SEASONS, function(y) cfb_path("sch", y), "")
  f <- c(f, vapply(CFB_SEASONS, function(y) cfb_path("adv", y), ""))
  f <- f[file.exists(f)]
  if (!length(f)) stop("Could not load college football data. Check your connection.")
  paste(f, as.numeric(file.mtime(f)), collapse = "|")
}

cfb_iso <- function(x) {
  s <- sub("Z$", "", sub("\\.[0-9]+", "", as.character(x)))
  as.POSIXct(s, format = "%Y-%m-%dT%H:%M:%S", tz = "UTC")
}

cfb_sched <- function() {
  out <- lapply(CFB_SEASONS, function(y) {
    f <- cfb_path("sch", y); if (!file.exists(f)) return(NULL)
    d <- try(readRDS(f), silent = TRUE); if (inherits(d, "try-error")) return(NULL)
    d <- as.data.frame(d)
    need <- c("game_id", "season", "week", "season_type", "start_date", "completed",
              "neutral_site", "home_id", "home_team", "away_id", "away_team",
              "home_points", "away_points", "fbs_game")
    if (!all(need %in% names(d))) return(NULL)
    part <- if ("fbs_participant" %in% names(d)) d$fbs_participant %in% TRUE else d$fbs_game %in% TRUE
    d <- d[d$season_type == "regular" & (part | d$fbs_game %in% TRUE), ]
    tbd <- if ("start_time_tbd" %in% names(d)) d$start_time_tbd %in% TRUE else rep(FALSE, nrow(d))
    ko <- cfb_iso(d$start_date)
    fb <- as.POSIXct(paste(substr(as.character(d$start_date), 1, 10), CFB_TBD_UTC),
                     format = "%Y-%m-%d %H:%M", tz = "UTC")
    ko[tbd | is.na(ko)] <- fb[tbd | is.na(ko)]
    data.frame(game_id = as.character(d$game_id), season = as.integer(d$season),
               week = as.integer(d$week), ko = ko,
               home_id = as.character(d$home_id), away_id = as.character(d$away_id),
               home_team = d$home_team, away_team = d$away_team,
               home_score = suppressWarnings(as.numeric(d$home_points)),
               away_score = suppressWarnings(as.numeric(d$away_points)),
               neutral = d$neutral_site %in% TRUE,
               both_fbs = d$fbs_game %in% TRUE,
               stringsAsFactors = FALSE)
  })
  s <- dplyr::bind_rows(out)
  if (!nrow(s)) stop("No college football schedule could be loaded.")
  s <- s[!is.na(s$ko) & s$week >= 1 & s$week <= CFB_MAX_WEEK, ]
  attr(s$ko, "tzone") <- TZ_ET
  s$final_at  <- s$ko + FINAL_AFTER_H * 3600
  s$has_score <- !is.na(s$home_score) & !is.na(s$away_score)
  s[order(s$season, s$week, s$ko), ]
}

cfb_teams <- function() {
  out <- lapply(CFB_SEASONS, function(y) {
    f <- cfb_path("team", y); if (!file.exists(f)) return(NULL)
    d <- try(readRDS(f), silent = TRUE); if (inherits(d, "try-error")) return(NULL)
    d <- as.data.frame(d)
    if (!all(c("team_id", "division") %in% names(d))) return(NULL)
    d <- d[!is.na(d$division) & d$division == "fbs", ]
    data.frame(season = y, team_id = as.character(d$team_id),
               name = if ("location" %in% names(d)) d$location else d$display_name,
               abbr = if ("abbreviation" %in% names(d)) d$abbreviation else NA_character_,
               col = if ("color" %in% names(d)) d$color else NA_character_,
               logo = if ("team_logo" %in% names(d)) d$team_logo else NA_character_,
               stringsAsFactors = FALSE)
  })
  t <- dplyr::bind_rows(out)
  if (!nrow(t)) return(NULL)
  t$col <- ifelse(is.na(t$col) | t$col == "", "#444444",
                  ifelse(grepl("^#", t$col), t$col, paste0("#", t$col)))
  t
}

cfb_panel <- function(sch, fbs) {
  key <- paste(fbs$season, fbs$team_id)
  out <- lapply(CFB_SEASONS, function(y) {
    f <- cfb_path("adv", y); if (!file.exists(f)) return(NULL)
    a <- try(readRDS(f), silent = TRUE); if (inherits(a, "try-error")) return(NULL)
    a <- as.data.frame(a)
    need <- c("game_id", "pos_team_id", "EPA_overall_off", "scrimmage_plays")
    if (!all(need %in% names(a))) return(NULL)
    d <- data.frame(game_id = as.character(a$game_id), tid = as.character(a$pos_team_id),
                    epa = a$EPA_overall_off / pmax(a$scrimmage_plays, 1),
                    plays = a$scrimmage_plays, stringsAsFactors = FALSE)
    d <- d[!is.na(d$epa) & !is.na(d$tid), ]
    d[!duplicated(paste(d$game_id, d$tid)), ]
  })
  p <- dplyr::bind_rows(out)
  if (!nrow(p)) return(NULL)
  o <- p[, c("game_id", "tid", "epa")]; names(o) <- c("game_id", "otid", "oepa")
  p <- merge(p, o, by = "game_id"); p <- p[p$tid != p$otid, ]
  g <- sch[, c("game_id", "season", "week", "ko", "home_id", "away_id",
               "home_score", "away_score", "neutral", "has_score", "both_fbs")]
  p <- merge(p, g, by = "game_id")
  p <- p[p$has_score, ]
  p$home <- as.integer(p$tid == p$home_id)
  p$pts  <- ifelse(p$home == 1, p$home_score, p$away_score)
  p$pa   <- ifelse(p$home == 1, p$away_score, p$home_score)
  p$net  <- p$epa - p$oepa
  p$marg <- p$pts - p$pa
  p$hfa  <- ifelse(p$neutral, 0, ifelse(p$home == 1, 1, -1))
  p$ent  <- ifelse(paste(p$season, p$tid) %in% key, p$tid, "FCS")
  p$oent <- ifelse(paste(p$season, p$otid) %in% key, p$otid, "FCS")
  p <- p[p$ent != "FCS", ]
  p[order(p$ko), ]
}

cfb_rate <- function(g, ents, lam, prior = NULL, pw = 0) {
  n <- length(ents); idx <- stats::setNames(seq_len(n), ents)
  A <- matrix(0, n + 1L, n + 1L); b <- numeric(n + 1L)
  if (nrow(g) > 0) {
    ti <- idx[g$ent]; oi <- idx[g$oent]
    ok <- !is.na(ti) & !is.na(oi)
    ti <- ti[ok]; oi <- oi[ok]; y <- g$net[ok]; h <- g$hfa[ok]
    m <- length(y)
    if (m > 0) {
      X <- Matrix::sparseMatrix(i = rep(seq_len(m), 3L), j = c(ti, oi, rep(n + 1L, m)),
                                x = c(rep(1, m), rep(-1, m), h), dims = c(m, n + 1L))
      A <- as.matrix(Matrix::crossprod(X))
      b <- as.numeric(Matrix::crossprod(X, y))
    }
  }
  dd <- cbind(seq_len(n), seq_len(n))
  A[dd] <- A[dd] + lam
  if (!is.null(prior) && pw > 0) {
    pv <- prior[ents]; pv[is.na(pv)] <- 0
    A[dd] <- A[dd] + pw; b[seq_len(n)] <- b[seq_len(n)] + pw * pv
  }
  A[n + 1L, n + 1L] <- A[n + 1L, n + 1L] + 1e-6
  x <- try(solve(A, b), silent = TRUE)
  if (inherits(x, "try-error")) return(stats::setNames(numeric(n), ents))
  r <- stats::setNames(x[seq_len(n)], ents)
  fb <- names(r) != "FCS"
  r - if (any(fb)) mean(r[fb]) else 0
}

cfb_end <- function(panel) {
  f <- cfb_path("end")
  cur <- max(panel$season)
  e <- if (file.exists(f)) try(readRDS(f), silent = TRUE) else NULL
  if (inherits(e, "try-error") || !is.list(e)) e <- list()
  for (s in sort(unique(panel$season))) {
    g <- panel[panel$season == s, ]
    if (nrow(g) < 200) next
    k <- as.character(s)
    if (!is.null(e[[k]]) && s < cur) next
    ents <- sort(unique(c(g$ent, g$oent)))
    e[[k]] <- cfb_rate(g, ents, CFB_END_LAM)
  }
  try(saveRDS(e, f), silent = TRUE)
  e
}

cfb_roster_feats <- function() {
  f <- cfb_path("rfeat")
  cache <- if (file.exists(f)) try(readRDS(f), silent = TRUE) else NULL
  if (inherits(cache, "try-error")) cache <- NULL
  need <- CFB_SEASONS[CFB_SEASONS > min(CFB_SEASONS)]
  if (!is.null(cache) && all(need %in% cache$season) &&
      age_min(f) < CFB_REFRESH_MIN * 4) return(cache)
  num <- function(x) { v <- suppressWarnings(as.numeric(as.character(x))); ifelse(is.na(v), 0, v) }
  prod_y <- function(y) {
    fp <- cfb_path("box", y); if (!file.exists(fp)) return(NULL)
    b <- try(readRDS(fp), silent = TRUE); if (inherits(b, "try-error")) return(NULL)
    b <- as.data.frame(b)
    g <- function(n) if (n %in% names(b)) num(b[[n]]) else 0
    d <- data.frame(aid = as.character(b$athlete_id), tid = as.character(b$team_id),
                    scr = g("rushingYards") + g("receivingYards"),
                    dv = 10 * g("totalTackles") + 25 * g("sacks") + 15 * g("passesDefended"),
                    stringsAsFactors = FALSE)
    d <- d[!is.na(d$aid) & d$aid != "" & !is.na(d$tid), ]
    d <- stats::aggregate(cbind(scr, dv) ~ aid + tid, data = d, FUN = sum)
    d <- d[order(-(d$scr + d$dv)), ]
    d[!duplicated(d$aid), ]
  }
  ros_y <- function(y) {
    fp <- cfb_path("ros", y); if (!file.exists(fp)) return(NULL)
    r <- try(readRDS(fp), silent = TRUE); if (inherits(r, "try-error")) return(NULL)
    r <- as.data.frame(r)
    d <- data.frame(aid = as.character(r$athlete_id), tid = as.character(r$team_id),
                    stringsAsFactors = FALSE)
    d <- d[!is.na(d$aid) & d$aid != "" & !is.na(d$tid), ]
    d[!duplicated(d$aid), ]
  }
  PR <- list(); RO <- list()
  for (y in CFB_SEASONS) { PR[[as.character(y)]] <- prod_y(y); RO[[as.character(y)]] <- ros_y(y) }
  rows <- list()
  for (y in need) {
    p <- PR[[as.character(y - 1)]]; r <- RO[[as.character(y)]]
    if (is.null(p) || is.null(r) || !nrow(p) || !nrow(r)) next
    tot <- stats::aggregate(cbind(scr, dv) ~ tid, data = p, FUN = sum)
    names(tot) <- c("tid", "t_scr", "t_dv")
    j <- merge(r, p, by = "aid", suffixes = c("_now", "_then"))
    if (!nrow(j)) next
    j$same <- j$tid_now == j$tid_then
    ag <- data.frame(tid = j$tid_now,
                     rs = ifelse(j$same, j$scr, 0), is_ = ifelse(j$same, 0, j$scr),
                     rd = ifelse(j$same, j$dv, 0), id_ = ifelse(j$same, 0, j$dv),
                     ni = as.integer(!j$same & (j$scr + j$dv) > 0), stringsAsFactors = FALSE)
    ag <- stats::aggregate(cbind(rs, is_, rd, id_, ni) ~ tid, data = ag, FUN = sum)
    ag <- merge(ag, tot, by = "tid", all.x = TRUE)
    ag$season <- y
    rows[[length(rows) + 1L]] <- ag
  }
  T <- dplyr::bind_rows(rows)
  if (!nrow(T)) return(NULL)
  T$t_scr[is.na(T$t_scr)] <- 0; T$t_dv[is.na(T$t_dv)] <- 0
  try(saveRDS(T, f), silent = TRUE)
  T
}

cfb_talent <- function() {
  if (!cfb_have_talent()) return(NULL)
  out <- lapply(CFB_SEASONS, function(y) {
    d <- cfb_parquet(cfb_path("tal", y, "parquet"))
    if (is.null(d) || !is.data.frame(d) || !nrow(d)) return(NULL)
    if (!all(c("season", "team_id", "talent_composite") %in% names(d))) return(NULL)
    data.frame(season = as.integer(d$season), team_id = as.character(d$team_id),
               talent = suppressWarnings(as.numeric(d$talent_composite)),
               stringsAsFactors = FALSE)
  })
  t <- dplyr::bind_rows(out)
  if (!nrow(t)) NULL else t
}

cfb_feat <- function(fbs, rf, tal, endr) {
  if (is.null(rf) || !nrow(rf)) return(NULL)
  F <- merge(fbs[, c("season", "team_id")], rf,
             by.x = c("season", "team_id"), by.y = c("season", "tid"))
  if (!nrow(F)) return(NULL)
  med <- function(v, s) { m <- stats::ave(v, s, FUN = function(x) stats::median(x, na.rm = TRUE)); ifelse(is.na(m) | m <= 0, 1, m) }
  ms <- med(F$t_scr, F$season); md <- med(F$t_dv, F$season)
  F$R_scr <- pmin(F$rs / ms, 3); F$I_scr <- pmin(F$is_ / ms, 3)
  F$R_dv  <- pmin(F$rd / md, 3); F$I_dv  <- pmin(F$id_ / md, 3)
  if (!is.null(tal)) {
    F <- merge(F, tal, by = c("season", "team_id"), all.x = TRUE)
    mu <- stats::ave(F$talent, F$season, FUN = function(x) mean(x, na.rm = TRUE))
    sd <- stats::ave(F$talent, F$season, FUN = function(x) stats::sd(x, na.rm = TRUE))
    F$tal_z <- ifelse(is.na(sd) | sd == 0, 0, (F$talent - mu) / sd)
  } else F$tal_z <- NA_real_
  gv <- function(s, k) { r <- endr[[as.character(s)]]; if (is.null(r)) NA_real_ else unname(r[k]) }
  F$last_rating <- mapply(function(s, k) gv(s - 1L, k), F$season, F$team_id)
  F$cur         <- mapply(function(s, k) gv(s, k),     F$season, F$team_id)
  for (c in c("last_rating", "tal_z", "R_scr", "I_scr", "I_dv")) {
    m <- stats::ave(F[[c]], F$season, FUN = function(x) stats::median(x, na.rm = TRUE))
    F[[c]] <- ifelse(is.na(F[[c]]), m, F[[c]])
    F[[c]] <- ifelse(is.na(F[[c]]), 0, F[[c]])
  }
  F
}

cfb_prior <- function(F, endr, season_) {
  fall <- function() {
    r <- endr[[as.character(season_ - 1L)]]
    if (is.null(r)) return(NULL)
    r * CFB_RHO
  }
  if (is.null(F)) return(fall())
  xs <- CFB_PRIOR_X
  tr <- F[F$season < season_ & !is.na(F$cur), c("cur", xs), drop = FALSE]
  tr <- tr[stats::complete.cases(tr), , drop = FALSE]
  if (nrow(tr) < 200) return(fall())
  keep <- vapply(xs, function(c) stats::sd(tr[[c]]) > 1e-9, TRUE)
  xs <- xs[keep]
  if (!length(xs)) return(fall())
  tr <- tr[, c("cur", xs), drop = FALSE]
  m <- try(stats::lm(stats::as.formula(paste("cur ~", paste(xs, collapse = " + "))), data = tr),
           silent = TRUE)
  if (inherits(m, "try-error")) return(fall())
  te <- F[F$season == season_, , drop = FALSE]
  if (!nrow(te)) return(fall())
  p <- try(as.numeric(stats::predict(m, newdata = te)), silent = TRUE)
  if (inherits(p, "try-error")) return(fall())
  v <- stats::setNames(p, te$team_id)
  pr <- endr[[as.character(season_ - 1L)]]
  v["FCS"] <- if (!is.null(pr) && "FCS" %in% names(pr)) pr[["FCS"]] else -0.30
  v[!is.na(v)]
}

cfb_week_rows <- function(panel, F, endr, season_, ents) {
  sg <- panel[panel$season == season_, ]
  if (!nrow(sg)) return(NULL)
  pr <- cfb_prior(F, endr, season_)
  out <- list()
  for (w in sort(unique(sg$week))) {
    cut <- min(sg$ko[sg$week == w], na.rm = TRUE)
    hist <- sg[sg$ko < cut, ]
    gp <- if (nrow(hist)) nrow(hist) / max(1L, length(unique(hist$ent))) else 0
    r <- cfb_rate(hist, ents, CFB_LAM, pr, CFB_PW / (1 + gp / CFB_PW_G))
    tw <- sg[sg$week == w & sg$home == 1 & sg$oent != "FCS", ]
    if (!nrow(tw)) next
    out[[length(out) + 1L]] <- data.frame(
      season = season_, week = w, game_id = tw$game_id,
      rd = unname(r[tw$ent]) - unname(r[tw$oent]), hfa = tw$hfa, marg = tw$marg,
      stringsAsFactors = FALSE)
  }
  dplyr::bind_rows(out)
}

cfb_rows <- function(panel, F, endr, ents, upto) {
  f <- cfb_path("rows")
  R <- if (file.exists(f)) try(readRDS(f), silent = TRUE) else NULL
  if (inherits(R, "try-error") || !is.data.frame(R)) R <- NULL
  have <- if (is.null(R)) integer(0) else unique(R$season)
  want <- CFB_PICK[CFB_PICK < upto]
  miss <- setdiff(want, have)
  if (!length(miss)) return(R)
  add <- dplyr::bind_rows(lapply(miss, function(s) cfb_week_rows(panel, F, endr, s, ents)))
  R <- dplyr::bind_rows(R, add)
  R <- R[!is.na(R$rd) & !is.na(R$marg), ]
  try(saveRDS(R, f), silent = TRUE)
  R
}

# v2: the rating-to-points slope is allowed to differ in weeks 1-2 and 3-4. Early
# ratings are mostly the preseason prior, which is compressed, so the same rating gap
# is worth more points then. Walk-forward 2018-2025: accuracy 71.4% -> 71.6%, margin
# error 13.50 -> 13.42, and the week 1-2 underconfidence (said 68%, won 75%) is gone.
cfb_phase <- function(week, rd) {
  w <- as.numeric(week)
  data.frame(rd = rd, rd_e1 = rd * as.numeric(w <= 2), rd_e2 = rd * as.numeric(w > 2 & w <= 4))
}
cfb_fit <- function(R, season_) {
  h <- R[R$season < season_, ]
  if (nrow(h) < 800) return(NULL)
  ph <- cfb_phase(h$week, h$rd); h$rd_e1 <- ph$rd_e1; h$rd_e2 <- ph$rd_e2
  lm1 <- stats::lm(marg ~ rd + hfa + rd_e1 + rd_e2, data = h)
  h$pred <- stats::predict(lm1)
  h$win <- as.integer(h$marg > 0)
  h <- h[h$marg != 0, ]
  lg <- suppressWarnings(stats::glm(win ~ pred, data = h, family = stats::binomial()))
  list(marg = lm1, conf = lg, n = nrow(h))
}

cfb_predict <- function(panel, F, endr, ents, m, g, cutoff) {
  if (is.null(m) || !nrow(g)) return(NULL)
  s <- g$season[1]
  hist <- panel[panel$season == s & panel$ko < cutoff, ]
  pr <- cfb_prior(F, endr, s)
  gp <- if (nrow(hist)) nrow(hist) / max(1L, length(unique(hist$ent))) else 0
  r <- cfb_rate(hist, ents, CFB_LAM, pr, CFB_PW / (1 + gp / CFB_PW_G))
  fk <- ents
  hm <- ifelse(g$home_id %in% fk, g$home_id, "FCS")
  aw <- ifelse(g$away_id %in% fk, g$away_id, "FCS")
  rd <- unname(r[hm]) - unname(r[aw])
  hfa <- ifelse(g$neutral, 0, 1)
  nd <- cfb_phase(g$week, rd); nd$hfa <- hfa
  pred <- as.numeric(stats::predict(m$marg, newdata = nd))
  conf <- as.numeric(stats::predict(m$conf, newdata = data.frame(pred = pred), type = "response"))
  conf <- pmin(pmax(conf, 0.03), 0.97)   # no college game is a 99% lock (walk-forward log loss)
  data.frame(game_id = g$game_id, season = s, week = g$week, rd = rd,
             pred = pred, conf = pmax(conf, 1 - conf),
             stringsAsFactors = FALSE)
}

cfb_empty_ledger <- function() data.frame(
  game_id = character(0), season = integer(0), week = integer(0),
  kickoff = as.POSIXct(character(0), tz = TZ_ET),
  rd = numeric(0), pred = numeric(0), conf = numeric(0),
  model_ver = character(0), locked_at = as.POSIXct(character(0), tz = TZ_ET),
  stringsAsFactors = FALSE)

cfb_read_ledger <- function() {
  if (!file.exists(CFB_LEDGER)) return(cfb_empty_ledger())
  L <- try(readRDS(CFB_LEDGER), silent = TRUE)
  if (inherits(L, "try-error") || !is.data.frame(L)) return(cfb_empty_ledger())
  L
}

cfb_append_ledger <- function(new) {
  L <- cfb_read_ledger()
  new <- new[!new$game_id %in% L$game_id, , drop = FALSE]
  if (!nrow(new)) return(invisible(L))
  L <- dplyr::bind_rows(L, new)
  tmp <- paste0(CFB_LEDGER, ".tmp"); saveRDS(L, tmp); file.rename(tmp, CFB_LEDGER)
  invisible(L)
}

cfb_settle <- function(panel, F, endr, ents, m, g, now) {
  if (!nrow(g)) return(NULL)
  L <- cfb_read_ledger()
  Lg <- L[L$game_id %in% g$game_id, , drop = FALSE]
  out <- list()
  if (nrow(Lg)) { Lg$locked <- TRUE; out[[1]] <- Lg }
  todo <- g[!g$game_id %in% Lg$game_id, , drop = FALSE]
  if (nrow(todo)) {
    cut <- as.POSIXct(pmin(as.numeric(todo$ko), as.numeric(now)),
                      origin = "1970-01-01", tz = TZ_ET)
    for (u in unique(as.numeric(cut))) {
      gi <- todo[as.numeric(cut) == u, , drop = FALSE]
      c1 <- as.POSIXct(u, origin = "1970-01-01", tz = TZ_ET)
      x <- cfb_predict(panel, F, endr, ents, m, gi, c1)
      if (is.null(x) || !nrow(x)) next
      x$kickoff <- gi$ko[match(x$game_id, gi$game_id)]
      x$model_ver <- CFB_MODEL; x$locked_at <- now
      x$locked <- !is.na(x$kickoff) & now >= x$kickoff
      out[[length(out) + 1L]] <- x
      lk <- x[x$locked, , drop = FALSE]
      if (nrow(lk)) cfb_append_ledger(lk[, intersect(names(cfb_empty_ledger()), names(lk)), drop = FALSE])
    }
  }
  if (!length(out)) return(NULL)
  r <- dplyr::bind_rows(out)
  r[match(g$game_id, r$game_id), , drop = FALSE]
}

cfb_current_season <- function(sch, now) {
  y <- sch$season[!is.na(sch$ko) & sch$ko <= now]
  if (!length(y)) return(min(CFB_PICK))
  as.integer(max(y))
}

cfb_current_week <- function(sch, season_, now) {
  g <- sch[sch$season == season_ & !is.na(sch$ko), ]
  if (!nrow(g)) return(1L)
  up <- g$week[g$ko > now]
  if (length(up)) return(as.integer(min(up)))
  as.integer(max(g$week))
}

cfb_load <- function() {
  sch <- cfb_sched()
  fbs <- cfb_teams()
  if (is.null(fbs)) stop("Could not load the FBS team list.")
  pan <- cfb_panel(sch, fbs)
  if (is.null(pan) || !nrow(pan)) stop("No college football play data could be loaded.")
  endr <- cfb_end(pan)
  F <- cfb_feat(fbs, cfb_roster_feats(), cfb_talent(), endr)
  ents <- sort(unique(c(pan$ent, pan$oent, "FCS")))
  cur <- fbs[fbs$season == max(fbs$season), ]
  game_grade_history(CFB_LEDGER, sch)
  list(sch = sch, fbs = fbs, pan = pan, endr = endr, F = F, ents = ents,
       col = stats::setNames(cur$col, cur$team_id),
       logo = stats::setNames(cur$logo, cur$team_id),
       nm = stats::setNames(cur$name, cur$team_id),
       talent = !is.null(cfb_talent()))
}

cfb_conf_col <- function(p) {
  x <- pmin(pmax((p - 0.5) / 0.45, 0), 1)
  m <- CONF_RAMP(ifelse(is.na(x), 0, x))
  grDevices::rgb(m[, 1], m[, 2], m[, 3], maxColorValue = 255)
}

cfb_name <- function(d, id) {
  v <- unname(d$nm[id])
  ifelse(is.na(v), as.character(id), v)
}

cfb_badge <- function(d, id) {
  u <- unname(d$logo[id]); c0 <- unname(d$col[id])
  c0[is.na(c0) | c0 == ""] <- "#444444"
  ifelse(is.na(u) | u == "",
         sprintf('<span class="bdg" style="background:%s"></span>', c0),
         sprintf('<span class="bdg"><img src="%s" alt=""></span>', u))
}

# ==================== COLLEGE TOUCHDOWN SCORERS ====================
# Anytime-touchdown chance for every college skill player with a track record, from
# ESPN's player box scores. Inputs, all from games before kickoff: carries, catches and
# yards per game this season blended with last season (worth 2 games), the player's
# touchdowns a game (shrunk toward 0.3), his share of his team's carries and catches --
# trusted more as the season's sample grows -- his last game's usage, and the scoring
# environment (his team's points a game against the opponent's points allowed). Fit by
# logistic regression on completed prior seasons only.
# Out of sample on 2025 (fit on 2016-24, inputs as of each kickoff): among players who
# played, 26.2% average chance and 26.7% scored; each game's top three averaged 46%
# and 43% scored, counting the 5% who did not play. Candidates are the players who
# touched the ball in their team's previous game; the chance assumes he plays.
CFB_TD_VER   <- 1L
CFB_TD_YEARS <- 9L         # seasons of history in a fit
CFB_TD_W     <- 2          # last season counts as this many games in the blend
CFB_TD_LG    <- 26.9       # points per team-game, FBS 2014-26
CFB_TD_X     <- c("(Intercept)", "lcar", "lrec", "lryd", "lcyd", "ltd", "ltd_rel", "lpts", "shr_c", "shr_r",
                  "shr_c_rel", "shr_r_rel", "llcar", "llrec", "first", "lgames")

# one season's player-games with at least one carry or catch
cfb_td_box <- function(y) {
  f <- cfb_path("box", y)
  if (!file.exists(f)) return(NULL)
  b <- tryCatch(readRDS(f), error = function(e) NULL)
  if (is.null(b) || !NROW(b) || !all(c("category", "game_id", "team_id", "athlete_id") %in% names(b))) return(NULL)
  keep <- intersect(c("category", "game_id", "team_id", "athlete_id", "athlete_name", "rushingAttempts",
                      "rushingYards", "rushingTouchdowns", "receptions", "receivingYards", "receivingTouchdowns"), names(b))
  # .subset takes the columns without method dispatch: these files are data.tables, and with
  # data.table loaded b[keep] would be read as a join (and error) instead of a column pick
  b <- as.data.frame(.subset(b, keep), stringsAsFactors = FALSE)
  b <- b[b$category %in% c("rushing", "receiving"), , drop = FALSE]
  if (!nrow(b)) return(NULL)
  num <- function(n) {
    if (!n %in% names(b)) return(rep(0, nrow(b)))
    v <- suppressWarnings(as.numeric(as.character(b[[n]]))); ifelse(is.na(v), 0, v)
  }
  x <- data.frame(game_id = as.character(b$game_id), team_id = as.character(b$team_id),
                  aid = as.character(b$athlete_id),
                  car = num("rushingAttempts"), ryd = num("rushingYards"), rtd = num("rushingTouchdowns"),
                  rec = num("receptions"), cyd = num("receivingYards"), ctd = num("receivingTouchdowns"),
                  stringsAsFactors = FALSE)
  nm <- if ("athlete_name" %in% names(b)) as.character(b$athlete_name) else rep(NA_character_, nrow(b))
  ok <- !is.na(x$aid) & nzchar(x$aid) & !is.na(x$game_id) & !is.na(x$team_id)
  x <- x[ok, , drop = FALSE]; nm <- nm[ok]
  if (!nrow(x)) return(NULL)
  key <- paste(x$game_id, x$team_id, x$aid, sep = "|")
  s <- rowsum(as.matrix(x[, c("car", "ryd", "rtd", "rec", "cyd", "ctd")]), key, reorder = FALSE)
  k <- match(rownames(s), key)
  a <- data.frame(game_id = x$game_id[k], team_id = x$team_id[k], aid = x$aid[k], s,
                  name = nm[k], stringsAsFactors = FALSE, row.names = NULL)
  a$season <- as.integer(y)
  a <- a[(a$car + a$rec) > 0, , drop = FALSE]
  a$td <- as.integer(a$rtd + a$ctd > 0)
  a
}

# each team's points per game and points allowed per game before every game
cfb_td_teamctx <- function(sch) {
  s <- sch[sch$has_score & !is.na(sch$ko), c("game_id", "season", "ko", "home_id", "away_id", "home_score", "away_score")]
  tg <- rbind(data.frame(game_id = s$game_id, season = s$season, ko = s$ko, team = s$home_id,
                         pf = s$home_score, pa = s$away_score, stringsAsFactors = FALSE),
              data.frame(game_id = s$game_id, season = s$season, ko = s$ko, team = s$away_id,
                         pf = s$away_score, pa = s$home_score, stringsAsFactors = FALSE))
  tg[order(tg$team, tg$season, tg$ko), , drop = FALSE]
}
# scoring environment for team vs opp before time t (shrunk toward the league early on)
cfb_td_pts <- function(tg, season, team, opp, t) {
  pre <- tg$season == season & tg$ko < t
  a <- tg[pre & tg$team == team, , drop = FALSE]; b <- tg[pre & tg$team == opp, , drop = FALSE]
  nt <- nrow(a)
  pf <- if (nt) mean(a$pf) else CFB_TD_LG
  pa <- if (nrow(b)) mean(b$pa) else CFB_TD_LG
  (nt * (pf + pa) / 2 + 2 * CFB_TD_LG) / (nt + 2)
}

# model inputs from season-to-date sums (s_*), last-season totals (ly_*) and context.
# Touchdowns are shrunk toward 0.3 a game (2 games' worth) and, like the usage shares,
# trusted more as this season's sample grows (rel); early-season samples are noisy.
cfb_td_x <- function(x) {
  has_ly <- x$ly_g > 0
  g0 <- x$n_prev + ifelse(has_ly, CFB_TD_W, 0)
  b <- function(s, lyv, k = 0, mu = 0) {
    num <- s + ifelse(has_ly, CFB_TD_W * lyv / pmax(x$ly_g, 1), 0) + k * mu
    ifelse(g0 > 0, num / (g0 + k), NA_real_)
  }
  rel <- x$n_prev / (x$n_prev + 3)
  ltd <- log1p(b(x$s_td, x$ly_td, 2, 0.3))
  shr_c <- ifelse(x$s_tcar > 0, x$s_car / x$s_tcar, 0); shr_r <- ifelse(x$s_trec > 0, x$s_rec / x$s_trec, 0)
  data.frame(lcar = log1p(b(x$s_car, x$ly_car)), lrec = log1p(b(x$s_rec, x$ly_rec)),
             lryd = log1p(pmax(b(x$s_ryd, x$ly_ryd), 0)), lcyd = log1p(pmax(b(x$s_cyd, x$ly_cyd), 0)),
             ltd = ltd, ltd_rel = ltd * rel, lpts = log(x$e_pts),
             shr_c = shr_c, shr_r = shr_r, shr_c_rel = shr_c * rel, shr_r_rel = shr_r * rel,
             llcar = log1p(ifelse(is.na(x$l_car), 0, x$l_car)), llrec = log1p(ifelse(is.na(x$l_rec), 0, x$l_rec)),
             first = as.integer(x$n_prev == 0), lgames = log1p(g0))
}
cfb_td_lastyear <- function(p) {
  if (is.null(p) || !nrow(p)) return(NULL)
  s <- rowsum(cbind(p$car, p$rec, p$ryd, p$cyd, p$rtd + p$ctd, 1), p$aid, reorder = FALSE)
  data.frame(aid = rownames(s), ly_car = s[, 1], ly_rec = s[, 2], ly_ryd = s[, 3], ly_cyd = s[, 4],
             ly_td = s[, 5], ly_g = s[, 6], stringsAsFactors = FALSE, row.names = NULL)
}

# training rows: every player-game of a season with its pre-game inputs (vectorised)
cfb_td_rows <- function(p, prev, sch, tg) {
  p <- merge(p, sch[, c("game_id", "ko", "home_id", "away_id")], by = "game_id")
  p <- p[!is.na(p$ko), , drop = FALSE]
  if (!nrow(p)) return(NULL)
  p$opp <- ifelse(p$team_id == p$home_id, p$away_id, p$home_id)
  gk <- paste(p$game_id, p$team_id)
  tt <- rowsum(cbind(p$car, p$rec), gk, reorder = FALSE)
  k <- match(gk, rownames(tt)); p$t_car <- tt[k, 1]; p$t_rec <- tt[k, 2]
  p <- p[order(p$aid, p$ko), , drop = FALSE]
  cs <- function(v) stats::ave(v, p$aid, FUN = cumsum) - v
  lg1 <- function(v) stats::ave(v, p$aid, FUN = function(z) c(NA, head(z, -1)))
  p$n_prev <- stats::ave(rep(1, nrow(p)), p$aid, FUN = cumsum) - 1
  p$s_car <- cs(p$car); p$s_rec <- cs(p$rec); p$s_ryd <- cs(p$ryd); p$s_cyd <- cs(p$cyd)
  p$s_td <- cs(p$rtd + p$ctd); p$s_tcar <- cs(p$t_car); p$s_trec <- cs(p$t_rec)
  p$l_car <- lg1(p$car); p$l_rec <- lg1(p$rec)
  ly <- cfb_td_lastyear(prev)
  p <- if (is.null(ly)) cbind(p, ly_car = 0, ly_rec = 0, ly_ryd = 0, ly_cyd = 0, ly_td = 0, ly_g = 0) else
    merge(p, ly, by = "aid", all.x = TRUE)
  for (v in c("ly_car", "ly_rec", "ly_ryd", "ly_cyd", "ly_td", "ly_g")) p[[v]][is.na(p[[v]])] <- 0
  # scoring environment, vectorised over the team-game table
  tg$n_t <- stats::ave(rep(1, nrow(tg)), paste(tg$team, tg$season), FUN = cumsum) - 1
  tg$pf_pg <- (stats::ave(tg$pf, paste(tg$team, tg$season), FUN = cumsum) - tg$pf) / pmax(tg$n_t, 1)
  tg$pa_pg <- (stats::ave(tg$pa, paste(tg$team, tg$season), FUN = cumsum) - tg$pa) / pmax(tg$n_t, 1)
  k1 <- match(paste(p$game_id, p$team_id), paste(tg$game_id, tg$team))
  k2 <- match(paste(p$game_id, p$opp), paste(tg$game_id, tg$team))
  nt <- ifelse(is.na(k1), 0, tg$n_t[k1])
  pf <- ifelse(is.na(k1) | nt == 0, CFB_TD_LG, tg$pf_pg[k1])
  pa <- ifelse(is.na(k2) | tg$n_t[k2] == 0, CFB_TD_LG, tg$pa_pg[k2])
  p$e_pts <- (nt * (pf + pa) / 2 + 2 * CFB_TD_LG) / (nt + 2)
  p
}

# athlete ids on each team's roster this season (NULL when the roster file is missing)
cfb_td_roster <- function(s) {
  f <- cfb_path("ros", s)
  if (!file.exists(f)) return(NULL)
  r <- tryCatch(as.data.frame(readRDS(f)), error = function(e) NULL)
  if (is.null(r) || !nrow(r) || !all(c("athlete_id", "team_id") %in% names(r))) return(NULL)
  data.frame(aid = as.character(r$athlete_id), team_id = as.character(r$team_id), stringsAsFactors = FALSE)
}

# the fit for a season: prior seasons only, kept as coefficients
cfb_td_fit <- function(s, sch) {
  f <- cfb_path(sprintf("tdfit%d", CFB_TD_VER), s)
  if (file.exists(f)) {
    m <- tryCatch(readRDS(f), error = function(e) NULL)
    if (is.list(m) && !is.null(m$coef)) return(m)
  }
  ys <- max(min(CFB_SEASONS) + 1L, s - CFB_TD_YEARS):(s - 1L)
  if (length(ys) < 3L) return(NULL)
  tg <- cfb_td_teamctx(sch)
  prev <- cfb_td_box(ys[1] - 1L); rows <- list()
  for (y in ys) {
    p <- cfb_td_box(y)
    if (!is.null(p)) {
      r <- cfb_td_rows(p, prev, sch, tg)
      if (!is.null(r) && nrow(r)) {
        X <- cfb_td_x(r); X$td <- r$td
        rows[[length(rows) + 1L]] <- X[stats::complete.cases(X), , drop = FALSE]
      }
    }
    prev <- p; r <- NULL
    invisible(gc(verbose = FALSE))                       # keep the peak to one season's worth
  }
  X <- dplyr::bind_rows(rows); rm(rows)
  if (nrow(X) < 5000) return(NULL)
  # glm.fit on a bare matrix: a fraction of glm()'s memory (it keeps the data, a model frame
  # and fitted values) -- this runs inside the one R process every visitor shares
  M <- cbind(1, as.matrix(X[, CFB_TD_X[-1], drop = FALSE])); colnames(M) <- CFB_TD_X
  y <- X$td; n <- nrow(X); rt <- mean(y); rm(X); invisible(gc(verbose = FALSE))
  fit <- stats::glm.fit(M, y, family = stats::binomial())
  if (!isTRUE(fit$converged)) return(NULL)
  m <- list(coef = fit$coefficients, n = n, rate = rt, years = range(ys), ver = CFB_TD_VER)
  rm(fit, M, y); invisible(gc(verbose = FALSE))
  try(saveRDS(m, f), silent = TRUE)
  m
}
cfb_td_predict <- function(m, X) {
  b <- m$coef[CFB_TD_X]; b[is.na(b)] <- 0
  M <- cbind(1, as.matrix(X[, CFB_TD_X[-1], drop = FALSE]))
  as.vector(stats::plogis(M %*% b))
}

# every candidate's chance in each game of g (a week of d$sch), as of kickoff (or now)
cfb_td_week <- function(d, s, g, now = now_et(), recent = 1L) {
  if (is.null(g) || !nrow(g)) return(NULL)
  m <- cfb_td_fit(s, d$sch)
  if (is.null(m)) return(NULL)
  cur <- cfb_td_box(s); prev <- cfb_td_box(s - 1L)
  if (is.null(cur) && is.null(prev)) return(NULL)
  sch <- d$sch
  tg <- cfb_td_teamctx(sch)
  if (!is.null(cur)) {
    cur <- merge(cur, sch[, c("game_id", "ko")], by = "game_id")
    cur <- cur[!is.na(cur$ko), , drop = FALSE]
    gk <- paste(cur$game_id, cur$team_id)
    tt <- rowsum(cbind(cur$car, cur$rec), gk, reorder = FALSE)
    k <- match(gk, rownames(tt)); cur$t_car <- tt[k, 1]; cur$t_rec <- tt[k, 2]
  }
  ly <- cfb_td_lastyear(prev)
  ros <- cfb_td_roster(s)
  nm <- c(if (!is.null(cur)) stats::setNames(cur$name, cur$aid), if (!is.null(prev)) stats::setNames(prev$name, prev$aid))
  nm <- nm[!is.na(nm) & !duplicated(names(nm))]
  out <- list()
  for (i in seq_len(nrow(g))) {
    t0 <- if (is.na(g$ko[i])) now else min(g$ko[i], now + 365 * 86400)
    for (side in c("home", "away")) {
      tm <- if (side == "home") g$home_id[i] else g$away_id[i]
      op <- if (side == "home") g$away_id[i] else g$home_id[i]
      pre <- if (is.null(cur)) NULL else cur[cur$ko < t0, , drop = FALSE]
      tgames <- if (is.null(pre)) character(0) else unique(pre$game_id[pre$team_id == tm])
      tko <- if (length(tgames)) sort(unique(pre$ko[pre$team_id == tm]), decreasing = TRUE) else NULL
      if (length(tko)) {
        cand <- unique(pre$aid[pre$team_id == tm & pre$ko %in% head(tko, recent)])
      } else {
        # no game yet this season: last season's players who are on this year's roster
        # (graduates would otherwise be listed); without a roster, nobody until a game is played
        cand <- if (is.null(prev) || is.null(ros) || !any(ros$team_id == tm)) character(0) else
          intersect(unique(prev$aid), ros$aid[ros$team_id == tm])
      }
      if (!length(cand)) next
      h <- if (is.null(pre)) NULL else pre[pre$aid %in% cand, , drop = FALSE]
      agg <- data.frame(aid = cand, stringsAsFactors = FALSE)
      sm <- function(col) if (is.null(h) || !nrow(h)) rep(0, length(cand)) else
        as.vector(tapply(h[[col]], factor(h$aid, levels = cand), sum, default = 0))
      agg$n_prev <- if (is.null(h) || !nrow(h)) 0 else as.vector(table(factor(h$aid, levels = cand)))
      agg$s_car <- sm("car"); agg$s_rec <- sm("rec"); agg$s_ryd <- sm("ryd"); agg$s_cyd <- sm("cyd")
      agg$s_td <- if (is.null(h) || !nrow(h)) 0 else
        as.vector(tapply(h$rtd + h$ctd, factor(h$aid, levels = cand), sum, default = 0))
      agg$s_tcar <- sm("t_car"); agg$s_trec <- sm("t_rec")
      last <- if (is.null(h) || !nrow(h)) NULL else h[order(h$aid, -as.numeric(h$ko)), , drop = FALSE]
      last <- if (is.null(last)) NULL else last[!duplicated(last$aid), , drop = FALSE]
      agg$l_car <- if (is.null(last)) NA else last$car[match(cand, last$aid)]
      agg$l_rec <- if (is.null(last)) NA else last$rec[match(cand, last$aid)]
      j <- if (is.null(ly)) rep(NA_integer_, length(cand)) else match(cand, ly$aid)
      for (v in c("ly_car", "ly_rec", "ly_ryd", "ly_cyd", "ly_td", "ly_g"))
        agg[[v]] <- if (is.null(ly)) 0 else ifelse(is.na(j), 0, ly[[v]][j])
      agg <- agg[agg$n_prev > 0 | agg$ly_g > 0, , drop = FALSE]
      if (!nrow(agg)) next
      agg$e_pts <- cfb_td_pts(tg, s, tm, op, t0)
      X <- cfb_td_x(agg)
      ok <- stats::complete.cases(X)
      if (!any(ok)) next
      praw <- cfb_td_predict(m, X[ok, , drop = FALSE])
      out[[length(out) + 1L]] <- data.frame(
        game_id = g$game_id[i], team_id = tm, opp_id = op, aid = agg$aid[ok],
        name = unname(nm[agg$aid[ok]]), p = praw, p_raw = praw,
        car_pg = ifelse(agg$n_prev[ok] > 0, agg$s_car[ok] / agg$n_prev[ok], NA_real_),
        rec_pg = ifelse(agg$n_prev[ok] > 0, agg$s_rec[ok] / agg$n_prev[ok], NA_real_),
        td_n = agg$s_td[ok], gp = agg$n_prev[ok], kickoff = g$ko[i], stringsAsFactors = FALSE)
    }
  }
  if (!length(out)) return(NULL)
  x <- dplyr::bind_rows(out)
  # This board said 52.1% across 600 graded picks and 44.0% happened, an eight point
  # overprediction measured out of sample. The model underneath is fitted on prior seasons
  # only and is not wrong about who scores -- it is optimistic at the top of the board,
  # which is exactly what a recalibration is for.
  cal <- tryCatch(prop_calib("cfb", "anytime_td", suppressWarnings(min(g$ko, na.rm = TRUE))),
                  error = function(e) NULL)
  x$p <- prop_apply(x$p_raw, cal)
  # Report the first slate that actually gets a correction, not the first slate built --
  # the earliest week of the season has nothing before it by definition, and saying so
  # every run read as though the correction were never working.
  if (isTRUE(cal$ok)) {
    if (!isTRUE(.cfb_td_said)) {
      .cfb_td_said <<- TRUE
      mlog(sprintf("CFB td     | recalibrated on %d graded prop(s) settled before this slate: slope %.2f, shift %+.2f -- a raw 25%% becomes %.0f%%, a raw 60%% becomes %.0f%%",
                   cal$n, cal$a, cal$b,
                   100 * prop_apply(0.25, cal), 100 * prop_apply(0.60, cal)))
    }
  } else if (!isTRUE(.cfb_td_none)) {
    .cfb_td_none <<- TRUE
    mlog(sprintf("CFB td     | %d graded prop(s) on file; the earliest slates have nothing before them to correct against",
                 nrow(prop_read())))
  }
  # the result, once the game is in the box scores
  if (!is.null(cur)) {
    k <- match(paste(x$game_id, x$aid), paste(cur$game_id, cur$aid))
    played <- x$game_id %in% cur$game_id
    x$scored <- ifelse(!played, NA, ifelse(is.na(k), 0L, cur$td[k]))
  } else x$scored <- NA
  x[order(x$game_id, -x$p), , drop = FALSE]
}
CFB_TD_SHOW  <- 100L       # players listed in the weekly table

empty_ledger <- function() data.frame(
  game_id = character(0), season = integer(0), week = integer(0),
  home = character(0), away = character(0),
  kickoff = as.POSIXct(character(0), tz = TZ_ET),
  pred = numeric(0), conf = numeric(0), model_ver = character(0),
  locked_at = as.POSIXct(character(0), tz = TZ_ET),
  inputs_complete = logical(0), stringsAsFactors = FALSE)

read_ledger <- function() {
  if (!file.exists(LEDGER_FILE)) return(empty_ledger())
  L <- try(readRDS(LEDGER_FILE), silent = TRUE)
  if (inherits(L, "try-error") || !is.data.frame(L)) return(empty_ledger())
  L
}

append_ledger <- function(new) {
  L <- read_ledger()
  new <- new[!new$game_id %in% L$game_id, , drop = FALSE]
  if (nrow(new) == 0) return(invisible(L))
  # bind_rows, not rbind: a settled row later gains result columns (home_score,
  # away_score, won, settled_at), so the stored ledger is wider than a fresh pick.
  # rbind refuses that and the pick was lost instead of written.
  L <- dplyr::bind_rows(L, new)
  tmp <- paste0(LEDGER_FILE, ".tmp")
  saveRDS(L, tmp); file.rename(tmp, LEDGER_FILE)
  invisible(L)
}

inputs_complete <- function(d, s, ko) {
  need <- d$sch[which(d$sch$season == s & d$sch$final_at <= ko), ]
  nrow(need) == 0 || (all(need$has_score) && all(need$game_id %in% d$pbp_ids))
}

predict_games <- function(d, m, s, g, now) {
  if (nrow(g) == 0) return(numeric(0))
  cut <- as.POSIXct(pmin(as.numeric(g$ko), as.numeric(now)), origin = "1970-01-01", tz = TZ_ET)
  prev <- rate_teams(d$tw, s - 1, FAR_FUTURE, d$teams, carry = NULL)
  grp <- inclusion_groups(d$tw, d$pdl, s, cut)
  pred <- rep(NA_real_, nrow(g))
  for (k in unique(grp)) {
    ix <- which(grp == k); c1 <- cut[ix[1]]
    R <- rate_teams(d$tw, s, c1, d$teams, carry = prev)
    P <- pd_rating(d$pdl, s, c1, d$teams)
    pred[ix] <- project(m, g$week[ix],
                        as.numeric(R[g$home_team[ix]]) - as.numeric(R[g$away_team[ix]]),
                        as.numeric(P[g$home_team[ix]]) - as.numeric(P[g$away_team[ix]]),
                        as.numeric(g$a_qbchg[ix] %||% 0) - as.numeric(g$h_qbchg[ix] %||% 0))
  }
  pred
}

settle <- function(d, m, s, g, now) {
  L <- read_ledger()
  hit <- match(g$game_id, L$game_id); have <- !is.na(hit)
  pred <- rep(NA_real_, nrow(g)); conf <- pred
  pred[have] <- L$pred[hit[have]]; conf[have] <- L$conf[hit[have]]
  locked <- have
  todo <- which(!have)
  if (length(todo)) {
    pr <- predict_games(d, m, s, g[todo, , drop = FALSE], now)
    pred[todo] <- pr; conf[todo] <- conf_of(m, pr)
    new <- todo[!is.na(g$ko[todo]) & now >= g$ko[todo]]
    if (length(new)) {
      comp <- vapply(new, function(i) inputs_complete(d, s, g$ko[i]), logical(1))
      append_ledger(data.frame(
        game_id = g$game_id[new], season = as.integer(s), week = as.integer(g$week[new]),
        home = g$home_team[new], away = g$away_team[new], kickoff = g$ko[new],
        pred = pred[new], conf = conf[new], model_ver = MODEL_VER,
        locked_at = rep(now, length(new)), inputs_complete = comp,
        stringsAsFactors = FALSE))
      locked[new] <- TRUE
    }
  }
  list(pred = pred, conf = conf, locked = locked)
}

PLR_LEDGER <- file.path(LEDGER_DIR, "player_props.rds")

empty_plr_ledger <- function() data.frame(
  game_id = character(0), pid = character(0), pname = character(0),
  pos = character(0), team = character(0), oppt = character(0),
  season = integer(0), week = integer(0),
  kickoff = as.POSIXct(character(0), tz = TZ_ET),
  p_td = numeric(0), p_ry = numeric(0),
  o40 = numeric(0), o60 = numeric(0), o80 = numeric(0),
  f_opp_n = numeric(0), f_rz_opp = numeric(0), f_i5_opp = numeric(0),
  f_tgt = numeric(0), f_ypt = numeric(0), implied = numeric(0),
  gp_season = numeric(0), inj_tag = character(0),
  model_ver = character(0), locked_at = as.POSIXct(character(0), tz = TZ_ET),
  stringsAsFactors = FALSE)

read_plr_ledger <- function() {
  if (!file.exists(PLR_LEDGER)) return(empty_plr_ledger())
  L <- try(readRDS(PLR_LEDGER), silent = TRUE)
  if (inherits(L, "try-error") || !is.data.frame(L)) return(empty_plr_ledger())
  L
}

append_plr_ledger <- function(new) {
  L <- read_plr_ledger()
  k <- paste(new$game_id, new$pid)
  new <- new[!k %in% paste(L$game_id, L$pid), , drop = FALSE]
  if (nrow(new) == 0) return(invisible(L))
  L <- dplyr::bind_rows(L, new)
  tmp <- paste0(PLR_LEDGER, ".tmp")
  saveRDS(L, tmp); file.rename(tmp, PLR_LEDGER)
  invisible(L)
}

migrate_plr_ledger <- function(d) {
  L <- read_plr_ledger()
  if (nrow(L) == 0) return(invisible(FALSE))
  chg <- FALSE
  if (!"inj_tag" %in% names(L)) { L$inj_tag <- NA_character_; chg <- TRUE }
  j <- match(L$game_id, d$sch$game_id)
  bad <- is.na(L$week) & !is.na(j)
  if (any(bad)) { L$week[bad] <- d$sch$week[j][bad]; chg <- TRUE }
  bad <- is.na(L$season) & !is.na(j)
  if (any(bad)) { L$season[bad] <- d$sch$season[j][bad]; chg <- TRUE }
  old <- is.na(L$inj_tag) & !is.na(L$season) & !is.na(L$week)
  if (any(old)) {
    keep <- rep(TRUE, nrow(L)); tg <- L$inj_tag
    for (k in unique(paste(L$season[old], L$week[old]))) {
      i <- which(old & paste(L$season, L$week) == k)
      se <- L$season[i[1]]; wk <- L$week[i[1]]
      keep[i] <- plr_avail(d$ros, d$inj, se, wk, L$pid[i], L$team[i])
      tg[i] <- plr_flag(d$inj, se, wk, L$pid[i])
    }
    L$inj_tag <- tg
    if (!all(keep)) L <- L[keep, , drop = FALSE]
    chg <- TRUE
  }
  if (!chg) return(invisible(FALSE))
  tmp <- paste0(PLR_LEDGER, ".tmp")
  saveRDS(L, tmp); file.rename(tmp, PLR_LEDGER)
  invisible(TRUE)
}

plr_name <- function(d, team, pname, tag) {
  if (is.null(tag)) tag <- rep("", length(pname))
  tag <- ifelse(is.na(tag), "", tag)
  q <- ifelse(tag == "", "",
       ifelse(tag == "Q-DNP", '<span class="qt dnp">Q\u00b7DNP</span>',
                              '<span class="qt">Q</span>'))
  sprintf('%s<span class="tm">%s</span>%s',
          vapply(team, function(t) badge(d, t), ""), pname, q)
}

PLR_KEEP <- c("game_id","pid","pname","pos","season","week","kickoff","p_td","p_ry",
              "o40","o60","o80","f_opp_n","f_rz_opp","f_i5_opp","f_tgt","f_ypt","implied",
              "gp_season","inj_tag")

settle_players <- function(d, m, s, g, now) {
  if (nrow(g) == 0) return(NULL)
  L <- read_plr_ledger()
  Lg <- L[L$game_id %in% g$game_id, , drop = FALSE]
  fresh_g <- g[!g$game_id %in% Lg$game_id | is.na(g$ko) | now < g$ko, , drop = FALSE]
  fresh_g <- fresh_g[!fresh_g$game_id %in% Lg$game_id, , drop = FALSE]
  out <- list()
  if (nrow(Lg) > 0) {
    Lg$team <- Lg$team; Lg$locked <- TRUE
    out[[length(out) + 1]] <- Lg
  }
  todo <- g[!g$game_id %in% Lg$game_id, , drop = FALSE]
  if (nrow(todo) > 0) {
    cut <- as.POSIXct(pmin(as.numeric(todo$ko), as.numeric(now)),
                      origin = "1970-01-01", tz = TZ_ET)
    for (u in unique(as.numeric(cut))) {
      gi <- todo[as.numeric(cut) == u, , drop = FALSE]
      c1 <- as.POSIXct(u, origin = "1970-01-01", tz = TZ_ET)
      x <- project_players(d, m, s, gi, c1)
      if (is.null(x) || nrow(x) == 0) next
      x$team <- x$team_now; x$kickoff <- x$ko
      x$model_ver <- paste0(MODEL_VER, "/", PLR_VER); x$locked_at <- now
      x$locked <- !is.na(x$ko) & now >= x$ko
      out[[length(out) + 1]] <- x
      lk <- x[x$locked, , drop = FALSE]
      if (nrow(lk) > 0) {
        cols <- intersect(c(PLR_KEEP, "team", "oppt", "model_ver", "locked_at"), names(lk))
        append_plr_ledger(lk[, cols, drop = FALSE])
      }
    }
  }
  if (length(out) == 0) return(NULL)
  dplyr::bind_rows(out)
}

player_actuals <- function(d, g) {
  if (is.null(d$plr) || nrow(d$plr) == 0) return(NULL)
  a <- d$plr[d$plr$game_id %in% g$game_id, c("game_id", "pid", "td", "recyds"), drop = FALSE]
  if (nrow(a) == 0) return(NULL)
  a$key <- paste(a$game_id, a$pid); a
}

current_week <- function(sch, season_, now) {
  g <- sch[sch$season == season_ & !is.na(sch$ko), ]
  if (nrow(g) == 0) return(1L)
  up <- g$week[g$ko > now]
  if (length(up)) return(as.integer(min(up)))
  as.integer(max(g$week))
}

current_season <- function(sch, now) {
  s <- sch$season[!is.na(sch$ko) & sch$ko <= now + 30 * 86400]
  if (length(s) == 0) NA_integer_ else max(s)
}

badge <- function(d, t) sprintf(
  '<span class="bdg" style="background:%s">%s</span>',
  d$col[[t]],
  if (is.na(d$logo[[t]])) "" else
    sprintf('<img src="%s" onerror="this.remove()">', d$logo[[t]]))

prob_bar <- function(p, hi = 0.65) {
  ifelse(is.na(p), "\u2014", sprintf(
    '<div class="cf"><span class="cfn">%d%%</span><span class="cft"><span class="cfb" style="width:%.0f%%;background:%s"></span></span></div>',
    round(p * 100), 100 * pmin(pmax(p / hi, 0.04), 1), conf_col(0.5 + 0.30 * pmin(p / hi, 1))))
}


# ==================== NHL ====================
NHL_VER      <- 1L
NHL_SEASONS  <- 2015:2026
NHL_LAM      <- 30
NHL_PW       <- 20
NHL_PW_G     <- 10
NHL_RHO      <- 0.4
NHL_END_LAM  <- 30
NHL_GS_KP    <- 15
NHL_GS_BASE  <- c(C = 0.1846, D = 0.0702, L = 0.1928, R = 0.2039)
NHL_GS_RECENT <- 10L
# Goaltending. The save percentage of a goalie with few shots behind him says almost
# nothing, so it is shrunk hard toward the era average -- 750 shots is about a third of
# a starter's season. The result is turned into goals per game at a typical shot volume,
# which is the unit the margin model already works in.
NHL_GK_LG   <- 0.905   # era average save percentage: the shrinkage target
NHL_GK_KS   <- 750     # shots of shrinkage toward it
NHL_GK_SPG  <- 30      # shots a starter faces in a typical game
NHL_GK_LOOK <- 10L     # how many of a team's recent games are looked at
NHL_GK_HL   <- 3       # starts of half-life: the last start counts most, and a goalie
                       # who has just taken over outvotes one who started more often
                       # a fortnight ago. A flat vote took five games to notice a change.
NHL_MIN_UNIQ <- 5L
NHL_LEDGER   <- file.path(LEDGER_DIR, "nhl_predictions.rds")
NHL_MODEL    <- sprintf("nhl-marg-v%d", NHL_VER)

nhl_dir <- file.path(CACHE_DIR, "nhl")
dir.create(nhl_dir, showWarnings = FALSE, recursive = TRUE)
nhl_path <- function(k, y = NULL)
  file.path(nhl_dir, if (is.null(y)) sprintf("%s_v%d.rds", k, NHL_VER)
            else sprintf("%s_v%d_%d.rds", k, NHL_VER, y))

nhl_season_of <- function(d) {
  d <- as.Date(d); y <- as.integer(format(d, "%Y"))
  ifelse(as.integer(format(d, "%m")) >= 8L, y, y - 1L)
}

nhl_sync <- function(force = FALSE) {
  cur <- nhl_season_of(now_et())
  for (y in NHL_SEASONS) {
    sf <- nhl_path("sch", y)
    if (force || (y >= cur && age_min(sf) > SDV_REFRESH_MIN)) unlink(sf)
    sdv_fetch("nhl_schedules", sprintf("nhl_schedule_%d.rds", y + 1L), sf)
    pf <- nhl_path("pb", y)
    if (force || (y >= cur && age_min(pf) > SDV_REFRESH_MIN)) unlink(pf)
    sdv_fetch("nhl_player_boxscores", sprintf("player_box_%d.rds", y + 1L), pf)
  }
  f <- vapply(NHL_SEASONS, function(y) nhl_path("sch", y), "")
  f <- f[file.exists(f)]
  if (!length(f)) stop("Could not load NHL data. Check your connection.")
  paste(f, as.numeric(file.mtime(f)), collapse = "|")
}

nhl_sched <- function() {
  out <- lapply(NHL_SEASONS, function(y) {
    f <- nhl_path("sch", y); if (!file.exists(f)) return(NULL)
    d <- try(readRDS(f), silent = TRUE); if (inherits(d, "try-error")) return(NULL)
    d <- as.data.frame(d)
    need <- c("game_id", "game_type", "game_date", "home_team_abbr", "away_team_abbr",
              "home_score", "away_score")
    if (!all(need %in% names(d))) return(NULL)
    d <- d[d$game_type == "R", ]
    tm <- if ("game_time" %in% names(d)) as.character(d$game_time) else rep(NA_character_, nrow(d))
    tm[is.na(tm) | tm == ""] <- "19:00"
    ko <- as.POSIXct(paste(d$game_date, tm), format = "%Y-%m-%d %H:%M", tz = "UTC")
    bad <- is.na(ko)
    ko[bad] <- as.POSIXct(paste(d$game_date[bad], "19:00"), format = "%Y-%m-%d %H:%M", tz = "UTC")
    nm <- function(a, b) if (a %in% names(d)) as.character(d[[a]]) else rep(NA_character_, nrow(d))
    data.frame(game_id = as.character(d$game_id), date = as.Date(d$game_date), ko = ko,
               home = as.character(d$home_team_abbr), away = as.character(d$away_team_abbr),
               home_name = nm("home_team_name"), away_name = nm("away_team_name"),
               home_score = suppressWarnings(as.numeric(d$home_score)),
               away_score = suppressWarnings(as.numeric(d$away_score)),
               stringsAsFactors = FALSE)
  })
  s <- dplyr::bind_rows(out)
  if (!nrow(s)) stop("No NHL schedule could be loaded.")
  s <- s[!is.na(s$ko) & !is.na(s$home) & !is.na(s$away), ]
  s <- s[!duplicated(s$game_id), ]
  lv <- tryCatch(nhl_live_sched(nhl_season_of(now_et())), error = function(e) NULL)
  if (!is.null(lv) && nrow(lv)) {
    j <- match(s$game_id, lv$game_id); fx <- !is.na(j) & !is.na(lv$ko[j])
    if (any(fx)) s$ko[fx] <- lv$ko[j[fx]]               # the season files often lack a start time
    # The season files run a day or more behind on last night's results. Where the live
    # feed already calls a game final and carries its score, that score wins -- otherwise
    # a finished game sits with no result until the season file catches up.
    if (!("api_final" %in% names(s))) s$api_final <- NA
    hv <- !is.na(j) & !is.na(lv$api_final[j]) & lv$api_final[j] &
          !is.na(lv$home_score[j]) & !is.na(lv$away_score[j])
    if (any(hv)) {
      s$home_score[hv] <- lv$home_score[j[hv]]
      s$away_score[hv] <- lv$away_score[j[hv]]
      s$api_final[hv]  <- TRUE
    }
    lv <- lv[!(lv$game_id %in% s$game_id), , drop = FALSE]
    if (nrow(lv)) {
      attr(lv$ko, "tzone") <- attr(s$ko, "tzone")
      s <- dplyr::bind_rows(s, lv)
    }
  }
  s$season <- nhl_season_of(s$date)
  attr(s$ko, "tzone") <- TZ_ET
  s$final_at  <- s$ko + 4 * 3600
  if ("api_final" %in% names(s)) {
    af <- !is.na(s$api_final) & s$api_final
    if (any(af)) s$final_at[af] <- s$ko[af]
  }
  s$has_score <- !is.na(s$home_score) & !is.na(s$away_score)
  u <- tapply(s$home_score[s$has_score], s$season[s$has_score],
              function(x) length(unique(x[!is.na(x)])))
  n <- tapply(s$home_score[s$has_score], s$season[s$has_score], length)
  bad <- as.integer(names(u))[u < NHL_MIN_UNIQ & n[names(u)] >= NHL_CORRUPT_N]
  s$corrupt <- s$season %in% bad
  s[order(s$ko), ]
}

nhl_panel <- function(sch) {
  g <- sch[sch$has_score & !sch$corrupt, ]
  if (!nrow(g)) return(NULL)
  mk <- function(t, o, gf, ga, h) data.frame(
    game_id = g$game_id, season = g$season, date = g$date, ko = g$ko,
    team = t, opp = o, gf = gf, ga = ga, home = h, stringsAsFactors = FALSE)
  p <- rbind(mk(g$home, g$away, g$home_score, g$away_score, 1L),
             mk(g$away, g$home, g$away_score, g$home_score, 0L))
  p$marg <- p$gf - p$ga
  p$hfa  <- ifelse(p$home == 1L, 1, -1)
  p[order(p$ko), ]
}

nhl_rate <- function(g, ents, lam, prior = NULL, pw = 0) {
  n <- length(ents); idx <- stats::setNames(seq_len(n), ents)
  A <- matrix(0, n + 1L, n + 1L); b <- numeric(n + 1L)
  if (nrow(g) > 0) {
    ti <- idx[g$team]; oi <- idx[g$opp]
    ok <- !is.na(ti) & !is.na(oi)
    ti <- ti[ok]; oi <- oi[ok]; y <- g$marg[ok]; h <- g$hfa[ok]
    m <- length(y)
    if (m > 0) {
      X <- Matrix::sparseMatrix(i = rep(seq_len(m), 3L), j = c(ti, oi, rep(n + 1L, m)),
                                x = c(rep(1, m), rep(-1, m), h), dims = c(m, n + 1L))
      A <- as.matrix(Matrix::crossprod(X)); b <- as.numeric(Matrix::crossprod(X, y))
    }
  }
  dd <- cbind(seq_len(n), seq_len(n))
  A[dd] <- A[dd] + lam
  if (!is.null(prior) && pw > 0) {
    pv <- prior[ents]; pv[is.na(pv)] <- 0
    A[dd] <- A[dd] + pw; b[seq_len(n)] <- b[seq_len(n)] + pw * pv
  }
  A[n + 1L, n + 1L] <- A[n + 1L, n + 1L] + 1e-6
  x <- try(solve(A, b), silent = TRUE)
  if (inherits(x, "try-error")) return(stats::setNames(numeric(n), ents))
  r <- stats::setNames(x[seq_len(n)], ents)
  r - mean(r)
}

nhl_end <- function(panel) {
  f <- nhl_path("end")
  e <- if (file.exists(f)) try(readRDS(f), silent = TRUE) else NULL
  if (inherits(e, "try-error") || !is.list(e)) e <- list()
  cur <- max(panel$season)
  ents <- sort(unique(c(panel$team, panel$opp)))
  for (s in sort(unique(panel$season))) {
    g <- panel[panel$season == s, ]
    if (nrow(g) < 400) next
    k <- as.character(s)
    if (!is.null(e[[k]]) && s < cur) next
    e[[k]] <- nhl_rate(g, ents, NHL_END_LAM)
  }
  try(saveRDS(e, f), silent = TRUE)
  e
}

nhl_prior <- function(endr, season_) {
  ks <- suppressWarnings(as.integer(names(endr)))
  ks <- ks[!is.na(ks) & ks < season_]
  if (!length(ks)) return(NULL)
  if (max(ks) != season_ - 1L) return(NULL)
  endr[[as.character(max(ks))]] * NHL_RHO
}

nhl_rows <- function(panel, endr, ents, upto, gf = NULL) {
  f <- nhl_path("rows")
  R <- if (file.exists(f)) try(readRDS(f), silent = TRUE) else NULL
  if (inherits(R, "try-error") || !is.data.frame(R)) R <- NULL
  have <- if (is.null(R)) integer(0) else unique(R$season)
  want <- sort(unique(panel$season[panel$season < upto]))
  miss <- setdiff(want, have)
  if (!length(miss)) return(nhl_rows_gd(R, gf))
  add <- list()
  for (s in miss) {
    sg <- panel[panel$season == s, ]
    if (!nrow(sg)) next
    pr <- nhl_prior(endr, s)
    for (d in sort(unique(sg$date))) {
      hist <- sg[sg$date < d, ]
      gp <- if (nrow(hist)) nrow(hist) / max(1L, length(unique(hist$team))) else 0
      r <- nhl_rate(hist, ents, NHL_LAM, pr, NHL_PW / (1 + gp / NHL_PW_G))
      tw <- sg[sg$date == d & sg$home == 1L, ]
      if (!nrow(tw)) next
      add[[length(add) + 1L]] <- data.frame(
        season = s, game_id = tw$game_id,
        rd = unname(r[tw$team]) - unname(r[tw$opp]), marg = tw$marg,
        stringsAsFactors = FALSE)
    }
  }
  R <- dplyr::bind_rows(R, dplyr::bind_rows(add))
  R <- R[!is.na(R$rd) & !is.na(R$marg), ]
  try(saveRDS(R, f), silent = TRUE)
  nhl_rows_gd(R, gf)
}

# The goalie column is attached rather than stored, because it depends only on the game
# id: that way adding it costs nothing and does not throw away a rating cache that took
# eleven seasons of walk-forward passes to build.
nhl_rows_gd <- function(R, gf) {
  if (is.null(R) || !nrow(R)) return(R)
  R$gd <- if (is.null(gf) || !nrow(gf)) 0 else {
    v <- gf$gd[match(as.character(R$game_id), as.character(gf$game_id))]
    ifelse(is.na(v), 0, v)
  }
  R
}

nhl_fit <- function(R, season_) {
  h <- R[R$season < season_, ]
  if (nrow(h) < 1200) return(NULL)
  # Only ask for a goalie term if there is a goalie signal in the training seasons to
  # measure it from. Where there is not, this is exactly the model it has always been.
  use_gd <- "gd" %in% names(h) && sum(abs(h$gd) > 1e-8, na.rm = TRUE) >= 500 &&
            stats::sd(h$gd, na.rm = TRUE) > 1e-6
  m1 <- stats::lm(marg ~ rd, data = h)
  gd_b <- NA_real_; gd_se <- NA_real_
  if (use_gd) {
    m2 <- stats::lm(marg ~ rd + gd, data = h)
    cf <- tryCatch(summary(m2)$coefficients, error = function(e) NULL)
    if (!is.null(cf) && "gd" %in% rownames(cf)) {
      gd_b <- cf["gd", 1]; gd_se <- cf["gd", 2]
    }
    # A goalie expected to save more goals cannot make his team lose by more, so a
    # negative coefficient is noise wearing a result's clothes. Two standard errors and
    # the right sign, or the term does not go in the model at all.
    if (is.finite(gd_b) && is.finite(gd_se) && gd_b > 0 && gd_b > 2 * gd_se) m1 <- m2
    else use_gd <- FALSE
  }
  h$pred <- stats::predict(m1)
  h <- h[h$marg != 0, ]; h$win <- as.integer(h$marg > 0)
  lg <- suppressWarnings(stats::glm(win ~ pred, data = h, family = stats::binomial()))
  # said once per run, not once per day page
  if (!isTRUE(.nhl_gk$said)) {
    .nhl_gk$said <- TRUE
    if (is.finite(gd_b)) {
      mlog(sprintf("NHL goalie | measured %+.2f goals of margin per goal of starter edge (se %.2f) on %d prior-season game(s) -- %s",
                   gd_b, gd_se, nrow(h),
                   if (use_gd) "used" else "NOT used: needs the right sign and two standard errors"))
    } else {
      mlog(sprintf("NHL goalie | too little starter signal in the prior seasons to measure: team-only model, %d game(s)", nrow(h)))
    }
  }
  list(marg = m1, conf = lg, n = nrow(h), gd = use_gd, gd_beta = gd_b, gd_se = gd_se)
}

nhl_predict <- function(panel, endr, ents, m, g, cutoff, gf = NULL) {
  if (is.null(m) || !nrow(g)) return(NULL)
  s <- g$season[1]
  # v2: ratings use games from EARLIER dates only -- the same rule the walk-forward
  # training rows use (and the NHL kickoff times are not reliably time-zoned).
  hist <- panel[panel$season == s & panel$date < min(g$date) & panel$ko < cutoff, ]
  pr <- nhl_prior(endr, s)
  gp <- if (nrow(hist)) nrow(hist) / max(1L, length(unique(hist$team))) else 0
  r <- nhl_rate(hist, ents, NHL_LAM, pr, NHL_PW / (1 + gp / NHL_PW_G))
  rd <- unname(r[g$home]) - unname(r[g$away])
  rd[is.na(rd)] <- 0
  gd <- if (is.null(gf) || !nrow(gf)) rep(0, nrow(g)) else {
    v <- gf$gd[match(as.character(g$game_id), as.character(gf$game_id))]
    ifelse(is.na(v), 0, v)
  }
  pred <- as.numeric(stats::predict(m$marg, newdata = data.frame(rd = rd, gd = gd)))
  conf <- as.numeric(stats::predict(m$conf, newdata = data.frame(pred = pred), type = "response"))
  data.frame(game_id = g$game_id, season = s, rd = rd, gd = gd, pred = pred,
             conf = pmax(conf, 1 - conf), stringsAsFactors = FALSE)
}

# Every goalie appearance the season files know about.
#
# In this feed a goalie is a row with no position but a shot count, and time on ice is
# "mm:ss" text rather than a number, which is why it reads as missing if taken directly.
nhl_goalies <- function(sch) {
  out <- lapply(NHL_SEASONS, function(y) {
    f <- nhl_path("pb", y); if (!file.exists(f)) return(NULL)
    d <- try(readRDS(f), silent = TRUE); if (inherits(d, "try-error")) return(NULL)
    d <- as.data.frame(d)
    need <- c("game_id", "player_id", "team_abbrev", "shots_against", "saves")
    if (!all(need %in% names(d))) return(NULL)
    sa <- suppressWarnings(as.numeric(d$shots_against))
    keep <- !is.na(d$game_id) & !is.na(sa)
    if ("position" %in% names(d)) keep <- keep & is.na(d$position)
    d <- d[keep, , drop = FALSE]
    if (!nrow(d)) return(NULL)
    data.frame(game_id = as.character(d$game_id), pid = as.character(d$player_id),
               team = as.character(d$team_abbrev),
               shots = suppressWarnings(as.numeric(d$shots_against)),
               saves = suppressWarnings(as.numeric(d$saves)),
               toi = if ("toi" %in% names(d)) vapply(d$toi, nhl_mmss, 0, USE.NAMES = FALSE)
                     else rep(NA_real_, nrow(d)),
               stringsAsFactors = FALSE)
  })
  g <- dplyr::bind_rows(out)
  lv <- .nhl_gk$log
  if (!is.null(lv) && nrow(lv)) {
    lv <- lv[, intersect(c("game_id", "pid", "team", "shots", "saves", "toi"), names(lv)), drop = FALSE]
    if (nrow(g)) lv <- lv[!(lv$game_id %in% g$game_id), , drop = FALSE]
    if (nrow(lv)) g <- dplyr::bind_rows(g, lv)
  }
  if (!nrow(g)) return(NULL)
  j <- match(g$game_id, sch$game_id)
  g$date <- sch$date[j]; g$season <- sch$season[j]
  g <- g[!is.na(g$date) & !is.na(g$pid) & nzchar(g$pid), , drop = FALSE]
  if (!nrow(g)) return(NULL)
  # the starter is whoever faced the most of his team's shots in that game
  g$started <- FALSE
  k <- paste(g$game_id, g$team)
  for (u in unique(k)) {
    i <- which(k == u)
    w <- if (any(!is.na(g$toi[i]))) g$toi[i] else g$shots[i]
    g$started[i[which.max(ifelse(is.na(w), -1, w))]] <- TRUE
  }
  g[order(g$date), , drop = FALSE]
}

# How much better or worse than average the likely starters are, in goals, for every
# game -- using nothing but games already played when that game started.
#
# The likely starter rather than the actual one on purpose: that is all that is knowable
# before a game, so measuring it that way is the only way the fitted coefficient means
# anything when it is used on a game that has not been played.
nhl_gk_feature <- function(gl, sch) {
  if (is.null(gl) || !nrow(gl) || is.null(sch) || !nrow(sch)) return(NULL)
  gl <- gl[order(gl$date), , drop = FALSE]
  # each goalie's record BEFORE each of his own appearances
  o <- order(gl$pid, gl$date)
  q <- gl[o, , drop = FALSE]
  sv <- ifelse(is.na(q$saves), 0, q$saves)
  sh <- ifelse(is.na(q$shots), 0, q$shots)
  cum <- function(x, grp) stats::ave(x, grp, FUN = cumsum)
  q$cs <- cum(sv, q$pid) - sv
  q$ch <- cum(sh, q$pid) - sh
  q$eff <- ((q$cs + NHL_GK_KS * NHL_GK_LG) / (q$ch + NHL_GK_KS) - NHL_GK_LG) * NHL_GK_SPG
  gl <- q[order(q$date), , drop = FALSE]

  # a goalie's standing as of a date, and a team's likely starter as of a date
  st <- gl[gl$started %in% TRUE, , drop = FALSE]
  if (!nrow(st)) return(NULL)
  rows <- list()
  for (tm in unique(st$team)) {
    s <- st[st$team == tm, , drop = FALSE]
    s <- s[order(s$date), , drop = FALSE]
    if (!nrow(s)) next
    exp_pid <- rep(NA_character_, nrow(s)); exp_eff <- rep(NA_real_, nrow(s))
    for (i in seq_len(nrow(s))) {
      lo <- max(1L, i - NHL_GK_LOOK); hi <- i - 1L
      if (hi < lo) next
      w <- rev(s$pid[lo:hi])                     # most recent start first
      wt <- 0.5 ^ ((seq_along(w) - 1L) / NHL_GK_HL)
      tb <- sort(tapply(wt, w, sum), decreasing = TRUE)
      pid <- names(tb)[1]
      exp_pid[i] <- pid
      # That goalie's standing as of this date, measured against what this team's
      # goaltending has been overall.
      #
      # Against the team's own baseline on purpose. The team rating is built from goal
      # margins, which already contain whatever the goalies did, so a goalie's absolute
      # quality is largely in the rating twice over -- and measured that way it came out
      # with the wrong sign. What the rating cannot know is which of a team's goalies is
      # in tonight, and that is exactly this.
      h <- gl[gl$pid == pid & gl$date < s$date[i], , drop = FALSE]
      me <- if (nrow(h)) h$eff[nrow(h)] else 0
      tb2 <- gl[gl$team == tm & gl$date < s$date[i], , drop = FALSE]
      base <- if (nrow(tb2) && sum(tb2$shots, na.rm = TRUE) > 0)
        stats::weighted.mean(tb2$eff, pmax(tb2$shots, 0), na.rm = TRUE) else 0
      exp_eff[i] <- me - (if (is.finite(base)) base else 0)
    }
    rows[[length(rows) + 1L]] <- data.frame(game_id = s$game_id, team = tm,
                                            gk = exp_pid, eff = exp_eff,
                                            stringsAsFactors = FALSE)
  }
  if (!length(rows)) return(NULL)
  E <- dplyr::bind_rows(rows)
  hm <- E[match(paste(sch$game_id, sch$home), paste(E$game_id, E$team)), ]
  aw <- E[match(paste(sch$game_id, sch$away), paste(E$game_id, E$team)), ]
  gd <- ifelse(is.na(hm$eff) | is.na(aw$eff), 0, hm$eff - aw$eff)
  data.frame(game_id = as.character(sch$game_id), gd = as.numeric(gd),
             gk_home = hm$gk, gk_away = aw$gk, stringsAsFactors = FALSE)
}

nhl_skaters <- function(sch) {
  out <- lapply(NHL_SEASONS, function(y) {
    f <- nhl_path("pb", y); if (!file.exists(f)) return(NULL)
    d <- try(readRDS(f), silent = TRUE); if (inherits(d, "try-error")) return(NULL)
    d <- as.data.frame(d)
    need <- c("game_id", "player_id", "player_name", "position", "goals", "team_abbrev")
    if (!all(need %in% names(d))) return(NULL)
    # Goalies carry no position in this feed, so they fall out here as NA rather than
    # as "G" -- without the is.na guard they came through as rows of nothing.
    d <- d[!is.na(d$game_id) & !is.na(d$position) & d$position != "G", ]
    if (!nrow(d)) return(NULL)
    data.frame(game_id = as.character(d$game_id), pid = as.character(d$player_id),
               pname = as.character(d$player_name), pos = as.character(d$position),
               team = as.character(d$team_abbrev),
               goals = suppressWarnings(as.numeric(d$goals)), stringsAsFactors = FALSE)
  })
  k <- dplyr::bind_rows(out)
  lv <- tryCatch(nhl_live_box(sch), error = function(e) NULL)
  if (!is.null(lv) && nrow(lv)) {
    if (nrow(k)) lv <- lv[!(lv$game_id %in% k$game_id), , drop = FALSE]
    if (nrow(lv)) k <- dplyr::bind_rows(k, lv)
  }
  if (!nrow(k)) return(NULL)
  j <- match(k$game_id, sch$game_id)
  k$date <- sch$date[j]; k$ko <- sch$ko[j]; k$season <- sch$season[j]
  k <- k[!is.na(k$ko) & !is.na(k$goals), ]
  k$scored <- as.integer(k$goals > 0)
  k[order(k$ko), ]
}

NHL_INJ_URL <- "https://site.api.espn.com/apis/site/v2/sports/hockey/nhl/injuries"
NHL_INJ_TTL <- 30
NHL_INJ_OUT <- c("injured reserve", "out", "long term injured reserve",
                 "suspension", "suspended", "not with team")

NHL_ACC_CP <- c(224:229, 232:235, 236:239, 242:246, 248:252, 253, 255, 231, 241)
NHL_ACC_RP <- utf8ToInt("aaaaaaeeeeiiiioooooouuuuyycn")

nhl_norm <- function(x) {
  x <- as.character(x); x[is.na(x)] <- ""
  vapply(x, function(s) {
    if (!nzchar(s)) return("")
    Encoding(s) <- "UTF-8"
    cp <- tryCatch(utf8ToInt(s), error = function(e) NULL)
    if (is.null(cp) || anyNA(cp)) return(gsub("[^a-z0-9]", "", tolower(s)))
    k <- match(cp, NHL_ACC_CP)
    cp[!is.na(k)] <- NHL_ACC_RP[k[!is.na(k)]]
    gsub("[^a-z0-9]", "", tolower(intToUtf8(cp)))
  }, "", USE.NAMES = FALSE)
}

# Who is unavailable, from ESPN's injury feed. One fetcher for every league: the NHL
# gate proved the shape, and basketball needs exactly the same thing.
espn_inj <- function(url, f, ttl, out_set, timeout = 15) {
  cached <- function() {
    o <- try(readRDS(f), silent = TRUE)
    if (!inherits(o, "try-error") && is.data.frame(o) && nrow(o)) o else NULL
  }
  if (file.exists(f) && age_min(f) < ttl) {
    o <- cached(); if (!is.null(o)) return(o)
  }
  r <- tryCatch(httr::GET(url, httr::timeout(timeout)), error = function(e) NULL)
  if (is.null(r) || !identical(httr::status_code(r), 200L)) return(cached())
  j <- tryCatch(jsonlite::fromJSON(httr::content(r, "text", encoding = "UTF-8"),
                                   simplifyVector = FALSE), error = function(e) NULL)
  if (is.null(j) || is.null(j$injuries)) return(cached())
  rows <- list()
  for (tm in j$injuries) {
    tn <- as.character(tm$displayName %||% "")
    for (i in (tm$injuries %||% list())) {
      a <- i$athlete
      if (is.null(a)) next
      rows[[length(rows) + 1L]] <- data.frame(
        team_name = tn,
        short  = as.character(a$shortName %||% ""),
        full   = as.character(a$displayName %||% ""),
        status = as.character(i$status %||% ""),
        kind   = as.character(i$details$type %||% ""),
        stringsAsFactors = FALSE)
    }
  }
  if (!length(rows)) return(cached())
  d <- dplyr::bind_rows(rows)
  d$tkey <- nhl_norm(d$team_name)
  d$pkey <- nhl_norm(d$short)
  d$out  <- tolower(trimws(d$status)) %in% out_set
  dir.create(dirname(f), recursive = TRUE, showWarnings = FALSE)
  try(saveRDS(d, f), silent = TRUE)
  d
}

# the team-name-to-abbreviation bridge, which every league needs the same way
espn_team_key <- function(sch) {
  nm <- c(stats::setNames(sch$home_name, sch$home),
          stats::setNames(sch$away_name, sch$away))
  nm <- nm[!is.na(nm) & nzchar(nm)]
  nm <- nm[!duplicated(paste(names(nm), nm))]
  stats::setNames(names(nm), nhl_norm(nm))
}

# Drops anyone ruled out, and labels the rest with their status. Shared because a board
# that lists a player who is not playing is wrong in exactly one way in every sport.
espn_inj_gate <- function(x, inj, tkey) {
  x$inj <- NA_character_
  if (is.null(inj) || !nrow(inj) || is.null(tkey) || !length(tkey)) return(x)
  inj$abbr <- unname(tkey[inj$tkey])
  inj <- inj[!is.na(inj$abbr), , drop = FALSE]
  if (!nrow(inj)) return(x)
  j <- match(paste(x$team, nhl_norm(x$pname)), paste(inj$abbr, inj$pkey))
  hit <- !is.na(j)
  x$inj[hit] <- inj$status[j[hit]]
  gone <- rep(FALSE, nrow(x))
  gone[hit] <- inj$out[j[hit]] %in% TRUE
  x[!gone, , drop = FALSE]
}

nhl_inj <- function()
  espn_inj(NHL_INJ_URL, file.path(nhl_live_dir, "inj.rds"), NHL_INJ_TTL,
           NHL_INJ_OUT, timeout = NHL_API_TO)

nhl_team_key <- function(sch) espn_team_key(sch)

nhl_gs <- function(K, cutoff, teams, inj = NULL, tkey = NULL) {
  if (is.null(K) || !nrow(K)) return(NULL)
  h <- K[K$ko < cutoff, ]
  if (!nrow(h)) return(NULL)
  ag <- stats::aggregate(cbind(n = rep(1, nrow(h)), g = h$scored) ~ pid, data = h, FUN = sum)
  last <- h[!duplicated(h$pid, fromLast = TRUE), c("pid", "pname", "pos", "team", "ko")]
  x <- merge(ag, last, by = "pid")
  rec <- h[h$team %in% teams, ]
  if (nrow(rec)) {
    keep <- unlist(lapply(split(rec, rec$team), function(z) {
      g <- unique(z$game_id[order(z$ko, decreasing = TRUE)])
      unique(z$pid[z$game_id %in% utils::head(g, NHL_GS_RECENT)])
    }), use.names = FALSE)
    x <- x[x$pid %in% keep & x$team %in% teams, ]
  } else x <- x[0, ]
  if (!nrow(x)) return(NULL)
  x$inj <- NA_character_
  if (!is.null(inj) && nrow(inj) && !is.null(tkey) && length(tkey)) {
    inj$abbr <- unname(tkey[inj$tkey])
    inj <- inj[!is.na(inj$abbr), , drop = FALSE]
    if (nrow(inj)) {
      j <- match(paste(x$team, nhl_norm(x$pname)), paste(inj$abbr, inj$pkey))
      hit <- !is.na(j)
      x$inj[hit] <- inj$status[j[hit]]
      gone <- rep(FALSE, nrow(x))
      gone[hit] <- isTRUE(TRUE) & inj$out[j[hit]]
      x <- x[!gone, , drop = FALSE]
    }
  }
  if (!nrow(x)) return(NULL)
  b <- unname(NHL_GS_BASE[x$pos]); b[is.na(b)] <- 0.15
  x$p <- pmin(pmax((x$g + NHL_GS_KP * b) / (x$n + NHL_GS_KP), 0.004), 0.60)
  x[order(-x$p), c("pid", "pname", "pos", "team", "n", "g", "p", "inj")]
}

NHL_ESPN_AB <- c(LAK = "la", NJD = "nj", SJS = "sj", TBL = "tb")

nhl_logo <- function(ab) {
  a <- as.character(ab)
  e <- ifelse(!is.na(a) & a %in% names(NHL_ESPN_AB), unname(NHL_ESPN_AB[a]), a)
  ifelse(is.na(a) | !nzchar(a), NA_character_,
         sprintf("https://a.espncdn.com/i/teamlogos/nhl/500/%s.png", tolower(e)))
}

nhl_names <- function(sch) {
  tn <- rbind(
    data.frame(ab = sch$home, nm = sch$home_name, ko = sch$ko, stringsAsFactors = FALSE),
    data.frame(ab = sch$away, nm = sch$away_name, ko = sch$ko, stringsAsFactors = FALSE))
  tn <- tn[!is.na(tn$ab) & nzchar(tn$ab) & !is.na(tn$nm) & nzchar(tn$nm), , drop = FALSE]
  if (!nrow(tn)) return(stats::setNames(character(0), character(0)))
  tn <- tn[order(tn$ko), , drop = FALSE]
  tn <- tn[!duplicated(tn$ab, fromLast = TRUE), , drop = FALSE]
  stats::setNames(tn$nm, tn$ab)
}

nhl_current_season <- function(sch, now) {
  y <- sch$season[!is.na(sch$ko) & sch$ko <= now]
  if (!length(y)) return(max(sch$season))
  as.integer(max(y))
}

nhl_gk_report <- function(gkl, gf) {
  if (is.null(gkl) || !nrow(gkl)) {
    mlog("NHL goalie | no goalie appearances found: the model stays team-only")
    return(invisible(NULL))
  }
  st <- gkl[gkl$started %in% TRUE, , drop = FALSE]
  mlog(sprintf("NHL goalie | %d appearance(s), %d start(s), %d goalie(s), %d season(s) %d-%d",
               nrow(gkl), nrow(st), length(unique(gkl$pid)),
               length(unique(gkl$season)), min(gkl$season, na.rm = TRUE),
               max(gkl$season, na.rm = TRUE)))
  if (is.null(gf) || !nrow(gf)) {
    mlog("NHL goalie | no usable starter differential")
  } else {
    nz <- abs(gf$gd) > 1e-8
    mlog(sprintf("NHL goalie | starter edge on %d of %d game(s) (%.0f%%); sd %.3f, range %+.2f to %+.2f goals",
                 sum(nz), nrow(gf), 100*mean(nz), stats::sd(gf$gd[nz]),
                 min(gf$gd), max(gf$gd)))
  }
  invisible(NULL)
}

nhl_live_report <- function(sch, k) {
  a <- nhl_api_stats()
  cur <- nhl_season_of(now_et())
  g <- sch[sch$season == cur & sch$has_score, , drop = FALSE]
  got <- if (is.null(k) || !nrow(k)) character(0) else unique(k$game_id)
  miss <- setdiff(g$game_id, got)
  last <- if (!nrow(g)) "none" else
    sprintf("%s (game %s)", format(max(g$date, na.rm = TRUE)), max(g$game_id))
  mlog(sprintf("NHL        | %d final game(s) this season, %d with box scores, %d missing%s",
               nrow(g), length(intersect(g$game_id, got)), length(miss),
               if (isTRUE(a$dead)) " -- API breaker tripped" else ""))
  mlog(sprintf("NHL        | latest final: %s | today %s has %d game(s), %d final | feed %d hit / %d fetched",
               last, format(today_et()),
               sum(sch$date == today_et(), na.rm = TRUE),
               sum(sch$date == today_et() & sch$has_score, na.rm = TRUE),
               a$hits, a$miss))
  gk <- .nhl_gk$log
  if (is.null(gk) || !nrow(gk)) {
    mlog("NHL goalie | no goalie rows found in this run's box scores")
  } else {
    st <- gk[gk$started %in% TRUE, , drop = FALSE]
    mlog(sprintf("NHL goalie | %d appearance(s) across %d game(s); %d identifiable starter(s), %d distinct goalie(s)",
                 nrow(gk), length(unique(gk$game_id)), nrow(st), length(unique(gk$pid))))
    mlog(sprintf("NHL goalie | fields present -- toi %.0f%%, shots %.0f%%, saves %.0f%%, goals against %.0f%%",
                 100*mean(!is.na(gk$toi)), 100*mean(!is.na(gk$shots)),
                 100*mean(!is.na(gk$saves)), 100*mean(!is.na(gk$ga))))
    if (nrow(st) && any(!is.na(st$shots)) && any(!is.na(st$saves))) {
      sp <- sum(st$saves, na.rm = TRUE) / max(1, sum(st$shots, na.rm = TRUE))
      mlog(sprintf("NHL goalie | starters league save pct %.4f over %d shots",
                   sp, as.integer(sum(st$shots, na.rm = TRUE))))
    }
  }
  if (length(miss))
    mlog(sprintf("NHL        | no box score for %s",
                 paste(utils::head(sort(miss, decreasing = TRUE), 6), collapse = ", ")))
  k
}

nhl_load <- function() {
  nhl_api_reset()
  sch <- nhl_sched()
  pan <- nhl_panel(sch)
  if (is.null(pan) || !nrow(pan)) stop("No usable NHL results could be loaded.")
  endr <- nhl_end(pan)
  ents <- sort(unique(c(pan$team, pan$opp)))
  nmv <- nhl_names(sch)
  game_grade_history(NHL_LEDGER, sch)
  gkl <- tryCatch(nhl_goalies(sch), error = function(e) NULL)
  gf  <- tryCatch(nhl_gk_feature(gkl, sch), error = function(e) NULL)
  nhl_gk_report(gkl, gf)
  list(sch = sch, pan = pan, endr = endr, ents = ents, gf = gf,
       nm = nmv, logo = stats::setNames(nhl_logo(names(nmv)), names(nmv)),
       sk = nhl_live_report(sch, nhl_skaters(sch)),
       dropped = sort(unique(sch$season[sch$corrupt])))
}

NHL_API       <- "https://api-web.nhle.com/v1"
NHL_API_TO    <- 15
NHL_API_FAIL  <- 8L
NHL_WK_TTL    <- 4
NHL_SEED_TTL  <- 12 * 60
NHL_BOX_CAP   <- 60L
NHL_BOX_TTL    <- 5     # minutes a box score is re-read for, until the game is over
NHL_SCORE_TTL  <- 3     # minutes the live scoreboard is cached for
NHL_SCORE_DAYS <- 3L    # days back the scoreboard is asked who won
NHL_LIVE_DAYS <- 45L
NHL_WK_GUARD  <- 40L
NHL_CORRUPT_N <- 200L

# Goalie appearances found in this run's box scores. Kept here rather than threaded
# through every return value, because the skater path is what drives the fetching.
.nhl_gk <- new.env(hash = TRUE, parent = emptyenv())
.nhl_gk$log <- NULL
.nhl_gk$said <- FALSE
.cfb_td_said <- FALSE
.cfb_td_none <- FALSE

.nhl_api <- new.env(hash = TRUE, parent = emptyenv())
.nhl_api$fail <- 0L
.nhl_api$dead <- FALSE
.nhl_api$hits <- 0L
.nhl_api$miss <- 0L

nhl_live_dir <- file.path(nhl_dir, "live")
dir.create(nhl_live_dir, showWarnings = FALSE, recursive = TRUE)

nhl_api_reset <- function() {
  .nhl_api$fail <- 0L; .nhl_api$dead <- FALSE
  .nhl_api$hits <- 0L; .nhl_api$miss <- 0L
}

nhl_api_stats <- function()
  list(hits = .nhl_api$hits, miss = .nhl_api$miss, dead = isTRUE(.nhl_api$dead))

nhl_api_json <- function(path, cache, ttl_min = 0, perm = FALSE) {
  f <- if (nzchar(cache)) file.path(nhl_live_dir, paste0(cache, ".rds")) else ""
  old <- NULL
  if (nzchar(f) && file.exists(f)) {
    o <- try(readRDS(f), silent = TRUE)
    if (!inherits(o, "try-error") && is.list(o) && !is.null(o$v)) {
      if (isTRUE(o$perm) || age_min(f) < ttl_min) {
        .nhl_api$hits <- .nhl_api$hits + 1L
        return(o$v)
      }
      old <- o$v
    }
  }
  if (isTRUE(.nhl_api$dead)) return(old)
  r <- tryCatch(httr::GET(paste0(NHL_API, path), httr::timeout(NHL_API_TO)),
                error = function(e) NULL)
  if (is.null(r) || !identical(httr::status_code(r), 200L)) {
    .nhl_api$fail <- .nhl_api$fail + 1L
    if (.nhl_api$fail >= NHL_API_FAIL) .nhl_api$dead <- TRUE
    return(old)
  }
  .nhl_api$fail <- 0L
  v <- tryCatch(jsonlite::fromJSON(httr::content(r, "text", encoding = "UTF-8"),
                                   simplifyVector = FALSE), error = function(e) NULL)
  if (is.null(v)) return(old)
  .nhl_api$miss <- .nhl_api$miss + 1L
  if (nzchar(f))
    try(saveRDS(list(v = v, t = Sys.time(), perm = isTRUE(perm)), f), silent = TRUE)
  v
}

nhl_api_final <- function(st) as.character(st) %in% c("OFF", "FINAL")

# Keeps a cached answer for good. Only called once the game it describes is over, so
# that a box score read while the game was still being played is never the last word:
# caching that permanently is how a goalscorer board froze with the goals not yet in.
nhl_api_seal <- function(cache) {
  f <- file.path(nhl_live_dir, paste0(cache, ".rds"))
  if (!file.exists(f)) return(invisible(FALSE))
  o <- try(readRDS(f), silent = TRUE)
  if (inherits(o, "try-error") || !is.list(o) || isTRUE(o$perm)) return(invisible(FALSE))
  o$perm <- TRUE
  try(saveRDS(o, f), silent = TRUE)
  invisible(TRUE)
}

nhl_parse_week <- function(j) {
  if (is.null(j)) return(NULL)
  gw <- j$gameWeek
  nxt <- as.character(j$nextStartDate %||% "")
  if (!length(gw)) return(list(rows = NULL, nxt = nxt, start = as.character(
    j$regularSeasonStartDate %||% "")))
  rows <- list()
  for (d in gw) {
    dd <- as.character(d$date %||% "")
    for (g in (d$games %||% list())) {
      fin <- nhl_api_final(g$gameState %||% "")
      ht <- g$homeTeam; at <- g$awayTeam
      if (is.null(ht) || is.null(at)) next
      nm <- function(t) trimws(paste(as.character(t$placeName$default %||% ""),
                                     as.character(t$commonName$default %||% "")))
      rows[[length(rows) + 1L]] <- data.frame(
        game_id = as.character(g$id),
        date = as.character(if (nzchar(dd)) dd else (g$gameDate %||% NA)),
        kos = as.character(g$startTimeUTC %||% NA),
        home = as.character(ht$abbrev %||% NA),
        away = as.character(at$abbrev %||% NA),
        home_name = nm(ht), away_name = nm(at),
        home_score = if (fin) suppressWarnings(as.numeric(ht$score %||% NA)) else NA_real_,
        away_score = if (fin) suppressWarnings(as.numeric(at$score %||% NA)) else NA_real_,
        api_final = fin,
        gtype = suppressWarnings(as.integer(g$gameType %||% NA)),
        stringsAsFactors = FALSE)
    }
  }
  list(rows = if (length(rows)) dplyr::bind_rows(rows) else NULL, nxt = nxt,
       start = as.character(j$regularSeasonStartDate %||% ""))
}

# Who actually won, last night and tonight.
#
# The weekly /schedule feed is served from a cache that can sit hours behind the ice:
# it will call a finished game LIVE and hand back the score as it stood at the time,
# which the app then reads as no result at all. /score is the live scoreboard and is
# current, so for the last few days it has the last word. It only ever adds a result:
# a game already known to be final is never walked back to unfinished.
nhl_score_day <- function(d) {
  ds <- format(as.Date(d))
  j <- nhl_api_json(sprintf("/score/%s", ds), paste0("sc_", ds), NHL_SCORE_TTL)
  if (is.null(j) || !length(j$games)) return(NULL)
  rows <- list()
  for (g in j$games) {
    ht <- g$homeTeam; at <- g$awayTeam
    if (is.null(ht) || is.null(at)) next
    if (!nhl_api_final(g$gameState %||% "")) next
    hs <- suppressWarnings(as.numeric(ht$score %||% NA))
    as_ <- suppressWarnings(as.numeric(at$score %||% NA))
    if (is.na(hs) || is.na(as_)) next
    rows[[length(rows) + 1L]] <- data.frame(
      game_id = as.character(g$id %||% NA), home_score = hs, away_score = as_,
      stringsAsFactors = FALSE)
  }
  if (!length(rows)) return(NULL)
  dplyr::bind_rows(rows)
}

nhl_live_sched <- function(season_, upto = NULL) {
  if (is.null(upto)) upto <- Sys.Date() + 21L
  seed <- nhl_api_json(sprintf("/schedule/%d-10-01", season_),
                       sprintf("seed_%d", season_), NHL_SEED_TTL)
  w0 <- nhl_parse_week(seed)
  ds <- if (!is.null(w0) && nzchar(w0$start)) w0$start else sprintf("%d-10-01", season_)
  out <- list(); seen <- character(0)
  for (k in seq_len(NHL_WK_GUARD)) {
    if (!nzchar(ds) || ds %in% seen) break
    seen <- c(seen, ds)
    d0 <- suppressWarnings(as.Date(ds))
    if (is.na(d0)) break
    w <- nhl_parse_week(nhl_api_json(sprintf("/schedule/%s", ds),
                                     paste0("wk_", ds), NHL_WK_TTL,
                                     perm = (d0 + 7L) < Sys.Date()))
    if (is.null(w) && isTRUE(.nhl_api$dead)) break
    if (!is.null(w) && !is.null(w$rows)) out[[length(out) + 1L]] <- w$rows
    if (d0 > upto) break
    ds <- if (!is.null(w) && nzchar(w$nxt)) w$nxt else format(d0 + 7L)
  }
  if (!length(out)) return(NULL)
  r <- dplyr::bind_rows(out)
  r <- r[!is.na(r$gtype) & r$gtype == 2L, , drop = FALSE]
  r <- r[!is.na(r$home) & !is.na(r$away) & !is.na(r$date), , drop = FALSE]
  if (!nrow(r)) return(NULL)
  ko <- as.POSIXct(r$kos, format = "%Y-%m-%dT%H:%M:%SZ", tz = "UTC")
  bad <- is.na(ko)
  if (any(bad))
    ko[bad] <- as.POSIXct(paste(r$date[bad], "23:00"), format = "%Y-%m-%d %H:%M", tz = "UTC")
  out <- data.frame(game_id = r$game_id, date = as.Date(r$date), ko = ko,
                    home = r$home, away = r$away,
                    home_name = r$home_name, away_name = r$away_name,
                    home_score = r$home_score, away_score = r$away_score,
                    api_final = r$api_final %||% NA,
                    stringsAsFactors = FALSE)
  out <- out[!duplicated(out$game_id), , drop = FALSE]
  today <- as.Date(format(now_et(), "%Y-%m-%d"))
  for (i in 0:NHL_SCORE_DAYS) {
    sd <- tryCatch(nhl_score_day(today - i), error = function(e) NULL)
    if (is.null(sd) || !nrow(sd)) next
    j <- match(sd$game_id, out$game_id)
    k <- which(!is.na(j))
    if (!length(k)) next
    out$home_score[j[k]] <- sd$home_score[k]
    out$away_score[j[k]] <- sd$away_score[k]
    out$api_final[j[k]]  <- TRUE
  }
  out
}

nhl_parse_box <- function(j, id) {
  if (is.null(j)) return(NULL)
  pbg <- j$playerByGameStats
  if (is.null(pbg)) return(NULL)
  rows <- list()
  for (side in c("awayTeam", "homeTeam")) {
    tm <- as.character(j[[side]]$abbrev %||% NA)
    s <- pbg[[side]]
    if (is.null(s)) next
    for (grp in c("forwards", "defense")) {
      for (p in (s[[grp]] %||% list())) {
        po <- as.character(p$position %||% "")
        if (!nzchar(po) || po == "G") next
        rows[[length(rows) + 1L]] <- data.frame(
          game_id = as.character(id), pid = as.character(p$playerId %||% NA),
          pname = as.character(p$name$default %||% ""), pos = po, team = tm,
          goals = suppressWarnings(as.numeric(p$goals %||% 0)),
          stringsAsFactors = FALSE)
      }
    }
  }
  if (!length(rows)) return(NULL)
  dplyr::bind_rows(rows)
}

# Goalies out of a box score. Nothing here costs a request: the same JSON is already
# being fetched and parsed for the skaters, and the goalies sit beside them.
#
# The starter is taken as whoever was in net longest, rather than any 'starter' flag,
# because the flag is not in every season's feed and time on ice always is.
nhl_mmss <- function(s) {
  s <- as.character(s %||% "")
  if (!nzchar(s) || !grepl(":", s)) return(NA_real_)
  q <- strsplit(s, ":")[[1]]
  if (length(q) != 2L) return(NA_real_)
  suppressWarnings(as.numeric(q[1]) + as.numeric(q[2]) / 60)
}

# "28/30" -> saves 28, shots 30
nhl_saves <- function(s) {
  s <- as.character(s %||% "")
  q <- strsplit(s, "/")[[1]]
  if (length(q) != 2L) return(c(NA_real_, NA_real_))
  suppressWarnings(as.numeric(q))
}

nhl_parse_goalies <- function(j, id) {
  if (is.null(j)) return(NULL)
  pbg <- j$playerByGameStats
  if (is.null(pbg)) return(NULL)
  rows <- list()
  for (side in c("awayTeam", "homeTeam")) {
    tm <- as.character(j[[side]]$abbrev %||% NA)
    for (q in (pbg[[side]]$goalies %||% list())) {
      sv <- nhl_saves(q$saveShotsAgainst)
      rows[[length(rows) + 1L]] <- data.frame(
        game_id = as.character(id),
        pid   = as.character(q$playerId %||% NA),
        gname = as.character(q$name$default %||% ""),
        team  = tm,
        toi   = nhl_mmss(q$toi),
        saves = sv[1], shots = sv[2],
        ga    = suppressWarnings(as.numeric(q$goalsAgainst %||% NA)),
        stringsAsFactors = FALSE)
    }
  }
  if (!length(rows)) return(NULL)
  d <- dplyr::bind_rows(rows)
  d <- d[!is.na(d$pid) & nzchar(d$pid), , drop = FALSE]
  if (!nrow(d)) return(NULL)
  d$started <- FALSE
  for (tm in unique(d$team)) {
    i <- which(d$team == tm)
    if (!length(i)) next
    d$started[i[which.max(ifelse(is.na(d$toi[i]), -1, d$toi[i]))]] <- TRUE
  }
  d
}

nhl_live_box <- function(sch, cap = NHL_BOX_CAP) {
  cur <- nhl_season_of(now_et())
  g <- sch[sch$season == cur & sch$has_score, , drop = FALSE]
  if (!nrow(g)) return(NULL)
  g <- g[as.numeric(Sys.Date() - g$date) <= NHL_LIVE_DAYS, , drop = FALSE]
  if (!nrow(g)) return(NULL)
  g <- g[order(g$ko, decreasing = TRUE), , drop = FALSE]
  out <- list(); gout <- list(); spent <- 0L
  for (i in seq_len(nrow(g))) {
    id <- g$game_id[i]
    tag <- paste0("bx_", id)
    have <- file.exists(file.path(nhl_live_dir, paste0(tag, ".rds")))
    if (!have) {
      if (spent >= cap) next
      spent <- spent + 1L
    }
    bj <- nhl_api_json(sprintf("/gamecenter/%s/boxscore", id), tag, NHL_BOX_TTL)
    if (!is.null(bj) && nhl_api_final(bj$gameState %||% "")) nhl_api_seal(tag)
    b <- nhl_parse_box(bj, id)
    if (!is.null(b)) out[[length(out) + 1L]] <- b
    gk <- tryCatch(nhl_parse_goalies(bj, id), error = function(e) NULL)
    if (!is.null(gk)) gout[[length(gout) + 1L]] <- gk
  }
  .nhl_gk$log <- if (length(gout)) dplyr::bind_rows(gout) else NULL
  if (!length(out)) return(NULL)
  dplyr::bind_rows(out)
}

# ==================== NBA ====================
NBA_VER      <- 1L
NBA_SEASONS  <- 2017:2027
NBA_LAM      <- 10
NBA_PW       <- 30
NBA_PW_G     <- 8
NBA_RHO      <- 0.6
NBA_END_LAM  <- 20
NBA_FB_KPL   <- 70
NBA_FB_BASE  <- c(C = 0.1309, F = 0.1009, G = 0.0908, PF = 0.0794,
                  PG = 0.0798, SF = 0.0851, SG = 0.0919)
NBA_FB_RECENT <- 12L
NBA_FB_START_N <- 20L   # games of his team's recent run used to ask whether he starts
NBA_LEDGER   <- file.path(LEDGER_DIR, "nba_predictions.rds")
NBA_INJ_URL  <- "https://site.api.espn.com/apis/site/v2/sports/basketball/nba/injuries"
NBA_INJ_TTL  <- 30
NBA_ROS_URL  <- "https://site.api.espn.com/apis/site/v2/sports/basketball/nba/teams/%s/roster"
NBA_SUM_URL  <- "https://site.api.espn.com/apis/site/v2/sports/basketball/nba/summary?event=%s"
NBA_FB_LIVE_MAX <- 40L      # finished games read per load, so a cold start cannot stall
NBA_ROS_TTL  <- 12 * 60     # a roster changes rarely; a stale one is the whole bug
# Basketball rests healthy players, so the feed carries states hockey's does not.
NBA_INJ_OUT  <- c("out", "injured reserve", "suspension", "suspended",
                  "not with team", "out for season")
NBA_MODEL    <- sprintf("nba-marg-v%d", NBA_VER)

nba_dir <- file.path(CACHE_DIR, "nba")
dir.create(nba_dir, showWarnings = FALSE, recursive = TRUE)
nba_path <- function(k, y = NULL)
  file.path(nba_dir, if (is.null(y)) sprintf("%s_v%d.rds", k, NBA_VER)
            else sprintf("%s_v%d_%d.rds", k, NBA_VER, y))

nba_sync <- function(force = FALSE) {
  cur <- max(NBA_SEASONS)
  for (y in NBA_SEASONS) {
    sf <- nba_path("sch", y)
    if (force || (y >= cur - 1L && age_min(sf) > SDV_REFRESH_MIN)) unlink(sf)
    sdv_fetch("espn_nba_schedules", sprintf("nba_schedule_%d.rds", y), sf)
    tf <- nba_path("tb", y)
    if (force || (y >= cur - 1L && age_min(tf) > SDV_REFRESH_MIN)) unlink(tf)
    sdv_fetch("espn_nba_team_boxscores", sprintf("team_box_%d.rds", y), tf)
    if (y >= max(NBA_SEASONS) - 4L) {
      shf <- nba_path("sh", y)
      if (force || (y >= cur - 1L && age_min(shf) > SDV_REFRESH_MIN)) unlink(shf)
      sdv_fetch("espn_nba_shots", sprintf("shots_%d.rds", y), shf)
      gf <- nba_path("gr", y)
      if (force || (y >= cur - 1L && age_min(gf) > SDV_REFRESH_MIN)) unlink(gf)
      sdv_fetch("espn_nba_game_rosters", sprintf("game_rosters_%d.rds", y), gf)
    }
  }
  f <- vapply(NBA_SEASONS, function(y) nba_path("sch", y), "")
  f <- f[file.exists(f)]
  if (!length(f)) stop("Could not load NBA data. Check your connection.")
  paste(f, as.numeric(file.mtime(f)), collapse = "|")
}

nba_sched <- function() {
  out <- lapply(NBA_SEASONS, function(y) {
    f <- nba_path("sch", y); if (!file.exists(f)) return(NULL)
    d <- try(readRDS(f), silent = TRUE); if (inherits(d, "try-error")) return(NULL)
    d <- as.data.frame(d)
    if (!all(c("id", "home_id", "away_id") %in% names(d))) return(NULL)
    gv <- function(a) if (a %in% names(d)) d[[a]] else rep(NA, nrow(d))
    ko <- as.POSIXct(sub("Z$", "", as.character(gv("start_date"))),
                     format = "%Y-%m-%dT%H:%M", tz = "UTC")
    data.frame(game_id = as.character(d$id), season = y,
               stype = suppressWarnings(as.integer(gv("season_type"))),
               ko = ko,
               home = as.character(d$home_id), away = as.character(d$away_id),
               home_name = as.character(gv("home_display_name")),
               away_name = as.character(gv("away_display_name")),
               home_abbr = as.character(gv("home_abbreviation")),
               away_abbr = as.character(gv("away_abbreviation")),
               home_logo = as.character(gv("home_logo")),
               away_logo = as.character(gv("away_logo")),
               home_score = suppressWarnings(as.numeric(gv("home_score"))),
               away_score = suppressWarnings(as.numeric(gv("away_score"))),
               neutral = gv("neutral_site") %in% TRUE,
               done = gv("status_type_completed") %in% TRUE,
               stringsAsFactors = FALSE)
  })
  s <- dplyr::bind_rows(out)
  if (!nrow(s)) stop("No NBA schedule could be loaded.")
  s <- s[!is.na(s$ko) & s$stype %in% 2L, ]
  s <- s[!duplicated(s$game_id), ]
  attr(s$ko, "tzone") <- TZ_ET
  s$date <- as.Date(format(s$ko, "%Y-%m-%d"))
  s$final_at  <- s$ko + 4 * 3600
  fin <- s$done %in% TRUE
  if (any(fin)) s$final_at[fin] <- s$ko[fin]
  s$has_score <- s$done & !is.na(s$home_score) & !is.na(s$away_score)
  s[order(s$ko), ]
}

nba_panel <- function(sch) {
  g <- sch[sch$has_score, ]
  if (!nrow(g)) return(NULL)
  mk <- function(t, o, pf, pa, h) data.frame(
    game_id = g$game_id, season = g$season, date = g$date, ko = g$ko,
    team = t, opp = o, pf = pf, pa = pa, home = h, neu = g$neutral,
    stringsAsFactors = FALSE)
  p <- rbind(mk(g$home, g$away, g$home_score, g$away_score, 1L),
             mk(g$away, g$home, g$away_score, g$home_score, 0L))
  p$marg <- p$pf - p$pa
  p$hfa  <- ifelse(p$neu, 0, ifelse(p$home == 1L, 1, -1))
  p <- p[order(p$team, p$ko), ]
  d <- as.numeric(p$date)
  prev <- ave(d, p$team, FUN = function(x) c(NA, utils::head(x, -1)))
  p$rest <- pmin(pmax(d - prev, 0), 3)
  p$rest[is.na(p$rest)] <- 3
  p[order(p$ko), ]
}

nba_rate <- function(g, ents, lam, prior = NULL, pw = 0) {
  n <- length(ents); idx <- stats::setNames(seq_len(n), ents)
  A <- matrix(0, n + 1L, n + 1L); b <- numeric(n + 1L)
  if (nrow(g) > 0) {
    ti <- idx[g$team]; oi <- idx[g$opp]
    ok <- !is.na(ti) & !is.na(oi)
    ti <- ti[ok]; oi <- oi[ok]; y <- g$marg[ok]; h <- g$hfa[ok]
    m <- length(y)
    if (m > 0) {
      X <- Matrix::sparseMatrix(i = rep(seq_len(m), 3L), j = c(ti, oi, rep(n + 1L, m)),
                                x = c(rep(1, m), rep(-1, m), h), dims = c(m, n + 1L))
      A <- as.matrix(Matrix::crossprod(X)); b <- as.numeric(Matrix::crossprod(X, y))
    }
  }
  dd <- cbind(seq_len(n), seq_len(n))
  A[dd] <- A[dd] + lam
  if (!is.null(prior) && pw > 0) {
    pv <- prior[ents]; pv[is.na(pv)] <- 0
    A[dd] <- A[dd] + pw; b[seq_len(n)] <- b[seq_len(n)] + pw * pv
  }
  A[n + 1L, n + 1L] <- A[n + 1L, n + 1L] + 1e-6
  x <- try(solve(A, b), silent = TRUE)
  if (inherits(x, "try-error")) return(stats::setNames(numeric(n), ents))
  r <- stats::setNames(x[seq_len(n)], ents)
  r - mean(r)
}

nba_end <- function(panel) {
  f <- nba_path("end")
  e <- if (file.exists(f)) try(readRDS(f), silent = TRUE) else NULL
  if (inherits(e, "try-error") || !is.list(e)) e <- list()
  cur <- max(panel$season); ents <- sort(unique(c(panel$team, panel$opp)))
  for (s in sort(unique(panel$season))) {
    g <- panel[panel$season == s, ]
    if (nrow(g) < 500) next
    k <- as.character(s)
    if (!is.null(e[[k]]) && s < cur) next
    e[[k]] <- nba_rate(g, ents, NBA_END_LAM)
  }
  try(saveRDS(e, f), silent = TRUE)
  e
}

nba_rows <- function(panel, endr, ents, upto) {
  f <- nba_path("rows")
  R <- if (file.exists(f)) try(readRDS(f), silent = TRUE) else NULL
  if (inherits(R, "try-error") || !is.data.frame(R)) R <- NULL
  have <- if (is.null(R)) integer(0) else unique(R$season)
  want <- sort(unique(panel$season[panel$season < upto]))
  miss <- setdiff(want, have)
  if (!length(miss)) return(R)
  add <- list()
  for (s in miss) {
    sg <- panel[panel$season == s, ]
    if (!nrow(sg)) next
    pv <- endr[[as.character(s - 1L)]]
    pr <- if (is.null(pv)) NULL else pv * NBA_RHO
    away <- sg[sg$home == 0L, c("game_id", "rest")]
    names(away)[2] <- "arest"
    for (d in sort(unique(sg$date))) {
      hist <- sg[sg$date < d, ]
      gp <- if (nrow(hist)) nrow(hist) / max(1L, length(unique(hist$team))) else 0
      r <- nba_rate(hist, ents, NBA_LAM, pr, NBA_PW / (1 + gp / NBA_PW_G))
      tw <- sg[sg$date == d & sg$home == 1L, ]
      if (!nrow(tw)) next
      a <- away$arest[match(tw$game_id, away$game_id)]
      add[[length(add) + 1L]] <- data.frame(
        season = s, game_id = tw$game_id,
        rd = unname(r[tw$team]) - unname(r[tw$opp]), hfa = tw$hfa,
        rdiff = tw$rest - ifelse(is.na(a), 2, a), marg = tw$marg,
        stringsAsFactors = FALSE)
    }
  }
  R <- dplyr::bind_rows(R, dplyr::bind_rows(add))
  R <- R[!is.na(R$rd) & !is.na(R$marg), ]
  try(saveRDS(R, f), silent = TRUE)
  R
}

nba_fit <- function(R, season_) {
  h <- R[R$season < season_, ]
  if (nrow(h) < 2000) return(NULL)
  m1 <- stats::lm(marg ~ rd + hfa + rdiff, data = h)
  h$pred <- stats::predict(m1)
  h <- h[h$marg != 0, ]; h$win <- as.integer(h$marg > 0)
  lg <- suppressWarnings(stats::glm(win ~ pred, data = h, family = stats::binomial()))
  list(marg = m1, conf = lg, n = nrow(h))
}

nba_predict <- function(panel, endr, ents, m, g, cutoff) {
  if (is.null(m) || !nrow(g)) return(NULL)
  s <- g$season[1]
  # v2: earlier dates only, matching the walk-forward training rows.
  hist <- panel[panel$season == s & panel$date < min(g$date) & panel$ko < cutoff, ]
  pv <- endr[[as.character(s - 1L)]]
  pr <- if (is.null(pv)) NULL else pv * NBA_RHO
  gp <- if (nrow(hist)) nrow(hist) / max(1L, length(unique(hist$team))) else 0
  r <- nba_rate(hist, ents, NBA_LAM, pr, NBA_PW / (1 + gp / NBA_PW_G))
  lastd <- if (nrow(hist)) tapply(as.numeric(hist$date), hist$team, max) else numeric(0)
  # unname, like rd below: looking a team up in lastd when it has not played yet returns NA
  # carrying an NA name, and data.frame() takes a single NA name as a row name and stops. A
  # slate of two or more games hid it, because duplicate NA names make R fall back to
  # integers -- so only a game alone in its minute, early in a season, ever hit it.
  rst <- function(t) {
    v <- unname(lastd[as.character(t)])
    ifelse(is.na(v), 2, pmin(pmax(as.numeric(g$date) - v, 0), 3))
  }
  rd <- unname(r[g$home]) - unname(r[g$away]); rd[is.na(rd)] <- 0
  nd <- data.frame(rd = rd, hfa = ifelse(g$neutral, 0, 1),
                   rdiff = rst(g$home) - rst(g$away), row.names = NULL)
  nd$rdiff[is.na(nd$rdiff)] <- 0
  pred <- as.numeric(stats::predict(m$marg, newdata = nd))
  conf <- as.numeric(stats::predict(m$conf, newdata = data.frame(pred = pred), type = "response"))
  data.frame(game_id = g$game_id, season = s, rd = rd, pred = pred,
             conf = pmax(conf, 1 - conf), stringsAsFactors = FALSE)
}

nba_fb_hist <- function(sch) {
  f <- nba_path("fbh")
  H <- if (file.exists(f)) try(readRDS(f), silent = TRUE) else NULL
  if (!inherits(H, "try-error") && is.data.frame(H) && nrow(H) &&
      age_min(f) < SDV_REFRESH_MIN) return(H)
  sec <- function(c) {
    p <- strsplit(as.character(c), ":")
    vapply(p, function(x) if (length(x) == 2) as.numeric(x[1]) * 60 + as.numeric(x[2])
           else NA_real_, 0)
  }
  out <- list()
  for (y in NBA_SEASONS) {
    fs <- nba_path("sh", y); fg <- nba_path("gr", y)
    if (!file.exists(fs) || !file.exists(fg)) next
    s <- try(as.data.frame(readRDS(fs)), silent = TRUE)
    g <- try(as.data.frame(readRDS(fg)), silent = TRUE)
    if (inherits(s, "try-error") || inherits(g, "try-error")) next
    if (!all(c("period_number", "scoring_play", "score_value", "athlete_id_1") %in% names(s))) next
    s <- s[s$period_number == 1 & s$scoring_play %in% TRUE, ]
    if (!nrow(s)) next
    s$t <- sec(s$clock_display_value)
    s <- s[!is.na(s$t), ]
    s <- s[order(s$game_id, -s$t), ]
    fg1 <- s[s$score_value >= 2, ]; an1 <- s[s$score_value >= 1, ]
    a <- fg1[!duplicated(fg1$game_id), c("game_id", "athlete_id_1")]
    names(a) <- c("game_id", "w_fg")
    b <- an1[!duplicated(an1$game_id), c("game_id", "athlete_id_1")]
    names(b) <- c("game_id", "w_any")
    w <- merge(a, b, by = "game_id", all = TRUE)
    g <- g[g$starter %in% TRUE & !(g$did_not_play %in% TRUE), ]
    if (!nrow(g)) next
    r <- data.frame(game_id = as.character(g$game_id), team = as.character(g$team_id),
                    pid = as.character(g$athlete_id),
                    pname = as.character(g$athlete_display_name),
                    pos = as.character(g$athlete_position), season = y,
                    stringsAsFactors = FALSE)
    w$game_id <- as.character(w$game_id)
    r <- merge(r, w, by = "game_id")
    r$y_fg  <- as.integer(!is.na(r$w_fg)  & r$pid == as.character(r$w_fg))
    r$y_any <- as.integer(!is.na(r$w_any) & r$pid == as.character(r$w_any))
    out[[length(out) + 1L]] <- r[, c("game_id", "season", "team", "pid", "pname", "pos",
                                     "y_fg", "y_any")]
  }
  H <- dplyr::bind_rows(out)
  if (!nrow(H)) return(NULL)
  j <- match(H$game_id, sch$game_id)
  H$ko <- sch$ko[j]
  H <- H[!is.na(H$ko), ]
  H <- H[order(H$ko), ]
  try(saveRDS(H, f), silent = TRUE)
  H
}

nba_inj <- function()
  espn_inj(NBA_INJ_URL, file.path(nba_dir, "inj.rds"), NBA_INJ_TTL, NBA_INJ_OUT)

# Today's roster for one team. The upstream game-roster files are published per season
# and the current season's does not appear until it is well under way, so the newest
# line-ups on hand in October are last season's: a player who moved in the summer is
# still filed under the team he left. This is the only source that knows otherwise.
#
# Every failure returns whatever is cached, or NULL, and the caller then behaves as it
# did before -- a feed outage must not empty a board.
nba_roster_one <- function(id, timeout = 15) {
  f <- file.path(nba_dir, sprintf("ros_%s.rds", id))
  cached <- function() {
    if (!file.exists(f)) return(NULL)        # readRDS warns on a missing file; the log is read
    o <- try(readRDS(f), silent = TRUE)
    if (!inherits(o, "try-error") && is.data.frame(o) && nrow(o)) o else NULL
  }
  if (file.exists(f) && age_min(f) < NBA_ROS_TTL) {
    o <- cached(); if (!is.null(o)) return(o)
  }
  r <- tryCatch(httr::GET(sprintf(NBA_ROS_URL, id), httr::timeout(timeout)),
                error = function(e) NULL)
  if (is.null(r) || !identical(httr::status_code(r), 200L)) return(cached())
  j <- tryCatch(jsonlite::fromJSON(httr::content(r, "text", encoding = "UTF-8"),
                                   simplifyVector = FALSE), error = function(e) NULL)
  if (is.null(j)) return(cached())
  # basketball returns one flat list of athletes; other sports group them under items
  ath <- j$athletes %||% list()
  if (length(ath) && !is.null(ath[[1]]$items))
    ath <- unlist(lapply(ath, function(z) z$items %||% list()), recursive = FALSE)
  rows <- lapply(ath, function(a) {
    pid <- as.character(a$id %||% "")
    if (!nzchar(pid)) return(NULL)
    data.frame(team = as.character(id), pid = pid,
               pname = as.character(a$displayName %||% a$fullName %||% ""),
               pos = as.character(a$position$abbreviation %||% a$position$name %||% ""),
               stringsAsFactors = FALSE)
  })
  rows <- rows[!vapply(rows, is.null, TRUE)]
  if (!length(rows)) return(cached())
  d <- dplyr::bind_rows(rows)
  dir.create(dirname(f), recursive = TRUE, showWarnings = FALSE)
  try(saveRDS(d, f), silent = TRUE)
  d
}
# the rosters of the teams on one slate, skipping any that cannot be read
nba_roster <- function(ids) {
  ids <- unique(as.character(ids))
  ids <- ids[!is.na(ids) & nzchar(ids)]
  if (!length(ids)) return(NULL)
  out <- lapply(ids, function(i) tryCatch(nba_roster_one(i), error = function(e) NULL))
  out <- out[!vapply(out, is.null, TRUE)]
  if (!length(out)) return(NULL)
  dplyr::bind_rows(out)
}

# The five a side starts, out of a game summary. ESPN posts them shortly before tip-off
# and keeps them there afterwards, so one reader serves both the line-up the board needs
# tonight and the record it needs once the game is over.
#
# Two shapes are accepted because the payload changes as the game does: before tip the
# names sit under rosters, afterwards under the box score.
espn_nba_starters <- function(j) {
  if (is.null(j)) return(NULL)
  rows <- list()
  add <- function(tid, a, flag) {
    if (!isTRUE(flag)) return(invisible())
    pid <- as.character(a$id %||% "")
    if (!nzchar(pid) || !nzchar(tid)) return(invisible())
    rows[[length(rows) + 1L]] <<- data.frame(team = tid, pid = pid,
      pname = as.character(a$displayName %||% a$fullName %||% ""),
      pos = as.character(a$position$abbreviation %||% a$position$name %||% ""),
      stringsAsFactors = FALSE)
  }
  for (tm in (j$boxscore$players %||% list())) {
    tid <- as.character(tm$team$id %||% "")
    for (st in (tm$statistics %||% list())) for (a in (st$athletes %||% list()))
      add(tid, a$athlete, a$starter)
  }
  for (tm in (j$rosters %||% list())) {
    tid <- as.character(tm$team$id %||% "")
    for (a in (tm$roster %||% list())) add(tid, a$athlete %||% a, a$starter)
  }
  if (!length(rows)) return(NULL)
  d <- dplyr::bind_rows(rows)
  d[!duplicated(d$pid), , drop = FALSE]
}

# Tonight's five a side, for a game that has not been played. Checked often, because the
# line-up appears at some point in the hour before tip-off and nothing before it does.
nba_starters <- function(gid) {
  espn_cached(sprintf("nbast_%s", gid), ttl = 10, function() {
    j <- espn_get(sprintf(NBA_SUM_URL, gid))
    d <- espn_nba_starters(j)
    if (is.null(d) || !nrow(d)) return(NULL)
    # once the game is over the five can never change again
    attr(d, "final") <- isTRUE(j$header$competitions[[1]]$status$type$completed)
    d
  })
}
# The five a side for every game on a slate, where they are known. Games further off than
# NBA_ST_WINDOW are skipped: no line-up exists for a game three days away, and asking
# every ten minutes for one would be a few thousand pointless requests a week.
NBA_ST_WINDOW <- 8      # hours before tip-off worth asking
nba_starters_slate <- function(gids, ko = NULL, now = Sys.time()) {
  keep <- if (is.null(ko)) rep(TRUE, length(gids)) else {
    hrs <- as.numeric(difftime(ko, now, units = "hours"))
    is.na(hrs) | hrs <= NBA_ST_WINDOW
  }
  gids <- unique(as.character(gids[keep]))
  gids <- gids[!is.na(gids) & nzchar(gids)]
  if (!length(gids)) return(NULL)
  out <- lapply(gids, function(g) tryCatch(nba_starters(g), error = function(e) NULL))
  out <- out[!vapply(out, is.null, TRUE)]
  if (!length(out)) return(NULL)
  dplyr::bind_rows(out)
}

# One finished game's starters, and who opened the scoring, from ESPN's summary. The
# shape mirrors nba_fb_hist's rows so the two can simply be stacked.
nba_fbh_one <- function(gid, season, ko) {
  espn_cached(sprintf("nbafb_%s", gid), ttl = 60 * 24, function() {
    j <- espn_get(sprintf(NBA_SUM_URL, gid))
    if (is.null(j)) return(NULL)
    d <- espn_nba_starters(j)
    if (is.null(d) || !nrow(d)) return(NULL)
    # the opening period's first play worth at least this many points
    first_scorer <- function(minval) {
      for (pl in (j$plays %||% list())) {
        if (!isTRUE(pl$scoringPlay)) next
        per <- suppressWarnings(as.integer(pl$period$number %||% NA))
        if (!is.na(per) && per != 1L) next
        sv <- suppressWarnings(as.numeric(pl$scoreValue %||% NA))
        if (!is.finite(sv) || sv < minval) next
        for (q in (pl$participants %||% list())) {
          id <- as.character(q$athlete$id %||% "")
          if (nzchar(id)) return(id)
        }
        id <- as.character(pl$athlete$id %||% "")
        if (nzchar(id)) return(id)
      }
      NA_character_
    }
    wf <- first_scorer(2); wa <- first_scorer(1)
    d$y_fg  <- as.integer(!is.na(wf) & d$pid == wf)
    d$y_any <- as.integer(!is.na(wa) & d$pid == wa)
    d$game_id <- as.character(gid)
    d$season <- as.integer(season)
    d$ko <- ko
    out <- d[, c("game_id", "season", "team", "pid", "pname", "pos", "y_fg", "y_any", "ko")]
    # a finished game is finished: keep it rather than ask again
    attr(out, "final") <- TRUE
    out
  })
}

# Every finished game the season files have not caught up with yet, appended.
nba_live_fbh <- function(H, sch, now = Sys.time()) {
  if (is.null(sch) || !nrow(sch)) return(H)
  have <- if (is.null(H) || !nrow(H)) character(0) else unique(as.character(H$game_id))
  cur <- suppressWarnings(max(sch$season, na.rm = TRUE))
  if (!is.finite(cur)) return(H)
  done <- sch[sch$season >= cur - 1L & sch$has_score %in% TRUE &
              !is.na(sch$ko) & sch$ko < now, , drop = FALSE]
  need <- setdiff(as.character(done$game_id), have)
  if (!length(need)) return(H)
  need <- utils::head(need, NBA_FB_LIVE_MAX)
  add <- lapply(need, function(g) {
    k <- match(g, as.character(sch$game_id))
    if (is.na(k)) return(NULL)
    tryCatch(nba_fbh_one(g, sch$season[k], sch$ko[k]), error = function(e) NULL)
  })
  add <- add[!vapply(add, is.null, TRUE)]
  if (!length(add)) return(H)
  out <- dplyr::bind_rows(H, dplyr::bind_rows(add))
  out[order(out$ko), , drop = FALSE]
}

nba_fb <- function(H, cutoff, teams, inj = NULL, tkey = NULL, ros = NULL, st = NULL) {
  if (is.null(H) || !nrow(H)) return(NULL)
  h <- H[H$ko < cutoff, ]
  if (!nrow(h)) return(NULL)
  ag <- stats::aggregate(cbind(n = rep(1, nrow(h)), f = h$y_fg, a = h$y_any) ~ pid,
                         data = h, FUN = sum)
  last <- h[!duplicated(h$pid, fromLast = TRUE), c("pid", "pname", "pos", "team", "ko")]
  x <- merge(ag, last, by = "pid")
  # Does he actually start? His share of the last 20 games played by the team he was most
  # recently with. This is the question the old last-twelve-games filter was asking as a
  # yes or no, and the board needs it as a number: the rate below is the chance of the
  # first basket GIVEN a start, so without this it is quoted for men who will not be on
  # the floor. Measured before the roster is applied and against his historical team,
  # because someone who moved in the summer has started no games for his new club.
  # each team's last 20 games, worked out once rather than once per player
  tg20 <- lapply(split(h$game_id, h$team), function(v) utils::tail(unique(v), NBA_FB_START_N))
  pg <- split(h$game_id, h$pid)       # each man's starts
  x$s <- vapply(seq_len(nrow(x)), function(i) {
    tg <- tg20[[as.character(x$team[i])]]
    if (!length(tg)) return(0)
    mean(tg %in% pg[[as.character(x$pid[i])]])
  }, 0)
  x <- x[x$s > 0, , drop = FALSE]     # nobody who has not started lately can be ranked
  if (!nrow(x)) return(NULL)
  # Where a current roster could be read it decides the team, not the last box score,
  # and it decides the candidate set: without this season's games there is no way to
  # tell who starts, and the last-twelve-games heuristic would be reading last season.
  # Teams whose roster could not be read keep the old behaviour exactly.
  have <- if (is.null(ros) || !nrow(ros)) character(0) else unique(as.character(ros$team))
  if (length(have)) {
    j <- match(x$pid, ros$pid)
    i <- which(!is.na(j))
    x$team[i] <- as.character(ros$team[j[i]])
    rp <- as.character(ros$pos[j[i]]);   g <- !is.na(rp) & nzchar(rp); x$pos[i[g]]   <- rp[g]
    rn <- as.character(ros$pname[j[i]]); g <- !is.na(rn) & nzchar(rn); x$pname[i[g]] <- rn[g]
    # a player absent from every roster read is dropped only from the teams that were read
    x <- x[!is.na(j) | !(x$team %in% have), , drop = FALSE]
  }
  rec <- h[h$team %in% teams, ]
  keep <- if (!nrow(rec)) character(0) else unlist(lapply(split(rec, rec$team), function(z) {
    g <- unique(z$game_id[order(z$ko, decreasing = TRUE)])
    unique(z$pid[z$game_id %in% utils::head(g, NBA_FB_RECENT)])
  }), use.names = FALSE)
  x <- x[x$team %in% teams & (x$team %in% have | x$pid %in% keep), , drop = FALSE]
  if (!nrow(x)) return(NULL)
  # The announced five, where a game has them. This is the whole of the problem: five
  # names a side, each worth about a tenth of the first basket before anything else is
  # considered. Where they are known nobody else can take it, so the share is 1 for them
  # and the rest of that team leaves the board.
  if (!is.null(st) && nrow(st)) {
    st <- st[st$team %in% teams, , drop = FALSE]
    known <- unique(as.character(st$team))
    if (length(known)) {
      is_st <- paste(x$team, x$pid) %in% paste(st$team, st$pid)
      x$s[is_st] <- 1
      x <- x[is_st | !(x$team %in% known), , drop = FALSE]
      # a man starting with no first-basket history still belongs on the board, at his
      # position's rate: that is the honest number for someone unknown, and leaving him
      # off would be the same error in a quieter form
      new <- st[!paste(st$team, st$pid) %in% paste(x$team, x$pid), , drop = FALSE]
      if (nrow(new))
        x <- dplyr::bind_rows(x, data.frame(pid = as.character(new$pid),
          n = 0, f = 0, a = 0, pname = as.character(new$pname),
          pos = as.character(new$pos), team = as.character(new$team),
          ko = rep(cutoff, nrow(new)), s = 1, stringsAsFactors = FALSE))
    }
  }
  if (!nrow(x)) return(NULL)
  x <- espn_inj_gate(x, inj, tkey)
  if (!nrow(x)) return(NULL)
  b <- unname(NBA_FB_BASE[x$pos]); b[is.na(b)] <- 0.10
  # his rate if he starts, times the chance he does
  x$p_fg  <- (x$f + NBA_FB_KPL * b) / (x$n + NBA_FB_KPL) * x$s
  x$p_any <- (x$a + NBA_FB_KPL * b) / (x$n + NBA_FB_KPL) * x$s
  x[order(-x$p_fg), c("pid", "pname", "pos", "team", "n", "f", "a", "p_fg", "p_any")]
}

nba_current_season <- function(sch, now) {
  y <- sch$season[!is.na(sch$ko) & sch$ko <= now]
  if (!length(y)) return(min(sch$season))
  as.integer(max(y))
}

nba_load <- function() {
  sch <- nba_sched()
  pan <- nba_panel(sch)
  if (is.null(pan) || !nrow(pan)) stop("No usable NBA results could be loaded.")
  endr <- nba_end(pan)
  ents <- sort(unique(c(pan$team, pan$opp)))
  nm <- c(stats::setNames(sch$home_name, sch$home), stats::setNames(sch$away_name, sch$away))
  lg <- c(stats::setNames(sch$home_logo, sch$home), stats::setNames(sch$away_logo, sch$away))
  game_grade_history(NBA_LEDGER, sch)
  list(sch = sch, pan = pan, endr = endr, ents = ents,
       # the season files first, then this season's finished games from ESPN, which the
       # season files will not carry until long after they have been played
       fbh = tryCatch(nba_live_fbh(nba_fb_hist(sch), sch),
                      error = function(e) nba_fb_hist(sch)),
       nm = nm[!duplicated(names(nm))], logo = lg[!duplicated(names(lg))])
}

# ==================== WARM ====================
WARM_DIR      <- "proj_cache"
WARM_STAMP    <- file.path(WARM_DIR, "warm_stamp.rds")
WARM_TTL      <- 6 * 3600
WARM_RETRY    <- 20 * 60
WARM_FIRST    <- 9
WARM_GAP      <- 1.2
WARM_MLB_STEP <- 10L

warm_env <- new.env(parent = emptyenv())
warm_env$steps   <- list()
warm_env$i       <- 0L
warm_env$running <- FALSE
warm_env$done    <- FALSE
warm_env$label   <- ""
warm_env$fail    <- character(0)
warm_env$started <- NULL
warm_env$secs    <- NA_real_
warm_env$mlb     <- FALSE
warm_env$owned   <- character(0)

warm_own <- function(k) {
  warm_env$owned <- union(warm_env$owned, k)
  invisible(TRUE)
}

warm_held <- function(k) isTRUE(k %in% warm_env$owned)

warm_read <- function() {
  if (!file.exists(WARM_STAMP)) return(NULL)
  s <- try(readRDS(WARM_STAMP), silent = TRUE)
  if (inherits(s, "try-error") || !is.list(s)) NULL else s
}

warm_age <- function() {
  s <- warm_read()
  if (is.null(s) || is.null(s$at)) return(Inf)
  a <- as.numeric(Sys.time() - s$at, units = "secs")
  if (!is.finite(a) || a < 0) Inf else a
}

warm_fresh <- function() {
  s <- warm_read()
  if (is.null(s)) return(FALSE)
  a <- warm_age()
  if (isTRUE(s$complete)) a < WARM_TTL else a < WARM_RETRY
}

warm_bundle_mb <- function() {
  d <- c(tryCatch(CACHE_DIR, error = function(e) NULL), WARM_DIR)
  d <- d[!is.na(d) & nzchar(d)]
  f <- unlist(lapply(d[dir.exists(d)], list.files, recursive = TRUE, full.names = TRUE))
  led <- c("predictions_ledger.csv", "nrfi_ledger.csv")
  ld <- tryCatch(LEDGER_DIR, error = function(e) NULL)
  if (!is.null(ld) && dir.exists(ld))
    led <- c(led, list.files(ld, recursive = TRUE, full.names = TRUE))
  f <- c(f, led[file.exists(led)])
  if (!length(f)) return(0)
  sum(file.size(f), na.rm = TRUE) / 1048576
}

warm_build <- function() {
  st <- list()
  add <- function(lab, fn) st[[length(st) + 1L]] <<- list(lab = lab, fn = fn)

  add("NFL play-by-play", function() {
    if (warm_held("nfl")) return(invisible(NULL))
    sync_data(force = FALSE); invisible(load_all())
  })
  add("NCAAF play-by-play", function() {
    if (warm_held("cfb")) return(invisible(NULL))
    cfb_sync(FALSE); invisible(cfb_load())
  })
  add("NHL boxscores", function() {
    if (warm_held("nhl")) return(invisible(NULL))
    nhl_sync(FALSE); invisible(nhl_load())
  })
  add("NHL walk-forward ratings", function() {
    if (warm_held("nhl")) return(invisible(NULL))
    d <- nhl_load()
    invisible(nhl_rows(d$pan, d$endr, d$ents, nhl_season_of(Sys.Date()), d$gf))
  })
  add("NBA boxscores and shots", function() {
    if (warm_held("nba")) return(invisible(NULL))
    nba_sync(FALSE); invisible(nba_load())
  })
  add("NBA walk-forward ratings", function() {
    if (warm_held("nba")) return(invisible(NULL))
    d <- nba_load()
    s <- d$sch$season[match(TRUE, d$sch$date >= Sys.Date())]
    if (is.na(s)) s <- max(d$sch$season, na.rm = TRUE)
    invisible(nba_rows(d$pan, d$endr, d$ents, s))
  })

  if (isTRUE(warm_env$mlb)) {
    ed <- Sys.Date() - 1L
    fl <- mlb_season_start(format(ed, "%Y"))
    if (fl <= ed) {
      cuts <- as.numeric(unique(c(seq(fl, ed, by = WARM_MLB_STEP), ed)))
      cuts <- cuts[cuts >= as.numeric(fl)]
      for (k in seq_along(cuts)) local({
        e <- as.Date(cuts[k], origin = "1970-01-01")
        add(paste("MLB results to", format(e, "%b %d")), function() {
          if (warm_held("mlb")) return(invisible(NULL))
          try(awm_catch_up(end_date = e), silent = TRUE)
          try(nrfi_catch_up(end_date = e), silent = TRUE)
          invisible(NULL)
        })
      })
    }
    add("MLB slate", function() {
      if (warm_held("mlb")) return(invisible(NULL))
      invisible(prepare_data(recent_games = 15L,
                            date_str = format(Sys.Date(), "%Y-%m-%d")))
    })
  }
  st
}

warm_finish <- function() {
  warm_env$running <- FALSE
  warm_env$done    <- TRUE
  warm_env$label   <- ""
  warm_env$secs    <- as.numeric(Sys.time() - warm_env$started, units = "secs")
  try(saveRDS(list(at = Sys.time(), mlb = isTRUE(warm_env$mlb),
                   complete = length(warm_env$fail) == 0L && isTRUE(warm_env$mlb),
                   fail = warm_env$fail, secs = warm_env$secs,
                   mb = round(warm_bundle_mb(), 1)), WARM_STAMP), silent = TRUE)
  invisible()
}

warm_tick <- function() {
  if (!isTRUE(warm_env$running)) return(invisible())
  warm_env$i <- warm_env$i + 1L
  if (warm_env$i > length(warm_env$steps)) return(warm_finish())
  s <- warm_env$steps[[warm_env$i]]
  warm_env$label <- s$lab
  ok <- tryCatch({ s$fn(); TRUE }, error = function(e) FALSE,
                 warning = function(w) TRUE)
  if (!isTRUE(ok)) warm_env$fail <- c(warm_env$fail, s$lab)
  later::later(warm_tick, WARM_GAP)
  invisible()
}

warm_start <- function() {
  if (isTRUE(warm_env$running) || isTRUE(warm_env$done)) return(invisible(FALSE))
  if (!requireNamespace("later", quietly = TRUE)) return(invisible(FALSE))
  if (warm_fresh()) {
    warm_env$done <- TRUE
    return(invisible(FALSE))
  }
  dir.create(WARM_DIR, showWarnings = FALSE, recursive = TRUE)
  warm_env$mlb     <- isTRUE(tryCatch(mlb_api_alive(), error = function(e) FALSE))
  warm_env$steps   <- warm_build()
  warm_env$i       <- 0L
  warm_env$fail    <- character(0)
  warm_env$started <- Sys.time()
  warm_env$running <- TRUE
  later::later(warm_tick, WARM_FIRST)
  invisible(TRUE)
}

warm_status <- function() {
  n <- length(warm_env$steps)
  list(running = isTRUE(warm_env$running), done = isTRUE(warm_env$done),
       i = warm_env$i, n = n, label = warm_env$label, fail = warm_env$fail,
       mlb = isTRUE(warm_env$mlb), secs = warm_env$secs,
       age = warm_age(), mb = warm_bundle_mb(),
       pct = if (n > 0L) max(2, min(99, round(100 * (warm_env$i - 1L) / n))) else 0)
}

warm_banner <- function() {
  s <- warm_read()
  cat("\n", APP_NAME, " is running.\n", sep = "")
  if (!is.null(s) && isTRUE(s$complete))
    cat(sprintf("Cache is warm (%s, %.0f MB). Ready to publish.\n",
                format(s$at, "%b %d %H:%M"), s$mb %||% warm_bundle_mb()))
  else if (!is.null(s) && !isTRUE(s$mlb))
    cat("Cache is warm except MLB, which needs statsapi.mlb.com to be reachable.\n")
  else
    cat("Warming the cache in the background.\n")
  cat("To publish the web page, run:  source(\"publish_site.R\")   (Shiny version: source(\"deploy_projections.R\"))\n\n")
  invisible()
}

# ==================== UI ====================
PROJ_CSS_BASE <- "      *{box-sizing:border-box;margin:0;padding:0}
      body{font-family:'Barlow',sans-serif;background:#0a0d14;color:#e2e8f0;font-size:14px}
      .app-header{background:#0a0d14;border-bottom:2px solid #1e3a8a;padding:18px 32px;display:flex;align-items:center;gap:20px;flex-wrap:wrap}
      .logo-badge{width:52px;height:52px;border-radius:12px;background:#1e40af;display:flex;align-items:center;justify-content:center;font-size:26px;flex-shrink:0}
      .header-title{font-family:'Barlow Condensed',sans-serif;font-size:28px;font-weight:800;color:#f1f5f9;letter-spacing:1.5px;text-transform:uppercase}
      .header-sub{font-family:'IBM Plex Mono',monospace;font-size:10px;color:#475569;margin-top:3px}
      .header-pills{margin-left:auto;display:flex;gap:8px;flex-wrap:wrap;align-items:center}
      .pill{background:rgba(30,64,175,.18);border:1px solid rgba(59,130,246,.28);border-radius:20px;padding:4px 12px;font-family:'IBM Plex Mono',monospace;font-size:11px;color:#93c5fd}
      .pill.green{background:rgba(16,185,129,.15);border-color:rgba(16,185,129,.3);color:#6ee7b7}
      .pill.amber{background:rgba(245,158,11,.15);border-color:rgba(245,158,11,.3);color:#fcd34d}
      .pill.integ{background:rgba(167,139,250,.15);border-color:rgba(167,139,250,.35);color:#c4b5fd}
      .controls-bar{background:#111827;border-bottom:1px solid #1e293b;padding:12px 32px;display:flex;align-items:flex-end;gap:20px;flex-wrap:wrap}
      .ctrl-lbl{font-family:'IBM Plex Mono',monospace;font-size:10px;text-transform:uppercase;letter-spacing:1.5px;color:#64748b;display:block;margin-bottom:5px}
      .form-control,.shiny-date-input .form-control{background:#0a0d14!important;border:1px solid #334155!important;border-radius:6px!important;color:#e2e8f0!important;font-size:13px!important;height:36px!important}
      .form-control:focus{border-color:#3b82f6!important;box-shadow:0 0 0 2px rgba(59,130,246,.2)!important}
      .irs--shiny .irs-bar{background:#1e40af}.irs--shiny .irs-handle{background:#3b82f6;border-color:#1e40af}
      .btn-run{background:#1e40af!important;border:none!important;color:#fff!important;font-family:'Barlow Condensed',sans-serif!important;font-size:15px!important;font-weight:700!important;letter-spacing:1.5px!important;text-transform:uppercase!important;padding:8px 24px!important;border-radius:6px!important;height:36px!important;cursor:pointer!important}
      .btn-run:hover{background:#2563eb!important}
      .content{padding:24px 32px}
      .section-hdr{display:flex;align-items:center;gap:12px;margin-bottom:16px;margin-top:8px}
      .section-hdr-line{flex:1;height:1px;background:#1e40af}
      .section-title{font-family:'Barlow Condensed',sans-serif;font-size:14px;font-weight:700;letter-spacing:3px;text-transform:uppercase;color:#64748b;white-space:nowrap}
      .accuracy-bar{background:#111827;border:1px solid #1e293b;border-radius:10px;padding:14px 24px;margin-bottom:24px;display:flex;align-items:center;gap:24px;flex-wrap:wrap}
      .acc-stat{display:flex;flex-direction:column;align-items:center}
      .acc-val{font-family:'IBM Plex Mono',monospace;font-size:24px;font-weight:600;color:#3b82f6}
      .acc-lbl{font-size:10px;color:#64748b;text-transform:uppercase;letter-spacing:1px;margin-top:2px}
      .acc-divider{width:1px;height:44px;background:#1e293b}
      .tbl-wrap{background:#111827;border:1px solid #1e293b;border-radius:12px;overflow:hidden;margin-bottom:32px}
      table.dataTable{background:#111827!important;color:#e2e8f0!important;font-size:13px!important;width:100%!important}
      table.dataTable thead th{background:#0a0d14!important;color:#475569!important;font-family:'IBM Plex Mono',monospace!important;font-size:10px!important;font-weight:600!important;text-transform:uppercase!important;letter-spacing:1.5px!important;border-bottom:1px solid #1e293b!important;border-top:none!important;padding:10px 14px!important}
      table.dataTable tbody td{border-top:1px solid rgba(30,41,59,.8)!important;padding:9px 14px!important;vertical-align:middle!important}
      table.dataTable tbody tr.row-correct td{background:rgba(16,185,129,.12)!important}
      table.dataTable tbody tr.row-incorrect td{background:rgba(239,68,68,.14)!important}
      table.dataTable tbody tr.row-live td{background:rgba(245,158,11,.07)!important}
      table.dataTable tbody tr:hover td{background:rgba(30,64,175,.09)!important}
      table.dataTable.stripe tbody tr.odd td{background:#111827!important}
      table.dataTable.stripe tbody tr.even td{background:rgba(10,13,20,.6)!important}
      .dataTables_wrapper .dataTables_filter input{background:#0a0d14!important;border:1px solid #334155!important;border-radius:5px!important;padding:4px 10px!important;color:#e2e8f0!important}
      .dataTables_wrapper .dataTables_info,.dataTables_wrapper .dataTables_paginate{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#475569!important;padding:10px 14px!important}
      .dataTables_wrapper .paginate_button{color:#475569!important;border-radius:4px!important;font-size:11px!important}
      .dataTables_wrapper .paginate_button.current{background:#1e40af!important;color:#fff!important;border-color:#1e40af!important}
      .dataTables_wrapper .paginate_button:hover:not(.current){background:#1e293b!important;color:#e2e8f0!important}
      .conf-high{display:inline-block;background:rgba(30,64,175,.22);border:1px solid rgba(59,130,246,.35);border-radius:4px;padding:2px 8px;font-family:'IBM Plex Mono',monospace;font-size:11px;font-weight:600;color:#93c5fd}
      .conf-med{display:inline-block;background:rgba(245,158,11,.12);border:1px solid rgba(245,158,11,.3);border-radius:4px;padding:2px 8px;font-family:'IBM Plex Mono',monospace;font-size:11px;color:#fcd34d}
      .conf-low{display:inline-block;background:rgba(30,41,59,.5);border:1px solid #334155;border-radius:4px;padding:2px 8px;font-family:'IBM Plex Mono',monospace;font-size:11px;color:#64748b}
      .sp-elite{display:inline-block;background:rgba(167,139,250,.18);border:1px solid rgba(167,139,250,.4);border-radius:4px;padding:2px 7px;font-family:'IBM Plex Mono',monospace;font-size:10px;color:#c4b5fd}
      .sp-good{display:inline-block;background:rgba(16,185,129,.12);border:1px solid rgba(16,185,129,.3);border-radius:4px;padding:2px 7px;font-family:'IBM Plex Mono',monospace;font-size:10px;color:#6ee7b7}
      .sp-avg{display:inline-block;background:rgba(30,41,59,.5);border:1px solid #334155;border-radius:4px;padding:2px 7px;font-family:'IBM Plex Mono',monospace;font-size:10px;color:#64748b}
      .sp-below{display:inline-block;background:rgba(245,158,11,.12);border:1px solid rgba(245,158,11,.3);border-radius:4px;padding:2px 7px;font-family:'IBM Plex Mono',monospace;font-size:10px;color:#fcd34d}
      .sp-struggling{display:inline-block;background:rgba(239,68,68,.15);border:1px solid rgba(239,68,68,.35);border-radius:4px;padding:2px 7px;font-family:'IBM Plex Mono',monospace;font-size:10px;color:#f87171}
      .winner-cell{font-family:'Barlow Condensed',sans-serif;font-size:15px;font-weight:700;color:#60a5fa}
      .total-cell{font-family:'IBM Plex Mono',monospace;color:#e2e8f0}
      .result-correct{color:#6ee7b7;font-weight:600}
      .result-incorrect{color:#f87171;font-weight:600}
      .result-live{color:#fcd34d}
      .result-pending{color:#475569}
      .hr-hi{font-family:'IBM Plex Mono',monospace;font-weight:700;color:#60a5fa}
      .hr-mid{font-family:'IBM Plex Mono',monospace;color:#fcd34d}
      .hr-lo{font-family:'IBM Plex Mono',monospace;color:#94a3b8}
      .result-hr{color:#6ee7b7;font-weight:600}
      .result-nohr{color:#f87171}
      .nrfi-hi{font-family:'IBM Plex Mono',monospace;font-size:15px;font-weight:600;color:#6ee7b7}
      .nrfi-mid{font-family:'IBM Plex Mono',monospace;font-size:15px;font-weight:600;color:#fcd34d}
      .nrfi-lo{font-family:'IBM Plex Mono',monospace;font-size:15px;font-weight:600;color:#f87171}
      .pick-nrfi{display:inline-block;background:rgba(16,185,129,.15);border:1px solid rgba(16,185,129,.35);border-radius:4px;padding:2px 8px;font-family:'IBM Plex Mono',monospace;font-size:11px;font-weight:600;color:#6ee7b7}
      .pick-yrfi{display:inline-block;background:rgba(239,68,68,.13);border:1px solid rgba(239,68,68,.32);border-radius:4px;padding:2px 8px;font-family:'IBM Plex Mono',monospace;font-size:11px;font-weight:600;color:#f87171}
      .nrfi-flag{font-family:'IBM Plex Mono',monospace;font-size:10px;color:#c4b5fd;background:rgba(167,139,250,.12);border-radius:3px;padding:1px 5px;margin-left:3px}
      .half-cell{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#94a3b8}
      .sp-line{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#94a3b8}
      .edge-pos{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#6ee7b7}
      .edge-neg{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#f87171}
      .whip-flag{font-family:'IBM Plex Mono',monospace;font-size:10px;color:#60a5fa;background:rgba(59,130,246,.12);border-radius:3px;padding:1px 5px;margin-left:4px}
      .lob-plus{font-family:'IBM Plex Mono',monospace;font-size:10px;color:#6ee7b7;background:rgba(16,185,129,.12);border-radius:3px;padding:1px 5px;margin-left:3px}
      .lob-minus{font-family:'IBM Plex Mono',monospace;font-size:10px;color:#f87171;background:rgba(239,68,68,.12);border-radius:3px;padding:1px 5px;margin-left:3px}
      .ser-badge{font-family:'IBM Plex Mono',monospace;font-size:10px;color:#fcd34d;background:rgba(245,158,11,.12);border-radius:3px;padding:1px 5px;margin-left:3px}
      .lock-badge{font-family:'IBM Plex Mono',monospace;font-size:10px;color:#94a3b8;background:rgba(148,163,184,.12);border:1px solid rgba(148,163,184,.25);border-radius:3px;padding:1px 5px;margin-left:3px}
      .legend-panel{background:#111827;border:1px solid #1e293b;border-radius:12px;padding:20px 24px;margin-bottom:24px}
      .legend-title{font-family:'Barlow Condensed',sans-serif;font-size:16px;font-weight:700;letter-spacing:2px;text-transform:uppercase;color:#64748b;margin-bottom:14px}
      .legend-note{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#c4b5fd;background:rgba(167,139,250,.10);border:1px solid rgba(167,139,250,.25);border-radius:8px;padding:10px 14px;margin-bottom:14px;line-height:1.5}
      .legend-cat{font-family:'IBM Plex Mono',monospace;font-size:10px;text-transform:uppercase;letter-spacing:1.5px;color:#3b82f6;margin:14px 0 6px;font-weight:600}
      .legend-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:4px 20px}
      .legend-row{display:flex;align-items:baseline;gap:8px;padding:3px 0;font-size:12px}
      .legend-abbr{font-family:'IBM Plex Mono',monospace;font-weight:600;color:#93c5fd;min-width:72px;flex-shrink:0}
      .legend-full{color:#94a3b8;line-height:1.4}
      ::-webkit-scrollbar{width:6px;height:6px}
      ::-webkit-scrollbar-track{background:#0a0d14}
      ::-webkit-scrollbar-thumb{background:#334155;border-radius:3px}
"

PROJ_CSS_EXTRA <- "      .shell{display:flex;min-height:calc(100vh - 92px)}
      .side{width:186px;flex-shrink:0;background:#0d111a;border-right:1px solid #1e293b;padding:18px 0}
      .side .grp{font-family:'IBM Plex Mono',monospace;font-size:10px;letter-spacing:1.6px;color:#475569;text-transform:uppercase;margin:4px 0 10px 20px}
      .main{flex:1;min-width:0;overflow-x:auto}
      ul#lg.nav{border:none;padding:0 12px}
      ul#lg.nav>li{float:none;width:100%}
      ul#lg.nav>li>a{display:flex;align-items:center;gap:11px;padding:10px 14px;margin:3px 0;border:none!important;border-radius:9px;
        font-family:'Barlow Condensed',sans-serif;font-size:17px;font-weight:700;letter-spacing:1.4px;text-transform:uppercase;color:#64748b;background:transparent!important}
      ul#lg.nav>li>a:hover{background:#151b28!important;color:#cbd5e1}
      ul#lg.nav>li.active>a,ul#lg.nav>li.active>a:hover,ul#lg.nav>li.active>a:focus{
        background:rgba(30,64,175,.24)!important;color:#bfdbfe;box-shadow:inset 3px 0 0 #3b82f6}
      .nv-ic{font-size:18px;line-height:1;filter:saturate(.85)}
      ul#lg.nav>li>a.soon{opacity:.42;cursor:not-allowed}
      .soon-tag{margin-left:auto;font-family:'IBM Plex Mono',monospace;font-size:8px;letter-spacing:1px;color:#475569;border:1px solid #1e293b;border-radius:3px;padding:1px 4px}

      .hdr{font-family:'Barlow Condensed',sans-serif;font-size:22px;font-weight:800;letter-spacing:1.4px;text-transform:uppercase;color:#f1f5f9;margin:4px 0 2px}
      .sub{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#475569;margin-bottom:18px}
      .rec{background:#111827;border:1px solid #1e293b;border-left:3px solid #1e40af;border-radius:10px;padding:13px 20px;margin:0 0 22px;font-size:14px;color:#cbd5e1}
      .err{background:rgba(239,68,68,.10);border:1px solid rgba(239,68,68,.28);border-radius:10px;padding:13px 20px;margin:0 0 22px;font-size:13px;color:#fca5a5}
      .leak{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#475569;margin-top:22px;line-height:1.75;max-width:900px}
      .leak b{color:#64748b}
      .hint{color:#475569;font-size:11px;font-family:'IBM Plex Mono',monospace;margin:9px 2px 0;line-height:1.6;max-width:900px}
      .sec-hdr{font-family:'Barlow Condensed',sans-serif;font-size:14px;font-weight:700;letter-spacing:3px;text-transform:uppercase;color:#64748b;
        margin:34px 0 14px;padding-bottom:8px;border-bottom:1px solid #1e293b}

      .bdg{display:inline-block;width:23px;height:23px;border-radius:50%;vertical-align:middle;margin-right:8px;overflow:hidden}
      .bdg img{width:23px;height:23px;display:block}
      .tm{vertical-align:middle;color:#e2e8f0}
      .at{color:#475569;margin:0 8px;vertical-align:middle;font-size:12px}
      .chip{display:inline-block;padding:3px 12px 3px 4px;border-radius:13px;border:1px solid;font-weight:600;white-space:nowrap;color:#0a0d14}
      .cf{display:flex;align-items:center;gap:9px}
      .cfn{width:36px;text-align:right;font-family:'IBM Plex Mono',monospace;font-size:12px;color:#cbd5e1}
      .cft{flex:1;min-width:52px;height:6px;background:#1e293b;border-radius:4px;overflow:hidden}
      .cfb{display:block;height:6px;border-radius:4px}
      .rs{padding:2px 9px;border-radius:10px;font-weight:600;font-size:11px;font-family:'IBM Plex Mono',monospace}
      .ok{background:rgba(16,185,129,.15);color:#6ee7b7}
      .no{background:rgba(239,68,68,.15);color:#f87171}
      .nt{color:#334155}
      .mg{font-family:'IBM Plex Mono',monospace;font-weight:600;color:#e2e8f0}
      .qt{display:inline-block;margin-left:7px;padding:1px 6px;border-radius:4px;font-family:'IBM Plex Mono',monospace;font-size:9px;font-weight:700;
        letter-spacing:.4px;vertical-align:middle;background:rgba(245,158,11,.14);color:#fcd34d;border:1px solid rgba(245,158,11,.3)}
      .qt.dnp{background:rgba(239,68,68,.14);color:#f87171;border-color:rgba(239,68,68,.3)}

      .det{border:1px solid #1e293b;border-radius:12px;padding:0 0 18px;margin-top:20px;background:#111827;overflow:hidden}
      .det .band{height:4px}
      .det h4{font-family:'Barlow Condensed',sans-serif;font-size:19px;font-weight:700;letter-spacing:1px;text-transform:uppercase;color:#f1f5f9;margin:16px 22px 4px}
      .det .pk{color:#93c5fd;font-weight:600;margin:0 22px 14px;font-size:13px}
      .det table{width:calc(100% - 44px);margin:0 22px;font-size:12.5px;border-collapse:collapse}
      .det td,.det th{padding:5px 9px;color:#cbd5e1}
      .det thead th{border-bottom:1px solid #1e293b;text-align:right;font-family:'IBM Plex Mono',monospace;font-size:10px;
        text-transform:uppercase;letter-spacing:1.2px;color:#475569;font-weight:600}
      .det thead th:first-child{text-align:left}
      .det td{text-align:right;font-family:'IBM Plex Mono',monospace}
      .det td:first-child{text-align:left;font-family:'Barlow',sans-serif}
      .det tr.sec td{padding-top:13px;font-weight:600;color:#94a3b8}
      .det .rk{color:#334155;font-size:10px}
      .edge{margin:14px 22px 0;padding:10px 13px;background:rgba(30,64,175,.12);border:1px solid rgba(59,130,246,.2);border-radius:7px;font-size:12.5px;color:#bfdbfe}

      .selectize-input,.selectize-dropdown{background:#0a0d14!important;border-color:#334155!important;color:#e2e8f0!important;font-size:13px!important}
      .selectize-input.focus{border-color:#3b82f6!important;box-shadow:0 0 0 2px rgba(59,130,246,.2)!important}
      .selectize-dropdown .active{background:#1e40af!important;color:#fff!important}
      .control-label{font-family:'IBM Plex Mono',monospace;font-size:10px;text-transform:uppercase;letter-spacing:1.5px;color:#64748b}
      .shiny-progress .progress-bar{background:#1e40af}
      .shiny-progress .progress-text{background:#111827!important;border:1px solid #1e293b!important;color:#cbd5e1!important;
        font-family:'IBM Plex Mono',monospace!important;font-size:11px!important;opacity:1!important}

      #splash{position:fixed;inset:0;z-index:9999;background:#0a0d14;display:flex;align-items:center;justify-content:center;
        flex-direction:column;gap:20px;transition:opacity .35s ease}
      #splash.gone{opacity:0;pointer-events:none}
      #splash .t{font-family:'Barlow Condensed',sans-serif;font-size:30px;font-weight:800;letter-spacing:3px;text-transform:uppercase;color:#f1f5f9}
      #splash .s{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#475569;max-width:380px;text-align:center;line-height:1.7}
      #splash .track{width:260px;height:3px;background:#1e293b;border-radius:3px;overflow:hidden}
      #splash .track i{display:block;width:40%;height:3px;border-radius:3px;background:#3b82f6;animation:sweep 1.25s ease-in-out infinite}
      @keyframes sweep{0%{margin-left:-42%}100%{margin-left:102%}}
      table.dataTable tbody tr{background:#111827!important}
      table.dataTable tbody td{background:transparent!important;color:#cbd5e1!important;border-top:1px solid rgba(30,41,59,.85)!important}
      table.dataTable thead th{background:#0a0d14!important}
      #board .dataTables_wrapper,#cboard .dataTables_wrapper{background:#111827;border:1px solid #1e293b;border-radius:12px;overflow:hidden}
      #board table.dataTable,#cboard table.dataTable{margin:0!important}
      #board .dataTables_filter,#cboard .dataTables_filter{padding:10px 14px}
      .side .tab-content{display:none}
      .side .row{margin:0}

      .dash-top{display:flex;align-items:flex-end;justify-content:space-between;gap:16px;flex-wrap:wrap;margin-bottom:4px}
      .dash .section-hdr{margin-top:30px}
      .dash-top .sub{margin-bottom:0}
      .dash-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:12px;margin:0 0 18px}
      .kpi{background:#111827;border:1px solid #1e293b;border-radius:10px;padding:12px 16px}
      .kpi .v{font-family:'IBM Plex Mono',monospace;font-size:22px;font-weight:600;color:#e2e8f0;line-height:1.2}
      .kpi .v.good{color:#6ee7b7}
      .kpi .v.bad{color:#f87171}
      .kpi .l{font-family:'IBM Plex Mono',monospace;font-size:10px;letter-spacing:1.2px;text-transform:uppercase;color:#64748b;margin-top:4px}
      .kpi .s{font-size:11px;color:#94a3b8;margin-top:2px}
      .dtab{width:100%;border-collapse:separate;border-spacing:0;background:#111827;border:1px solid #1e293b;border-radius:12px;overflow:hidden;margin:0 0 6px}
      .dtab th{background:#0a0d14;color:#475569;font-family:'IBM Plex Mono',monospace;font-size:10px;font-weight:600;text-transform:uppercase;letter-spacing:1.5px;text-align:left;padding:10px 14px;border-bottom:1px solid #1e293b;white-space:nowrap}
      .dtab td{padding:9px 14px;border-top:1px solid rgba(30,41,59,.85);color:#cbd5e1;font-size:13px;vertical-align:middle}
      .dtab tbody tr:first-child td{border-top:none}
      .dtab tbody tr:hover td{background:rgba(30,64,175,.09)}
      .dtab th.num,.dtab td.num{text-align:right;font-family:'IBM Plex Mono',monospace;white-space:nowrap}
      .dtab .cf{min-width:130px}
      .dim{color:#64748b}
      .lg-chip{display:inline-block;min-width:46px;text-align:center;padding:2px 7px;border-radius:4px;font-family:'IBM Plex Mono',monospace;font-size:10px;font-weight:600;letter-spacing:.6px}
      .lg-mlb{background:rgba(59,130,246,.16);color:#93c5fd}
      .lg-nfl{background:rgba(16,185,129,.14);color:#6ee7b7}
      .lg-ncaaf{background:rgba(245,158,11,.14);color:#fcd34d}
      .lg-nhl{background:rgba(167,139,250,.16);color:#c4b5fd}
      .lg-nba{background:rgba(239,68,68,.14);color:#fca5a5}
      .dash-lg{display:flex;align-items:center;gap:10px;margin:18px 2px 8px;font-size:13px;color:#94a3b8}
      .dash-note{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#64748b;margin:10px 2px 26px;line-height:1.65;max-width:980px}
      .dash-note b{color:#94a3b8;font-weight:600}
      .dash-wait{color:#475569;font-family:'IBM Plex Mono',monospace;font-size:12px;padding:8px 2px 18px}
      .dash-two{display:grid;grid-template-columns:repeat(auto-fit,minmax(420px,1fr));gap:14px}
      @media (max-width:760px){.content{padding:18px 14px}.dash-two{grid-template-columns:1fr}.dtab td,.dtab th{padding:8px 9px}}
      #shiny-disconnected-overlay{background:rgba(10,13,20,.55)!important;opacity:1!important}
      #shiny-disconnected-overlay::after{content:'Reconnecting\\2026';position:fixed;top:18px;left:50%;transform:translateX(-50%);
        background:#111827;border:1px solid #1e293b;border-radius:8px;padding:9px 16px;color:#cbd5e1;
        font-family:'IBM Plex Mono',monospace;font-size:12px}
"

PROJ_CSS_DASH <- "
      .sp-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(460px,1fr));gap:16px;margin:20px 0 4px}
      .sp{background:#111827;border:1px solid #1e293b;border-radius:12px;overflow:hidden;align-self:start}
      .sp-h{display:flex;align-items:center;gap:12px;padding:12px 16px;background:#0d1320;border-bottom:1px solid #1e293b}
      .sp-h .sp-n{color:#94a3b8;font-size:13px;white-space:nowrap}
      .sp-h .sp-y{margin-left:auto;font-family:'IBM Plex Mono',monospace;font-size:12px;color:#94a3b8;white-space:nowrap}
      .sp-h .sp-y b{color:#e2e8f0;font-weight:600;margin-left:4px}
      .sp-h .sp-y b.good{color:#6ee7b7}
      .sp-h .sp-y b.bad{color:#f87171}
      .sp-go{font-family:'IBM Plex Mono',monospace;font-size:11px;color:#60a5fa;text-decoration:none;white-space:nowrap}
      .sp-go:hover,.sp-go:focus{color:#93c5fd;text-decoration:none}
      .sp-t{width:100%;border-collapse:collapse}
      .sp-t th{color:#475569;font-family:'IBM Plex Mono',monospace;font-size:10px;font-weight:600;letter-spacing:1.3px;text-transform:uppercase;text-align:left;padding:10px 16px 6px;white-space:nowrap}
      .sp-t td{padding:9px 16px;border-top:1px solid rgba(30,41,59,.75);color:#cbd5e1;font-size:13px;vertical-align:middle}
      .sp-t th.num,.sp-t td.num{text-align:right;font-family:'IBM Plex Mono',monospace;white-space:nowrap}
      .sp-t td.st{white-space:nowrap;width:1%}
      .sp-t .when{color:#94a3b8;font-family:'IBM Plex Mono',monospace;font-size:12px}
      .sp-t .bet{font-family:'Barlow Condensed',sans-serif;font-size:17px;font-weight:700;color:#60a5fa}
      .sp-t .vs{color:#64748b;font-size:12px;margin-left:7px;white-space:nowrap}
      .sp-t .odds{color:#e2e8f0;font-weight:600;font-size:14px}
      .sp-t .ev.hi{color:#6ee7b7;font-weight:600}
      .sp-t .rs{white-space:nowrap}
      .rs.live{background:rgba(245,158,11,.14);color:#fcd34d}
      .sp-none{padding:14px 16px;color:#64748b;font-size:12.5px}
      .sp-sub{padding:11px 16px 2px;color:#64748b;font-family:'IBM Plex Mono',monospace;font-size:11px}
      .vsum{background:#0b1018;border:1px solid #1e293b;border-radius:10px;overflow:hidden;margin:20px 0 4px}
      .vs-h{display:flex;align-items:baseline;gap:12px;padding:13px 16px 11px;background:#0d1320;border-bottom:1px solid #1e293b}
      .vs-h .vs-t1{font-family:'Barlow Condensed',sans-serif;font-size:19px;font-weight:700;letter-spacing:.3px;color:#e2e8f0}
      .vs-h .vs-n{color:#64748b;font-size:12px}
      .vsum .sp-t td{padding:8px 16px}
      .vsum .sp-t td.lgc{width:1%;white-space:nowrap}
      .dog{display:inline-block;margin-left:8px;padding:1px 6px;border-radius:3px;background:rgba(251,146,60,.14);
           border:1px solid rgba(251,146,60,.35);color:#fdba74;font-family:'IBM Plex Mono',monospace;
           font-size:9.5px;font-weight:600;letter-spacing:.7px;text-transform:uppercase;vertical-align:1px}
      .vs-more{padding:9px 16px;color:#64748b;font-size:12px;border-top:1px solid rgba(30,41,59,.75)}
      .vs-rec{padding:12px 16px 13px;background:#090d14;border-top:1px solid #1e293b;color:#94a3b8;
              font-size:12px;line-height:1.75}
      .vs-rec b{color:#cbd5e1;font-weight:600}
      .vs-rec .vfig{font-family:'IBM Plex Mono',monospace;color:#e2e8f0}
      .vs-none{padding:16px;color:#64748b;font-size:13px}
      .dash-cav{font-family:'IBM Plex Mono',monospace;font-size:10.5px;color:#475569;margin:12px 2px 0;line-height:1.65;max-width:1000px}
      .dash-cav b{color:#64748b;font-weight:600}
      table.dataTable td.tdx-cell{padding:0!important;background:#0b1120!important;border-top:none!important}
      table.dataTable tbody tr.tdx-open>td{background:rgba(30,64,175,.13)!important}
      table.dataTable tbody tr{cursor:pointer}
      .tdx{padding:12px 18px 14px 26px;border-left:3px solid #1e40af;cursor:default}
      .tdx-h{font-family:'IBM Plex Mono',monospace;font-size:10px;font-weight:600;letter-spacing:1.4px;text-transform:uppercase;color:#94a3b8;margin-bottom:8px}
      .tdx-h span{text-transform:none;letter-spacing:0;font-weight:400;color:#475569}
      .tdx-t{border-collapse:collapse;min-width:540px}
      .tdx-t th{color:#475569;font-family:'IBM Plex Mono',monospace;font-size:9.5px;font-weight:600;letter-spacing:1.2px;text-transform:uppercase;padding:3px 18px 6px 0;text-align:left}
      .tdx-t td{padding:5px 18px 5px 0;border-top:1px solid rgba(30,41,59,.65);color:#cbd5e1;font-size:13px;vertical-align:middle}
      .tdx-t .num{text-align:right;font-family:'IBM Plex Mono',monospace;white-space:nowrap}
      .tdx-t .ps{color:#64748b;font-size:11px;margin-left:9px;white-space:nowrap}
      .tdx-t .pl{white-space:nowrap}
      table.dataTable .tdx-t th,table.dataTable .tdx-t td{background:transparent!important;box-shadow:none!important}
      table.dataTable .tdx-t th{padding:3px 18px 6px 0!important;border-bottom:none!important}
      table.dataTable .tdx-t td{padding:5px 18px 5px 0!important;border-top:1px solid rgba(30,41,59,.65)!important}
      .tdx-none,.tdx-wait{color:#64748b;font-family:'IBM Plex Mono',monospace;font-size:11.5px;padding:2px 0}
      .sm-only{display:none}
      @media (max-width:760px){
        .shell{flex-direction:column}
        .side{width:auto;border-right:none;border-bottom:1px solid #1e293b;padding:6px 0}
        .side .grp{display:none}
        ul#lg.nav{display:flex;flex-wrap:nowrap;overflow-x:auto;padding:0 8px;-webkit-overflow-scrolling:touch}
        ul#lg.nav>li{width:auto;flex:0 0 auto}
        ul#lg.nav>li+li{margin-top:0;margin-left:2px}
        ul#lg.nav>li>a{padding:8px 11px;margin:0;gap:7px}
        .sp-grid{grid-template-columns:1fr}
        .sp-h{flex-wrap:wrap;gap:6px 12px}
        .sp-h .sp-y{margin-left:0}
        .sp-t th,.sp-t td{padding:8px 10px}
        .sp-t .hide-sm{display:none}
        .sp-t .vs{display:block;margin-left:0;margin-top:1px;font-size:11px}
        .sp-t .bet{font-size:15px}
        .sp-t .sm-only{display:inline}
        .sp-t .vs{white-space:normal}
        .sp-t .sm-only .rs{padding:1px 6px;font-size:10px}
        .tdx{padding:10px 10px 12px 12px;position:sticky;left:0;width:calc(100vw - 60px);max-width:calc(100vw - 60px)}
        .tdx-t{min-width:0;width:100%}
        .tdx-t .bdg{width:18px;height:18px;margin-right:6px}
        .tdx-t .ps{margin-left:6px}
        table.dataTable .tdx-t th,table.dataTable .tdx-t td{padding-right:8px!important}
      }
"

# ==================== TODAY (overview) ====================
# The landing page: yesterday's results and today's picks across every league,
# assembled from the same models, ledgers and locks as the league tabs (so a pick
# on this page is always the pick on its own tab).

# Running on a hosting service (shinyapps.io, Posit Connect, Shiny Server)?
dash_hosted <- function() {
  identical(Sys.getenv("R_CONFIG_ACTIVE"), "shinyapps") ||
    identical(toupper(Sys.getenv("RSTUDIO_PRODUCT")), "CONNECT") ||
    nzchar(Sys.getenv("CONNECT_SERVER")) || nzchar(Sys.getenv("SHINY_PORT"))
}

# Rough month-day windows when a league has games worth loading for the overview
# (regular season + playoffs). Outside its window a league is skipped entirely, so
# the page never downloads and fits a sport that is not playing.
DASH_SEASONS <- list(mlb = c(3, 15, 11, 10), nfl = c(8, 1, 2, 20), cfb = c(8, 15, 1, 25),
                     nhl = c(9, 20, 6, 30), nba = c(10, 1, 6, 30))
dash_in_season <- function(lg, d = Sys.Date()) {
  w <- DASH_SEASONS[[lg]]; if (is.null(w)) return(TRUE)
  d <- as.Date(d); md <- as.integer(format(d, "%m")) * 100L + as.integer(format(d, "%d"))
  a <- w[1] * 100 + w[2]; b <- w[3] * 100 + w[4]
  if (a <= b) md >= a && md <= b else md >= a || md <= b
}

# Local clock time of a first pitch / kickoff, in the viewer's time zone.
dash_time <- function(t, tz = "") {
  t <- suppressWarnings(as.POSIXct(t))
  if (!length(t)) return(character())
  tz <- if (is.null(tz) || !nzchar(tz)) "" else tz
  out <- tryCatch(format(t, "%a %l:%M %p", tz = tz), error = function(e) format(t, "%a %l:%M %p"))
  out <- gsub("  +", " ", out)
  ifelse(is.na(t), "", out)
}
dash_local_date <- function(t, tz = "") {
  t <- suppressWarnings(as.POSIXct(t))
  tz <- if (is.null(tz) || !nzchar(tz)) "" else tz
  as.Date(tryCatch(format(t, "%Y-%m-%d", tz = tz), error = function(e) format(t, "%Y-%m-%d")))
}
# Time only for a game today, day and time otherwise.
dash_when <- function(t, tz = "", today = NULL) {
  full <- dash_time(t, tz)
  if (is.null(today) || !length(t)) return(full)
  z <- if (is.null(tz) || !nzchar(tz)) "" else tz
  tm <- tryCatch(format(t, "%l:%M %p", tz = z), error = function(e) format(t, "%l:%M %p"))
  ifelse(!is.na(t) & dash_local_date(t, tz) == today, trimws(gsub("  +", " ", tm)), full)
}
mlb_start_utc <- function(x) {
  x <- as.character(x); x[!nzchar(x)] <- NA_character_
  as.POSIXct(sub("Z$", "", x), format = "%Y-%m-%dT%H:%M:%S", tz = "UTC")
}

# ---- MLB results that nobody opened ------------------------------------------
# A game is graded in the ledgers when its slate is projected again after the final.
# A slate you looked at before first pitch and never re-opened therefore stayed
# ungraded, so "how did yesterday go" had nothing to report. This fills in finished
# results for the recent past from the light schedule/linescore endpoints, under the
# same rule as everywhere else: only the RESULT is written; a pick is never touched.
mlb_grade_pending <- function(days_back = 10L, today = mlb_today()) {
  today <- as.Date(today); lo <- today - as.integer(days_back)
  in_win <- function(x) {
    if (is.null(x) || !nrow(x) || !"GameDate" %in% names(x)) return(logical(NROW(x)))
    d <- suppressWarnings(as.Date(x$GameDate)); !is.na(d) & d >= lo & d < today
  }
  L <- awm_load(); M <- awm_load(AWM_MEMORY_PATH); N <- nrfi_ledger_load(); P <- props_ledger_load()
  pend <- function(x, col) if (!is.null(x) && col %in% names(x)) unique(x$GameID[in_win(x) & is.na(x[[col]])]) else c()
  gids <- unique(c(pend(L, "HomeWon"), pend(M, "HomeWon"), pend(P, "Hit")))
  nids <- pend(N, "ActualNRFI")
  if (!length(gids) && !length(nids)) return(invisible(0L))
  fin <- list()
  for (gid in gids) {
    bs <- tryCatch(fetch_game_boxscore(gid), error = function(e) NULL)
    if (!is.null(bs) && isTRUE(bs$GameStatus %in% c("Final", "Game Over", "Completed Early")) &&
        is.finite(bs$HomeScore) && is.finite(bs$AwayScore) && bs$HomeScore != bs$AwayScore)
      fin[[as.character(gid)]] <- bs
  }
  graded <- 0L
  grade_games <- function(x) {
    if (is.null(x) || !nrow(x) || !"HomeWon" %in% names(x)) return(NULL)
    k <- which(in_win(x) & is.na(x$HomeWon) & as.character(x$GameID) %in% names(fin))
    if (!length(k)) return(NULL)
    for (i in k) {
      bs <- fin[[as.character(x$GameID[i])]]; hw <- as.integer(bs$HomeScore > bs$AwayScore)
      mtc <- as.character(x$Matchup[i]); win <- if (hw == 1L) sub("^.* @ ", "", mtc) else sub(" @ .*$", "", mtc)
      x$HomeWon[i] <- hw; x$Started[i] <- TRUE
      x$IsCorrect[i] <- identical(as.character(x$ProjectedWinner[i]), win)
    }
    graded <<- graded + length(k); x
  }
  L2 <- grade_games(L); if (!is.null(L2)) try(csv_replace(L2, AWM_HISTORY_PATH), silent = TRUE)
  M2 <- grade_games(M); if (!is.null(M2)) try(csv_replace(M2, AWM_MEMORY_PATH), silent = TRUE)
  if (length(nids) && !is.null(N)) {
    ch <- FALSE
    for (gid in nids) {
      fr <- tryCatch(fetch_first_inning_result(gid), error = function(e) NULL)
      if (is.null(fr)) next
      for (i in which(N$GameID == gid & is.na(N$ActualNRFI))) {
        N$ActualNRFI[i] <- fr$nrfi; N$ActualF1Runs[i] <- fr$runs; N$Started[i] <- TRUE
        N$IsCorrect[i] <- (as.character(N$Pick[i]) == "NRFI") == (fr$nrfi == 1L); ch <- TRUE
      }
    }
    if (ch) try(csv_replace(N, NRFI_LEDGER_PATH), silent = TRUE)
  }
  if (!is.null(P) && nrow(P)) {
    pk <- which(in_win(P) & is.na(P$Hit) & !.is_true(P$Graded) & as.character(P$GameID) %in% names(fin))
    if (length(pk)) {
      for (gid in unique(P$GameID[pk])) {
        rows <- pk[P$GameID[pk] == gid]
        hr_rows <- rows[P$Type[rows] == "HR"]; k_rows <- rows[P$Type[rows] == "K"]
        if (length(hr_rows)) {
          st <- tryCatch(fetch_game_player_stats(gid), error = function(e) data.frame())
          for (i in hr_rows) {
            r <- if (nrow(st) && "PlayerID" %in% names(st)) st[!is.na(st$PlayerID) & st$PlayerID == P$PlayerID[i], , drop = FALSE] else st[0, ]
            P$Graded[i] <- TRUE
            if (nrow(r)) { P$Actual[i] <- r$HomeRuns[1]; P$Hit[i] <- isTRUE(r$HomeRuns[1] > 0) }   # no row = did not bat: no grade
          }
        }
        if (length(k_rows)) {
          ks <- tryCatch(fetch_game_sp_ks(gid), error = function(e) NULL)
          for (i in k_rows) {
            P$Graded[i] <- TRUE
            a <- if (!is.null(ks)) ks[[as.character(P$Side[i])]] else NULL
            if (!is.null(a)) {                         # starter went 2+ innings
              P$Actual[i] <- a$k
              P$Hit[i] <- if (identical(as.character(P$Pick[i]), "Over")) a$k > P$Line[i] else a$k < P$Line[i]
            }
          }
        }
      }
      try(csv_replace(P, PROPS_LEDGER_PATH), silent = TRUE)
    }
  }
  invisible(graded)
}

# ---- props ledger (home runs, strikeouts) -------------------------------------
# Today's HR and strikeout picks, kept so the next day's overview can say how they
# went. Same first-pitch rule as the game ledger: a game's props are replaced as a
# set until it starts (lineups change who is ranked), then frozen.
PROPS_LEDGER_PATH <- "props_ledger.csv"
props_ledger_load <- function(path = PROPS_LEDGER_PATH) {
  if (!file.exists(path)) return(NULL)
  h <- tryCatch(read.csv(path, stringsAsFactors = FALSE), error = function(e) NULL)
  if (is.null(h) || !nrow(h)) NULL else h
}
props_rows_from_slate <- function(hr, kp, sched, ds) {
  started <- function(gid) {
    if (is.null(sched) || !nrow(sched)) return(rep(FALSE, length(gid)))
    gs <- sched$GameStatus[match(gid, sched$GameID)]
    !is.na(gs) & grepl("Progress|Live|Final|Over|Completed|Suspended|Review|Challenge", gs, ignore.case = TRUE)
  }
  out <- list()
  if (!is.null(hr) && nrow(hr) && all(c("GameID", "PlayerID") %in% names(hr)))
    out[[1]] <- data.frame(GameDate = ds, GameID = hr$GameID, Type = "HR", PlayerID = hr$PlayerID,
                           Player = hr$Player, Team = hr$Team, Side = NA_character_, Matchup = hr$Matchup,
                           Line = NA_real_, Pick = "HR", Prob = round(as.numeric(hr$HRProbNum) / 100, 4),
                           Started = started(hr$GameID), Graded = FALSE, Actual = NA_real_, Hit = NA,
                           stringsAsFactors = FALSE)
  if (!is.null(kp) && nrow(kp) && all(c("GameID", "PitcherID", "Side") %in% names(kp))) {
    po <- as.numeric(kp$POver) / 100
    out[[2]] <- data.frame(GameDate = ds, GameID = kp$GameID, Type = "K", PlayerID = kp$PitcherID,
                           Player = kp$SP, Team = NA_character_, Side = kp$Side, Matchup = kp$Matchup,
                           Line = as.numeric(kp$Line), Pick = kp$Pick,
                           Prob = round(ifelse(kp$Pick == "Over", po, 1 - po), 4),
                           Started = started(kp$GameID), Graded = FALSE, Actual = NA_real_, Hit = NA,
                           stringsAsFactors = FALSE)
  }
  if (!length(out)) return(NULL)
  dplyr::bind_rows(out)
}
props_ledger_append <- function(new, path = PROPS_LEDGER_PATH) {
  if (is.null(new) || !nrow(new)) return(invisible(FALSE))
  new <- new[!.is_true(new$Started), , drop = FALSE]     # a pick is only recorded before its game starts
  if (!nrow(new)) return(invisible(FALSE))
  old <- props_ledger_load(path)
  if (!is.null(old) && nrow(old)) {
    ko <- paste(old$GameID, old$Type); kn <- paste(new$GameID, new$Type)
    frozen <- unique(ko[.is_true(old$Started) | .is_true(old$Graded)])
    new <- new[!(kn %in% frozen), , drop = FALSE]
    old <- old[!(ko %in% setdiff(unique(kn), frozen)), , drop = FALSE]
    comb <- .ledger_bind(old, new)
  } else comb <- new
  tryCatch({ csv_replace(comb, path); invisible(TRUE) }, error = function(e) invisible(FALSE))
}

# ---- one MLB slate, shared by the MLB tab and the overview ---------------------
mlb_build_slate <- function(ds, progress = function(value, detail) NULL) {
  ds <- format(as.Date(ds), "%Y-%m-%d")
  warm_own("mlb")
  clear_cache()
  mlb_cache_reset_session()
  invisible(mlb_api_alive())
  mlog(sprintf("\n\u2500\u2500 Slate %s \u2500\u2500", ds))
  progress(0.02, "Updating model memory\u2026")
  tryCatch(awm_catch_up(end_date = min(as.Date(ds), Sys.Date()) - 1,
                        on_progress = function(f, dd) progress(0.02 + 0.16*f, paste0("Learning from ", dd, "\u2026"))),
           error = function(e) NULL)
  tryCatch(nrfi_catch_up(end_date = min(as.Date(ds), Sys.Date()) - 1,
                         on_progress = function(f, dd) progress(0.18 + 0.07*f, paste0("First innings from ", dd, "\u2026"))),
           error = function(e) NULL)
  tryCatch(mlb_grade_pending(), error = function(e) NULL)
  progress(0.25, "Schedule & point-in-time game logs\u2026")
  d <- prepare_data(recent_games=15L, date_str=ds)
  progress(0.45, "Run model (point-in-time, no leakage)\u2026")
  proj <- run_game_projection(d, as.Date(ds))
  progress(0.78, "Home-run model\u2026")
  hrp <- project_home_run_hitters(d$schedule_df, d$player_batting_df, d$pitching_df,
                                  d$recent_player_batting_df, d$recent_pitching_df, d$pitcher_stats_dict,
                                  top_n_per_game=3L, season=d$season)
  kprops <- tryCatch(project_pitcher_strikeouts(d$schedule_df, d$pitcher_stats_dict,
                                                d$pitching_df, season=d$season, allow_completed=TRUE,
                                                team_batting_df=d$team_batting_cur), error=function(e) data.frame())
  progress(0.90, "First-inning model (exact base-out DP)\u2026")
  nrfi <- tryCatch(project_first_inning(d$schedule_df, d$player_batting_df, d$pitching_df,
                                        d$pitcher_stats_dict, team_batting_df=d$team_batting_df,
                                        season=d$season, slate_date=as.Date(ds)),
                   error=function(e) data.frame())
  # props are recorded for the live slate only (a past date re-run is a replay, not a pick).
  # "Live" allows yesterday by the server clock: a hosted server runs on UTC, which is
  # already tomorrow during a North American evening. Started games are never recorded.
  if (as.Date(ds) >= Sys.Date() - 1)
    tryCatch(props_ledger_append(props_rows_from_slate(hrp, kprops, d$schedule_df, ds)), error = function(e) NULL)
  progress(1.0, "")
  acc <- tryCatch(compute_accuracy_summary(proj), error=function(e) NULL)
  if (!is.null(acc) && acc$total > 0)
    mlog(sprintf("Slate      | %d games \u00b7 record %d-%d (%.0f%%)",
                 nrow(proj), acc$correct, acc$total - acc$correct, acc$pct))
  else
    mlog(sprintf("Slate      | %d games \u00b7 none graded yet", nrow(proj)))
  mlog_http_report()
  cs <- mlb_cache_stats()
  mlog(sprintf("Cache      | %d files (%.1f MB) \u00b7 %d served from disk, %d fetched%s",
               cs$files, cs$mb, cs$hits, cs$miss,
               if (isTRUE(cs$offline)) " \u00b7 API unreachable" else ""))
  sched <- d$schedule_df
  sched <- if (!is.null(sched) && nrow(sched))
    sched[, intersect(c("GameID", "GameStatus", "StartUTC", "HomeTeam", "AwayTeam", "HomePitcher", "AwayPitcher"),
                      names(sched)), drop = FALSE] else data.frame()
  list(proj=proj, hr=hrp, kprops=kprops, nrfi=nrfi, si=d$season_info,
       season=d$season, cache=cs, sched=sched, date=as.Date(ds))
}

# Run an observer's body so that a failure (a feed that is down, a file that is
# missing) becomes a notification instead of ending the session. In Shiny an error
# inside an observer closes the connection -- that is the grey "Disconnected from
# the server" screen -- and the only way back was a full reload.
dash_guard <- function(label, expr) {
  tryCatch(expr, error = function(e) {
    if (inherits(e, "shiny.silent.error")) return(invisible(NULL))
    msg <- paste0(label, ": ", conditionMessage(e))
    try(mlog(paste("Session    |", msg)), silent = TRUE)
    try(shiny::showNotification(msg, type = "warning", duration = 10), silent = TRUE)
    invisible(NULL)
  })
}

# ---- small HTML pieces for the overview -----------------------------------------
dash_esc <- function(x) htmltools::htmlEscape(ifelse(is.na(x), "", as.character(x)))
dash_chip <- function(lg) sprintf('<span class="lg-chip lg-%s">%s</span>', tolower(lg),
                                  c(MLB = "MLB", NFL = "NFL", NCAAF = "NCAAF", NHL = "NHL", NBA = "NBA")[lg])
dash_result <- function(res, final = "") {
  ifelse(is.na(res), ifelse(nzchar(final), sprintf('<span class="nt">%s</span>', dash_esc(final)), '<span class="nt">&mdash;</span>'),
         ifelse(res, sprintf('<span class="rs ok">&#10003; %s</span>', dash_esc(final)),
                     sprintf('<span class="rs no">&#10007; %s</span>', dash_esc(final))))
}
dash_table <- function(head, rows, cls = NULL, num = integer()) {
  if (!length(rows)) return("")
  th <- paste(sprintf('<th%s>%s</th>', ifelse(seq_along(head) %in% num, ' class="num"', ""), head), collapse = "")
  tr <- vapply(rows, function(r) paste0("<tr>", paste(sprintf('<td%s>%s</td>',
         ifelse(seq_along(r) %in% num, ' class="num"', ""), r), collapse = ""), "</tr>"), "")
  sprintf('<table class="dtab%s"><thead><tr>%s</tr></thead><tbody>%s</tbody></table>',
          if (is.null(cls)) "" else paste0(" ", cls), th, paste(tr, collapse = ""))
}
dash_record <- function(ok) {                        # ok: logical vector of graded picks
  ok <- ok[!is.na(ok)]; n <- length(ok); w <- sum(ok)
  list(n = n, w = w, txt = if (n) sprintf("%d\u2013%d", w, n - w) else "\u2014",
       pct = if (n) 100 * w / n else NA_real_)
}

# What picks like the ones on the overview have actually done, measured from the lines
# ledger: every pick whose price was frozen at the start and whose game then finished.
# Computed rather than written down, so the page cannot keep advertising an edge the
# results have stopped supporting.
#
#   all  every settled pick       val  the ones this page would have listed
#   dog  the model backing the book's underdog -- the projected upsets
dash_edge_record <- function(L, min_n = 20L) {
  if (is.null(L) || !nrow(L) || !all(c("Result", "Profit", "ModelP", "VegasP") %in% names(L))) return(NULL)
  g <- L[L$Result %in% c("W", "L") & is.finite(suppressWarnings(as.numeric(L$Profit))), , drop = FALSE]
  if (nrow(g) < min_n) return(NULL)
  g$y <- as.integer(g$Result == "W")
  g$pl <- suppressWarnings(as.numeric(g$Profit))
  g$ed <- suppressWarnings(as.numeric(g$ModelP)) - suppressWarnings(as.numeric(g$VegasP))
  cut <- function(x) {
    if (!nrow(x)) return(NULL)
    roi <- 100 * sum(x$pl) / nrow(x)
    se <- if (nrow(x) > 1) 100 * stats::sd(x$pl) / sqrt(nrow(x)) else NA_real_
    list(n = nrow(x), w = sum(x$y), l = sum(1L - x$y), roi = roi, se = se,
         said = 100 * mean(x$ModelP, na.rm = TRUE), book = 100 * mean(x$VegasP, na.rm = TRUE),
         won = 100 * mean(x$y))
  }
  # the number of settled bets a 5%-a-bet edge would need before it clears the noise
  sd1 <- if (nrow(g) > 1) stats::sd(g$pl) else 1
  list(all = cut(g),
       val = cut(g[dash_is_value(g$ModelP, g$VegasP, g$EV), , drop = FALSE]),
       dog = cut(g[is.finite(g$VegasP) & g$VegasP < 0.5, , drop = FALSE]),
       need = ceiling((2.8 * sd1 / 0.05)^2 / 50) * 50,
       from = suppressWarnings(min(as.Date(g$StartT), na.rm = TRUE)))
}

# ==================== MARKET LINES ====================
# The book's moneylines come from ESPN's public scoreboard feed (DraftKings lines; no
# key, no scraping of a sportsbook). Kept per league and date: who plays, when, both
# moneylines and, once a game is over, the score. A game's odds leave the feed when it
# ends, so the price a pick was shown at is saved in the bets ledger before first pitch.
ESPN_DIR   <- file.path("proj_cache", "espn")
ESPN_SPORT <- c(nfl = "football/nfl", cfb = "football/college-football", mlb = "baseball/mlb",
                nhl = "hockey/nhl", nba = "basketball/nba")
ESPN_LG    <- c(NFL = "nfl", NCAAF = "cfb", MLB = "mlb", NHL = "nhl", NBA = "nba")
.espn_mem  <- new.env(parent = emptyenv())

# One request, short timeout. If the feed is unreachable or failing, it is left alone
# for 3 minutes, so a dead feed costs one timeout, not one per league and date (every
# visitor shares the one R process on a host).
espn_get <- function(url, timeout = 8) {
  down <- .espn_mem[[".down"]]
  if (!is.null(down) && as.numeric(difftime(Sys.time(), down, units = "mins")) < 3) return(NULL)
  r <- tryCatch(httr::GET(url, httr::timeout(timeout), httr::user_agent("Mozilla/5.0 (Projections)")),
                error = function(e) NULL)
  code <- if (is.null(r)) NA_integer_ else httr::status_code(r)
  if (isTRUE(code == 200L)) {
    txt <- tryCatch(httr::content(r, as = "text", encoding = "UTF-8"), error = function(e) NULL)
    j <- if (is.null(txt)) NULL else tryCatch(jsonlite::fromJSON(txt, simplifyVector = FALSE), error = function(e) NULL)
    if (!is.null(j)) return(j)
  }
  if (is.na(code) || code >= 500L || code == 403L || code == 429L) .espn_mem[[".down"]] <- Sys.time()
  NULL
}

# Parsed results are kept on disk. Within `ttl` minutes a copy is reused; after that
# the feed is asked again, and if it cannot be reached the last copy is used whatever
# its age (yesterday's line beats no line), with a new attempt at most every 2 minutes.
espn_cached <- function(key, ttl, build) {
  now <- Sys.time()
  fresh <- function(o) !is.null(o) && !is.null(o$v) &&
    (isTRUE(o$final) || as.numeric(difftime(now, o$t, units = "mins")) < ttl)
  hit <- .espn_mem[[key]]
  if (fresh(hit)) return(hit$v)
  f <- file.path(ESPN_DIR, paste0(key, ".rds"))
  if (is.null(hit) && file.exists(f)) {
    hit <- tryCatch(readRDS(f), error = function(e) NULL)
    if (fresh(hit)) { .espn_mem[[key]] <- hit; return(hit$v) }
  }
  if (!is.null(hit$chk) && as.numeric(difftime(now, hit$chk, units = "mins")) < 2) return(hit$v)
  v <- tryCatch(build(), error = function(e) NULL)
  if (is.null(v)) {
    if (is.null(hit)) hit <- list(v = NULL, t = now)
    hit$chk <- now; .espn_mem[[key]] <- hit
    return(hit$v)
  }
  obj <- list(v = v, t = now, chk = now, final = isTRUE(attr(v, "final")))
  .espn_mem[[key]] <- obj
  dir.create(ESPN_DIR, showWarnings = FALSE, recursive = TRUE)
  tmp <- paste0(f, ".tmp")
  ok <- try({ saveRDS(obj, tmp); file.rename(tmp, f) }, silent = TRUE)
  if (inherits(ok, "try-error")) unlink(tmp)
  v
}

espn_time <- function(x) {
  x <- sub("Z$", "", as.character(x))
  t <- as.POSIXct(x, format = "%Y-%m-%dT%H:%M:%S", tz = "UTC")
  bad <- is.na(t)
  if (any(bad)) t[bad] <- as.POSIXct(x[bad], format = "%Y-%m-%dT%H:%M", tz = "UTC")
  t
}

# "+950" / "-1650" / "EVEN" / -192 -> American price; "OFF", blanks and junk -> NA
espn_ml <- function(x) {
  if (is.null(x) || !length(x)) return(NA_real_)
  s <- toupper(trimws(as.character(x[[1]])))
  if (is.na(s) || !nzchar(s)) return(NA_real_)
  if (s %in% c("EVEN", "EV")) return(100)
  v <- suppressWarnings(as.numeric(sub("^\\+", "", s)))
  if (!is.finite(v) || abs(v) < 100) NA_real_ else v
}

espn_event <- function(ev) {
  cp <- if (length(ev$competitions)) ev$competitions[[1]] else NULL
  if (is.null(cp) || length(cp$competitors) < 2L) return(NULL)
  side <- function(ha) { for (x in cp$competitors) if (identical(x$homeAway, ha)) return(x); NULL }
  h <- side("home"); a <- side("away")
  if (is.null(h) || is.null(a)) return(NULL)
  tf <- function(x, f) { v <- x$team[[f]]; if (is.null(v) || !length(v)) NA_character_ else as.character(v[[1]]) }
  sc <- function(x) suppressWarnings(as.numeric(x$score %||% NA))
  o  <- if (length(cp$odds)) cp$odds[[1]] else NULL
  st <- ev$status$type %||% cp$status$type
  mh <- if (is.null(o)) NA_real_ else
    espn_ml(o$moneyline$home$close$odds %||% o$moneyline$home$open$odds %||% o$homeTeamOdds$moneyLine)
  ma <- if (is.null(o)) NA_real_ else
    espn_ml(o$moneyline$away$close$odds %||% o$moneyline$away$open$odds %||% o$awayTeamOdds$moneyLine)
  data.frame(eid = as.character(ev$id %||% cp$id %||% NA), start = espn_time(ev$date %||% cp$date %||% NA),
             state = as.character(st$state %||% NA), done = isTRUE(st$completed),
             stname = as.character(st$name %||% NA),
             h_id = tf(h, "id"), h_abbr = tf(h, "abbreviation"), h_name = tf(h, "displayName"),
             h_nick = tf(h, "name"), h_loc = tf(h, "location"),
             a_id = tf(a, "id"), a_abbr = tf(a, "abbreviation"), a_name = tf(a, "displayName"),
             a_nick = tf(a, "name"), a_loc = tf(a, "location"),
             h_score = sc(h), a_score = sc(a), h_win = isTRUE(h$winner), a_win = isTRUE(a$winner),
             ml_h = mh, ml_a = ma,
             book = if (is.null(o)) NA_character_ else gsub("\\s+", "", as.character(o$provider$name %||% NA)),
             stringsAsFactors = FALSE)
}

espn_parse <- function(j) {
  ev <- lapply(j$events %||% list(), function(e) tryCatch(espn_event(e), error = function(err) NULL))
  ev <- ev[!vapply(ev, is.null, logical(1))]
  if (!length(ev)) return(data.frame(eid = character(0), start = as.POSIXct(character(0), tz = "UTC"),
                                     stringsAsFactors = FALSE))
  dplyr::bind_rows(ev)
}

# One league's games on one date (US Eastern date, as ESPN files them).
espn_scoreboard <- function(lg, date) {
  date <- as.Date(date)
  if (is.na(date) || !lg %in% names(ESPN_SPORT)) return(NULL)
  ds <- format(date, "%Y%m%d")
  url <- sprintf("https://site.api.espn.com/apis/site/v2/sports/%s/scoreboard?dates=%s&limit=300%s",
                 ESPN_SPORT[[lg]], ds, if (lg == "cfb") "&groups=80" else "")
  past <- date < as.Date(format(Sys.time(), "%Y-%m-%d", tz = TZ_ET))
  espn_cached(paste0("sb_", lg, "_", ds), ttl = if (past) 20 else 8, function() {
    j <- espn_get(url)
    if (is.null(j)) return(NULL)
    out <- espn_parse(j)
    attr(out, "final") <- past && nrow(out) > 0L && all(out$state %in% "post")
    out
  })
}

# accents are folded by hand first: transliteration depends on the server's locale
ESPN_ACC_FROM <- paste0("\u00e1\u00e0\u00e2\u00e4\u00e3\u00e5\u00e9\u00e8\u00ea\u00eb\u00ed\u00ec\u00ee\u00ef\u00f3",
                        "\u00f2\u00f4\u00f6\u00f5\u00fa\u00f9\u00fb\u00fc\u00f1\u00e7\u00c1\u00c0\u00c2\u00c4\u00c3",
                        "\u00c5\u00c9\u00c8\u00ca\u00cb\u00cd\u00cc\u00ce\u00cf\u00d3\u00d2\u00d4\u00d6\u00d5\u00da",
                        "\u00d9\u00db\u00dc\u00d1\u00c7")
ESPN_ACC_TO   <- "aaaaaaeeeeiiiiooooouuuuncAAAAAAEEEEIIIIOOOOOUUUUNC"
espn_norm <- function(x) {
  x <- enc2utf8(as.character(x))
  x <- tryCatch(chartr(ESPN_ACC_FROM, ESPN_ACC_TO, x), error = function(e) x)
  x <- gsub("['\u2019\u02bb`]", "", x)
  x <- suppressWarnings(iconv(x, from = "UTF-8", to = "ASCII//TRANSLIT", sub = ""))
  x <- tolower(x); x[is.na(x)] <- ""
  trimws(gsub("\\s+", " ", gsub("[^a-z0-9 ]", " ", x)))
}
espn_nick <- function(x) {
  vapply(strsplit(espn_norm(x), " ", fixed = TRUE), function(p) {
    p <- p[nzchar(p)]; n <- length(p)
    if (!n) "" else if (p[n] == "sox" && n >= 2L) paste(p[n - 1L], p[n]) else p[n]
  }, "")
}
espn_keys <- function(...) { k <- unique(c(...)); k[!is.na(k) & nzchar(k)] }

# Which feed game is each of our games? By event id where our data carries ESPN's
# (college football, NBA, NFL), otherwise by both team names within 18 hours of the
# start. A game listed the other way round (neutral site) is matched with flip = TRUE.
espn_find <- function(home, away, t, eid, ev, home2 = NULL, away2 = NULL) {
  n <- length(home); idx <- rep(NA_integer_, n); flip <- rep(FALSE, n)
  if (is.null(home2)) home2 <- rep(NA_character_, n)
  if (is.null(away2)) away2 <- rep(NA_character_, n)
  if (is.null(ev) || !nrow(ev) || !n) return(list(idx = idx, flip = flip))
  if (!is.null(eid)) idx <- match(as.character(eid), ev$eid)
  todo <- which(is.na(idx))
  if (!length(todo)) return(list(idx = idx, flip = flip))
  hk <- lapply(seq_len(nrow(ev)), function(j) espn_keys(espn_norm(ev$h_name[j]), espn_norm(ev$h_loc[j]),
               espn_nick(ev$h_name[j]), espn_norm(ev$h_nick[j]), espn_norm(ev$h_abbr[j])))
  ak <- lapply(seq_len(nrow(ev)), function(j) espn_keys(espn_norm(ev$a_name[j]), espn_norm(ev$a_loc[j]),
               espn_nick(ev$a_name[j]), espn_norm(ev$a_nick[j]), espn_norm(ev$a_abbr[j])))
  for (i in todo) {
    mh <- espn_keys(espn_norm(home[i]), espn_nick(home[i]), espn_norm(home2[i]))
    ma <- espn_keys(espn_norm(away[i]), espn_nick(away[i]), espn_norm(away2[i]))
    if (!length(mh) || !length(ma)) next
    near <- if (is.na(t[i])) rep(TRUE, nrow(ev)) else
      !is.na(ev$start) & abs(as.numeric(difftime(ev$start, t[i], units = "hours"))) < 18
    hit <- function(K, k) vapply(K, function(z) any(k %in% z), logical(1))
    ok <- which(near & hit(hk, mh) & hit(ak, ma)); fl <- FALSE
    if (!length(ok)) { ok <- which(near & hit(hk, ma) & hit(ak, mh)); fl <- TRUE }
    if (!length(ok)) next
    if (length(ok) > 1L && !is.na(t[i]))
      ok <- ok[which.min(abs(as.numeric(difftime(ev$start[ok], t[i], units = "mins"))))]
    idx[i] <- ok[1]; flip[i] <- fl
  }
  list(idx = idx, flip = flip)
}

# ---- prices -----------------------------------------------------------------------
am2dec <- function(ml) {
  ml <- suppressWarnings(as.numeric(ml))
  ifelse(is.na(ml) | abs(ml) < 100, NA_real_, ifelse(ml < 0, 1 + 100 / abs(ml), 1 + ml / 100))
}
# Break-even decimal price for a probability: a bet on it has value only above this.
fair_dec <- function(p) {
  p <- suppressWarnings(as.numeric(p))
  ifelse(is.finite(p) & p > 0.005 & p < 0.995, 1 / p, NA_real_)
}
fmt_dec <- function(x) ifelse(is.finite(x), sprintf("%.2f", x), "\u2014")
# An edge of a third of a percent rounds to "+0%", which reads as nothing at all when it
# is in fact the smallest positive number on the page. Below one per cent, show it.
dash_ev <- function(ev) ifelse(!is.finite(ev), "&mdash;",
                        ifelse(abs(ev) < 0.01, sprintf("%+.2f%%", 100 * ev),
                                               sprintf("%+.0f%%", 100 * ev)))
fmt_units <- function(u) ifelse(is.finite(u), sprintf("%s%.2fu", ifelse(u >= 0, "+", "\u2212"), abs(u)), "")

DASH_TOP_N      <- 3      # value picks per league on the overview
# What counts as a value pick, defined once and in the units that matter: the price pays
# more than the model's chance is worth. EV = model chance x decimal price - 1, so a
# positive figure already clears the book's margin. No threshold beyond zero, because
# zero is the only bar on this page that is not arbitrary.
#
# There used to be a second condition -- the model at least three points of win
# probability over the line's fair chance. It went, for three reasons. It read as three
# points of margin, which is what "points" means everywhere else here. It was 0.34 of a
# standard deviation of the model's own typical gap from the price (6.8pp, sd 8.9pp), so
# it screened almost nothing, and it bought 0.4% of expected value at college football's
# typical price against 1.3% at hockey's -- not even the same bar across sports. And it
# did not work: across the settled ledger the win rate is 46, 47, 48, 47 and 50 per cent
# at buffers of 0, 3, 6, 10 and 15 points. The returns drift up with the buffer only
# because a higher one selects longer prices, so a win pays more; the picks are no better.
#
# What guards the list instead is on the list: the model's number beside the book's on
# every row, and the measured record underneath it.
dash_is_value <- function(p, vegas, ev) is.finite(ev) & ev > 0
# why a slate has nothing to list
dash_why_none <- function(n)
  sprintf("on %s the price already implies at least the model's chance",
          sprintf("%s game%s", if (n == 1) "the" else sprintf("all %d", n), if (n == 1) "" else "s"))

# ---- lines ledger -----------------------------------------------------------------
# Every game of the day the overview priced: the model's pick, its chance, the line's
# no-vig chance and decimal price. A game's odds leave the feed once it is played, so
# this is what keeps a value pick's price on the page after it starts. Like the other
# ledgers: a row is refreshed until its game starts, then frozen, then graded.
LINES_LEDGER_PATH <- "lines_ledger.csv"
lines_ledger_load <- function(path = LINES_LEDGER_PATH) {
  if (!file.exists(path)) return(NULL)
  h <- tryCatch(read.csv(path, stringsAsFactors = FALSE,
                         colClasses = c(EventID = "character", Result = "character", Start = "character")),
                error = function(e) NULL)
  if (is.null(h) || !nrow(h)) return(NULL)
  h$StartT <- as.POSIXct(h$Start, format = "%Y-%m-%d %H:%M:%S", tz = "UTC")
  h
}
lines_ledger_write <- function(L, path = LINES_LEDGER_PATH) {
  L$StartT <- NULL
  tmp <- paste0(path, ".tmp")
  ok <- try({ write.csv(L, tmp, row.names = FALSE); file.rename(tmp, path) }, silent = TRUE)
  if (inherits(ok, "try-error")) unlink(tmp)
  invisible(!inherits(ok, "try-error"))
}
lines_rows <- function(x, now = Sys.time()) {
  if (is.null(x) || !nrow(x)) return(NULL)
  x <- x[!is.na(x$eid_m) & nzchar(x$eid_m), , drop = FALSE]
  if (!nrow(x)) return(NULL)
  data.frame(League = x$lg, EventID = as.character(x$eid_m),
             Start = format(x$t, "%Y-%m-%d %H:%M:%S", tz = "UTC"),
             Matchup = x$matchup, Pick = x$pick, Side = x$side_m,
             ModelP = round(x$p, 4), VegasP = round(x$vegas, 4), Odds = round(x$dec_p, 3),
             EV = round(x$ev, 4), Book = x$book_m,
             Recorded = format(now, "%Y-%m-%d %H:%M:%S", tz = "UTC"),
             Result = NA_character_, Profit = NA_real_, stringsAsFactors = FALSE)
}
# new: today's priced games; priced: "League EventID" of every game whose line was read
lines_ledger_sync <- function(new, priced, now = Sys.time(), path = LINES_LEDGER_PATH) {
  old <- lines_ledger_load(path)
  key <- function(d) paste(d$League, d$EventID)
  n_old <- if (is.null(old)) 0L else nrow(old)
  if (!is.null(old)) {
    frozen <- (!is.na(old$StartT) & old$StartT <= now) | !is.na(old$Result)
    old <- old[frozen | !(key(old) %in% priced), , drop = FALSE]
    if (!is.null(new) && nrow(new)) new <- new[!(key(new) %in% key(old)), , drop = FALSE]
  }
  has_new <- !is.null(new) && nrow(new) > 0L
  if (!has_new && (is.null(old) || nrow(old) == n_old)) return(invisible(FALSE))
  if (!is.null(old)) old <- old[, setdiff(names(old), "StartT"), drop = FALSE]
  comb <- if (!has_new) old else if (is.null(old) || !nrow(old)) new else .ledger_bind(old, new)
  lines_ledger_write(comb, path)
}
# Results from the feed's final scores (ESPN files a game under its US Eastern date).
lines_ledger_grade <- function(now = Sys.time(), path = LINES_LEDGER_PATH) {
  L <- lines_ledger_load(path)
  if (is.null(L)) return(invisible(NULL))
  todo <- which(is.na(L$Result) & !is.na(L$StartT) & L$StartT < now - 2.5 * 3600)
  if (!length(todo)) return(invisible(L))
  ch <- FALSE
  grp <- paste(L$League[todo], format(L$StartT[todo], "%Y-%m-%d", tz = TZ_ET))
  for (g in split(todo, grp)) {
    lg <- ESPN_LG[L$League[g[1]]]
    if (is.na(lg)) next
    ev <- espn_scoreboard(lg, as.Date(format(L$StartT[g[1]], "%Y-%m-%d", tz = TZ_ET)))
    if (is.null(ev) || !nrow(ev)) next
    for (i in g) {
      k <- match(L$EventID[i], ev$eid)
      if (is.na(k) || !identical(ev$state[k], "post")) next
      if (grepl("POSTPONED|CANCEL|FORFEIT|SUSPENDED", toupper(ev$stname[k]))) {
        L$Result[i] <- "V"; L$Profit[i] <- 0; ch <- TRUE; next
      }
      hs <- ev$h_score[k]; as <- ev$a_score[k]
      if (!isTRUE(ev$done[k]) || !is.finite(hs) || !is.finite(as)) next
      if (hs == as) { L$Result[i] <- "P"; L$Profit[i] <- 0 }
      else {
        won <- identical(L$Side[i], "home") == (hs > as)
        L$Result[i] <- if (won) "W" else "L"
        L$Profit[i] <- if (won) round(as.numeric(L$Odds[i]) - 1, 3) else -1
      }
      ch <- TRUE
    }
  }
  if (ch) lines_ledger_write(L, path)
  invisible(L)
}
lines_record <- function(L) {
  if (is.null(L) || !nrow(L)) return(list(n = 0L, w = 0L, l = 0L, units = 0, txt = "\u2014"))
  g <- L[!is.na(L$Result) & L$Result %in% c("W", "L", "P"), , drop = FALSE]
  w <- sum(g$Result == "W"); l <- sum(g$Result == "L")
  u <- sum(suppressWarnings(as.numeric(g$Profit)), na.rm = TRUE)
  list(n = nrow(g), w = w, l = l, units = u,
       txt = if (w + l) sprintf("%d\u2013%d", w, l) else "\u2014")
}

# Short team names for the overview: "Atlanta Braves" -> "Braves" (college names stay).
DASH_TWO_WORD <- c("red sox", "white sox", "blue jays", "maple leafs", "golden knights",
                   "red wings", "blue jackets", "trail blazers")
# Cities whose name takes two words. The NHL feed names a team by its place alone
# ("New York", "New Jersey"), so dropping the first word to get a nickname instead
# produced "York" and "Jersey" on the overview.
DASH_CITY_2W <- c("new", "los", "san", "st.", "saint", "las", "salt", "kansas",
                  "tampa", "green", "oklahoma", "golden", "west", "north", "south", "east")
dash_short <- function(lg, x) {
  x <- as.character(x); out <- x
  for (i in which(lg %in% c("MLB", "NHL", "NBA") & !is.na(x))) {
    if (grepl(" Hockey Club$", x[i])) { out[i] <- sub(" Hockey Club$", "", x[i]); next }
    w <- strsplit(x[i], " ", fixed = TRUE)[[1]]; n <- length(w)
    if (n >= 3L && tolower(paste(w[n - 1L], w[n])) %in% DASH_TWO_WORD) out[i] <- paste(w[n - 1L], w[n])
    else if (n == 2L && tolower(w[1]) %in% DASH_CITY_2W) out[i] <- x[i]   # a place, not a nickname
    else if (n >= 2L) out[i] <- w[n]
  }
  out
}

nav_item <- function(icon, label, soon = FALSE) tagList(
  span(class = "nv-ic", icon), span(label),
  if (soon) span(class = "soon-tag", "SOON"))

ui <- fluidPage(
  tags$head(
    tags$link(rel = "stylesheet",
              href = "https://fonts.googleapis.com/css2?family=Barlow+Condensed:wght@400;600;700;800&family=IBM+Plex+Mono:wght@400;500;600&family=Barlow:wght@400;500;600&display=swap"),
    tags$style(HTML(paste0(PROJ_CSS_BASE, PROJ_CSS_EXTRA, PROJ_CSS_DASH)))
  ),
  tags$script(HTML("
    var go = function(ms) { setTimeout(function(){ $('#splash').addClass('gone'); }, ms); };
    $(document).on('shiny:value', function(e) {
      if (e.name === 'td_tbl' || e.name === 'cboard' || e.name === 'games_tbl' ||
          e.name === 'nboard' || e.name === 'bboard' || e.name === 'dash_sports' ||
          e.name === 'dash_date') go(250);
      if (e.name === 'board' || e.name === 'accuracy_ui') go(20000);
    });
    setTimeout(function(){ go(0); }, 240000);

    // a click on a board row opens that game's likely touchdown scorers under it
    window.tdxBind = function(table, tbl, inputId, col, pickId) {
      table.on('click', 'tbody tr', function() {
        var row = table.row(this), d = row.data();
        if (!d || d[col] === undefined || d[col] === null) return;
        var gid = String(d[col]), tr = $(this);
        if (row.child.isShown()) {
          row.child.hide(); tr.removeClass('tdx-open');
          if (pickId) Shiny.setInputValue(pickId, null);
          return;
        }
        row.child('<div class=tdx><div class=tdx-wait>Loading touchdown scorers&hellip;</div></div>', 'tdx-cell').show();
        tr.addClass('tdx-open');
        (window.__tdx = window.__tdx || {})[tbl + '|' + gid] = row;
        Shiny.setInputValue(inputId, { gid: gid, n: Date.now() }, { priority: 'event' });
        if (pickId) Shiny.setInputValue(pickId, row.index() + 1);
      });
    };
    $(function() {
      Shiny.addCustomMessageHandler('tdx', function(m) {
        var row = window.__tdx && window.__tdx[m.tbl + '|' + m.gid];
        if (row && row.child.isShown()) row.child(m.html, 'tdx-cell').show();
      });
    });

    // the viewer's own date and time zone (a hosted server's clock is UTC)
    $(document).on('shiny:connected', function() {
      var d = new Date(), p = function(n) { return (n < 10 ? '0' : '') + n; };
      Shiny.setInputValue('client_today', d.getFullYear() + '-' + p(d.getMonth() + 1) + '-' + p(d.getDate()));
      try { Shiny.setInputValue('client_tz', Intl.DateTimeFormat().resolvedOptions().timeZone); } catch (err) {}
    });

    // Keep-alive: a tiny message every 25 s while someone is using the page, so a
    // host's idle timer never closes an open tab. After an hour with no mouse or
    // keyboard activity it stops, and the host may let the app sleep.
    (function() {
      var last = Date.now();
      ['mousemove', 'mousedown', 'keydown', 'scroll', 'wheel', 'touchstart'].forEach(function(ev) {
        document.addEventListener(ev, function() { last = Date.now(); }, { passive: true });
      });
      var up = function() { return !!(window.Shiny && Shiny.shinyapp && Shiny.shinyapp.isConnected()); };
      setInterval(function() {
        if (!up() || Date.now() - last > 3600000) return;
        Shiny.setInputValue('keepalive', Date.now(), { priority: 'event' });
      }, 25000);
      // If the connection drops and cannot be re-established, reload in place: the
      // address bar carries the tab and date, so you land where you were. At most
      // three tries in ten minutes, so a stopped server does not reload forever.
      // An unattended tab (hidden, or nobody at the keyboard for an hour) is not
      // reloaded -- that would keep waking the host for nobody; it heals the moment
      // someone comes back to it.
      var pending = false;
      var heal = function(ms) {
        setTimeout(function() {
          if (up()) return;
          if (document.visibilityState !== 'visible' || Date.now() - last > 3600000) { pending = true; return; }
          var t = [];
          try { t = JSON.parse(sessionStorage.getItem('proj_reloads') || '[]'); } catch (err) {}
          t = t.filter(function(x) { return Date.now() - x < 600000; });
          if (t.length >= 3) return;
          t.push(Date.now());
          try { sessionStorage.setItem('proj_reloads', JSON.stringify(t)); } catch (err) {}
          location.reload();
        }, ms);
      };
      $(document).on('shiny:disconnected', function() { heal(8000); });
      document.addEventListener('visibilitychange', function() {
        if (document.visibilityState === 'visible' && window.Shiny && Shiny.shinyapp && !up()) heal(300);
      });
      ['mousemove', 'mousedown', 'keydown', 'touchstart'].forEach(function(ev) {
        document.addEventListener(ev, function() { if (pending && !up()) { pending = false; heal(300); } }, { passive: true });
      });
    })();
  ")),
  div(id = "splash",
      div(class = "t", "Projections"),
      div(class = "track", tags$i()),
      div(class = "s", "Loading league data, rating teams and fitting the models. ",
                       "The first launch downloads several seasons.")),
  div(class = "app-header",
      div(class = "logo-badge", "\U0001F4C8"),
      div(div(class = "header-title", "Projections"),
          div(class = "header-sub", "NFL \u00b7 NCAAF \u00b7 MLB \u00b7 NHL \u00b7 NBA"))),
  div(class = "shell",
    div(class = "side",
      div(class = "grp", "League"),
      navlistPanel(
        id = "lg", widths = c(12, 12), well = FALSE, selected = "today",
        tabPanel(nav_item("\U0001F4CB", "Today"), value = "today"),
        tabPanel(nav_item("\U0001F3C8", "NFL"),   value = "nfl"),
        tabPanel(nav_item("\U0001F3C8", "NCAAF"), value = "cfb"),
        tabPanel(nav_item("\u26be", "MLB"),       value = "mlb"),
        tabPanel(nav_item("\U0001F3D2", "NHL"), value = "nhl"),
        tabPanel(nav_item("\U0001F3C0", "NBA"), value = "nba")
      )
    ),
    div(class = "main",
      conditionalPanel(
        "input.lg == 'today'",
        div(class = "content dash",
          div(class = "dash-top",
              div(div(class = "hdr", "Today"), uiOutput("dash_date")),
              actionButton("dash_refresh", "\u27f3  Refresh", class = "btn-run")),
          uiOutput("dash_value"),
          uiOutput("dash_sports")
        )),
      conditionalPanel(
        "input.lg == 'nfl'",
        div(class = "content",
          div(class = "hdr", "NFL matchup confidence"),
          div(class = "sub", "Every game ranked from most predictable to coin toss."),
          fluidRow(
            column(3, selectInput("season", "Season", choices = rev(PICK_SEASONS),
                                  selected = max(PICK_SEASONS))),
            column(3, selectInput("week", "Week", choices = 1:18, selected = 1)),
            column(6, br(), actionButton("refresh", "Refresh data", class = "btn-run"))
          ),
          uiOutput("record"),
          DTOutput("board"),
          div(class = "hint", "Click a game for its likely touchdown scorers and the full matchup breakdown."),
          uiOutput("detail"),
          uiOutput("td_section"),
          uiOutput("ry_section"),
          uiOutput("leak_note")
        )),
      conditionalPanel(
        "input.lg == 'cfb'",
        div(class = "content",
          div(class = "hdr", "College football matchup confidence"),
          div(class = "sub", "Every FBS matchup ranked from most predictable to coin toss."),
          fluidRow(
            column(3, selectInput("cseason", "Season", choices = rev(CFB_PICK),
                                  selected = max(CFB_PICK))),
            column(3, selectInput("cweek", "Week", choices = 1:CFB_MAX_WEEK, selected = 1)),
            column(6, br(), actionButton("crefresh", "Refresh data", class = "btn-run"))
          ),
          uiOutput("crecord"),
          DTOutput("cboard"),
          div(class = "hint", "Click a game for its likely touchdown scorers."),
          uiOutput("cdetail"),
          uiOutput("ctd_section"),
          uiOutput("cleak")
        )),
      conditionalPanel(
        "input.lg == 'mlb'",
        div(class = "controls-bar",
            div(tags$label(class = "ctrl-lbl", "Date"),
                dateInput("date_picker", NULL, value = Sys.Date(),
                          min = "2022-01-01", max = "2027-12-31")),
            actionButton("refresh_btn", "\u27f3  Run forecast", class = "btn-run"),
            div(class = "header-pills", uiOutput("header_badges", inline = TRUE))),
        div(class = "content",
          uiOutput("accuracy_ui"),
          uiOutput("games_section"),
          uiOutput("nrfi_section"),
          uiOutput("hr_section"),
          uiOutput("k_section"),
          uiOutput("diag_section")
        )),
      conditionalPanel(
        "input.lg == 'nhl'",
        div(class = "controls-bar",
            div(tags$label(class = "ctrl-lbl", "Date"),
                dateInput("ndate", NULL, value = Sys.Date(), min = "2015-10-01", max = "2027-07-01")),
            actionButton("nrefresh", "\u27F3  Run forecast", class = "btn-run")),
        div(class = "content",
          uiOutput("nrecord"),
          uiOutput("nboard_sec"),
          uiOutput("ngoal_sec"),
          uiOutput("nleak")
        )),
      conditionalPanel(
        "input.lg == 'nba'",
        div(class = "controls-bar",
            div(tags$label(class = "ctrl-lbl", "Date"),
                dateInput("bdate", NULL, value = Sys.Date(), min = "2016-10-01", max = "2027-07-01")),
            actionButton("brefresh", "\u27F3  Run forecast", class = "btn-run")),
        div(class = "content",
          uiOutput("brecord"),
          uiOutput("bboard_sec"),
          uiOutput("bfb_sec"),
          uiOutput("bleak")
        ))
    )
  )
)

# ==================== SERVER ====================
server <- function(input, output, session) {

  cleanup_old_caches()

  # ---- connection: survive drops instead of greying out ---------------------------
  # On a host the browser reconnects to a fresh session and replays its inputs; a
  # keep-alive from the page (see the UI script) stops the host's idle timer from
  # closing an open tab, and the page reloads itself in place if a reconnect fails.
  if (dash_hosted()) session$allowReconnect(TRUE)

  # Where the viewer was (tab, dates, weeks) lives in the URL, so a reload -- or a
  # bookmarked link -- comes back to the same place.
  url_state <- local({
    q <- tryCatch(parseQueryString(isolate(session$clientData$url_search) %||% ""), error = function(e) list())
    dt <- function(x) { d <- suppressWarnings(as.Date(x %||% NA_character_)); if (length(d) == 1L && !is.na(d)) d else NULL }
    iv <- function(x) { v <- suppressWarnings(as.integer(x %||% NA_character_)); if (length(v) == 1L && !is.na(v)) v else NULL }
    out <- list()
    if (!is.null(q$lg) && q$lg %in% c("today", "nfl", "cfb", "mlb", "nhl", "nba")) out$lg <- q$lg
    out$date_picker <- dt(q$d); out$ndate <- dt(q$nd); out$bdate <- dt(q$bd)
    out$week <- iv(q$wk); out$cweek <- iv(q$cw)
    out
  })
  if (!is.null(url_state$lg)) updateNavlistPanel(session, "lg", selected = url_state$lg)
  if (!is.null(url_state$date_picker)) updateDateInput(session, "date_picker", value = url_state$date_picker)
  url_ok <- reactiveVal(is.null(url_state$lg))
  observe({ if (!isTRUE(url_ok()) && identical(input$lg, url_state$lg)) url_ok(TRUE) })
  observe(dash_guard("Address bar", {
    req(isTRUE(url_ok()), input$lg)
    lg <- input$lg; q <- list(lg = lg)
    if (lg == "mlb" && !is.null(input$date_picker)) q$d  <- format(as.Date(input$date_picker))
    if (lg == "nfl" && !is.null(input$week))        q$wk <- input$week
    if (lg == "cfb" && !is.null(input$cweek))       q$cw <- input$cweek
    if (lg == "nhl" && !is.null(input$ndate))       q$nd <- format(as.Date(input$ndate))
    if (lg == "nba" && !is.null(input$bdate))       q$bd <- format(as.Date(input$bdate))
    updateQueryString(paste0("?", paste(names(q), vapply(q, function(v)
      utils::URLencode(as.character(v), reserved = TRUE), ""), sep = "=", collapse = "&")), mode = "replace")
  }))

  # The viewer's own date and time zone. A hosted server runs on UTC, so its clock
  # rolls to tomorrow in the North American evening; "today" is the viewer's today.
  today_local <- reactive({
    d <- suppressWarnings(as.Date(input$client_today %||% NA_character_))
    if (length(d) == 1L && !is.na(d)) d else Sys.Date()
  })
  view_tz <- reactive({ z <- input$client_tz %||% ""; if (z %in% OlsonNames()) z else "" })
  observeEvent(input$client_today, {
    if (is.null(url_state$date_picker)) updateDateInput(session, "date_picker", value = today_local())
  }, once = TRUE, ignoreInit = FALSE)

  mig_done <- reactiveVal(FALSE)
  observe(dash_guard("NFL data", {
    if (isTRUE(mig_done())) return()
    d <- dat(); req(d)
    migrate_plr_ledger(d)
    mig_done(TRUE)
  }), priority = 10)

  wk_init <- reactiveVal(FALSE)
  wk_gate <- new.env(); wk_gate$target <- NULL     # week the selector is being moved to
  observe(dash_guard("NFL data", {
    if (isTRUE(wk_init())) return()
    d <- dat(); req(d)
    now <- now_et()
    cs <- current_season(d$sch, now)
    if (is.na(cs) || !cs %in% PICK_SEASONS) { wk_init(TRUE); return() }
    if (as.integer(isolate(input$season)) != cs)
      updateSelectInput(session, "season", selected = as.character(cs))
    wk <- url_state$week %||% current_week(d$sch, cs, now)     # a reload keeps the week you were on
    wk_gate$target <- wk
    updateSelectInput(session, "week", selected = as.character(wk))
    wk_init(TRUE)
  }))

  force_next <- reactiveVal(FALSE)
  stamp <- reactiveVal(NULL)
  observeEvent(input$refresh, force_next(TRUE), ignoreInit = TRUE)
  observe(dash_guard("NFL data could not be refreshed", {
    invalidateLater(POLL_MIN * 60 * 1000)
    f <- isTRUE(force_next())
    if (f) force_next(FALSE)
    st <- withProgress(message = "Checking for new NFL data", value = 0.5,
                       detail = "First launch downloads several seasons",
                       sync_data(force = f))
    stamp(st)
  }))

  dat <- reactive({
    req(stamp())
    warm_own("nfl")
    withProgress(message = "Loading NFL data", value = 0.5, load_all())
  })

  model <- reactive({
    d <- dat()
    withProgress(message = "Rating teams", value = 0.5,
                 detail = "Opponent-adjusted efficiency",
                 fit_history(d$tw, d$sch, d$pdl, d$teams, as.integer(input$season)))
  })

  observe(dash_guard("NFL picks", {
    invalidateLater(POLL_MIN * 60 * 1000)
    d <- dat()
    now <- now_et(); cs <- current_season(d$sch, now)
    if (is.na(cs) || !cs %in% PICK_SEASONS) return()
    m <- fit_history(d$tw, d$sch, d$pdl, d$teams, cs)
    if (is.null(m)) return()
    g <- d$sch[which(d$sch$season == cs & d$sch$ko <= now), ]
    if (nrow(g)) settle(d, m, cs, g, now)
  }))

  board <- reactive({
    # Nothing until the selector has reached the current week: it starts on week 1, and
    # drawing that first showed last month's record for a moment (and cost a full pass).
    req(isTRUE(wk_init()))
    if (!is.null(wk_gate$target)) {
      req(identical(as.integer(input$week), as.integer(wk_gate$target))); wk_gate$target <- NULL
    }
    d <- dat(); m <- model(); req(m)
    s <- as.integer(input$season); w <- as.integer(input$week)
    g <- d$sch[d$sch$season == s & d$sch$week == w, ]
    if (nrow(g) == 0) return(NULL)
    now <- now_et()
    st <- settle(d, m, s, g, now)
    pred <- st$pred; conf <- st$conf
    nxt <- g$ko[!st$locked & !is.na(g$ko) & g$ko > now]
    if (length(nxt))
      invalidateLater(min(POLL_MIN * 60 * 1000,
        max(1000, as.numeric(difftime(min(nxt), now, units = "secs")) * 1000 + 5000)))

    pick <- ifelse(pred > 0, g$home_team, g$away_team)
    done   <- g$has_score & !is.na(g$final_at) & g$final_at <= now
    game_grade_slate(LEDGER_FILE, g, done)
    tie    <- done & g$home_score == g$away_score
    picked <- done & !tie & ((pred > 0) == (g$home_score > g$away_score))

    matchup <- vapply(seq_len(nrow(g)), function(i) sprintf(
      '%s<span class="tm">%s</span><span class="at">@</span>%s<span class="tm">%s</span>',
      badge(d, g$away_team[i]), nick(g$away_team[i]),
      badge(d, g$home_team[i]), nick(g$home_team[i])), "")
    chip <- vapply(seq_len(nrow(g)), function(i) sprintf(
      '<span class="chip" style="background:%s;border-color:%s">%s%s</span>',
      mix_white(d$col[[pick[i]]], 0.90), mix_white(d$col[[pick[i]]], 0.55),
      badge(d, pick[i]), nick(pick[i])), "")
    cf <- vapply(seq_len(nrow(g)), function(i) if (is.na(conf[i])) "\u2014" else sprintf(
      '<div class="cf"><span class="cfn">%d%%</span><span class="cft"><span class="cfb" style="width:%.0f%%;background:%s"></span></span></div>',
      round(conf[i] * 100), 100 * pmin(pmax((conf[i] - 0.5) / 0.30, 0.04), 1),
      conf_col(conf[i])), "")
    res <- ifelse(!done, '<span class="nt">\u2014</span>',
            ifelse(tie, '<span class="rs">Tie</span>',
             ifelse(picked, '<span class="rs ok">Correct</span>',
                            '<span class="rs no">Wrong</span>')))

    o <- order(-conf)
    tbl <- data.frame(
      Matchup       = matchup,
      Pick          = chip,
      `Proj margin` = sprintf('<span class="mg">%.1f</span>', abs(pred)),
      Confidence    = cf,
      Vegas         = ifelse(is.na(g$spread_line), "",
                        paste0(nick(ifelse(g$spread_line > 0, g$home_team, g$away_team)),
                               " -", sprintf("%.1f", abs(g$spread_line)))),
      Final         = ifelse(done, paste0(g$away_score, "-", g$home_score), ""),
      Result        = res,
      check.names = FALSE, stringsAsFactors = FALSE)

    list(tbl = tbl[o, ], g = g[o, ], pred = pred[o], conf = conf[o],
         pick = pick[o], done = done[o], tie = tie[o], picked = picked[o],
         locked = st$locked[o])
  })

  output$record <- renderUI({
    b <- board()
    if (is.null(b)) return(div(class = "rec", "No games scheduled for that week."))
    if (!any(b$done)) return(div(class = "rec",
      sprintf("%d games. None played yet \u2014 these are forward-looking picks.",
              nrow(b$tbl))))
    n <- sum(b$done & !b$tie); ok <- sum(b$picked)
    vg <- b$g$spread_line
    vn  <- sum(b$done & !b$tie & !is.na(vg))
    vok <- sum(b$done & !b$tie & !is.na(vg) &
                 ((vg > 0) == (b$g$home_score > b$g$away_score)))
    div(class = "rec",
      sprintf("Model went %d-%d (%.0f%%) on %d decided games.",
              ok, n - ok, 100 * ok / max(n, 1), n),
      if (vn > 0) sprintf("  Vegas favourites went %d-%d (%.0f%%).",
                          vok, vn - vok, 100 * vok / vn) else "")
  })

  output$board <- renderDT({
    b <- board(); req(b)
    tbl <- b$tbl; tbl$gid <- b$g$game_id
    datatable(tbl, rownames = FALSE, selection = "none", escape = FALSE,
              callback = JS("tdxBind(table, 'board', 'nfl_tdx', 7, 'board_pick');"),
              options = list(pageLength = 20, dom = "t", ordering = FALSE,
                columnDefs = list(
                  list(targets = c(2, 4, 5), className = "dt-right"),
                  list(targets = 3, width = "150px"),
                  list(targets = 7, visible = FALSE))))
  }, server = FALSE)

  # a game's likely touchdown scorers: this week's player projections for that game
  nfl_tdx_html <- function(gid) tryCatch({
    x <- props(); d <- dat()
    if (is.null(x)) tdx_none("No player projections for this week yet.") else {
      x <- x[x$game_id == gid & is.finite(x$p_td), , drop = FALSE]
      x <- head(x[order(-x$p_td), , drop = FALSE], 8)
      tdx_html(plr_name(d, x$team, x$pname, x$inj_tag), x$pos, x$p_td, x$act_td, TDX_NOTE)
    }
  }, error = function(e) tdx_none(if (inherits(e, "shiny.silent.error"))
    "Player projections are still loading \u2014 click the game again in a moment." else conditionMessage(e)))
  observeEvent(input$nfl_tdx, {
    gid <- as.character(input$nfl_tdx$gid %||% "")
    session$sendCustomMessage("tdx", list(tbl = "board", gid = gid, html = nfl_tdx_html(gid)))
  }, ignoreInit = TRUE)

  output$detail <- renderUI({
    b <- board(); req(b)
    i <- input$board_pick
    if (is.null(i) || length(i) == 0) return(NULL)
    d <- dat(); se <- as.integer(input$season); wk <- as.integer(input$week)
    cut <- as.POSIXct(min(as.numeric(b$g$ko[i]), as.numeric(now_et())),
                      origin = "1970-01-01", tz = TZ_ET)
    f <- team_form(d$tw, se, cut, d$teams)
    ht <- b$g$home_team[i]; at <- b$g$away_team[i]
    ih <- match(ht, f$team); ia <- match(at, f$team)
    if (is.na(ih) || is.na(ia)) return(NULL)
    H <- f[ih, ]; A <- f[ia, ]
    hn <- nick(ht); an <- nick(at)
    hc <- d$col[[ht]]; ac <- d$col[[at]]
    hp <- pd_to_date(d$pdl, se, cut, ht); ap <- pd_to_date(d$pdl, se, cut, at)
    pdtxt <- function(v) if (is.na(v[1])) "\u2014" else
      sprintf("%+.1f  (%d gp)", v[1], as.integer(v[2]))

    r_oepa <- rank_desc(f$o_epa);  r_depa <- rank_asc(f$d_epa)
    r_opep <- rank_desc(f$o_pepa); r_dpep <- rank_asc(f$d_pepa)
    r_orep <- rank_desc(f$o_repa); r_drep <- rank_asc(f$d_repa)

    row <- function(lbl, hv, av, rh = NA, ra = NA, fn = fmt, sec = FALSE, better = NA) {
      sh <- ""; sa <- ""
      if (!is.na(better) && length(hv) && length(av) && !is.na(hv) && !is.na(av) && hv != av) {
        if (if (better == "hi") hv > av else hv < av)
          sh <- paste0("background:", mix_white(hc, 0.87))
        else sa <- paste0("background:", mix_white(ac, 0.87))
      }
      tags$tr(class = if (sec) "sec" else "",
        tags$td(lbl),
        tags$td(style = sh, fn(hv),
                if (!is.na(rh)) tags$span(class = "rk", paste0(" ", ord(rh)))),
        tags$td(style = sa, fn(av),
                if (!is.na(ra)) tags$span(class = "rk", paste0(" ", ord(ra)))))
    }
    gaps <- c(H$o_pepa - A$d_pepa, H$o_repa - A$d_repa,
              A$o_pepa - H$d_pepa, A$o_repa - H$d_repa)
    names(gaps) <- c(
      sprintf("%s passing offence vs %s pass defence", hn, an),
      sprintf("%s rushing offence vs %s run defence",  hn, an),
      sprintf("%s passing offence vs %s pass defence", an, hn),
      sprintf("%s rushing offence vs %s run defence",  an, hn))
    gaps <- gaps[!is.na(gaps)]
    biggest <- if (length(gaps)) names(gaps)[which.max(abs(gaps))] else NULL

    div(class = "det",
      div(class = "band", style = sprintf("background:linear-gradient(90deg,%s 0%%,%s 100%%)", ac, hc)),
      tags$h4(HTML(sprintf("%s%s<span class=\"at\">at</span>%s%s",
                           badge(d, at), full(at), badge(d, ht), full(ht)))),
      div(class = "pk", sprintf(
        "%s by %.1f  \u00b7  %s confidence  \u00b7  form from %d and %d games played",
        nick(b$pick[i]), abs(b$pred[i]),
        if (is.na(b$conf[i])) "\u2014" else paste0(round(b$conf[i] * 100), "%"),
        num0(H$games), num0(A$games))),
      tags$table(
        tags$thead(tags$tr(tags$th("Metric"),
          tags$th(style = paste0("color:", hc), HTML(paste0(badge(d, ht), hn))),
          tags$th(style = paste0("color:", ac), HTML(paste0(badge(d, at), an))))),
        tags$tbody(
          row("OFFENCE  EPA/play", H$o_epa, A$o_epa, r_oepa[ih], r_oepa[ia], sec = TRUE, better = "hi"),
          row("\u2003passing",           H$o_pepa,  A$o_pepa, r_opep[ih], r_opep[ia], better = "hi"),
          row("\u2003rushing",           H$o_repa,  A$o_repa, r_orep[ih], r_orep[ia], better = "hi"),
          row("\u2003early down",        H$o_eepa,  A$o_eepa, better = "hi"),
          row("\u2003red zone",          H$o_rzepa, A$o_rzepa, better = "hi"),
          row("\u2003success rate",      H$o_sr,    A$o_sr,   fn = pct, better = "hi"),
          row("\u2003explosive rate",    H$o_expl,  A$o_expl, fn = pct, better = "hi"),
          row("\u2003sack rate allowed", H$o_sack,  A$o_sack, fn = pct, better = "lo"),
          row("\u2003turnover rate",     H$o_to,    A$o_to,   fn = pct, better = "lo"),
          row("DEFENCE  EPA allowed", H$d_epa, A$d_epa, r_depa[ih], r_depa[ia], sec = TRUE, better = "lo"),
          row("\u2003vs pass",           H$d_pepa,  A$d_pepa, r_dpep[ih], r_dpep[ia], better = "lo"),
          row("\u2003vs rush",           H$d_repa,  A$d_repa, r_drep[ih], r_drep[ia], better = "lo"),
          row("\u2003early down",        H$d_eepa,  A$d_eepa, better = "lo"),
          row("\u2003red zone",          H$d_rzepa, A$d_rzepa, better = "lo"),
          row("\u2003success allowed",   H$d_sr,    A$d_sr,   fn = pct, better = "lo"),
          row("\u2003explosive allowed", H$d_expl,  A$d_expl, fn = pct, better = "lo"),
          row("\u2003sack rate",         H$d_sack,  A$d_sack, fn = pct, better = "hi"),
          row("\u2003takeaway rate",     H$d_to,    A$d_to,   fn = pct, better = "hi"),
          tags$tr(class = "sec", tags$td("QUARTERBACK"),
                  tags$td(chr(H$qb)), tags$td(chr(A$qb))),
          row("\u2003EPA/dropback", H$qepa, A$qepa, better = "hi"),
          tags$tr(class = "sec",
                  tags$td(if (wk >= PD_FROM_WEEK) "POINT DIFF / GAME  (in model)"
                          else "POINT DIFF / GAME  (enters model from Week 5)"),
                  tags$td(style = if (!is.na(hp[1]) && !is.na(ap[1]) && hp[1] > ap[1])
                            paste0("background:", mix_white(hc, 0.87)) else "", pdtxt(hp)),
                  tags$td(style = if (!is.na(hp[1]) && !is.na(ap[1]) && ap[1] > hp[1])
                            paste0("background:", mix_white(ac, 0.87)) else "", pdtxt(ap))),
          tags$tr(class = "sec", tags$td("Rest days"),
                  tags$td(chr(b$g$home_rest[i])), tags$td(chr(b$g$away_rest[i])))
        )
      ),
      if (!is.null(biggest))
        div(class = "edge", tags$b("Largest mismatch: "), biggest,
            sprintf(" (%+.3f EPA/play).", gaps[[biggest]])),
      div(class = "hint",
          "The pick uses the net EPA rating, this season's point differential from ",
          "Week 5 onward, and whether either team is starting a different quarterback ",
          "than in its previous game. Everything else here is context \u2014 adding it as ",
          "model input was tested and did not improve accuracy.")
    )
  })

  pmodel <- reactive({
    d <- dat(); req(d)
    s <- as.integer(input$season); w <- as.integer(input$week)
    g <- d$sch[d$sch$season == s & d$sch$week == w, ]
    if (nrow(g) == 0) return(NULL)
    cut <- min(g$ko, na.rm = TRUE)
    f <- file.path(CACHE_DIR, sprintf("pfit_v%d_%s_%s_%d_%d.rds", CACHE_VER, MODEL_VER, PLR_VER, s, w))
    if (file.exists(f)) {
      m <- try(readRDS(f), silent = TRUE)
      if (!inherits(m, "try-error") && is.list(m) && !is.null(m$td)) {
        if (!isTRUE(m$slim)) { m <- slim_fits(m, c("td", "over")); try(saveRDS(m, f), silent = TRUE) }
        return(m)
      }
    }
    withProgress(message = "Fitting player models", value = 0.35,
                 detail = "Reading game history", {
      h <- memo_history(d$plr, d$pos, cut)
      m <- NULL
      if (!is.null(h) && nrow(h) >= 2000) {
        setProgress(0.6, detail = "Building training set")
        tr <- plr_training(h, d$ros, d$sch, cutoff = cut)
        if (!is.null(tr)) {
          setProgress(0.85, detail = "Estimating coefficients")
          m <- fit_player_models(tr, s)
          if (!is.null(m)) try(saveRDS(m, f), silent = TRUE)
        }
      }
      m
    })
  })

  props <- reactive({
    req(mig_done())
    d <- dat(); m <- pmodel(); req(d)
    if (is.null(m)) return(NULL)
    s <- as.integer(input$season); w <- as.integer(input$week)
    g <- d$sch[d$sch$season == s & d$sch$week == w, ]
    if (nrow(g) == 0) return(NULL)
    x <- withProgress(message = "Projecting players", value = 0.6,
                      detail = "Applying availability and matchups",
                      settle_players(d, m, s, g, now_et()))
    if (is.null(x) || nrow(x) == 0) return(NULL)
    a <- player_actuals(d, g)
    x$key <- paste(x$game_id, x$pid)
    x$act_td <- if (is.null(a)) NA_integer_ else a$td[match(x$key, a$key)]
    x$act_ry <- if (is.null(a)) NA_real_ else a$recyds[match(x$key, a$key)]
    fin <- g$has_score & !is.na(g$final_at) & g$final_at <= now_et()
    x$done <- fin[match(x$game_id, g$game_id)]
    x$act_td[!x$done %in% TRUE] <- NA
    x$act_ry[!x$done %in% TRUE] <- NA
    x$act_td[x$done %in% TRUE & is.na(x$act_td)] <- 0L
    local({
      pl <- x$done %in% TRUE & !is.na(x$act_td)
      if (any(pl))
        tryCatch(prop_record("nfl", "anytime_td", x$game_id[pl], x$pid[pl], x$pname[pl],
                             x$kickoff[pl], x$p_td[pl], as.integer(x$act_td[pl] > 0),
                             sprintf("nfl-td-v%s", PLR_VER)),
                 error = function(e) NULL)
    })
    x$act_ry[x$done %in% TRUE & is.na(x$act_ry)] <- 0
    x
  })

  output$td_section <- renderUI({
    x <- props()
    if (is.null(x)) return(NULL)
    tagList(div(class = "sec-hdr", sprintf("Anytime Touchdown \u2014 %d players", nrow(x))),
            DTOutput("td_tbl"),
            div(class = "hint",
                "Probability that the player scores a rushing or receiving touchdown, ",
                "assuming he plays \u2014 the same basis on which these markets settle, so a ",
                "quarterback counts for his rushing touchdowns (each team's expected starter is ",
                "listed; for him Opp/gm is carries). Driven by projected volume and the market's ",
                "implied team total, and for quarterbacks also goal-line carries and how often ",
                "they have scored; otherwise the red zone and goal-line columns are context, not ",
                "model inputs, because adding them was tested and gained nothing. Gm is games ",
                "played this season. ",
                "Probabilities above about 45% have run a few points high in backtesting. ",
                "Players ruled out or doubtful, on injured reserve, waived or left off the ",
                "game-day active list are dropped as soon as that becomes public, which ",
                "lifts the share of listed players who actually take a snap from 83% to 97%. ",
                "Q marks a questionable player and Q\u00b7DNP one who also missed practice ",
                "all week \u2014 those have played only about half the time."))
  })

  output$td_tbl <- renderDT({
    x <- props(); req(x)
    d <- dat()
    x <- x[order(-x$p_td), ]
    res <- ifelse(is.na(x$act_td), '<span class="nt">\u2014</span>',
            ifelse(x$act_td > 0, '<span class="rs ok">Scored</span>',
                                 '<span class="rs no">No TD</span>'))
    tbl <- data.frame(
      Player = plr_name(d, x$team, x$pname, x$inj_tag),
      Pos = x$pos,
      Opp = sprintf('%s<span class="tm">%s</span>', vapply(x$oppt, function(t) badge(d, t), ""), nick(x$oppt)),
      `TD prob` = prob_bar(x$p_td),
      `Opp/gm` = sprintf("%.1f", x$f_opp_n),
      `RZ/gm` = sprintf("%.1f", x$f_rz_opp),
      `Goal line/gm` = sprintf("%.1f", x$f_i5_opp),
      `Team pts` = sprintf("%.1f", x$implied),
      Gm = ifelse(is.na(x$gp_season), "", sprintf("%d", as.integer(x$gp_season))),
      Result = res,
      check.names = FALSE, stringsAsFactors = FALSE)
    datatable(tbl, rownames = FALSE, escape = FALSE,
              options = list(pageLength = 25, dom = "ftp", ordering = FALSE,
                columnDefs = list(list(targets = 4:8, className = "dt-right"),
                                  list(targets = 3, width = "130px"))))
  }, server = FALSE)

  output$ry_section <- renderUI({
    x <- props()
    if (is.null(x)) return(NULL)
    r <- x[x$pos %in% c("WR", "TE", "RB") & x$f_tgt >= PLR_MIN_OPP, ]
    if (nrow(r) == 0) return(NULL)
    tagList(div(class = "sec-hdr", sprintf("Receiving Yards \u2014 %d players", nrow(r))),
            DTOutput("ry_tbl"),
            div(class = "hint",
                "Projected yards assuming the player plays, with the historically observed ",
                "rate of clearing each line for a projection of this size. Over probabilities ",
                "are fit on prior seasons only and run about 1-2 points high."))
  })

  output$ry_tbl <- renderDT({
    x <- props(); req(x)
    d <- dat()
    x <- x[x$pos %in% c("WR", "TE", "RB") & x$f_tgt >= PLR_MIN_OPP, ]
    x <- x[order(-x$p_ry), ]
    act <- ifelse(is.na(x$act_ry), '<span class="nt">\u2014</span>',
                  sprintf('<span class="mg">%d</span>', round(x$act_ry)))
    tbl <- data.frame(
      Player = plr_name(d, x$team, x$pname, x$inj_tag),
      Pos = x$pos,
      Opp = sprintf('%s<span class="tm">%s</span>', vapply(x$oppt, function(t) badge(d, t), ""), nick(x$oppt)),
      `Proj yds` = sprintf('<span class="mg">%.0f</span>', x$p_ry),
      `Tgt/gm` = sprintf("%.1f", x$f_tgt),
      `Yds/tgt` = sprintf("%.1f", x$f_ypt),
      Gm = ifelse(is.na(x$gp_season), "", sprintf("%d", as.integer(x$gp_season))),
      `O 40` = prob_bar(x$o40, 0.9),
      `O 60` = prob_bar(x$o60, 0.9),
      `O 80` = prob_bar(x$o80, 0.9),
      Actual = act,
      check.names = FALSE, stringsAsFactors = FALSE)
    datatable(tbl, rownames = FALSE, escape = FALSE,
              options = list(pageLength = 25, dom = "ftp", ordering = FALSE,
                columnDefs = list(list(targets = 3:6, className = "dt-right"),
                                  list(targets = 7:9, width = "95px"))))
  }, server = FALSE)

  output$leak_note <- renderUI({
    m <- model()
    if (is.null(m)) return(div(class = "err",
      "Not enough completed prior seasons to calibrate this year. ",
      "Pick a later season, or widen LOAD_SEASONS at the top of the file."))
    s <- as.integer(input$season); w <- as.integer(input$week)
    div(class = "leak",
      tags$b("No leakage. "),
      sprintf(paste0("Each prediction uses only games that had finished before that ",
                     "game's kickoff, plus completed prior seasons. Until kickoff it ",
                     "updates automatically as new results arrive; at kickoff it is ",
                     "locked permanently and never recomputed. Both model regimes and ",
                     "the confidence curve are fit only on %s."),
              paste(m$seasons, collapse = ", ")),
      tags$br(),
      tags$b("Model. "),
      if (w >= PD_FROM_WEEK)
        "This week uses EPA plus this season's point differential."
      else
        sprintf("Through Week %d the pick uses EPA only; this season's point differential joins from Week %d.",
                PD_FROM_WEEK - 1, PD_FROM_WEEK),
      tags$br(),
      tags$b("Confidence "),
      "is the historically observed hit rate for predictions of this size, fit as ",
      "a smooth curve. Games near the bottom really are coin tosses.",
      tags$br(),
      tags$b("Caveat. "),
      "This model does not beat the betting market: walk-forward over 2017-2025 it called ",
      "64.6% of games straight up (Brier 0.221) against 67.1% (Brier 0.210) for the closing ",
      "moneyline favourite, and it has no edge against the spread."
    )
  })

  cforce <- reactiveVal(FALSE)
  cstamp <- reactiveVal(NULL)
  observeEvent(input$crefresh, cforce(TRUE), ignoreInit = TRUE)
  observe(dash_guard("College football data could not be refreshed", {
    req(identical(input$lg, "cfb") || (identical(input$lg, "today") && isTRUE(dash$cfb) && dash_in_season("cfb", today_local())))
    invalidateLater(POLL_MIN * 60 * 1000)
    f <- isTRUE(cforce())
    if (f) cforce(FALSE)
    st <- withProgress(message = "Checking for new college football data", value = 0.5,
                       detail = "First launch downloads several seasons",
                       cfb_sync(force = f))
    cstamp(st)
  }))

  cdat <- reactive({
    req(cstamp())
    warm_own("cfb")
    withProgress(message = "Loading college football data", value = 0.4,
                 detail = "Ratings, rosters and recruiting", cfb_load())
  })

  cwk_init <- reactiveVal(FALSE)
  cwk_gate <- new.env(); cwk_gate$target <- NULL
  observe(dash_guard("College football data", {
    if (isTRUE(cwk_init())) return()
    d <- cdat(); req(d)
    now <- now_et()
    cs <- cfb_current_season(d$sch, now)
    if (is.na(cs) || !cs %in% CFB_PICK) { cwk_init(TRUE); return() }
    if (as.integer(isolate(input$cseason)) != cs)
      updateSelectInput(session, "cseason", selected = as.character(cs))
    wk <- url_state$cweek %||% cfb_current_week(d$sch, cs, now)
    cwk_gate$target <- wk
    updateSelectInput(session, "cweek", selected = as.character(wk))
    cwk_init(TRUE)
  }))

  cmodel <- reactive({
    d <- cdat(); req(d)
    s <- as.integer(input$cseason)
    withProgress(message = "Rating college teams", value = 0.5,
                 detail = "Opponent-adjusted EPA and preseason priors", {
      R <- cfb_rows(d$pan, d$F, d$endr, d$ents, s)
      if (is.null(R)) NULL else cfb_fit(R, s)
    })
  })

  cgames <- reactive({
    d <- cdat()
    s <- as.integer(input$cseason); w <- as.integer(input$cweek)
    g <- d$sch[d$sch$season == s & d$sch$week == w & d$sch$both_fbs, ]
    g[order(g$ko), ]
  })

  cboard <- reactive({
    req(isTRUE(cwk_init()))
    if (!is.null(cwk_gate$target)) {
      req(identical(as.integer(input$cweek), as.integer(cwk_gate$target))); cwk_gate$target <- NULL
    }
    d <- cdat(); m <- cmodel(); req(m)
    g <- cgames()
    if (!nrow(g)) return(NULL)
    now <- now_et()
    st <- withProgress(message = "Projecting matchups", value = 0.7,
                       cfb_settle(d$pan, d$F, d$endr, d$ents, m, g, now))
    req(st)
    nxt <- g$ko[!st$locked %in% TRUE & !is.na(g$ko) & g$ko > now]
    if (length(nxt))
      invalidateLater(min(POLL_MIN * 60 * 1000,
        max(1000, as.numeric(difftime(min(nxt), now, units = "secs")) * 1000 + 5000)))
    pred <- st$pred; conf <- st$conf
    pick <- ifelse(pred > 0, g$home_id, g$away_id)
    done <- g$has_score & !is.na(g$final_at) & g$final_at <= now
    game_grade_slate(CFB_LEDGER, g, done)
    tie  <- done & g$home_score == g$away_score
    ok   <- done & !tie & ((pred > 0) == (g$home_score > g$away_score))
    list(g = g, st = st, pred = pred, conf = conf, pick = pick,
         done = done, tie = tie, ok = ok)
  })

  output$crecord <- renderUI({
    b <- cboard()
    if (is.null(b)) return(div(class = "rec", "No FBS games scheduled for this week."))
    d <- cdat()
    n <- sum(b$done & !b$tie); h <- sum(b$ok, na.rm = TRUE)
    lock <- sum(b$st$locked %in% TRUE); tot <- nrow(b$g)
    txt <- if (n == tot)
      sprintf("Model went %d-%d (%.0f%%) on %d decided games.", h, n - h, 100 * h / n, n)
    else if (n > 0)
      sprintf("%d FBS matchups, %d still to play. %d-%d so far.", tot, tot - n, h, n - h)
    else
      sprintf("%d FBS matchups. %d locked at kickoff, the rest update until theirs.",
              tot, lock)
    div(class = "rec", txt,
        if (!isTRUE(d$talent))
          span(style = "color:#a8620a",
               "  Recruiting is off: install.packages(\"nanoparquet\") to switch it on."))
  })

  output$cboard <- renderDT({
    b <- cboard(); req(b)
    d <- cdat(); g <- b$g
    cn <- function(i) cfb_name(d, i)
    matchup <- vapply(seq_len(nrow(g)), function(i) sprintf(
      '%s<span class="tm">%s</span><span class="at">@</span>%s<span class="tm">%s</span>',
      cfb_badge(d, g$away_id[i]), cn(g$away_id[i]),
      cfb_badge(d, g$home_id[i]), cn(g$home_id[i])), "")
    chip <- vapply(seq_len(nrow(g)), function(i) {
      c0 <- unname(d$col[b$pick[i]]); if (is.na(c0)) c0 <- "#444444"
      sprintf('<span class="chip" style="background:%s;border-color:%s">%s%s</span>',
              mix_white(c0, 0.90), mix_white(c0, 0.55),
              cfb_badge(d, b$pick[i]), cn(b$pick[i]))}, "")
    cf <- vapply(seq_len(nrow(g)), function(i) if (is.na(b$conf[i])) "&mdash;" else sprintf(
      '<div class="cf"><span class="cfn">%d%%</span><span class="cft"><span class="cfb" style="width:%.0f%%;background:%s"></span></span></div>',
      round(b$conf[i] * 100), 100 * pmin(pmax((b$conf[i] - 0.5) / 0.45, 0.04), 1),
      cfb_conf_col(b$conf[i])), "")
    res <- ifelse(!b$done, '<span class="nt">&mdash;</span>',
            ifelse(b$tie, '<span class="rs">Tie</span>',
             ifelse(b$ok, '<span class="rs ok">Correct</span>',
                          '<span class="rs no">Wrong</span>')))
    o <- order(-b$conf)
    tbl <- data.frame(
      Matchup        = matchup,
      Pick           = chip,
      `Proj margin`  = sprintf('<span class="mg">%.1f</span>', abs(b$pred)),
      Confidence     = cf,
      Edge           = sprintf("%.3f", abs(b$st$rd)),
      Final          = ifelse(b$done, paste0(g$away_score, "-", g$home_score), ""),
      Result         = res,
      check.names = FALSE, stringsAsFactors = FALSE)
    tbl$gid <- g$game_id
    datatable(tbl[o, ], rownames = FALSE, escape = FALSE, selection = "none",
              callback = JS("tdxBind(table, 'cboard', 'cfb_tdx', 7);"),
              options = list(pageLength = 60, dom = "t", ordering = FALSE,
                columnDefs = list(list(targets = 2:5, className = "dt-right"),
                                  list(targets = 3, width = "150px"),
                                  list(targets = 7, visible = FALSE))))
  }, server = FALSE)

  # touchdown scorers for the selected college week
  ctd <- reactive({
    d <- cdat(); g <- cgames()
    if (is.null(g) || !nrow(g)) return(NULL)
    s <- as.integer(input$cseason)
    x <- withProgress(message = "Projecting touchdown scorers", value = 0.5,
                      detail = "Usage, touchdown rate and scoring environment",
                      cfb_td_week(d, s, g, now_et()))
    if (!is.null(x) && nrow(x)) {
      pl <- !is.na(x$scored)
      if (any(pl))
        tryCatch(prop_record("cfb", "anytime_td", x$game_id[pl], x$aid[pl], x$name[pl],
                             x$kickoff[pl], x$p_raw[pl], as.integer(x$scored[pl] > 0),
                             sprintf("cfb-td-v%d", CFB_TD_VER)),
                 error = function(e) NULL)
    }
    x
  })
  cfb_pname <- function(d, team, name) paste0(cfb_badge(d, team), '<span class="tm">', dash_esc(name), '</span>')
  cfb_tdx_html <- function(gid) tryCatch({
    x <- ctd(); d <- cdat()
    x <- if (is.null(x)) NULL else x[x$game_id == gid, , drop = FALSE]
    if (is.null(x) || !nrow(x)) tdx_none("Projections start once each team has played a game this season.") else {
      x <- head(x[order(-x$p), , drop = FALSE], 8)
      use <- ifelse(x$gp > 0, sprintf("%.1f car \u00b7 %.1f rec a game", x$car_pg, x$rec_pg), "last season")
      tdx_html(cfb_pname(d, x$team_id, x$name), use, x$p, x$scored, TDX_NOTE)
    }
  }, error = function(e) tdx_none(if (inherits(e, "shiny.silent.error"))
    "Player projections are still loading \u2014 click the game again in a moment." else conditionMessage(e)))
  observeEvent(input$cfb_tdx, {
    gid <- as.character(input$cfb_tdx$gid %||% "")
    session$sendCustomMessage("tdx", list(tbl = "cboard", gid = gid, html = cfb_tdx_html(gid)))
  }, ignoreInit = TRUE)

  output$ctd_section <- renderUI({
    x <- ctd()
    if (is.null(x) || !nrow(x)) return(NULL)
    tagList(div(class = "sec-hdr", sprintf("Anytime Touchdown \u2014 top %d of %d players",
                                           min(nrow(x), CFB_TD_SHOW), nrow(x))),
            DTOutput("ctd_tbl"),
            div(class = "hint",
                "Chance the player scores a rushing or receiving touchdown, assuming he plays. ",
                "Built from his carries, catches, yards and touchdowns this season (last season counts ",
                "as two games early on), his share of his team's touches and the scoring matchup, all as ",
                "of kickoff; fit on prior seasons only. Out of sample on 2025 it was well calibrated: ",
                "players given 26% scored 27% of the time; chances above 60% ran a few points high. ",
                "Listed players touched the ball in their team's previous game. Fair odds = 1 \u00f7 chance."))
  })
  output$ctd_tbl <- renderDT({
    x <- ctd(); req(x); d <- cdat()
    x <- head(x[order(-x$p), , drop = FALSE], CFB_TD_SHOW)
    res <- ifelse(is.na(x$scored), '<span class="nt">\u2014</span>',
                  ifelse(x$scored > 0, '<span class="rs ok">Scored</span>', '<span class="rs no">No TD</span>'))
    tbl <- data.frame(
      Player = cfb_pname(d, x$team_id, x$name),
      Opp = cfb_pname(d, x$opp_id, cfb_name(d, x$opp_id)),
      `TD prob` = prob_bar(x$p),
      `Fair odds` = fmt_dec(fair_dec(x$p)),
      `Car/gm` = ifelse(x$gp > 0, sprintf("%.1f", x$car_pg), ""),
      `Rec/gm` = ifelse(x$gp > 0, sprintf("%.1f", x$rec_pg), ""),
      TDs = ifelse(x$gp > 0, sprintf("%d", as.integer(x$td_n)), ""),
      Gm = sprintf("%d", as.integer(x$gp)),
      Result = res,
      check.names = FALSE, stringsAsFactors = FALSE)
    datatable(tbl, rownames = FALSE, escape = FALSE,
              options = list(pageLength = 25, dom = "ftp", ordering = FALSE,
                columnDefs = list(list(targets = 3:7, className = "dt-right"),
                                  list(targets = 2, width = "130px"))))
  }, server = FALSE)

  output$cdetail <- renderUI({
    b <- cboard()
    if (is.null(b)) return(NULL)
    d <- cdat()
    div(class = "hint",
        paste("Edge is the picked team's opponent-adjusted net EPA-per-play advantage,",
              "before home field. Projected margin converts it to points."))
  })

  output$cleak <- renderUI({
    m <- cmodel()
    if (is.null(m)) return(div(class = "err",
      "Not enough completed prior seasons to calibrate this year."))
    d <- cdat()
    s <- as.integer(input$cseason)
    div(class = "leak",
      tags$b("No leakage. "),
      sprintf(paste0("Every rating uses only games finished before that game's kickoff, ",
                     "plus completed prior seasons. The rating-to-points mapping and the ",
                     "confidence curve are fit on %s alone (%s games). Until kickoff a ",
                     "prediction updates as results arrive; at kickoff it is locked ",
                     "permanently and never recomputed."),
              paste(min(CFB_PICK), s - 1, sep = "-"), format(m$n, big.mark = ",")),
      tags$br(),
      tags$b("Model. "),
      "A team's rating blends its games so far this season with a preseason prior. The ",
      "prior is fit on prior seasons from last year's rating, the four-year recruiting ",
      "composite, and how much on-field production the roster kept or imported through ",
      "the transfer portal. Early weeks lean on the prior; by November it is almost all ",
      "on-field EPA.",
      tags$br(),
      tags$b("Accuracy. "),
      "Walk-forward over 2018-2025 (5,620 FBS matchups) the model called 71.6% correctly ",
      "with an average margin error of 13.4 points. Recruiting and transfer terms are worth ",
      "about a point of accuracy overall and three in the opening weeks. Since v2 the ",
      "rating-to-points slope is steeper in weeks 1-4, which fixed the early-season ",
      "underconfidence (it said 68% in weeks 1-2 and won 75%).",
      tags$br(),
      tags$b("Scope. "),
      "FBS against FBS only. Games against FCS opponents still inform the ratings but are ",
      "not shown, because a 99% pick tells you nothing."
    )
  })

  mlb_seen <- reactiveVal(FALSE)
  observeEvent(input$lg, {
    if (identical(input$lg, "mlb")) mlb_seen(TRUE)
  }, ignoreNULL = TRUE, ignoreInit = FALSE)

  mlb_memo <- reactiveValues(key = NULL, val = NULL)
  store <- reactive({
    req(isTRUE(mlb_seen()))
    req(input$date_picker)
    ds  <- format(as.Date(input$date_picker), "%Y-%m-%d")
    key <- paste(ds, input$refresh_btn %||% 0L, dash_n(), sep = "|")
    if (identical(key, isolate(mlb_memo$key)) && !is.null(isolate(mlb_memo$val)))
      return(isolate(mlb_memo$val))
    res <- withProgress(message = "Loading MLB data\u2026", value = 0,
                        mlb_build_slate(ds, progress = function(v, dt) setProgress(v, detail = dt)))
    mlb_memo$key <- key; mlb_memo$val <- res
    res
  })
  
  output$legend_panel_ui <- renderUI({
    cats <- unique(sapply(LEGEND_TERMS, `[[`, "cat"))
    cat_sections <- lapply(cats, function(cat) {
      terms_in_cat <- Filter(function(t) t$cat == cat, LEGEND_TERMS)
      rows_html <- paste(sapply(terms_in_cat, function(t)
        sprintf('<div class="legend-row"><span class="legend-abbr">%s</span><span class="legend-full">%s</span></div>',
                t$abbr, t$full)), collapse="")
      HTML(sprintf('<div class="legend-cat">%s</div><div class="legend-grid">%s</div>', cat, rows_html))
    })
    div(class="legend-panel",
        div(class="legend-title", "\u2139  Abbreviations & Integrity Notes"),
        div(class="legend-note",
            "Every input uses only games BEFORE the selected date \u2014 including the home-field edge and the NRFI league base rate, which are re-measured point-in-time rather than from the full ledger. Batter-vs-pitcher is removed (it leaked the graded game). Statcast is off (season aggregates can't be made point-in-time). Once a game is graded its pick is written to the ledger and locked: re-opening a past slate replays the pick that was made, so a historical record never changes. Spring-training and exhibition games are excluded from every ledger, fit and backfill. Vegas lines are not used."),
        tagList(cat_sections))
  })
  
  output$header_badges <- renderUI({
    s <- store(); if (is.null(s)) return(NULL)
    acc <- compute_accuracy_summary(s$proj); if (is.null(acc)) return(NULL)
    span(class=paste("pill", if(acc$pct>=60)"green" else if(acc$pct>=50)"amber" else ""),
         paste0("Accuracy: ", acc$pct, "% (", acc$correct, "/", acc$total, ")"))
  })
  
  output$accuracy_ui <- renderUI({
    s <- store(); if (is.null(s)) return(NULL)
    acc <- compute_accuracy_summary(s$proj); if (is.null(acc) || acc$total == 0) return(NULL)
    wrong <- acc$total - acc$correct
    div(class="accuracy-bar",
        div(class="acc-stat", div(class="acc-val", paste0(acc$pct,"%")), div(class="acc-lbl","Accuracy")),
        div(class="acc-divider"),
        div(class="acc-stat", div(class="acc-val", acc$correct), div(class="acc-lbl","Correct")),
        div(class="acc-divider"),
        div(class="acc-stat", div(class="acc-val", wrong), div(class="acc-lbl","Incorrect")),
        div(class="acc-divider"),
        div(class="acc-stat", div(class="acc-val", acc$total), div(class="acc-lbl","Resolved")),
        if (is.finite(acc$brier %||% NA_real_)) tagList(div(class="acc-divider"),
          div(class="acc-stat", div(class="acc-val", sprintf("%.3f", acc$brier)),
              div(class="acc-lbl","Brier (0.250 = coin flip)"))))
  })
  
  output$games_section <- renderUI({
    s <- store()
    if (is.null(s) || is.null(s$proj) || nrow(s$proj) == 0)
      return(div(style="color:#475569;font-family:'IBM Plex Mono',monospace;font-size:13px;padding:24px 0;",
                 "No games found. Try Run Forecast or select another date."))
    tagList(div(class="section-hdr",
                div(class="section-title", paste0("Game Outcomes \u2014 ",
                                                  format(as.Date(input$date_picker), "%B %d, %Y"), " (", nrow(s$proj), " games)")),
                div(class="section-hdr-line")),
            div(class="tbl-wrap", DTOutput("games_tbl")))
  })
  
  output$games_tbl <- renderDT({
    s <- store(); req(!is.null(s), !is.null(s$proj), nrow(s$proj) > 0)
    df <- s$proj
    disp <- data.frame(
      Matchup = df$Matchup,
      `Projected winner` = sapply(df$ProjectedWinner, function(w) paste0('<span class="winner-cell">', w, '</span>')),
      `Conf.` = sapply(seq_len(nrow(df)), function(i) {
        c  <- df$Confidence[i]; w <- df$WHIPSignal[i] %||% ""
        lo <- df$LOBSignal[i] %||% ""; sg <- df$SeriesGame[i] %||% ""
        cls   <- if (c == "High") "conf-high" else if (c == "Medium") "conf-med" else "conf-low"
        badge <- paste0('<span class="', cls, '">', c, '</span>')
        if (nchar(w)  > 0) badge <- paste0(badge, '<span class="whip-flag">',  w,  '</span>')
        if (nchar(lo) > 0) { lc <- if (lo == "LOB+") "lob-plus" else "lob-minus"
        badge <- paste0(badge, '<span class="', lc, '">', lo, '</span>') }
        if (nchar(sg) > 0) badge <- paste0(badge, '<span class="ser-badge">', sg, '</span>')
        if (isTRUE(df$Locked[i]))                       # pick replayed from the ledger, not re-derived
          badge <- paste0(badge, '<span class="lock-badge" title="Pick locked when this game was first graded">\u25a0 LOCK</span>')
        badge
      }),
      `O/U` = sapply(df$Total, function(t) paste0('<span class="total-cell">', t, '</span>')),
      Result = mapply(function(result, is_live, is_correct) {
        if (!is.na(is_live) && is_live) paste0('<span class="result-live">\u25cf ', result, '</span>')
        else if (!is.na(is_correct) && isTRUE(is_correct)) paste0('<span class="result-correct">\u2713 ', result, '</span>')
        else if (!is.na(is_correct) && !is_correct) paste0('<span class="result-incorrect">\u2717 ', result, '</span>')
        else paste0('<span class="result-pending">', result, '</span>')
      }, df$ActualResult, df$IsLive, df$IsCorrect, SIMPLIFY=TRUE),
      check.names=FALSE, stringsAsFactors=FALSE)
    row_cls <- ifelse(!is.na(df$IsCorrect) & df$IsCorrect, "row-correct",
                      ifelse(!is.na(df$IsCorrect) & !df$IsCorrect, "row-incorrect",
                             ifelse(df$IsLive %in% TRUE, "row-live", "")))
    disp$gid <- df$GameID
    datatable(disp, callback=JS("tdxBind(table, 'games_tbl', 'mlb_tdx', 5);"),
              options=list(pageLength=30, scrollX=FALSE, dom="ftp",
                           columnDefs=list(list(targets=5, visible=FALSE)),
                                 rowCallback=JS(sprintf("function(row,data,index){var cls=%s;if(cls[index]&&cls[index]!=='')$(row).addClass(cls[index]);}",
                                                        jsonlite::toJSON(row_cls)))),
              rownames=FALSE, class="stripe", escape=FALSE)
  }, server = FALSE)
  
  output$nrfi_section <- renderUI({
    s <- store(); if (is.null(s) || is.null(s$nrfi) || nrow(s$nrfi) == 0) return(NULL)
    df <- s$nrfi
    res <- df[!is.na(df$IsCorrect), , drop=FALSE]
    acc <- if (nrow(res) > 0)
      sprintf(" \u00b7 %d/%d correct (%.0f%%)", sum(res$IsCorrect), nrow(res),
              100*mean(res$IsCorrect)) else ""
    tagList(div(class="section-hdr",
                div(class="section-title",
                    paste0("First Inning \u2014 Run / No Run (", nrow(df), " games", acc, ")")),
                div(class="section-hdr-line")),
            div(style="font-family:'IBM Plex Mono',monospace;font-size:11px;color:#64748b;margin:-6px 0 12px;",
                paste0("Ranked by confidence that NO run scores. Exact base-out dynamic program over the top of the order vs. the starter at his first time through \u00b7 league base rate ",
                       sprintf("%.1f%%", NRFI_LG_BASE*100))),
            local({
              tr <- tryCatch(nrfi_track_record(), error = function(e) NULL)
              if (is.null(tr)) NULL else
                div(style="font-family:'IBM Plex Mono',monospace;font-size:11px;color:#a8620a;background:rgba(245,158,11,.10);border:1px solid rgba(245,158,11,.28);border-radius:6px;padding:7px 10px;margin:-4px 0 14px;",
                    tr)
            }),
            div(class="tbl-wrap", DTOutput("nrfi_tbl")))
  })
  
  output$nrfi_tbl <- renderDT({
    s <- store(); req(!is.null(s), !is.null(s$nrfi), nrow(s$nrfi) > 0)
    df <- s$nrfi
    disp <- data.frame(
      Matchup = df$Matchup,
      Starters = sapply(df$Starters, function(x) paste0('<span class="sp-line">', x, '</span>')),
      `NRFI %` = sapply(seq_len(nrow(df)), function(i) {
        n <- df$NRFIProbNum[i]
        cls <- if (n >= 58) "nrfi-hi" else if (n >= 48) "nrfi-mid" else "nrfi-lo"
        paste0('<span class="', cls, '">', df$NRFIProb[i], '</span>')
      }),
      Pick = sapply(df$Pick, function(p)
        paste0('<span class="', if (p == "NRFI") "pick-nrfi" else "pick-yrfi", '">', p, '</span>')),
      `Conf.` = sapply(seq_len(nrow(df)), function(i) {
        c <- df$Confidence[i]; fl <- df$Flags[i] %||% ""; e <- df$Edge[i]
        cls <- if (c == "High") "conf-high" else if (c == "Medium") "conf-med" else "conf-low"
        badge <- paste0('<span class="', cls, '">', c, '</span>')
        ecls  <- if (!is.na(e) && e >= 0) "edge-pos" else "edge-neg"
        badge <- paste0(badge, ' <span class="', ecls, '">',
                        if (!is.na(e) && e >= 0) "+" else "", e, '</span>')
        if (nchar(fl) > 0) for (f in strsplit(fl, " ")[[1L]])
          badge <- paste0(badge, '<span class="nrfi-flag">', f, '</span>')
        badge
      }),
      `Top/Bot` = sprintf('<span class="half-cell">%.0f%% / %.0f%%</span>',
                          df$TopScoreless, df$BotScoreless),
      `F1 runs` = sprintf('<span class="total-cell">%.2f</span>', df$F1Runs),
      Result = sapply(seq_len(nrow(df)), function(i) {
        r <- df$Result[i]; ic <- df$IsCorrect[i]
        if (!is.na(ic) && isTRUE(ic)) paste0('<span class="result-correct">\u2713 ', r, '</span>')
        else if (!is.na(ic) && !ic)   paste0('<span class="result-incorrect">\u2717 ', r, '</span>')
        else paste0('<span class="result-pending">', r, '</span>')
      }),
      check.names=FALSE, stringsAsFactors=FALSE)
    row_cls <- ifelse(!is.na(df$IsCorrect) & df$IsCorrect, "row-correct",
                      ifelse(!is.na(df$IsCorrect) & !df$IsCorrect, "row-incorrect", ""))
    datatable(disp, options=list(pageLength=30, scrollX=FALSE, dom="ftp", ordering=FALSE,
                                 rowCallback=JS(sprintf("function(row,data,index){var cls=%s;if(cls[index]&&cls[index]!=='')$(row).addClass(cls[index]);}",
                                                        jsonlite::toJSON(row_cls)))),
              rownames=FALSE, class="stripe", escape=FALSE)
  }, server = FALSE)
  
  # A game's eight likeliest home-run hitters. The slate board keeps every hitter;
  # this is the same numbers narrowed to the game that was tapped.
  mlb_tdx_html <- function(gid) tryCatch({
    s <- store()
    if (is.null(s) || is.null(s$hr) || !nrow(s$hr)) tdx_none("No home-run projections for this game yet.") else {
      x <- s$hr[as.character(s$hr$GameID) == as.character(gid), , drop = FALSE]
      pr <- suppressWarnings(as.numeric(x$HRProbNum)) / 100
      ok <- is.finite(pr)
      x <- x[ok, , drop = FALSE]; pr <- pr[ok]
      o <- order(-pr)
      x <- utils::head(x[o, , drop = FALSE], 8L); pr <- utils::head(pr[o], 8L)
      sc <- if ("IsCorrect" %in% names(x)) as.integer(x$IsCorrect) else rep(NA_integer_, nrow(x))
      tdx_html(sprintf('<span class="tm">%s</span>', dash_esc(x$Player)), x$Team, pr, sc,
               TDX_HR_NOTE, title = "Most likely home-run hitters", miss = "No home run")
    }
  }, error = function(e) tdx_none(if (inherits(e, "shiny.silent.error"))
    "Home-run projections are still loading \u2014 tap the game again in a moment." else conditionMessage(e)))
  observeEvent(input$mlb_tdx, {
    gid <- as.character(input$mlb_tdx$gid %||% "")
    session$sendCustomMessage("tdx", list(tbl = "games_tbl", gid = gid, html = mlb_tdx_html(gid)))
  }, ignoreInit = TRUE)

  output$hr_section <- renderUI({
    s <- store(); if (is.null(s) || is.null(s$hr) || nrow(s$hr) == 0) return(NULL)
    tagList(div(class="section-hdr",
                div(class="section-title", paste0("HR Picks \u2014 ", nrow(s$hr), " Players")),
                div(class="section-hdr-line")),
            div(class="tbl-wrap", DTOutput("hr_tbl")))
  })
  
  output$hr_tbl <- renderDT({
    s <- store(); req(!is.null(s), !is.null(s$hr), nrow(s$hr) > 0)
    df <- s$hr
    disp <- data.frame(
      Player=df$Player, Team=df$Team, Matchup=df$Matchup, `Opp. pitcher`=df$OppPitcher,
      `HR %` = mapply(function(p, n) {
        cls <- if (n >= 18) "hr-hi" else if (n >= 12) "hr-mid" else "hr-lo"
        paste0('<span class="', cls, '">', p, '</span>')
      }, df$HRProb, df$HRProbNum, SIMPLIFY=TRUE),
      Result = sapply(df$Result, function(r) {
        if (grepl("\u2713", r)) paste0('<span class="result-hr">', r, '</span>')
        else if (grepl("\u2717", r)) paste0('<span class="result-nohr">', r, '</span>')
        else paste0('<span class="result-pending">', r, '</span>')
      }),
      check.names=FALSE, stringsAsFactors=FALSE)
    row_cls <- ifelse(!is.na(df$IsCorrect) & df$IsCorrect, "row-correct",
                      ifelse(!is.na(df$IsCorrect) & !df$IsCorrect, "row-incorrect", ""))
    datatable(disp, options=list(pageLength=50, scrollX=FALSE, dom="ftp",
                                 rowCallback=JS(sprintf("function(row,data,index){var cls=%s;if(cls[index]&&cls[index]!=='')$(row).addClass(cls[index]);}",
                                                        jsonlite::toJSON(row_cls)))),
              rownames=FALSE, class="stripe", escape=FALSE)
  }, server = FALSE)
  
  output$k_section <- renderUI({
    s <- store(); if (is.null(s) || is.null(s$kprops) || nrow(s$kprops) == 0) return(NULL)
    tagList(div(class="section-hdr",
                div(class="section-title", paste0("K Props \u2014 ", nrow(s$kprops), " Starters")),
                div(class="section-hdr-line")),
            div(class="tbl-wrap", DTOutput("k_tbl")))
  })
  
  output$k_tbl <- renderDT({
    s <- store(); req(!is.null(s), !is.null(s$kprops), nrow(s$kprops) > 0)
    df <- s$kprops; df <- df[order(-df$ExpKNum), ]
    expk_html <- sprintf('<span style="font-family:\'IBM Plex Mono\',monospace;font-weight:600;color:#60a5fa">%.1f</span>', df$ExpK)
    result_html <- sapply(seq_len(nrow(df)), function(i) {
      r <- df$Result[i]; ic <- df$IsCorrect[i]
      if (!is.na(ic) && isTRUE(ic)) paste0('<span class="result-correct">', r, '</span>')
      else if (!is.na(ic) && !ic) paste0('<span class="result-incorrect">', r, '</span>')
      else paste0('<span class="result-pending">', r, '</span>')
    })
    row_cls <- ifelse(!is.na(df$IsCorrect) & df$IsCorrect, "row-correct",
                      ifelse(!is.na(df$IsCorrect) & !df$IsCorrect, "row-incorrect", ""))
    line_html <- if ("Line" %in% names(df)) sprintf('<span class="total-cell">%s %.1f</span>',
                                                  ifelse(df$Pick == "Over", "O", "U"), df$Line) else ""
    pov_html  <- if ("POver" %in% names(df)) sprintf('<span class="half-cell">%d%%</span>', as.integer(df$POver)) else ""
    disp <- data.frame(SP=df$SP, Matchup=df$Matchup, `Exp. K`=expk_html, Pick=line_html,
                       `P(over)`=pov_html, Result=result_html,
                       stringsAsFactors=FALSE, check.names=FALSE)
    datatable(disp, options=list(pageLength=30, dom="tp", ordering=FALSE,
                                 rowCallback=JS(sprintf("function(row,data,index){var cls=%s;if(cls[index]&&cls[index]!=='')$(row).addClass(cls[index]);}",
                                                        jsonlite::toJSON(row_cls)))),
              rownames=FALSE, class="stripe", escape=FALSE)
  }, server = FALSE)
  
  # ---- Model self-diagnostics: what's working, what busted, is it calibrated ----
  output$diag_section <- renderUI({
    s <- store(); if (is.null(s)) return(NULL)
    dg <- tryCatch(compute_model_diagnostics(awm_load(), awm_load(AWM_MEMORY_PATH)), error=function(e) NULL)
    if (is.null(dg) || dg$n < 20) return(NULL)
    tbl <- function(df, headers) {
      if (is.null(df) || !nrow(df)) return("")
      hd <- paste0("<tr>", paste(sprintf("<th style='text-align:left;padding:4px 14px 4px 0;color:#64748b;font-family:IBM Plex Mono,monospace;font-size:10px;text-transform:uppercase;letter-spacing:1px'>%s</th>", headers), collapse=""), "</tr>")
      bd <- paste(apply(df, 1, function(r) paste0("<tr>", paste(sprintf("<td style='padding:3px 14px 3px 0;font-family:IBM Plex Mono,monospace;font-size:12px;color:#cbd5e1'>%s</td>", r), collapse=""), "</tr>")), collapse="")
      paste0("<table style='border-collapse:collapse;margin:4px 0 14px'>", hd, bd, "</table>")
    }
    cur <- s$proj
    coef_line <- if (!is.null(cur) && nrow(cur) && "CoefMC" %in% names(cur))
      sprintf("Live weights \u2014 run model %.3f | Pythagorean gap %.3f | fit on %s graded %s games (%.0f%% data, rest prior) | %s",
              cur$CoefMC[1], cur$CoefPyth[1], format(as.integer(cur$LearnGames[1]), big.mark = ","), MLB_MODEL_VER,
              100 * (cur$LearnWeight[1] %||% 0), awm_half_life_label(cur$LearnHalfLife[1])) else ""
    score_line <- if (isTRUE(dg$from_memory))
      sprintf("Current model (%s), every game scored point-in-time: accuracy %.1f%%, Brier %.4f (0.250 = coin flip), log loss %.4f (0.693 = coin flip)",
              dg$version, dg$overall, dg$brier %||% NA_real_, dg$logloss %||% NA_real_)
    else
      sprintf("Scored on %s: accuracy %.1f%%, Brier %.4f (0.250 = coin flip), log loss %.4f (0.693 = coin flip)",
              dg$version, dg$overall, dg$brier %||% NA_real_, dg$logloss %||% NA_real_)
    rec <- dg$record
    record_line <- if (isTRUE(dg$from_memory) && !is.null(rec))
      sprintf("Picks on record (locked at first pitch, any model version): %s games, accuracy %.1f%%, Brier %.4f",
              format(rec$n, big.mark = ","), rec$overall, rec$brier) else ""
    HTML(paste0(
      "<div class='section-hdr'><div class='section-title'>Model Diagnostics \u2014 ", format(dg$n, big.mark = ","),
      " graded games (overall ", dg$overall, "%)</div><div class='section-hdr-line'></div></div>",
      "<div style='font-family:IBM Plex Mono,monospace;font-size:11px;color:#93c5fd;margin-bottom:4px'>", coef_line, "</div>",
      "<div style='font-family:IBM Plex Mono,monospace;font-size:11px;color:#cbd5e1;margin-bottom:", if (nzchar(record_line)) "4px" else "12px", "'>", score_line, "</div>",
      if (nzchar(record_line)) paste0("<div style='font-family:IBM Plex Mono,monospace;font-size:11px;color:#94a3b8;margin-bottom:12px'>", record_line, "</div>") else "",
      "<div style='color:#94a3b8;font-size:11px;font-family:IBM Plex Mono,monospace;margin-bottom:2px'>Each metric: how often it pointed at the actual winner (under 50% = hurting)</div>",
      tbl(dg$attrib, c("metric","games","right_pct")),
      if (!is.null(dg$busted)) paste0("<div style='color:#94a3b8;font-size:11px;font-family:IBM Plex Mono,monospace;margin-bottom:2px'>On losses, which metric pushed hardest the WRONG way</div>", tbl(dg$busted, c("metric","pct_of_losses"))) else "",
      "<div style='color:#94a3b8;font-size:11px;font-family:IBM Plex Mono,monospace;margin-bottom:2px'>Calibration \u2014 if 'actual' tracks 'predicted', confidence is real</div>",
      tbl(dg$cal, c("bucket","predicted","actual","n"))))
  })


  nhl_seen <- reactiveVal(FALSE)
  observeEvent(input$lg, { if (identical(input$lg, "nhl")) nhl_seen(TRUE) },
               ignoreNULL = TRUE, ignoreInit = FALSE)
  ndat <- reactive({
    req(isTRUE(nhl_seen()))
    invalidateLater(POLL_MIN * 60 * 1000)
    warm_own("nhl")
    withProgress(message = "Loading NHL data", value = 0.4, {
      nhl_sync(force = isTRUE(input$nrefresh > 0 && FALSE))
      nhl_load()
    })
  })
  nwk <- reactiveVal(FALSE)
  observe(dash_guard("NHL data", {
    if (isTRUE(nwk())) return()
    d <- ndat(); req(d)
    td <- today_et()
    up <- d$sch$ko[d$sch$ko > now_et()]
    dd <- if (any(d$sch$date == td, na.rm = TRUE)) td
          else if (length(up)) day_et(min(up))
          else max(d$sch$date, na.rm = TRUE)
    if (!is.null(url_state$ndate)) dd <- url_state$ndate                # a reload keeps the date you were on
    updateDateInput(session, "ndate", value = dd)
    nwk(TRUE)
  }))
  nmodel <- reactive({
    d <- ndat(); req(d, input$ndate)
    s <- nhl_season_of(as.Date(input$ndate))
    withProgress(message = "Rating NHL teams", value = 0.6, {
      R <- nhl_rows(d$pan, d$endr, d$ents, s, d$gf)
      if (is.null(R)) NULL else nhl_fit(R, s)
    })
  })
  nboard <- reactive({
    d <- ndat(); m <- nmodel(); req(m, input$ndate)
    dd <- as.Date(input$ndate)
    g <- d$sch[d$sch$date == dd, ]
    if (!nrow(g)) return(NULL)
    now <- now_et()
    cut <- as.POSIXct(pmin(as.numeric(g$ko), as.numeric(now)), origin = "1970-01-01", tz = TZ_ET)
    st <- game_settle(NHL_LEDGER, NHL_MODEL,
                      function(gi, cutoff) nhl_predict(d$pan, d$endr, d$ents, m, gi, cutoff, d$gf),
                      g, now)
    if (is.null(st) || !nrow(st)) return(NULL)
    done <- g$has_score & g$final_at <= now
    game_grade_slate(NHL_LEDGER, g, done)
    list(g = g, st = st, done = done,
         pick = ifelse(st$pred > 0, g$home, g$away),
         ok = done & ((st$pred > 0) == (g$home_score > g$away_score)),
         cut = min(cut))
  })
  output$nrecord <- renderUI({
    d <- ndat()
    b <- nboard()
    msg <- if (is.null(b)) "No NHL games on this date." else {
      n <- sum(b$done); h <- sum(b$ok, na.rm = TRUE)
      if (n == nrow(b$g) && n > 0) sprintf("Model went %d-%d on %d games.", h, n - h, n)
      else if (n > 0) sprintf("%d games, %d still to play. %d-%d so far.",
                              nrow(b$g), nrow(b$g) - n, h, n - h)
      else sprintf("%d games. %d locked at puck drop, the rest update until theirs.",
                   nrow(b$g), sum(b$st$locked %in% TRUE))
    }
    div(class = "rec", msg,
        if (length(d$dropped))
          span(style = "color:#fcd34d", sprintf(
            "  Seasons %s dropped: the public feed has one identical score for every game.",
            paste(d$dropped, collapse = ", "))))
  })
  output$nboard_sec <- renderUI({
    req(nboard())
    tagList(div(class = "sec-hdr", "Game outcomes"), DTOutput("nboard"))
  })
  output$nboard <- renderDT({
    b <- nboard(); req(b); d <- ndat(); g <- b$g
    o <- order(-b$st$conf)
    bd <- function(id) lg_badge(unname(d$logo[id]))
    nmv <- function(id) ifelse(is.na(unname(d$nm[id])), id, unname(d$nm[id]))
    tbl <- data.frame(
      Matchup = sprintf('%s<span class="tm">%s</span><span class="at">@</span>%s<span class="tm">%s</span>',
                        bd(g$away), nmv(g$away), bd(g$home), nmv(g$home)),
      Pick = sprintf('%s<span class="winner-cell">%s</span>', bd(b$pick), nmv(b$pick)),
      `Proj margin` = sprintf('<span class="mg">%.2f</span>', abs(b$st$pred)),
      Confidence = prob_pill(b$st$conf),
      Final = ifelse(b$done, paste0(g$away_score, "-", g$home_score), ""),
      Result = ifelse(!b$done, '<span class="nt">&mdash;</span>',
               ifelse(b$ok, '<span class="rs ok">Correct</span>',
                            '<span class="rs no">Wrong</span>')),
      check.names = FALSE, stringsAsFactors = FALSE)
    tbl$gid <- g$game_id
    datatable(tbl[o, ], rownames = FALSE, escape = FALSE, selection = "none",
              callback = JS("tdxBind(table, 'nboard', 'nhl_tdx', 6);"),
              options = list(pageLength = 20, dom = "t", ordering = FALSE,
                             columnDefs = list(list(targets = 2:4, className = "dt-right"),
                                               list(targets = 6, visible = FALSE))))
  }, server = FALSE)
  # A game's eight likeliest goalscorers, pulled from the same slate-wide board shown
  # below it -- the board carries a team rather than a game, so the game's two teams
  # are what select it.
  nhl_tdx_html <- function(gid) tryCatch({
    x <- ngoal_tbl(); b <- nboard()
    if (is.null(x) || is.null(b)) tdx_none("No skater projections for this game yet.") else {
      i <- match(as.character(gid), as.character(b$g$game_id))
      if (is.na(i)) tdx_none("No skater projections for this game yet.") else {
        x <- x[x$team %in% c(b$g$home[i], b$g$away[i]) & is.finite(x$p), , drop = FALSE]
        x <- utils::head(x[order(-x$p), , drop = FALSE], 8L)
        sc <- ifelse(x$state == "played", x$scored, NA_integer_)
        d <- ndat()
        nm <- ifelse(is.na(x$inj),
               sprintf('%s<span class="tm">%s</span>', lg_badge(unname(d$logo[x$team])), x$pname),
               sprintf('%s<span class="tm">%s</span><span class="qt dnp">%s</span>',
                       lg_badge(unname(d$logo[x$team])), x$pname, x$inj))
        tdx_html(nm, x$pos, x$p, sc, TDX_NOTE,
                 title = "Most likely goalscorers", miss = "No goal")
      }
    }
  }, error = function(e) tdx_none(if (inherits(e, "shiny.silent.error"))
    "Skater projections are still loading \u2014 tap the game again in a moment." else conditionMessage(e)))
  observeEvent(input$nhl_tdx, {
    gid <- as.character(input$nhl_tdx$gid %||% "")
    session$sendCustomMessage("tdx", list(tbl = "nboard", gid = gid, html = nhl_tdx_html(gid)))
  }, ignoreInit = TRUE)

  ngoal_tbl <- reactive({
    b <- nboard(); d <- ndat(); req(b, d)
    live <- isTRUE(day_et(b$cut) >= today_et())
    inj <- if (live) tryCatch(nhl_inj(), error = function(e) NULL) else NULL
    tk  <- if (live) tryCatch(nhl_team_key(d$sch), error = function(e) NULL) else NULL
    x <- nhl_gs(d$sk, b$cut, unique(c(b$g$home, b$g$away)), inj, tk)
    if (is.null(x) || !nrow(x)) return(NULL)
    st <- grade_state(x$pid, x$team, b, d$sk)
    j <- attr(st, "row"); r <- attr(st, "src")
    x$state <- as.character(st)
    x$scored <- NA_integer_
    pl <- x$state == "played"
    if (any(pl)) x$scored[pl] <- as.integer(r$scored[j[pl]] > 0)
    if (any(pl)) {
      tg <- stats::setNames(c(b$g$game_id, b$g$game_id), c(b$g$home, b$g$away))
      tk2 <- stats::setNames(c(b$g$ko, b$g$ko), c(b$g$home, b$g$away))
      tryCatch(prop_record("nhl", "anytime_goal", unname(tg[x$team[pl]]),
                           x$pid[pl], x$pname[pl], unname(tk2[x$team[pl]]),
                           x$p[pl], x$scored[pl], sprintf("nhl-gs-v%d", NHL_VER)),
               error = function(e) NULL)
    }
    x
  })
  output$ngoal_sec <- renderUI({
    x <- ngoal_tbl()
    if (is.null(x) || !nrow(x)) return(NULL)
    k <- utils::head(x, 10L)
    tally <- if (any(!is.na(k$scored)))
      sprintf(" \u00b7 top 10: %d of %d scored", sum(k$scored, na.rm = TRUE),
              sum(!is.na(k$scored))) else ""
    tagList(div(class = "sec-hdr", sprintf("Anytime goalscorer \u2014 %d skaters%s",
                                           nrow(x), tally)),
            DTOutput("ngoal"),
            div(class = "hint",
                "Probability the skater records at least one goal, assuming he dresses. ",
                "His own scoring rate shrunk toward the positional base rate. Shots on goal ",
                "and time on ice were tested as multipliers and made it worse, so they are out. ",
                "Calibrated to within a point in every bucket over 2024-25 and 2025-26."))
  })
  output$ngoal <- renderDT({
    x <- ngoal_tbl(); req(x)
    res <- ifelse(x$state == "pending", '<span class="nt">\u2014</span>',
           ifelse(x$state == "dnp", '<span class="rs">Did not dress</span>',
           ifelse(x$scored > 0, '<span class="rs ok">Scored</span>',
                                '<span class="rs no">No goal</span>')))
    nm <- ifelse(is.na(x$inj), sprintf('<span class="tm">%s</span>', x$pname),
                 sprintf('<span class="tm">%s</span><span class="qt dnp">%s</span>',
                         x$pname, x$inj))
    tbl <- data.frame(
      Skater = nm,
      Pos = x$pos, Team = x$team,
      `Goal prob` = prob_pill(x$p, 0.55),
      Gm = x$n, G = x$g, Result = res,
      check.names = FALSE, stringsAsFactors = FALSE)
    datatable(tbl, rownames = FALSE, escape = FALSE, selection = "none",
              options = list(pageLength = 25, dom = "ftp", ordering = FALSE,
                             columnDefs = list(list(targets = 3:5, className = "dt-right"))))
  }, server = FALSE)
  output$nleak <- renderUI({
    m <- nmodel()
    if (is.null(m)) return(div(class = "err", "Not enough completed prior seasons to calibrate."))
    div(class = "leak",
      tags$b("No leakage. "),
      sprintf(paste0("Ratings use only games finished before the slate, and the ",
                     "rating-to-goals mapping plus the confidence curve are fit on earlier ",
                     "seasons alone (%s games)."), format(m$n, big.mark = ",")),
      tags$br(), tags$b("Accuracy. "),
      "57.97% of games called correctly [55.7, 59.5], average margin error 2.09 goals, on ",
      "5,125 games. Confidence is calibrated: 54.7% at the flat end rising to 67.3% at the top. ",
      "Hockey is the hardest of these leagues to predict and the market itself sits near 58%.")
  })

  nba_seen <- reactiveVal(FALSE)
  observeEvent(input$lg, { if (identical(input$lg, "nba")) nba_seen(TRUE) },
               ignoreNULL = TRUE, ignoreInit = FALSE)
  bdat <- reactive({
    req(isTRUE(nba_seen()))
    invalidateLater(POLL_MIN * 60 * 1000)
    warm_own("nba")
    withProgress(message = "Loading NBA data", value = 0.4, { nba_sync(); nba_load() })
  })
  bwk <- reactiveVal(FALSE)
  observe(dash_guard("NBA data", {
    if (isTRUE(bwk())) return()
    d <- bdat(); req(d)
    td <- today_et()
    up <- d$sch$ko[d$sch$ko > now_et()]
    dd <- if (any(d$sch$date == td, na.rm = TRUE)) td
          else if (length(up)) day_et(min(up))
          else max(d$sch$date, na.rm = TRUE)
    if (!is.null(url_state$bdate)) dd <- url_state$bdate                # a reload keeps the date you were on
    updateDateInput(session, "bdate", value = dd)
    bwk(TRUE)
  }))
  bmodel <- reactive({
    d <- bdat(); req(d, input$bdate)
    s <- d$sch$season[match(TRUE, d$sch$date >= as.Date(input$bdate))]
    if (is.na(s)) s <- max(d$sch$season)
    withProgress(message = "Rating NBA teams", value = 0.6, {
      R <- nba_rows(d$pan, d$endr, d$ents, s)
      if (is.null(R)) NULL else nba_fit(R, s)
    })
  })
  bboard <- reactive({
    d <- bdat(); m <- bmodel(); req(m, input$bdate)
    g <- d$sch[d$sch$date == as.Date(input$bdate), ]
    if (!nrow(g)) return(NULL)
    now <- now_et()
    cut <- as.POSIXct(pmin(as.numeric(g$ko), as.numeric(now)), origin = "1970-01-01", tz = TZ_ET)
    st <- game_settle(NBA_LEDGER, NBA_MODEL,
                      function(gi, cutoff) nba_predict(d$pan, d$endr, d$ents, m, gi, cutoff),
                      g, now)
    if (is.null(st) || !nrow(st)) return(NULL)
    done <- g$has_score & g$final_at <= now
    game_grade_slate(NBA_LEDGER, g, done)
    list(g = g, st = st, done = done,
         pick = ifelse(st$pred > 0, g$home, g$away),
         ok = done & ((st$pred > 0) == (g$home_score > g$away_score)),
         cut = min(cut))
  })
  output$brecord <- renderUI({
    b <- bboard()
    if (is.null(b)) return(div(class = "rec", "No NBA games on this date."))
    n <- sum(b$done); h <- sum(b$ok, na.rm = TRUE)
    div(class = "rec", if (n == nrow(b$g) && n > 0)
      sprintf("Model went %d-%d on %d games.", h, n - h, n)
      else if (n > 0) sprintf("%d games, %d still to play. %d-%d so far.",
                              nrow(b$g), nrow(b$g) - n, h, n - h)
      else sprintf("%d games. %d locked at tip-off, the rest update until theirs.",
                   nrow(b$g), sum(b$st$locked %in% TRUE)))
  })
  output$bboard_sec <- renderUI({
    req(bboard()); tagList(div(class = "sec-hdr", "Game outcomes"), DTOutput("bboard"))
  })
  output$bboard <- renderDT({
    b <- bboard(); req(b); d <- bdat(); g <- b$g
    o <- order(-b$st$conf)
    bd <- function(id) lg_badge(unname(d$logo[id]))
    nmv <- function(id) ifelse(is.na(unname(d$nm[id])), id, unname(d$nm[id]))
    tbl <- data.frame(
      Matchup = sprintf('%s<span class="tm">%s</span><span class="at">@</span>%s<span class="tm">%s</span>',
                        bd(g$away), nmv(g$away), bd(g$home), nmv(g$home)),
      Pick = sprintf('%s<span class="winner-cell">%s</span>', bd(b$pick), nmv(b$pick)),
      `Proj margin` = sprintf('<span class="mg">%.1f</span>', abs(b$st$pred)),
      Confidence = prob_pill(b$st$conf),
      Final = ifelse(b$done, paste0(g$away_score, "-", g$home_score), ""),
      Result = ifelse(!b$done, '<span class="nt">&mdash;</span>',
               ifelse(b$ok, '<span class="rs ok">Correct</span>',
                            '<span class="rs no">Wrong</span>')),
      check.names = FALSE, stringsAsFactors = FALSE)
    tbl$gid <- g$game_id
    datatable(tbl[o, ], rownames = FALSE, escape = FALSE, selection = "none",
              callback = JS("tdxBind(table, 'bboard', 'nba_tdx', 6);"),
              options = list(pageLength = 20, dom = "t", ordering = FALSE,
                             columnDefs = list(list(targets = 2:4, className = "dt-right"),
                                               list(targets = 6, visible = FALSE))))
  }, server = FALSE)
  # Every starter in the game, not a top eight: exactly one of the ten gets the first
  # basket, so cutting two of them would be hiding candidates rather than noise.
  nba_tdx_html <- function(gid) tryCatch({
    x <- bfb_tbl(); b <- bboard()
    if (is.null(x) || is.null(b)) tdx_none("No starter projections for this game yet.") else {
      i <- match(as.character(gid), as.character(b$g$game_id))
      if (is.na(i)) tdx_none("No starter projections for this game yet.") else {
        x <- x[x$team %in% c(b$g$home[i], b$g$away[i]) & is.finite(x$p_fg), , drop = FALSE]
        x <- utils::head(x[order(-x$p_fg), , drop = FALSE], 10L)
        sc <- ifelse(x$state == "played", x$yf, NA_integer_)
        d <- bdat()
        nm <- sprintf('%s<span class="tm">%s</span>', lg_badge(unname(d$logo[x$team])), x$pname)
        tdx_html(nm, x$pos, x$p_fg, sc, TDX_FB_NOTE,
                 title = "Most likely first basket", miss = "Not first")
      }
    }
  }, error = function(e) tdx_none(if (inherits(e, "shiny.silent.error"))
    "Starter projections are still loading \u2014 tap the game again in a moment." else conditionMessage(e)))
  observeEvent(input$nba_tdx, {
    gid <- as.character(input$nba_tdx$gid %||% "")
    session$sendCustomMessage("tdx", list(tbl = "bboard", gid = gid, html = nba_tdx_html(gid)))
  }, ignoreInit = TRUE)

  bfb_tbl <- reactive({
    b <- bboard(); d <- bdat(); req(b, d)
    live <- isTRUE(day_et(b$cut) >= today_et())
    inj <- if (live) tryCatch(nba_inj(), error = function(e) NULL) else NULL
    tk  <- if (live) tryCatch(espn_team_key(d$sch), error = function(e) NULL) else NULL
    tms <- unique(c(b$g$home, b$g$away))
    # only for a slate that has not been played: on a past date the box-score team is right
    ros <- if (live) tryCatch(nba_roster(tms), error = function(e) NULL) else NULL
    st  <- if (live) tryCatch(nba_starters_slate(b$g$game_id, b$g$ko), error = function(e) NULL) else NULL
    x <- nba_fb(d$fbh, b$cut, tms, inj, tk, ros, st)
    if (is.null(x) || !nrow(x)) return(NULL)
    st <- grade_state(x$pid, x$team, b, d$fbh)
    j <- attr(st, "row"); r <- attr(st, "src")
    x$state <- as.character(st)
    x$yf <- NA_integer_; x$ya <- NA_integer_
    pl <- x$state == "played"
    if (any(pl)) { x$yf[pl] <- as.integer(r$y_fg[j[pl]])
                   x$ya[pl] <- as.integer(r$y_any[j[pl]]) }
    x
  })
  output$bfb_sec <- renderUI({
    x <- bfb_tbl()
    if (is.null(x) || !nrow(x)) return(NULL)
    k <- utils::head(x[order(-x$p_fg), ], 10L)
    tally <- if (any(!is.na(k$yf)))
      sprintf(" \u00b7 top 10: %d first FG, %d first score",
              sum(k$yf, na.rm = TRUE), sum(k$ya, na.rm = TRUE)) else ""
    tagList(div(class = "sec-hdr", sprintf("First basket \u2014 %d players%s",
                                           nrow(x), tally)),
            DTOutput("bfb"),
            div(class = "hint",
                "First FG excludes free throws; first score counts them. 99.9% of first field ",
                "goals are scored by a starter, and a free throw opens the game 7.1% of the time. ",
                "Each number is the man's own history shrunk toward his positional rate, times ",
                "his share of his team's last 20 games \u2014 so it is the chance he takes the first ",
                "basket, not the chance he takes it if he starts. Once a line-up is posted, about an ",
                "hour before tip-off, the five are taken as given and nobody else is listed. Rosters ",
                "come from the team feed, ",
                "because the season files that record who played are published a season behind. ",
                "Walk-forward on 1,479 games from 2023 the top pick hit 12.9%, against 10% for ",
                "picking a starter at random, and a game's stated chances sum to 1.02. A team ",
                "strength term was tested and earned zero weight."))
  })
  output$bfb <- renderDT({
    x <- bfb_tbl(); req(x)
    d <- bdat()
    res <- ifelse(x$state == "pending", '<span class="nt">\u2014</span>',
           ifelse(x$state == "dnp", '<span class="rs">Did not start</span>',
           ifelse(x$yf > 0, '<span class="rs ok">First FG</span>',
           ifelse(x$ya > 0, '<span class="rs ok">First score</span>',
                            '<span class="rs no">No</span>'))))
    tbl <- data.frame(
      Player = sprintf('%s<span class="tm">%s</span>', lg_badge(unname(d$logo[x$team])), x$pname),
      Pos = x$pos,
      `First FG` = prob_pill(x$p_fg, 0.26),
      `First score` = prob_pill(x$p_any, 0.26),
      Gm = x$n, FG = x$f, Any = x$a, Result = res,
      check.names = FALSE, stringsAsFactors = FALSE)
    datatable(tbl, rownames = FALSE, escape = FALSE, selection = "none",
              options = list(pageLength = 25, dom = "ftp", ordering = FALSE,
                             columnDefs = list(list(targets = 4:6, className = "dt-right"))))
  }, server = FALSE)
  output$bleak <- renderUI({
    m <- bmodel()
    if (is.null(m)) return(div(class = "err", "Not enough completed prior seasons to calibrate."))
    div(class = "leak",
      tags$b("No leakage. "),
      sprintf(paste0("Ratings use only games finished before the slate; the mapping and the ",
                     "confidence curve are fit on earlier seasons alone (%s games)."),
              format(m$n, big.mark = ",")),
      tags$br(), tags$b("Accuracy. "),
      "65.1% of games called correctly, average margin error 10.9 points. Rest is in the model: ",
      "a team on zero or one day's rest averages 1.95 points worse, against plus 0.43 on two or ",
      "more, which is a larger swing than the 2.14-point home advantage.")
  })

  # ===================== TODAY (overview) =====================
  # One card per league: yesterday's record on game picks, then today's best value --
  # the model's picks whose price pays more than their chance is worth -- each with its
  # status as the day goes on. Picks come from the same models, ledgers and locks as the
  # league tabs; prices are DraftKings' lines via ESPN, frozen at each game's start in
  # the lines ledger. Leagues load one per flush, so the cards fill in one by one.
  dash <- reactiveValues(y = FALSE, mlb = FALSE, nfl = FALSE, cfb = FALSE, nhl = FALSE, nba = FALSE)
  DASH_ORDER <- c("y", "mlb", "nfl", "cfb", "nhl", "nba")
  dash_n <- reactiveVal(0L)
  observeEvent(input$dash_refresh, {
    for (k in DASH_ORDER) dash[[k]] <- FALSE
    dash_n(dash_n() + 1L)
  }, ignoreInit = TRUE)
  observe(dash_guard("Overview", {
    req(identical(input$lg, "today"))
    dash_n()
    todo <- DASH_ORDER[!vapply(DASH_ORDER, function(k) isTRUE(isolate(dash[[k]])), logical(1))]
    if (!length(todo)) return()
    k <- todo[[1]]; td <- isolate(today_local())
    if (k == "mlb" && dash_in_season("mlb", td)) mlb_seen(TRUE)
    if (k == "nhl" && dash_in_season("nhl", td)) nhl_seen(TRUE)
    if (k == "nba" && dash_in_season("nba", td)) nba_seen(TRUE)
    dash[[k]] <- TRUE
    if (length(todo) > 1L) invalidateLater(200)
  }))

  dash_try <- function(f) tryCatch(f(), error = function(e) {
    if (inherits(e, "shiny.silent.error")) NULL else structure(list(error = conditionMessage(e)), class = "dash_err")
  })
  dash_ok <- function(x) !is.null(x) && !inherits(x, "dash_err")

  # -- MLB: yesterday's game picks from the ledger (graded first) ---------------------
  dash_mlb_y <- reactive({
    req(dash$y); dash_n()
    td <- today_local(); yd <- td - 1
    if (!dash_in_season("mlb", yd)) return(NULL)
    tryCatch(mlb_grade_pending(today = td), error = function(e) NULL)
    L <- awm_load()
    g <- if (!is.null(L)) L[as.character(L$GameDate) == format(yd), , drop = FALSE] else NULL
    if (is.null(g) || !nrow(g)) return(NULL)
    data.frame(lg = "MLB", matchup = g$Matchup, pick = g$ProjectedWinner,
               p = suppressWarnings(as.numeric(g$WinProbNum)) / 100,
               res = ifelse(is.na(g$HomeWon), NA, .is_true(g$IsCorrect)), stringsAsFactors = FALSE)
  })

  # -- MLB: today's slate (the MLB tab's own slate when it is on today) ---------------
  dash_memo <- reactiveValues(key = NULL, val = NULL)
  dash_mlb <- reactive({
    req(dash$mlb); dash_n()
    td <- today_local()
    if (!dash_in_season("mlb", td)) return(NULL)
    on_tab_date <- isTRUE(as.Date(isolate(input$date_picker)) == td)
    s <- if (on_tab_date) store() else {
      key <- paste(td, dash_n())
      if (identical(key, isolate(dash_memo$key))) isolate(dash_memo$val) else {
        v <- withProgress(message = "Loading today's MLB slate\u2026", value = 0,
                          mlb_build_slate(td, progress = function(x, dt) setProgress(x, detail = dt)))
        dash_memo$key <- key; dash_memo$val <- v; v
      }
    }
    P <- s$proj
    if (is.null(P) || !nrow(P)) return(list(rows = NULL))
    sc <- s$sched
    has_t <- !is.null(sc) && nrow(sc) && "StartUTC" %in% names(sc)
    t0 <- if (has_t) mlb_start_utc(sc$StartUTC[match(P$GameID, sc$GameID)]) else as.POSIXct(rep(NA_real_, nrow(P)), origin = "1970-01-01")
    fin <- .is_true(P$IsFinal); live <- .is_true(P$IsLive)
    # scores read from the pick's side: a final is reported winner-first, a live game home-first
    ar <- as.character(P$ActualResult); mtc <- as.character(P$Matchup)
    home_pick <- as.character(P$ProjectedWinner) == sub("^.* @ ", "", mtc)
    score <- vapply(seq_along(ar), function(i) {
      m <- regmatches(ar[i], regexec("([0-9]+)-([0-9]+)$", ar[i]))[[1]]
      if (length(m) != 3L || !(fin[i] || live[i])) return("")
      v <- as.integer(m[2:3])
      flip <- if (fin[i]) !.is_true(P$IsCorrect[i]) else !home_pick[i]
      if (flip) v <- rev(v)
      paste(v, collapse = "-")
    }, "")
    rows <- data.frame(lg = "MLB", t = t0, day = rep(td, nrow(P)), matchup = P$Matchup, pick = P$ProjectedWinner,
                       p = suppressWarnings(as.numeric(P$WinProbNum)) / 100,
                       live = live, final_ = fin, locked = .is_true(P$Locked),
                       res = ifelse(fin, .is_true(P$IsCorrect), NA), score = gsub("-", "\u2013", score),
                       home = sub("^.* @ ", "", mtc), away = sub(" @ .*$", "", mtc), ph = home_pick,
                       eid = NA_character_, home2 = NA_character_, away2 = NA_character_,
                       stringsAsFactors = FALSE)
    list(rows = rows)
  })

  # -- NFL: this week's picks (and last week's results) -------------------------------
  dash_nfl <- reactive({
    req(dash$nfl); dash_n()
    td <- today_local()
    if (!dash_in_season("nfl", td)) return(NULL)
    d <- dat(); now <- now_et(); cs <- current_season(d$sch, now)
    if (is.na(cs) || !cs %in% PICK_SEASONS) return(NULL)
    m <- if (identical(suppressWarnings(as.integer(input$season)), as.integer(cs))) model() else
      fit_history(d$tw, d$sch, d$pdl, d$teams, cs)
    if (is.null(m)) return(NULL)
    wk <- current_week(d$sch, cs, now)
    g <- d$sch[d$sch$season == cs & d$sch$week %in% c(wk - 1L, wk), ]
    if (!nrow(g)) return(NULL)
    st <- settle(d, m, cs, g, now)
    hp <- st$pred > 0
    done <- g$has_score & !is.na(g$final_at) & g$final_at <= now
    tie <- done & g$home_score == g$away_score
    rows <- data.frame(lg = "NFL", t = g$ko, day = dash_local_date(g$ko, view_tz()),
                       matchup = paste(nick(g$away_team), "@", nick(g$home_team)),
                       pick = nick(ifelse(hp, g$home_team, g$away_team)), p = st$conf,
                       live = !done & !is.na(g$ko) & g$ko <= now, final_ = done, locked = st$locked %in% TRUE,
                       res = ifelse(done & !tie, hp == (g$home_score > g$away_score), NA),
                       score = ifelse(done, ifelse(hp, paste0(g$home_score, "\u2013", g$away_score),
                                                    paste0(g$away_score, "\u2013", g$home_score)), ""),
                       home = full(g$home_team), away = full(g$away_team), ph = hp,
                       eid = if ("espn" %in% names(g)) as.character(g$espn) else NA_character_,
                       home2 = NA_character_, away2 = NA_character_,
                       ml_h0 = suppressWarnings(as.numeric(g$home_moneyline)),
                       ml_a0 = suppressWarnings(as.numeric(g$away_moneyline)),
                       stringsAsFactors = FALSE)
    list(rows = rows)
  })

  # -- College football: this week (and last week) ----------------------------------
  dash_cfb <- reactive({
    req(dash$cfb); dash_n()
    td <- today_local()
    if (!dash_in_season("cfb", td)) return(NULL)
    d <- cdat(); now <- now_et(); cs <- cfb_current_season(d$sch, now)
    if (is.na(cs) || !cs %in% CFB_PICK) return(NULL)
    m <- if (identical(suppressWarnings(as.integer(input$cseason)), as.integer(cs))) cmodel() else {
      R <- cfb_rows(d$pan, d$F, d$endr, d$ents, cs); if (is.null(R)) NULL else cfb_fit(R, cs) }
    if (is.null(m)) return(NULL)
    wk <- cfb_current_week(d$sch, cs, now)
    g <- d$sch[d$sch$season == cs & d$sch$week %in% c(wk - 1L, wk) & d$sch$both_fbs, ]
    if (!nrow(g)) return(NULL)
    g <- g[order(g$ko), ]
    st <- cfb_settle(d$pan, d$F, d$endr, d$ents, m, g, now)
    if (is.null(st)) return(NULL)
    nm <- function(ids) vapply(ids, function(i) as.character(cfb_name(d, i)), "")
    hp <- st$pred > 0
    done <- g$has_score & !is.na(g$final_at) & g$final_at <= now
    tie <- done & g$home_score == g$away_score
    rows <- data.frame(lg = "NCAAF", t = g$ko, day = dash_local_date(g$ko, view_tz()),
                       matchup = paste(nm(g$away_id), "@", nm(g$home_id)),
                       pick = nm(ifelse(hp, g$home_id, g$away_id)), p = st$conf,
                       live = !done & !is.na(g$ko) & g$ko <= now, final_ = done, locked = st$locked %in% TRUE,
                       res = ifelse(done & !tie, hp == (g$home_score > g$away_score), NA),
                       score = ifelse(done, ifelse(hp, paste0(g$home_score, "\u2013", g$away_score),
                                                    paste0(g$away_score, "\u2013", g$home_score)), ""),
                       home = nm(g$home_id), away = nm(g$away_id), ph = hp, eid = as.character(g$game_id),
                       home2 = NA_character_, away2 = NA_character_,
                       stringsAsFactors = FALSE)
    list(rows = rows)
  })

  # -- NHL / NBA: yesterday and today ------------------------------------------------
  dash_hoops_ice <- function(lg, d, m, predict_fn, names_fn, espn_ids = FALSE, abbr_fn = NULL) {
    td <- today_local(); now <- now_et()
    g <- d$sch[!is.na(d$sch$date) & d$sch$date %in% c(td - 1, td, td + 1), ]
    if (!nrow(g) || is.null(m)) return(list(rows = NULL))
    cut <- as.POSIXct(pmin(as.numeric(g$ko), as.numeric(now)), origin = "1970-01-01", tz = TZ_ET)
    st <- dplyr::bind_rows(lapply(unique(as.numeric(cut)), function(u) {
      gi <- g[as.numeric(cut) == u, , drop = FALSE]
      predict_fn(d$pan, d$endr, d$ents, m, gi, as.POSIXct(u, origin = "1970-01-01", tz = TZ_ET))
    }))
    st <- st[match(g$game_id, st$game_id), ]
    hp <- st$pred > 0
    done <- g$has_score & g$final_at <= now
    rows <- data.frame(lg = lg, t = g$ko, day = as.Date(g$date),
                       matchup = paste(names_fn(g$away), "@", names_fn(g$home)),
                       pick = names_fn(ifelse(hp, g$home, g$away)), p = st$conf,
                       live = !done & !is.na(g$ko) & g$ko <= now, final_ = done, locked = done,
                       res = ifelse(done, hp == (g$home_score > g$away_score), NA),
                       score = ifelse(done, ifelse(hp, paste0(g$home_score, "\u2013", g$away_score),
                                                    paste0(g$away_score, "\u2013", g$home_score)), ""),
                       home = names_fn(g$home), away = names_fn(g$away), ph = hp,
                       eid = if (espn_ids) as.character(g$game_id) else NA_character_,
                       home2 = if (is.null(abbr_fn)) NA_character_ else abbr_fn(g$home),
                       away2 = if (is.null(abbr_fn)) NA_character_ else abbr_fn(g$away),
                       stringsAsFactors = FALSE)
    list(rows = rows)
  }
  dash_nhl <- reactive({
    req(dash$nhl); dash_n()
    td <- today_local()
    if (!dash_in_season("nhl", td)) return(NULL)
    d <- ndat(); req(d)
    s <- nhl_season_of(td)
    m <- if (!is.null(input$ndate) && identical(nhl_season_of(as.Date(input$ndate)), s)) nmodel() else {
      R <- nhl_rows(d$pan, d$endr, d$ents, s, d$gf); if (is.null(R)) NULL else nhl_fit(R, s) }
    nmv <- function(id) ifelse(is.na(unname(d$nm[id])), id, unname(d$nm[id]))
    espn_ab <- function(a) { al <- c(LAK = "LA", NJD = "NJ", SJS = "SJ", TBL = "TB")
      a <- as.character(a); ifelse(a %in% names(al), unname(al[a]), a) }
    dash_hoops_ice("NHL", d, m, nhl_predict, nmv, abbr_fn = espn_ab)
  })
  dash_nba <- reactive({
    req(dash$nba); dash_n()
    td <- today_local()
    if (!dash_in_season("nba", td)) return(NULL)
    d <- bdat(); req(d)
    s <- d$sch$season[match(TRUE, d$sch$date >= td)]; if (is.na(s)) s <- max(d$sch$season)
    sb <- if (!is.null(input$bdate)) d$sch$season[match(TRUE, d$sch$date >= as.Date(input$bdate))] else NA
    m <- if (identical(sb, s)) bmodel() else { R <- nba_rows(d$pan, d$endr, d$ents, s); if (is.null(R)) NULL else nba_fit(R, s) }
    nmv <- function(id) ifelse(is.na(unname(d$nm[id])), id, unname(d$nm[id]))
    dash_hoops_ice("NBA", d, m, nba_predict, nmv, espn_ids = TRUE)
  })

  # every league's game rows that are ready so far
  dash_rows <- function() {
    parts <- list(); errs <- character()
    add <- function(lab, flag, f) {
      if (!isTRUE(dash[[flag]])) return(invisible())
      x <- dash_try(f)
      if (inherits(x, "dash_err")) errs <<- c(errs, sprintf("%s: %s", lab, x$error))
      else if (!is.null(x) && !is.null(x$rows) && nrow(x$rows)) parts[[lab]] <<- x$rows
    }
    add("MLB", "mlb", dash_mlb); add("NFL", "nfl", dash_nfl); add("NCAAF", "cfb", dash_cfb)
    add("NHL", "nhl", dash_nhl); add("NBA", "nba", dash_nba)
    cols <- c("lg", "t", "day", "matchup", "pick", "p", "live", "final_", "locked", "res", "score",
              "home", "away", "ph", "eid", "home2", "away2", "ml_h0", "ml_a0")
    rows <- if (length(parts)) dplyr::bind_rows(lapply(parts, function(x) x[, intersect(cols, names(x)), drop = FALSE])) else NULL
    list(rows = rows, errs = errs,
         pending = DASH_ORDER[-1][!vapply(DASH_ORDER[-1], function(k) isTRUE(dash[[k]]), logical(1)) &
                                   vapply(c("mlb", "nfl", "cfb", "nhl", "nba"), function(k) dash_in_season(k, today_local()), logical(1))])
  }
  LG_NAME <- c(MLB = "MLB", NFL = "NFL", NCAAF = "NCAAF", NHL = "NHL", NBA = "NBA")

  # -- the book's line for each of today's games still to start -------------------------
  dash_lines <- function(x, lg) {
    n <- nrow(x)
    x$ml_pick <- rep(NA_real_, n); x$ml_opp <- rep(NA_real_, n)
    x$eid_m <- as.character(x$eid); x$side_m <- ifelse(x$ph %in% TRUE, "home", "away")
    x$book_m <- rep(NA_character_, n); x$state_m <- rep(NA_character_, n)
    dates <- unique(format(x$t[!is.na(x$t)], "%Y-%m-%d", tz = TZ_ET))
    ev <- dplyr::bind_rows(lapply(dates, function(d) espn_scoreboard(lg, as.Date(d))))
    if (nrow(ev) && all(c("eid", "ml_h", "ml_a") %in% names(ev))) {
      m <- espn_find(x$home, x$away, x$t, x$eid, ev, x$home2, x$away2)
      for (i in which(!is.na(m$idx))) {
        e <- ev[m$idx[i], , drop = FALSE]
        hs <- xor(x$ph[i] %in% TRUE, m$flip[i])          # is the pick the feed's home side?
        x$ml_pick[i] <- if (hs) e$ml_h else e$ml_a
        x$ml_opp[i]  <- if (hs) e$ml_a else e$ml_h
        x$eid_m[i] <- e$eid; x$side_m[i] <- if (hs) "home" else "away"; x$book_m[i] <- e$book
        x$state_m[i] <- e$state
        if (!is.na(e$start)) x$t[i] <- e$start               # the feed's start time is the exact one
      }
    }
    if (all(c("ml_h0", "ml_a0") %in% names(x))) {         # NFL: nflverse's line when the feed has none
      miss <- is.na(x$ml_pick) | is.na(x$ml_opp)
      x$ml_pick[miss] <- ifelse(x$ph[miss] %in% TRUE, x$ml_h0[miss], x$ml_a0[miss])
      x$ml_opp[miss]  <- ifelse(x$ph[miss] %in% TRUE, x$ml_a0[miss], x$ml_h0[miss])
      x$book_m[miss & !is.na(x$ml_pick)] <- "consensus"
    }
    x
  }
  # prices every game of today that has not started and writes them to the lines ledger
  dash_board <- reactive({
    req(dash$y); dash_n()
    invalidateLater(5 * 60 * 1000)                       # games start, lines move
    R <- dash_rows(); rows <- R$rows
    now <- Sys.time(); td <- today_local(); tz <- view_tz()
    out <- list(R = R, priced = character(0))
    if (is.null(rows) || !nrow(rows)) return(out)
    # a wide net first (our start times can be rough), then the feed's own start and status
    up <- rows[!(rows$final_ %in% TRUE) & !(rows$live %in% TRUE) & !is.na(rows$t) & rows$t > now - 12 * 3600 &
               dash_local_date(rows$t, tz) %in% (td + (-1:1)), , drop = FALSE]
    if (!nrow(up)) return(out)
    up <- dplyr::bind_rows(lapply(split(up, up$lg), function(x)
      tryCatch(dash_lines(x, ESPN_LG[[x$lg[1]]]), error = function(e) x)))
    for (k in c("ml_pick", "ml_opp")) if (!k %in% names(up)) up[[k]] <- NA_real_
    for (k in c("eid_m", "side_m", "book_m", "state_m")) if (!k %in% names(up)) up[[k]] <- NA_character_
    up <- up[ifelse(is.na(up$state_m), up$t > now, up$state_m == "pre" & up$t > now - 600) &
             dash_local_date(up$t, tz) == td, , drop = FALSE]
    if (!nrow(up)) return(out)
    up$dec_p <- am2dec(up$ml_pick); up$dec_o <- am2dec(up$ml_opp)
    ok <- is.finite(up$dec_p) & is.finite(up$dec_o)
    up$vegas <- ifelse(ok, (1 / up$dec_p) / (1 / up$dec_p + 1 / up$dec_o), NA_real_)
    up$ev <- ifelse(ok, up$p * up$dec_p - 1, NA_real_)
    out$priced <- unique(up$lg[ok])
    tryCatch(lines_ledger_sync(lines_rows(up[ok, , drop = FALSE], now), priced = paste(up$lg, up$eid_m)[ok], now = now),
             error = function(e) NULL)
    out
  })
  dash_graded <- reactive({
    req(dash$y); dash_n()
    invalidateLater(15 * 60 * 1000)
    tryCatch(lines_ledger_grade(), error = function(e) NULL)
    TRUE
  })

  output$dash_date <- renderUI({
    td <- today_local()
    div(class = "sub", trimws(format(td, "%A, %B %e")))
  })

  # -- today's value, every league in one list -------------------------------------------
  # Ranked by what the price pays, not by how sure the model is. The two are not the same
  # thing and the difference is large: three points of model edge is worth about +12% at a
  # pick'em, +0.2% on a two-touchdown favourite and less than nothing beyond that, because
  # the price has already taken it. Sorting by confidence therefore puts the least valuable
  # bets at the top, which is what this replaces.
  DASH_VAL_ROWS <- 12L
  output$dash_value <- renderUI({
    req(dash$y)
    td <- today_local(); tz <- view_tz()
    B <- dash_board(); R <- B$R; rows <- R$rows
    dash_graded()
    L <- tryCatch(lines_ledger_load(), error = function(e) NULL)
    rec <- tryCatch(dash_edge_record(L), error = function(e) NULL)

    # the record, in words, computed every time -- see dash_edge_record
    fig <- function(...) sprintf('<span class="vfig">%s</span>', sprintf(...))
    # A proper minus sign, so a negative return does not read as a hyphen beside the dashes
    # around it -- as an HTML entity, which is plain ASCII here and a minus in the browser.
    # The character itself does not survive the trip: the publisher runs in the C locale,
    # where sub() refused the replacement outright and both paste0() and a format string
    # ended up writing the literal text "<e2><88><92>" into the page.
    pct <- function(v) fig(if (v < 0) "&minus;%.1f%%" else "+%.1f%%", abs(v))
    rec_html <- if (is.null(rec) || is.null(rec$all)) "" else {
      a <- rec$all
      verdict <- if (is.na(a$se)) "" else if (a$roi - 1.96 * a$se > 0)
        "That is ahead of the price by more than the noise in it." else if (a$roi + 1.96 * a$se < 0)
        "That is behind the price by more than the noise in it." else
        sprintf("That is indistinguishable from the price either way: showing a 5%%-a-bet edge would take about %s settled bets.",
                format(rec$need, big.mark = ","))
      paste0('<div class="vs-rec"><b>What this has been worth.</b> ',
        sprintf('%s settled picks since %s: %s, %s a bet. ',
                fig("%d", a$n), trimws(format(rec$from, "%e %b")), fig("%d&ndash;%d", a$w, a$l), pct(a$roi)),
        if (is.null(rec$val)) "" else sprintf(
          'The %s that cleared this list&rsquo;s own filter went %s, against the %s the model gave them. ',
          fig("%d", rec$val$n), fig("%d&ndash;%d", rec$val$w, rec$val$l), fig("%.0f%%", rec$val$said)),
        if (is.null(rec$dog)) "" else sprintf(
          'On the %s where the model took the book&rsquo;s underdog, the price said %s and %s came in &mdash; the model said %s. ',
          fig("%d", rec$dog$n), fig("%.0f%%", rec$dog$book), fig("%.0f%%", rec$dog$won), fig("%.0f%%", rec$dog$said)),
        verdict, '</div>')
    }
    shell <- function(inner, n_txt = "")
      HTML(sprintf(paste0('<div class="vsum"><div class="vs-h"><span class="vs-t1">Today&rsquo;s value</span>',
                          '<span class="vs-n">%s</span></div>%s%s</div>'),
                   n_txt, inner, rec_html))

    v <- if (!is.null(L) && nrow(L)) L[!is.na(L$StartT) & dash_local_date(L$StartT, tz) == td &
                                       is.finite(L$EV) & is.finite(L$VegasP), , drop = FALSE] else NULL
    if (is.null(v) || !nrow(v))
      return(shell(sprintf('<div class="vs-none">%s</div>',
        if (length(R$pending)) "Reading today&rsquo;s lines&hellip;" else
          "No prices read today yet &mdash; the book posts them closer to the games.")))

    v$edge <- v$ModelP - v$VegasP
    npriced <- nrow(v)
    pos <- v[dash_is_value(v$ModelP, v$VegasP, v$EV), , drop = FALSE]
    if (!nrow(pos))
      return(shell(sprintf('<div class="vs-none">Nothing to take today &mdash; %s.</div>',
                           dash_why_none(npriced)),
                   sprintf("%d game%s priced", npriced, if (npriced == 1) "" else "s")))

    # a game already under way is still shown, with its result, but it sinks below the
    # ones that can still be acted on
    started <- !is.na(pos$StartT) & pos$StartT <= Sys.time()
    pos <- pos[order(started, -pos$EV), , drop = FALSE]
    shown <- utils::head(pos, DASH_VAL_ROWS)

    stat <- function(lg, m, tt) {
      k <- if (is.null(rows) || !nrow(rows)) NA_integer_ else match(paste(lg, m), paste(rows$lg, rows$matchup))
      if (is.na(k)) return(sprintf('<span class="when">%s</span>', dash_esc(dash_when(tt, tz, td))))
      r <- rows[k, ]
      if (!is.na(r$res)) sprintf('<span class="rs %s">%s %s</span>', if (r$res) "ok" else "no",
                                 if (r$res) "&#10003;" else "&#10007;", dash_esc(r$score))
      else if (isTRUE(r$live)) sprintf('<span class="rs live">Live %s</span>', dash_esc(r$score))
      else if (isTRUE(r$final_)) '<span class="nt">Final</span>'
      else sprintf('<span class="when">%s</span>', dash_esc(dash_when(if (is.na(tt)) r$t else tt, tz, td)))
    }
    pick_cell <- function(lg, m, pk, dog) {
      q <- strsplit(as.character(m), " @ ", fixed = TRUE)[[1]]
      home <- length(q) == 2L && identical(q[2], as.character(pk))
      opp <- if (length(q) < 2L) "" else if (home) q[1] else q[2]
      sprintf('<span class="bet">%s</span><span class="vs">%s %s</span>%s',
              dash_esc(dash_short(lg, pk)), if (home) "vs" else "@", dash_esc(dash_short(lg, opp)),
              if (isTRUE(dog)) ' <span class="dog">Upset</span>' else "")
    }
    tr <- vapply(seq_len(nrow(shown)), function(i) sprintf(paste0(
      '<tr><td class="st hide-sm">%s</td><td class="lgc">%s</td><td>%s</td><td class="num">%d%%</td>',
      '<td class="num dim">%d%%</td><td class="num"><span class="odds">%s</span></td>',
      '<td class="num"><span class="ev%s">%s</span></td></tr>'),
      stat(shown$League[i], shown$Matchup[i], shown$StartT[i]), dash_chip(shown$League[i]),
      pick_cell(shown$League[i], shown$Matchup[i], shown$Pick[i], shown$VegasP[i] < 0.5),
      round(100 * shown$ModelP[i]), round(100 * shown$VegasP[i]),
      fmt_dec(as.numeric(shown$Odds[i])),
      if (shown$EV[i] >= 0.15) " hi" else "", dash_ev(shown$EV[i])), "")
    ndog <- sum(pos$VegasP < 0.5)
    shell(paste0(
      sprintf(paste0('<table class="sp-t"><thead><tr><th class="hide-sm"></th><th></th><th>Pick</th>',
                     '<th class="num">Model</th><th class="num">Vegas</th><th class="num">Price</th>',
                     '<th class="num">Value</th></tr></thead><tbody>%s</tbody></table>'),
              paste(tr, collapse = "")),
      if (nrow(pos) > nrow(shown)) sprintf('<div class="vs-more">and %d more paying above the model&rsquo;s chance.</div>',
                                           nrow(pos) - nrow(shown)) else ""),
      sprintf("%d value pick%s from %d priced game%s%s",
              nrow(pos), if (nrow(pos) == 1) "" else "s", npriced, if (npriced == 1) "" else "s",
              if (ndog) sprintf(" &middot; %d projected upset%s", ndog, if (ndog == 1) "" else "s") else ""))
  })

  # -- one card per league ---------------------------------------------------------------
  output$dash_sports <- renderUI({
    req(dash$y)
    td <- today_local(); yd <- td - 1; tz <- view_tz()
    B <- dash_board(); R <- B$R; rows <- R$rows
    dash_graded()
    L <- tryCatch(lines_ledger_load(), error = function(e) NULL)
    my <- dash_try(dash_mlb_y)
    cards <- character()
    for (lg in names(LG_NAME)) {
      key <- ESPN_LG[[lg]]
      if (!isTRUE(dash[[key]])) next
      lr <- if (!is.null(rows)) rows[rows$lg == lg, , drop = FALSE] else NULL
      yg <- if (lg == "MLB") { if (dash_ok(my)) my else NULL } else
        if (!is.null(lr)) lr[!is.na(lr$t) & dash_local_date(lr$t, tz) == yd, , drop = FALSE] else NULL
      tg <- if (!is.null(lr) && nrow(lr)) lr[!is.na(lr$t) & dash_local_date(lr$t, tz) == td, , drop = FALSE] else NULL
      ny <- if (is.null(yg)) 0L else nrow(yg); nt <- if (is.null(tg)) 0L else nrow(tg)
      if (!ny && !nt) next
      yr <- dash_record(if (ny) yg$res else logical(0))
      ytxt <- if (!ny) '<span class="dim">No games yesterday</span>' else if (!yr$n) '<span class="dim">Yesterday pending</span>' else
        sprintf('Yesterday <b class="%s">%s</b>', if (yr$pct >= 55) "good" else if (yr$pct < 45) "bad" else "", yr$txt)
      head_ <- sprintf(paste0('<div class="sp-h">%s<span class="sp-n">%s</span><span class="sp-y">%s</span>',
                              '<a class="sp-go" href="#" onclick="$(\'a[data-value=%s]\').click();return false;">All games &rsaquo;</a></div>'),
                       dash_chip(lg), if (nt) sprintf("%d game%s today", nt, if (nt == 1) "" else "s") else "No games today",
                       ytxt, key)
      body <- ""
      if (nt) {
        # today's value: the lines ledger has every priced game, its price frozen at the start
        lt <- if (!is.null(L) && nrow(L)) L[L$League == lg & !is.na(L$StartT) & dash_local_date(L$StartT, tz) == td, , drop = FALSE] else NULL
        status <- function(m, t) {
          k <- match(m, tg$matchup)
          if (is.na(k)) return(sprintf('<span class="when">%s</span>', dash_esc(dash_when(t, tz, td))))
          r <- tg[k, ]
          if (!is.na(r$res)) sprintf('<span class="rs %s">%s %s</span>', if (r$res) "ok" else "no",
                                     if (r$res) "&#10003;" else "&#10007;", dash_esc(r$score))
          else if (isTRUE(r$live)) sprintf('<span class="rs live">Live %s</span>', dash_esc(r$score))
          else if (isTRUE(r$final_)) '<span class="nt">Final</span>'
          else sprintf('<span class="when">%s</span>', dash_esc(dash_when(if (is.na(t)) r$t else t, tz, td)))
        }
        # the pick and its opponent; on a phone the status rides under the pick
        team_cell <- function(m, pick, st) {
          p <- strsplit(as.character(m), " @ ", fixed = TRUE)[[1]]
          home <- length(p) == 2L && identical(p[2], as.character(pick))
          opp <- if (length(p) < 2L) "" else if (home) p[1] else p[2]
          sprintf('<span class="bet">%s</span><span class="vs">%s %s<span class="sm-only"> &middot; %s</span></span>',
                  dash_esc(dash_short(lg, pick)), if (home) "vs" else "@", dash_esc(dash_short(lg, opp)), st)
        }
        if (!is.null(lt) && nrow(lt)) {
          lt$edge <- lt$ModelP - lt$VegasP
          v <- lt[dash_is_value(lt$ModelP, lt$VegasP, lt$EV), , drop = FALSE]
          v <- head(v[order(-v$EV), , drop = FALSE], DASH_TOP_N)
          if (nrow(v)) {
            v <- v[order(v$StartT), , drop = FALSE]
            tr <- vapply(seq_len(nrow(v)), function(i) { st <- status(v$Matchup[i], v$StartT[i]); sprintf(paste0(
              '<tr><td class="st hide-sm">%s</td><td>%s</td><td class="num">%d%%</td>',
              '<td class="num hide-sm dim">%d%%</td><td class="num"><span class="odds">%s</span></td>',
              '<td class="num"><span class="ev%s">%s</span></td></tr>'),
              st, team_cell(v$Matchup[i], v$Pick[i], st),
              round(100 * v$ModelP[i]), round(100 * v$VegasP[i]), fmt_dec(as.numeric(v$Odds[i])),
              if (v$EV[i] >= 0.15) " hi" else "", dash_ev(v$EV[i])) }, "")
            body <- sprintf(paste0('<table class="sp-t"><thead><tr><th class="hide-sm"></th><th>Best value</th><th class="num">Model</th>',
                                   '<th class="num hide-sm">Vegas</th><th class="num">Odds</th><th class="num">Edge</th></tr></thead>',
                                   '<tbody>%s</tbody></table>'), paste(tr, collapse = ""))
          } else body <- sprintf('<div class="sp-none">No value in today\'s lines &mdash; %s.</div>',
                                 dash_why_none(nrow(lt)))
        } else {
          ahead <- !(tg$live %in% TRUE) & !(tg$final_ %in% TRUE) & !is.na(tg$t) & tg$t > Sys.time()
          why <- if (any(ahead)) "No lines posted yet" else "Today's games started before their lines were read"
          if (lg != "NCAAF") {
            # no price: the strongest picks instead (college favourites at 60 points say little)
            s <- head(tg[order(-tg$p), , drop = FALSE], DASH_TOP_N)
            tr <- vapply(seq_len(nrow(s)), function(i) { st <- status(s$matchup[i], s$t[i]); sprintf(paste0(
              '<tr><td class="st hide-sm">%s</td><td>%s</td><td class="num">%d%%</td><td class="num hide-sm dim">&mdash;</td>',
              '<td class="num dim">&mdash;</td><td class="num dim">&mdash;</td></tr>'),
              st, team_cell(s$matchup[i], s$pick[i], st), round(100 * s$p[i])) }, "")
            body <- sprintf(paste0('<div class="sp-sub">%s \u2014 the strongest picks:</div>',
                                   '<table class="sp-t"><tbody>%s</tbody></table>'), why, paste(tr, collapse = ""))
          } else body <- sprintf('<div class="sp-none">%s.</div>', why)
        }
      }
      cards <- c(cards, sprintf('<div class="sp">%s%s</div>', head_, body))
    }
    tagList(
      if (length(cards)) HTML(sprintf('<div class="sp-grid">%s</div>', paste(cards, collapse = ""))) else
        div(class = "dash-wait", if (length(R$pending)) "Loading today's games\u2026" else "No games today or yesterday."),
      if (length(R$pending) && length(cards)) div(class = "dash-wait", sprintf("Still loading: %s",
        paste(c(mlb = "MLB", nfl = "NFL", cfb = "NCAAF", nhl = "NHL", nba = "NBA")[R$pending], collapse = ", "))),
      if (length(R$errs)) div(class = "err", paste(R$errs, collapse = " \u00b7 ")),
      if (length(cards)) div(class = "dash-cav", HTML(paste0(
        "<b>Value</b> = the model's pick at a price that pays more than its chance is worth: model chance ",
        "&times; decimal odds &minus; 1, so a positive figure already clears the book's margin. <b>Vegas</b> is the ",
        "line's own chance with that margin taken out, shown beside the model's so the size of the ",
        "disagreement is on every row. DraftKings lines via ESPN; a price is kept as it stood at the start. ",
        "What picks like these have actually returned is measured at the top of this page, from the settled ones.")))
    )
  })

  # ---- a game's most likely touchdown scorers, opened under its row on a board ----------
  # One renderer for every sport's dropdown. The wording is a parameter rather than
  # four near-copies of the same table: football scores touchdowns, hockey goals,
  # basketball a first basket and baseball home runs, and nothing else differs.
  tdx_html <- function(name_html, sub, p, scored, note,
                      title = "Most likely touchdown scorers", miss = "No TD") {
    if (!length(p)) return('<div class="tdx"><div class="tdx-none">No player projections for this game.</div></div>')
    res <- ifelse(is.na(scored), "", ifelse(scored > 0, '<span class="rs ok">Scored</span>',
                                            sprintf('<span class="rs no">%s</span>', miss)))
    tr <- sprintf(paste0('<tr><td class="pl">%s<span class="ps">%s</span></td><td class="num">%d%%</td>',
                         '<td class="num"><b>%s</b></td><td class="rz">%s</td></tr>'),
                  name_html, sub, round(100 * p), fmt_dec(fair_dec(p)), res)
    sprintf(paste0('<div class="tdx"><div class="tdx-h">%s<span>%s</span></div>',
                   '<table class="tdx-t"><thead><tr><th>Player</th><th class="num">Chance</th>',
                   '<th class="num">Fair odds</th><th></th></tr></thead><tbody>%s</tbody></table></div>'),
            title, note, paste(tr, collapse = ""))
  }
  tdx_none <- function(msg) sprintf('<div class="tdx"><div class="tdx-none">%s</div></div>', htmltools::htmlEscape(msg))
  TDX_NOTE <- " \u00b7 chance he scores, if he plays \u00b7 fair odds = 1 \u00f7 chance: bet only above them"
  TDX_FB_NOTE <- " \u00b7 chance he scores the game's first basket \u00b7 fair odds = 1 \u00f7 chance"
  TDX_HR_NOTE <- " \u00b7 chance he hits one, if he plays \u00b7 fair odds = 1 \u00f7 chance"

  # Keeps the data caches warm in the background (no sidebar display). Not on a host:
  # each warm-up step blocks the one R process every visitor shares for minutes at a
  # time; there each league loads when it is first opened instead.
  if (!dash_hosted()) warm_start()
}

warm_banner()

shinyApp(ui, server)
