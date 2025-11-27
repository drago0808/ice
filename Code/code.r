# Statistical Trend Analysis of Great Lakes Ice Cover Changes (1973 to 2025)
# Rongrong Qian & Carter Vonderahe
# November 21, 2025



# load libraries
library(tidyverse)
library(readr)
library(dplyr)
library(tidyr)
library(lubridate)
library(stringr)
library(knitr)
library(kableExtra)
library(ggplot2)
library(forecast)


## ----data_cleaning-------------------------------------------------------------------------------------
# read and clean column names
raw0 <- read_csv("greatlakesicedata.csv", show_col_types = FALSE)
nm   <- names(raw0)
nm[1] <- "day_mon"
year_cols <- str_extract(nm[-1], "\\b\\d{4}\\b")
keep     <- c(TRUE, !is.na(year_cols))
raw      <- raw0[, keep, drop = FALSE]
names(raw) <- c("day_mon", year_cols[!is.na(year_cols)])
# create day_mon factor levels
day_levels <- format(
  seq(from = as.Date("2020-11-10"),
      to   = as.Date("2021-06-05"),
      by   = "day"),
  "%e-%b"
) %>%  stringr::str_trim()

# pivot longer format
ice_clean <- raw %>%
  mutate(
    row_id  = row_number(),
    day_mon = str_trim(day_mon),
    # unify possible "Feb-29" to "29-Feb"
    day_mon = if_else(day_mon == "Feb-29", "29-Feb", day_mon)
  ) %>%
  pivot_longer(-c(day_mon, row_id),
               names_to  = "year",
               values_to = "ice") %>%
  mutate(
    year  = as.integer(year),
    ice   = suppressWarnings(as.numeric(ice)),
    date  = as.Date(paste0(day_mon, "-", year), format = "%d-%b-%Y"),
    month = factor(
      lubridate::month(date),
      levels = c(11, 12, 1, 2, 3, 4, 5, 6),
      labels = month.abb[c(11, 12, 1, 2, 3, 4, 5, 6)]
    ),
    day      = day(date),
    day_mon  = factor(day_mon, levels = day_levels, ordered = TRUE)
  ) %>%
  arrange(year, row_id) %>%
  select(date, year, month, day, day_mon, row_id, ice)


## ----imputation_code-----------------------------------------------------------------------------------
# Imputation 
# threshold for "close to zero" (%)
tau0 <- 5

feb28_idx <- 111L
feb29_idx <- 112L


impute_year <- function(x, y, tau0 = 5, feb29_idx = NA_integer_,
                        win_lead = 20, win_trail = 20) {
  # x: row_id (1..n) for one year
  # y: daily ice % (may contain NA) for the same year
  n  <- length(y)
  y2 <- y
  # keep values in [0, 100]
  clamp <- function(v) pmax(0, pmin(100, v))

  # Fill Feb 29 if NA and has neighbors
  if (!is.na(feb29_idx) && feb29_idx >= 2L && feb29_idx <= n - 1L &&
      is.na(y2[feb29_idx])) {
    a <- y2[feb29_idx - 1L]
    b <- y2[feb29_idx + 1L]
    y2[feb29_idx] <-
      if (is.finite(a) && is.finite(b)) (a + b) / 2 else
      if (is.finite(a)) a else
      if (is.finite(b)) b else NA_real_
  }
  # indices of non-missing observations
  obs <- which(!is.na(y2))
  if (!length(obs)) return(y2) 

  # leading gap (before first observed)
  k1 <- obs[1L] # first observed index
  if (k1 > 1L) {
    s <- 1L # start index of leading gap
    e <- k1 - 1L # end index of leading gap

   # observed indices AFTER the gap
    obs_after <- obs[obs >= k1]
    # use only the first 'win_lead' observed days to fit the line
    use_idx <- obs_after[seq_len(min(length(obs_after), win_lead))]

    if (length(use_idx) >= 2L) {
      fit <- lm(y ~ x, data = data.frame(
        y = y2[use_idx],
        x = x[use_idx]
      ))
      preds <- as.numeric(predict(fit, newdata = data.frame(x = x[s:e])))
      # enforce physical bounds: 0 <= preds <= first observed value
      upper <- y2[k1]
      preds <- clamp(preds)
      preds[preds > upper] <- upper
      preds[preds < 0]     <- 0
      y2[s:e] <- preds
    } else {
      # fallback: simple linear ramp 0 -> first observed
      y2[s:e] <- clamp(seq(0, y2[k1], length.out = e - s + 1L))
    }
  }

  # trailing gap
  k2 <- obs[length(obs)]
  if (k2 < n) {
    s <- k2 + 1L
    e <- n

    # observed indices BEFORE the gap
    obs_before <- obs[obs <= k2]
    # use only the last 'win_trail' observed days to fit the line
    use_idx <- tail(obs_before, n = min(length(obs_before), win_trail))

    if (length(use_idx) >= 2L) {
      fit <- lm(y ~ x, data = data.frame(
        y = y2[use_idx],
        x = x[use_idx]
      ))
      preds <- as.numeric(predict(fit, newdata = data.frame(x = x[s:e])))
      
      # enforce physical bounds: 0 <= preds <= last observed value
      upper <- y2[k2]
      preds <- clamp(preds)
      preds[preds > upper] <- upper
      preds[preds < 0]     <- 0

      y2[s:e] <- preds
    } else {
      # fallback: simple ramp last observed -> 0
      y2[s:e] <- clamp(seq(y2[k2], 0, length.out = e - s + 1L))
    }
  }

  y2
}

# years before 1993: run imputation
imputed_pre1993 <- ice_clean %>%
  filter(year < 1993) %>%
  group_by(year) %>%
  arrange(row_id, .by_group = TRUE) %>%
  mutate(
    ice_imp = impute_year(
      x         = row_id,
      y         = ice,
      tau0      = tau0,
      feb29_idx = feb29_idx
    )
  ) %>%
  ungroup() %>% 
  filter(row_id != feb29_idx)  # remove Feb-29 row

# years 1993 and later: keep original values but
# combine Feb 28 & Feb 29 by mean into Feb 28
post1993 <- ice_clean %>%
  filter(year >= 1993) %>%
  mutate(ice_imp = ice) %>%
  group_by(year) %>%
  mutate(
    # mean of Feb-28 and Feb-29 in this year
    feb_mean = mean(
      ice_imp[row_id %in% c(feb28_idx, feb29_idx)],
      na.rm = TRUE)
    ) %>%
  ungroup() %>%
  mutate(
    # 1) overwrite Feb-28 (row 111) with that mean
    ice_imp = if_else(row_id == feb28_idx, feb_mean, ice_imp),
    # 2) set all remaining NA to 0
    ice_imp = if_else(is.na(ice_imp), 0, ice_imp)
  ) %>%
  # 3) drop Feb-29 row (row 112)
  filter(row_id != feb29_idx) %>%
  select(-feb_mean)

# combine and keep row_id ordering
imputed <- bind_rows(imputed_pre1993, post1993) %>%
  arrange(year, row_id)


## ----auc_calculation, echo=FALSE-----------------------------------------------------------------------
# calculate AUC per year
auc_data <- imputed %>%
  group_by(year) %>%
  summarize(
    AUC = sum(ice_imp, na.rm = TRUE),
    .groups = "drop"
  )


## ----na_analysis, echo=FALSE, fig.height=4-------------------------------------------------------------
# check NAs
na_summary <- ice_clean %>%
  group_by(year) %>%
  summarize(
    total_days = n(),
    NA_count = sum(is.na(ice)),
    NA_percentage = (NA_count / total_days) * 100
  )

# show NA trend over years
ggplot(na_summary, aes(x = as.integer(year), y = NA_percentage)) +
  geom_line(color = "steelblue") +
  geom_point() +
  labs(x = "", y = "% of NA",
       title = "Figure 1",
       subtitle = "Trend of NA Over Years") +
  theme_minimal() +
  theme(
    plot.title = element_text(face = "bold")
  )


## ----imputed_viz, echo=FALSE---------------------------------------------------------------------------
# Start / End / Peak 
# season is the start, end and peak rows
season <- ice_clean %>% 
  group_by(year) %>% 
  summarise(
    start_row = { idx <- which(!is.na(ice)); if (length(idx)) min(idx) else NA_integer_ }, 
    end_row   = { idx <- which(!is.na(ice)); if (length(idx)) max(idx) else NA_integer_ },
    peak_row  = {
      if (all(is.na(ice))) NA_integer_
      else { v <- ifelse(is.na(ice), -Inf, ice); which.max(v) }
    },
    .groups = "drop"
  ) %>% 
  tidyr::drop_na(start_row, end_row)  

season_start <- as.Date("1973-11-10")
season_end   <- as.Date("1974-06-05")

# prepare data for plotting imputed vs original 
imputed_plot <- imputed %>%
  left_join(season, by = "year") %>%
  mutate(
    season_date = season_start + (row_id - 1),
    ice_obs     = if_else(row_id < start_row | row_id > end_row,
                          NA_real_, ice)
  )

selected_years <- c(1973, 1976, 1977, 1980, 1981, 1984)

ggplot(filter(imputed_plot, year %in% selected_years),
       aes(x = season_date)) +
  # grey imputed line on bottom
  geom_line(aes(y = ice_imp, color = "Imputed"),
            linewidth = 0.8, na.rm = TRUE) +
  # blue original line on top, only where observed
  geom_line(aes(y = ice_obs, color = "Original"),
            linewidth = 0.9, na.rm = TRUE) +
  facet_wrap(~ year, ncol = 2) +
  scale_color_manual(
    values = c("Imputed" = "grey70", "Original" = "steelblue"),
    name   = "Data Type"
  ) +
  scale_x_date(
    limits      = c(season_start, season_end),
    date_breaks = "1 month",
    date_labels = "%b"
  ) +
  labs(
    x     = "Date in Season (Nov 10 – Jun 5)",
    y     = "Ice Cover (%)",
    title = "Figure 2",
    subtitle = "Original vs Imputed Ice Cover Data for Selected Years"
  ) +
  theme_minimal(base_size = 12) +
  theme(
    plot.title = element_text(face = "bold")
  )
 


## ----start_peak_end, fig.height=4----------------------------------------------------------------------
# map row -> date
base_start <- as.Date("1973-11-10")
base_end   <- base_start + (nrow(raw) - 1)

season <- season %>%
  mutate(
    start_date = base_start + (start_row - 1),
    end_date   = base_start + (end_row   - 1),
    peak_date  = base_start + (peak_row  - 1)
  )

# prepare observed season data
imputed_startend <- imputed %>%
  mutate(
    is_ice = !is.na(ice_imp) & ice_imp > 0  # TRUE = has ice, FALSE = no ice (0 or NA)
  )
# Build Start / End / Peak (by row), then map row -> date on y using the imputed data
season_imp <- imputed_startend %>%
  group_by(year) %>%
  summarise(
    # start: first day where is_ice goes from FALSE (0) to TRUE (>0)
    start_row_im = {
      idx <- which(is_ice & !dplyr::lag(is_ice, default = FALSE))
      if (length(idx)) min(idx) else NA_integer_
    },
    # end: last day where is_ice goes from TRUE (>0) to FALSE (0)
    end_row_im = {
      idx <- which(is_ice & !dplyr::lead(is_ice, default = FALSE))
      if (length(idx)) max(idx) else NA_integer_
    },
    # peak: max ice within the ice season (only among is_ice == TRUE)
    peak_row_im = {
      if (!any(is_ice)) {
        NA_integer_
      } else {
        v <- ifelse(is_ice, ice_imp, -Inf)
        which.max(v)
      }
    },
    .groups = "drop"
  ) %>%
  tidyr::drop_na(start_row_im, end_row_im) %>%
  arrange(year)

# map row -> date
base_start_im <- as.Date("1973-11-10")
base_end_im   <- base_start_im + (nrow(raw) - 1)

# map observed season rows to dates
season_imp <- season_imp %>%
  mutate(
    start_date_im = base_start + (start_row_im - 1),
    end_date_im   = base_start + (end_row_im   - 1),
    peak_date_im  = base_start + (peak_row_im  - 1)
  )

# range for x-axis
min_year <- min(c(season$year, season_imp$year))
max_year <- max(c(season$year, season_imp$year))

ggplot() +
  # Bottom layer: imputed season band
  geom_ribbon(
    data = season_imp,
    aes(x = year, ymin = start_date_im, ymax = end_date_im),
    fill = "grey50", alpha=0.8, color = NA, na.rm = TRUE
  ) +
  # Top layer: observed season band
  geom_ribbon(
    data = season,
    aes(x = year, ymin = start_date, ymax = end_date),
    fill = "grey85", color = NA, na.rm = TRUE
  ) +
  # Observed peak line and points (on top)
  geom_line(
    data = season,
    aes(x = year, y = peak_date, group = 1),
    color = "steelblue", linewidth = 1
  ) +
  geom_point(
    data = season,
    aes(x = year, y = peak_date),
    color = "steelblue", size = 1.8
  ) +
  scale_x_continuous(
    breaks       = seq(min_year, max_year, by = 5),
    minor_breaks = seq(min_year, max_year, by = 5)
  ) +
  # Reverse y-axis so Nov-10 is at the top and Jun-05 at the bottom
  scale_y_date(
    limits      = c(base_end, base_start),   # reversed
    breaks      = seq(base_start, base_end, by = "1 month"),
    date_labels = "%d-%b",
    expand      = expansion(mult = c(0.01, 0.01))
  ) +
  labs(
    x = "",
    y = "Date (Nov-10 → Jun-05)",
    title    = "Figure 3",
    subtitle = "Duration of Ice Coverage over Time",
    caption = "Light grey = Observed Start–End; Dark grey = Imputed Start–End; Blue = Observed Peak"
  ) +
  theme_minimal(base_size = 12) +
  theme(
    plot.title = element_text(face = "bold")
  )


## ----heatmap_plot, fig.height=5------------------------------------------------------------------------
### HEAT MAP ###
ggplot() +
  geom_raster(aes(x = year, y = day_mon, fill = ice_imp), data = imputed) +
  # scale_fill_gradient(low = "white",
  #                     high = "navy",
  #                     guide = guide_colorbar(ticks = TRUE, label = TRUE,
  #                                            barheight = .5, barwidth = 8)) +
  scale_fill_viridis_c(option = "mako", direction = -1,
                       guide = guide_colorbar(ticks = TRUE, label = TRUE,
                                              barheight = .5, barwidth = 8)) +
  theme_minimal() +
  scale_x_continuous(expand = c(0, 0)) +
  scale_y_discrete(breaks = c("1-Dec", "1-Jan", "1-Feb", "1-Mar", "1-Apr", "1-May", "1-Jun"),
                   labels = c("Dec", "Jan", "Feb", "Mar", "Apr", "May", "Jun"),
                   limits = levels(imputed$day_mon)) +
  labs(title = "Figure 4",
       subtitle = "Intensity of Ice Coverage over Time",
       fill = "% Coverage",
       y = NULL,
       x = NULL) +
  theme(
    # text settings
    axis.text = element_text(size = 8),
   
    # legend settings
    legend.position = c(0.5, -0.15),
    legend.direction = "horizontal",
    legend.title = element_text(vjust = 1),
   
    # plot settings
    plot.margin = grid::unit(c(.5, .5, 1.5, .5), "cm"),
    plot.title = element_text(face = "bold")
  )


## ----auc_trend_plot, echo=FALSE------------------------------------------------------------------------
# calculate Theil-Sen slope
theil_sen_slope <- function(x, y) {
  n <- length(x)
  slopes <- c()
  for (i in 1:(n - 1)) {
    for (j in (i + 1):n) {
      if (x[j] != x[i]) {
        slopes <- c(slopes, (y[j] - y[i]) / (x[j] - x[i]))
      }
    }
  }
  median(slopes, na.rm = TRUE)
}

# calculate slope
slope_est <- theil_sen_slope(auc_data$year, auc_data$AUC)
intercept_est <- median(auc_data$AUC) - slope_est * median(auc_data$year)


## ----auc_trend_plot_gg, fig.height=4-------------------------------------------------------------------
# plot AUC time series with trend line
ggplot(auc_data, aes(x = year, y = AUC)) +
  geom_point(color = "steelblue", size = 2) +
  geom_line(color = "steelblue", linewidth = 0.8) +
  geom_abline(slope = slope_est, intercept = intercept_est,
              color = "darkred", linetype = "dashed", linewidth = 1) +
  labs(x = NULL,
       y = "Annual Ice Cover AUC",
       title = "Figure 5",
       subtitle = "Time Series of Annual Ice Cover AUC",
       caption = "Blue = Recorded AUC; Red = Theil-Sen Slope Estimate") +
  theme_minimal(base_size = 12) +
  theme(
    plot.title = element_text(face = "bold")
  )


## ----permutation_test, cache=TRUE----------------------------------------------------------------------
# number of random permutations to generate
n_perm <- 10000

# initialize vectors
TSs <- numeric(n_perm) # theil-sen slopes (these are slopes generated UNDER THE NULL)


### PERMUTATION TEST ###
set.seed(12345) # set seed for reproducibility
for (i in 1:n_perm) {
  
  # randomly permute AUC
  auc_data$AUC_rand <- sample(auc_data$AUC)
  
  # compute TS slope ON AUC_rand
  TSs[i] <- theil_sen_slope(auc_data$year, auc_data$AUC_rand)
}

# compute p-value
p_value <- mean(abs(TSs) > abs(slope_est))


## ----confidence_interval, eval=FALSE-------------------------------------------------------------------
# # CI using quantiles of null distribution
# slope_est - quantile(TSs, probs = c(0.975, 0.025))


## ----fig.height=3--------------------------------------------------------------------------------------
ggplot(data.frame(TSs)) +
  geom_histogram(aes(x=TSs),
                 fill = "skyblue",
                 color = "grey50") +
  geom_vline(xintercept = slope_est, color = "darkred") +
  geom_vline(xintercept = abs(slope_est), color = "darkred") +
  annotate(geom = "text", label = "-|Observed Slope|", x = -abs(slope_est), y = 950,
           hjust = -0.05, color = "darkred", fontface = "bold") +
  annotate(geom = "text", label = "|Observed Slope|", x = abs(slope_est), y = 950,
           hjust = 1.05, color = "darkred", fontface = "bold") +
  scale_y_continuous(expand = c(0, 0)) +
  labs(y = NULL,
       x = NULL,
       title = "Figure 6",
       subtitle = "Null Distribution of Permuted Theil-Sen Slopes") +
  theme_classic() +
  theme(
    axis.line.y = element_blank(),
    axis.text.y = element_blank(),
    axis.ticks.y = element_blank(),
    
    plot.title = element_text(face = "bold")
  )


## ----na_validation-------------------------------------------------------------------------------------
dat <- raw %>%
  mutate(row_id = row_number()) %>%
  pivot_longer(-c(day_mon, row_id), names_to = "year", values_to = "ice") %>%
  mutate(year = as.integer(year),
         ice  = suppressWarnings(as.numeric(ice))) %>%
  arrange(year, row_id)
# helper function to find mid-year NA runs
find_mid_na <- function(x, rows){
  w <- which(!is.na(x))
  if (length(w) == 0) return(tibble(start_row = integer(), end_row = integer()))
  first <- w[1]; last <- w[length(w)]
  z <- is.na(x[first:last]); if (!any(z)) return(tibble(start_row = integer(), end_row = integer()))
  r <- rle(z); ends <- cumsum(r$lengths); starts <- ends - r$lengths + 1
  idx <- which(r$values)
  tibble(start_row = rows[first:last][starts[idx]],
         end_row   = rows[first:last][ends[idx]])
}

# check the first non-NA row per year
starts <- dat %>%
  group_by(year) %>%
  summarise(first_data_row = min(row_id[!is.na(ice)], default = NA_integer_), .groups = "drop") %>%
  left_join(
    dat %>% filter(!is.na(ice)) %>%
      group_by(year) %>% slice_min(order_by = row_id, n = 1, with_ties = FALSE) %>%
      dplyr::select(year, first_day = day_mon),
    by = "year"
  ) %>%
  arrange(year)

# mid-year NA runs, which means how many runs of NAs between first and last non-NA
mid_runs <- dat %>%
  group_by(year) %>%
  reframe(find_mid_na(ice, row_id)) %>%                 
  left_join(dat %>% dplyr::select(year, row_id, day_mon),
            by = c("year","start_row" = "row_id")) %>%
  rename(start_day = day_mon) %>%
  left_join(dat %>% dplyr::select(year, row_id, day_mon),
            by = c("year","end_row" = "row_id")) %>%
  rename(end_day = day_mon) %>%
  mutate(n_days = end_row - start_row + 1) %>%
  arrange(year, start_row)

# summary of mid-year NAs
mid_summary <- mid_runs %>%
  group_by(year) %>%
  summarise(has_mid_NA = n() > 0,
            mid_NA_runs = n(),
            mid_NA_days = sum(n_days),
            .groups = "drop") %>%
  right_join(starts, by = "year") %>%
  arrange(year) %>%
  mutate(across(c(has_mid_NA, mid_NA_runs, mid_NA_days),
                ~ tidyr::replace_na(., 0)))

# show mid-year NA summary table using kable
mid_runs %>%
  kable("html", caption = "Appendix A: Mid-year NA Summary",
        col.names = c("Year", "Start Row", "End Row", "Start Day", "End Day", "Number of NAs")) %>%
  kable_styling(full_width = FALSE, position = "left", font_size = 12)


## ----acf_plot, fig.height=4----------------------------------------------------------------------------
# plot ACF of AUC time series
ggAcf(auc_data$AUC, lag.max = 20) +
  labs(title = "Appendix B",
       subtitle = "Autocorrelation Function (ACF) of Annual Ice Cover AUC Time Series") +
  theme_minimal(base_size = 12) +
  theme(
    plot.title = element_text(face = "bold")
  )


## ------------------------------------------------------------------------------------------------------
# knitr::purl(input = "Carter_Rongrong_FINAL_ANALYSIS.Rmd", output = "Ice_Cover.R")

