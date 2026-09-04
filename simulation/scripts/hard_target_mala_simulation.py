#!/usr/bin/env python3
"""Compare fixed-step and uniformly randomized MALA on Proposition A.1's target.

The target is

    U(x) = m x_1^2 / 2
           + sum_{i=2}^d [(L+m) x_i^2 / 4
                          - (L-m) h0 cos(x_i / sqrt(h0)) / 2].

Here h0 is the oscillation scale built into the target.  It is kept distinct
from the algorithmic MALA step h.  Two experiments are performed:

1. Acceptance at the origin as d grows, with h0 = 4/(L sqrt(d)), followed by
   a 40,000-iteration first-coordinate trace at d=200 from the origin.
2. Stationary acceptance and ESJD on a fixed d=200 target as H/h0 varies
   from 0.05 to 100;
   fixed-step MALA uses h=H and randomized MALA draws h~Unif(0,H).

All reported one-step quantities are Rao--Blackwellized over the accept/reject
uniform variable: the code averages alpha(x,y), and alpha(x,y)||y-x||^2/d.
"""

import argparse
import csv
from pathlib import Path

import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np


M = 0.1
L = 1.0
HARD_SCALE_CONSTANT = 4.0
SEED = 20260825

ORIGIN_DIMENSIONS = np.array([25, 50, 100, 200, 400])
ORIGIN_SAMPLES = 80_000
ORIGIN_CHUNK_SIZE = 4_000

STATIONARY_DIMENSION = 200
ENDPOINT_MULTIPLIERS = np.unique(
    np.concatenate(
        (
            np.geomspace(0.05, 3.0, 19),
            np.geomspace(4.0, 100.0, 11),
            np.array([1.0, 2.0, 5.0, 10.0, 20.0, 50.0, 100.0]),
        )
    )
)
STATIONARY_SAMPLES = 48_000
STATIONARY_CHUNK_SIZE = 2_000

TRACE_DIMENSION = 200
TRACE_ITERATIONS = 40_000


def potential_and_gradient(x, h0):
    """Evaluate U, grad U, and ||grad U||^2 row by row."""
    quadratic_curvature = (L + M) / 2.0
    perturbation_curvature = (L - M) / 2.0
    square_root_h0 = np.sqrt(h0)

    potential = 0.5 * M * x[:, 0] ** 2
    potential += np.sum(
        0.5 * quadratic_curvature * x[:, 1:] ** 2
        - perturbation_curvature
        * h0
        * np.cos(x[:, 1:] / square_root_h0),
        axis=1,
    )

    gradient = np.empty_like(x)
    gradient[:, 0] = M * x[:, 0]
    gradient[:, 1:] = (
        quadratic_curvature * x[:, 1:]
        + perturbation_curvature
        * square_root_h0
        * np.sin(x[:, 1:] / square_root_h0)
    )
    squared_gradient_norm = np.einsum("ij,ij->i", gradient, gradient)
    return potential, gradient, squared_gradient_norm


def stationary_sample(rng, sample_size, dimension, h0):
    """Draw exact independent samples using a Gaussian rejection envelope."""
    quadratic_curvature = (L + M) / 2.0
    perturbation_curvature = (L - M) / 2.0
    x = np.empty((sample_size, dimension))
    x[:, 0] = rng.normal(scale=1.0 / np.sqrt(M), size=sample_size)

    remaining = np.ones((sample_size, dimension - 1), dtype=bool)
    while np.any(remaining):
        number_remaining = int(remaining.sum())
        proposals = rng.normal(
            scale=1.0 / np.sqrt(quadratic_curvature),
            size=number_remaining,
        )
        acceptance_probability = np.exp(
            perturbation_curvature
            * h0
            * (np.cos(proposals / np.sqrt(h0)) - 1.0)
        )
        accepted = rng.random(number_remaining) < acceptance_probability
        flat_indices = np.flatnonzero(remaining)
        accepted_indices = flat_indices[accepted]
        x[:, 1:].flat[accepted_indices] = proposals[accepted]
        remaining.flat[accepted_indices] = False
    return x


def proposal_diagnostics(rng, x, h0, steps, cached=None):
    """Return alpha and alpha*||Y-X||^2/d for one MALA proposal per row."""
    if cached is None:
        potential_x, gradient_x, squared_gradient_x = potential_and_gradient(x, h0)
    else:
        potential_x, gradient_x, squared_gradient_x = cached

    noise = rng.standard_normal(x.shape)
    y = (
        x
        - steps[:, None] * gradient_x
        + np.sqrt(2.0 * steps)[:, None] * noise
    )
    potential_y, gradient_y, squared_gradient_y = potential_and_gradient(y, h0)
    increment = y - x
    log_hastings_ratio = (
        potential_x
        - potential_y
        + 0.5 * np.einsum("ij,ij->i", increment, gradient_x + gradient_y)
        + 0.25 * steps * (squared_gradient_x - squared_gradient_y)
    )
    acceptance_probability = np.exp(np.minimum(0.0, log_hastings_ratio))
    esjd = (
        acceptance_probability
        * np.einsum("ij,ij->i", increment, increment)
        / x.shape[1]
    )
    return acceptance_probability, esjd


class IIDMoments:
    """Accumulate an i.i.d. mean and its standard error stably in chunks."""

    def __init__(self):
        self.count = 0
        self.mean = 0.0
        self.sum_squared_deviations = 0.0

    def update(self, values):
        values = np.asarray(values, dtype=float)
        chunk_count = values.size
        if chunk_count == 0:
            return
        chunk_mean = float(values.mean())
        chunk_sum_squared_deviations = float(
            np.sum((values - chunk_mean) ** 2)
        )
        combined_count = self.count + chunk_count
        difference = chunk_mean - self.mean
        self.sum_squared_deviations += (
            chunk_sum_squared_deviations
            + difference**2 * self.count * chunk_count / combined_count
        )
        self.mean += difference * chunk_count / combined_count
        self.count = combined_count

    def mean_and_standard_error(self):
        if self.count < 2:
            raise ValueError("At least two observations are needed for a standard error.")
        sample_variance = self.sum_squared_deviations / (self.count - 1)
        return self.mean, np.sqrt(sample_variance / self.count)


def origin_experiment(rng):
    rows = []
    number_of_chunks = ORIGIN_SAMPLES // ORIGIN_CHUNK_SIZE
    for dimension in ORIGIN_DIMENSIONS:
        h0 = HARD_SCALE_CONSTANT / (L * np.sqrt(dimension))
        x = np.zeros((ORIGIN_CHUNK_SIZE, dimension))
        cached = potential_and_gradient(x, h0)
        for method, randomized in (("Fixed step", False), ("Randomized step", True)):
            moments = IIDMoments()
            for _ in range(number_of_chunks):
                if randomized:
                    steps = h0 * rng.random(ORIGIN_CHUNK_SIZE)
                else:
                    steps = np.full(ORIGIN_CHUNK_SIZE, h0)
                acceptance, _ = proposal_diagnostics(
                    rng, x, h0, steps, cached=cached
                )
                moments.update(acceptance)
            mean, standard_error = moments.mean_and_standard_error()
            rows.append(
                {
                    "dimension": int(dimension),
                    "h0": h0,
                    "method": method,
                    "acceptance": float(mean),
                    "acceptance_se": float(standard_error),
                    "mean_waiting_time": float(1.0 / mean),
                }
            )
    return rows


def stationary_experiment(rng):
    h0 = HARD_SCALE_CONSTANT / (L * np.sqrt(STATIONARY_DIMENSION))
    number_of_chunks = STATIONARY_SAMPLES // STATIONARY_CHUNK_SIZE
    results = {
        (index, method, statistic): IIDMoments()
        for index in range(len(ENDPOINT_MULTIPLIERS))
        for method in ("Fixed step", "Randomized step")
        for statistic in ("acceptance", "esjd")
    }

    for _ in range(number_of_chunks):
        x = stationary_sample(
            rng, STATIONARY_CHUNK_SIZE, STATIONARY_DIMENSION, h0
        )
        cached = potential_and_gradient(x, h0)
        for index, multiplier in enumerate(ENDPOINT_MULTIPLIERS):
            endpoint = multiplier * h0
            fixed_steps = np.full(STATIONARY_CHUNK_SIZE, endpoint)
            fixed_acceptance, fixed_esjd = proposal_diagnostics(
                rng, x, h0, fixed_steps, cached=cached
            )
            random_steps = endpoint * rng.random(STATIONARY_CHUNK_SIZE)
            random_acceptance, random_esjd = proposal_diagnostics(
                rng, x, h0, random_steps, cached=cached
            )
            results[(index, "Fixed step", "acceptance")].update(fixed_acceptance)
            results[(index, "Fixed step", "esjd")].update(fixed_esjd)
            results[(index, "Randomized step", "acceptance")].update(
                random_acceptance
            )
            results[(index, "Randomized step", "esjd")].update(random_esjd)

    rows = []
    for index, multiplier in enumerate(ENDPOINT_MULTIPLIERS):
        for method in ("Fixed step", "Randomized step"):
            acceptance, acceptance_se = results[
                (index, method, "acceptance")
            ].mean_and_standard_error()
            esjd, esjd_se = results[
                (index, method, "esjd")
            ].mean_and_standard_error()
            rows.append(
                {
                    "dimension": STATIONARY_DIMENSION,
                    "h0": h0,
                    "endpoint_multiplier": float(multiplier),
                    "endpoint": float(multiplier * h0),
                    "method": method,
                    "acceptance": float(acceptance),
                    "acceptance_se": float(acceptance_se),
                    "esjd_per_coordinate": float(esjd),
                    "esjd_se": float(esjd_se),
                }
            )
    return rows


def trace_experiment():
    """Run one fixed-step and one randomized-step chain from the origin."""
    h0 = HARD_SCALE_CONSTANT / (L * np.sqrt(TRACE_DIMENSION))
    child_seeds = np.random.SeedSequence(SEED).spawn(2)
    traces = {}
    summaries = {}

    for method, randomized, child_seed in (
        ("Fixed step", False, child_seeds[0]),
        ("Randomized step", True, child_seeds[1]),
    ):
        rng = np.random.default_rng(child_seed)
        x = np.zeros((1, TRACE_DIMENSION))
        potential_x, gradient_x, squared_gradient_x = potential_and_gradient(x, h0)
        first_coordinate_trace = np.empty(TRACE_ITERATIONS)
        accepted_count = 0
        first_accepted_iteration = None

        for iteration in range(1, TRACE_ITERATIONS + 1):
            step = h0 * rng.random() if randomized else h0
            noise = rng.standard_normal((1, TRACE_DIMENSION))
            y = x - step * gradient_x + np.sqrt(2.0 * step) * noise
            potential_y, gradient_y, squared_gradient_y = potential_and_gradient(
                y, h0
            )
            increment = y - x
            log_hastings_ratio = (
                potential_x
                - potential_y
                + 0.5
                * np.einsum("ij,ij->i", increment, gradient_x + gradient_y)
                + 0.25 * step * (squared_gradient_x - squared_gradient_y)
            )[0]
            if np.log(rng.random()) < min(0.0, log_hastings_ratio):
                x = y
                potential_x = potential_y
                gradient_x = gradient_y
                squared_gradient_x = squared_gradient_y
                accepted_count += 1
                if first_accepted_iteration is None:
                    first_accepted_iteration = iteration

            first_coordinate_trace[iteration - 1] = x[0, 0]

        traces[method] = first_coordinate_trace
        summaries[method] = {
            "acceptance_rate": accepted_count / TRACE_ITERATIONS,
            "accepted_moves": accepted_count,
            "first_accepted_iteration": first_accepted_iteration,
        }

    return traces, summaries


def write_csv(path, rows, columns):
    with path.open("w", encoding="utf-8") as handle:
        handle.write(",".join(columns) + "\n")
        for row in rows:
            handle.write(",".join(str(row[column]) for column in columns) + "\n")


def read_csv(path, integer_columns=()):
    """Read a result table while restoring numeric columns."""
    rows = []
    with path.open("r", encoding="utf-8", newline="") as handle:
        for row in csv.DictReader(handle):
            converted = {"method": row["method"]}
            for key, value in row.items():
                if key == "method":
                    continue
                converted[key] = int(value) if key in integer_columns else float(value)
            rows.append(converted)
    return rows


def configure_plotting():
    mpl.rcParams.update(
        {
            "font.size": 10,
            "axes.labelsize": 10,
            "legend.fontsize": 9,
            "xtick.labelsize": 9,
            "ytick.labelsize": 9,
            "pdf.fonttype": 42,
            "ps.fonttype": 42,
        }
    )


def plot_origin(rows, output_directory):
    configure_plotting()
    figure, axis = plt.subplots(figsize=(4.7, 3.25), constrained_layout=True)
    styles = {
        "Fixed step": ("#C44E52", "o"),
        "Randomized step": ("#4C72B0", "s"),
    }
    for method in ("Fixed step", "Randomized step"):
        selected = [row for row in rows if row["method"] == method]
        dimensions = np.array([row["dimension"] for row in selected])
        acceptance = np.array([row["acceptance"] for row in selected])
        standard_error = np.array([row["acceptance_se"] for row in selected])
        color, marker = styles[method]
        axis.errorbar(
            dimensions,
            acceptance,
            yerr=2.0 * standard_error,
            color=color,
            marker=marker,
            markersize=4,
            linewidth=1.6,
            elinewidth=1.0,
            capsize=3.0,
            capthick=1.0,
            label=method,
        )
    axis.set_yscale("log")
    axis.set_xlabel("Dimension $d$")
    axis.set_ylabel(r"Mean acceptance at $x=0$")
    axis.grid(True, which="both", color="#D9D9D9", linewidth=0.6)
    axis.spines[["top", "right"]].set_visible(False)
    axis.legend(frameon=False)
    figure.savefig(output_directory / "hard_target_origin_acceptance.pdf", bbox_inches="tight")
    figure.savefig(
        output_directory / "hard_target_origin_acceptance.png",
        dpi=220,
        bbox_inches="tight",
    )
    plt.close(figure)


def plot_trace(traces, summaries, output_directory):
    """Plot the first coordinate of both chains over 40,000 iterations."""
    configure_plotting()
    iterations = np.arange(1, TRACE_ITERATIONS + 1)
    styles = {
        "Fixed step": "#C44E52",
        "Randomized step": "#4C72B0",
    }
    figure, axes = plt.subplots(
        2, 1, figsize=(7.1, 3.75), sharex=True, sharey=True,
        constrained_layout=True
    )

    for axis, method in zip(axes, ("Fixed step", "Randomized step")):
        axis.plot(
            iterations,
            traces[method],
            color=styles[method],
            linewidth=0.65,
        )
        first_move = summaries[method]["first_accepted_iteration"]
        first_move_text = "none" if first_move is None else f"{first_move:,}"
        axis.text(
            0.985,
            0.93,
            "Overall acceptance: "
            f"{summaries[method]['acceptance_rate']:.3f}\n"
            f"First accepted move: {first_move_text}",
            transform=axis.transAxes,
            ha="right",
            va="top",
            fontsize=8.4,
            bbox={"boxstyle": "round,pad=0.25", "facecolor": "white",
                  "edgecolor": "#B0B0B0", "alpha": 0.92},
        )
        axis.set_title(method, loc="left", fontsize=10)
        axis.set_ylabel(r"$x_1$")
        axis.grid(True, color="#D9D9D9", linewidth=0.55)
        axis.spines[["top", "right"]].set_visible(False)

    axes[-1].set_xlabel("Iteration")
    axes[-1].set_xlim(1, TRACE_ITERATIONS)
    figure.savefig(
        output_directory / "hard_target_first_coordinate_trace.pdf",
        bbox_inches="tight",
    )
    figure.savefig(
        output_directory / "hard_target_first_coordinate_trace.png",
        dpi=220,
        bbox_inches="tight",
    )
    plt.close(figure)


def plot_stationary(rows, output_directory):
    configure_plotting()
    figure, axes = plt.subplots(1, 2, figsize=(7.1, 2.45), constrained_layout=True)
    styles = {
        "Fixed step": ("#C44E52", "o"),
        "Randomized step": ("#4C72B0", "s"),
    }
    for method in ("Fixed step", "Randomized step"):
        selected = [row for row in rows if row["method"] == method]
        multiplier = np.array([row["endpoint_multiplier"] for row in selected])
        acceptance = np.array([row["acceptance"] for row in selected])
        acceptance_se = np.array([row["acceptance_se"] for row in selected])
        esjd = np.array([row["esjd_per_coordinate"] for row in selected])
        esjd_se = np.array([row["esjd_se"] for row in selected])
        color, marker = styles[method]
        axes[0].errorbar(
            multiplier,
            acceptance,
            yerr=2.0 * acceptance_se,
            color=color,
            marker=marker,
            markersize=3.2,
            linewidth=1.5,
            elinewidth=0.9,
            capsize=2.2,
            capthick=0.9,
            label=method,
        )
        axes[1].errorbar(
            multiplier,
            esjd,
            yerr=2.0 * esjd_se,
            color=color,
            marker=marker,
            markersize=3.2,
            linewidth=1.5,
            elinewidth=0.9,
            capsize=2.2,
            capthick=0.9,
            label=method,
        )
    axes[0].set_ylabel("Stationary mean acceptance")
    axes[1].set_ylabel("Stationary ESJD per coordinate")
    for axis in axes:
        axis.set_xscale("log")
        axis.set_xlabel(r"Endpoint relative to hard scale $H/h_0$")
        axis.grid(True, which="both", color="#D9D9D9", linewidth=0.6)
        axis.spines[["top", "right"]].set_visible(False)
    axes[0].set_ylim(-0.02, 1.02)
    axes[0].legend(frameon=False, loc="lower left")
    figure.savefig(
        output_directory / "hard_target_stationary_comparison.pdf",
        bbox_inches="tight",
    )
    figure.savefig(
        output_directory / "hard_target_stationary_comparison.png",
        dpi=220,
        bbox_inches="tight",
    )
    plt.close(figure)


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--plots-only",
        action="store_true",
        help="Regenerate the figures from the committed CSV result tables.",
    )
    parser.add_argument(
        "--trace-only",
        action="store_true",
        help="Run only the 40,000-step first-coordinate trace experiment.",
    )
    return parser.parse_args()


def main():
    args = parse_args()
    script_directory = Path(__file__).resolve().parent
    repository_directory = script_directory.parent
    data_directory = repository_directory / "data"
    figure_directory = repository_directory / "figures"
    data_directory.mkdir(exist_ok=True)
    figure_directory.mkdir(exist_ok=True)
    origin_path = data_directory / "hard_target_origin_acceptance.csv"
    stationary_path = data_directory / "hard_target_stationary_comparison.csv"

    if args.trace_only:
        traces, summaries = trace_experiment()
        plot_trace(traces, summaries, figure_directory)
        for method in ("Fixed step", "Randomized step"):
            summary = summaries[method]
            print(
                f"{method}: acceptance={summary['acceptance_rate']:.6f}, "
                f"accepted_moves={summary['accepted_moves']}, "
                "first_accepted_iteration="
                f"{summary['first_accepted_iteration']}"
            )
        print(figure_directory / "hard_target_first_coordinate_trace.pdf")
        return

    if args.plots_only:
        origin_rows = read_csv(origin_path, integer_columns=("dimension",))
        stationary_rows = read_csv(
            stationary_path, integer_columns=("dimension",)
        )
    else:
        rng = np.random.default_rng(SEED)
        origin_rows = origin_experiment(rng)
        stationary_rows = stationary_experiment(rng)
        write_csv(
            origin_path,
            origin_rows,
            [
                "dimension",
                "h0",
                "method",
                "acceptance",
                "acceptance_se",
                "mean_waiting_time",
            ],
        )
        write_csv(
            stationary_path,
            stationary_rows,
            [
                "dimension",
                "h0",
                "endpoint_multiplier",
                "endpoint",
                "method",
                "acceptance",
                "acceptance_se",
                "esjd_per_coordinate",
                "esjd_se",
            ],
        )

    plot_origin(origin_rows, figure_directory)
    plot_stationary(stationary_rows, figure_directory)
    if not args.plots_only:
        traces, summaries = trace_experiment()
        plot_trace(traces, summaries, figure_directory)
        for method in ("Fixed step", "Randomized step"):
            summary = summaries[method]
            print(
                f"{method}: acceptance={summary['acceptance_rate']:.6f}, "
                f"accepted_moves={summary['accepted_moves']}, "
                "first_accepted_iteration="
                f"{summary['first_accepted_iteration']}"
            )
    for path in sorted((*data_directory.iterdir(), *figure_directory.iterdir())):
        print(path)


if __name__ == "__main__":
    main()
