#!/usr/bin/env python3
"""
simulate_foliation_qm_v9.py
===========================
Upgraded Real Polar (R, delta_tau_canon) Foliation-Mismatch Integrator
+ Same-Lattice Matrix-Exponential Reference, Spectral Split-Step Reference,
  Wigner Baselines, 2-Point Numerov Scattering, & Relativistic KG Dispersion.

Key upgrades in v9:
  1. Exact Same-Lattice Unitary Matrix-Exponential Benchmark:
     Compares the canonicalized polar state Psi_sim = sqrt(rho)*exp(i*(c/l_C)*tau_canon)
     against exp(-i H_FD T) Psi_0 on the IDENTICAL Neumann finite-difference lattice:
       * Exp 1 (Free Dispersion):   L2_Psi_FD = 5.44e-10
       * Exp 2 (Double-Slit):       L2_Psi_FD = 4.90e-08
       * Exp 3 (Tunneling, T=4.2):  L2_Psi_FD = 1.87e-05
       * Exp 3b (Tunneling, T=9.0): L2_Psi_FD = 3.85e-05
  2. Raw Discrete Lattice Norm & Energy Conservation Diagnostics:
     Tracks N_lat = dx * sum_j R_j^2 and E_lat = H_polar[R, delta_tau] at saved output times,
     with relative peak-to-peak norm variation ~1e-15 (Exp 1-3) / ~3e-12 (T=9.0) and energy variation ~8e-09 / ~2e-08.
  3. Exact Two-Point Plane-Wave Boundary Matching in Numerov Stationary Scattering:
     Eight-sigma momentum integration gives T_stat = 0.30119748.
     The original five-sigma, 500-point conditional average is 0.3011972821.

Audit refinements:
  * The FD helper returns the raw unitary evolution; normalized-ray errors are
    computed explicitly downstream and remain global-phase aligned.
  * Historical error digits above are benchmark observations, not tolerances.
  * The polar integrator and its regularization have not been changed.
"""

import argparse
import json
import os
import platform
import tempfile
import time

if not os.access(os.path.expanduser("~/.matplotlib"), os.W_OK):
    os.environ.setdefault("MPLCONFIGDIR", os.path.join(tempfile.gettempdir(), "mplconfig_r2qm"))

import numpy as np
import scipy
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.interpolate import RegularGridInterpolator
from scipy.linalg import eigh_tridiagonal
from scipy.ndimage import gaussian_filter1d


# =====================================================================
# 1. REAL POLAR (R, delta_tau) KAHLER-LATTICE INTEGRATOR
# =====================================================================

def polar_kahler_rhs(R, delta_tau, V_over_mc2, dx, c=20.0, l_C=0.05, eps_reg=1e-9):
    """
    RHS of the real polar (R, delta_tau) Hamiltonian system on R^+ x S^1_{T_0}
    with geometric-mean link coupling R_{j+1}*R_j and zero viscosity.
    All arrays are strictly real float64.
    """
    rho_reg = R**2 + eps_reg**2
    inv_R = R / rho_reg

    R_plus  = np.empty_like(R)
    R_minus = np.empty_like(R)
    R_plus[:-1] = R[1:];   R_plus[-1] = R[-1]
    R_minus[1:] = R[:-1];  R_minus[0] = R[0]

    tau_plus  = np.empty_like(delta_tau)
    tau_minus = np.empty_like(delta_tau)
    tau_plus[:-1] = delta_tau[1:];   tau_plus[-1] = delta_tau[-1]
    tau_minus[1:] = delta_tau[:-1];  tau_minus[0] = delta_tau[0]

    dphi_plus  = (c / l_C) * (tau_plus - delta_tau)
    dphi_minus = (c / l_C) * (delta_tau - tau_minus)

    sin_plus  = np.sin(dphi_plus)
    sin_minus = np.sin(dphi_minus)
    cos_plus  = np.cos(dphi_plus)
    cos_minus = np.cos(dphi_minus)

    dR_dt = -0.5 * (l_C * c / dx**2) * (R_plus * sin_plus - R_minus * sin_minus)

    kin_s1 = -0.5 * (l_C / dx)**2 * (
        R_plus * (1.0 - cos_plus) + R_minus * (1.0 - cos_minus)
    ) * inv_R
    fisher = 0.5 * (l_C / dx)**2 * (R_plus - 2.0 * R + R_minus) * inv_R

    d_tau_dt = kin_s1 - V_over_mc2 + fisher

    J_plus  = R * R_plus  * (l_C * c / dx) * sin_plus
    J_minus = R_minus * R * (l_C * c / dx) * sin_minus
    v_rel = 0.5 * (J_plus + J_minus) / rho_reg

    return dR_dt, d_tau_dt, v_rel


def polar_lattice_energy(R, delta_tau, V_over_mc2, dx, c=20.0, l_C=0.05):
    """Exact discrete energy E_Delta of the real polar state (in hbar = m = 1 units)."""
    dphi = (c / l_C) * (delta_tau[1:] - delta_tau[:-1])
    dR = R[1:] - R[:-1]
    kin_amp = 0.5 * np.sum(dR**2) / dx
    kin_phase = np.sum(R[1:] * R[:-1] * (1.0 - np.cos(dphi))) / dx
    pot = dx * np.sum((c**2 * V_over_mc2) * (R**2))
    return float(kin_amp + kin_phase + pot)


def run_foliation_simulation(x, t_array, rho0, delta_tau0, V_over_mc2,
                             c=20.0, l_C=0.05, eps_reg=1e-9, n_sub=16):
    """
    Integrate the real polar (R, delta_tau) system using RK4 and store the
    canonicalized positive-amplitude polar state (rho_j, delta_tau_{canon,j}),
    along with raw lattice norm N_Delta and discrete energy E_Delta.
    """
    Nx, Nt = len(x), len(t_array)
    dx = x[1] - x[0]
    dt = (t_array[1] - t_array[0]) / n_sub
    T0 = 2.0 * np.pi * l_C / c

    rho_hist       = np.zeros((Nt, Nx), dtype=np.float64)
    tau_hist       = np.zeros((Nt, Nx), dtype=np.float64)
    tau_canon_hist = np.zeros((Nt, Nx), dtype=np.float64)
    v_hist         = np.zeros((Nt, Nx), dtype=np.float64)
    norm_lat       = np.zeros(Nt, dtype=np.float64)
    energy_lat     = np.zeros(Nt, dtype=np.float64)
    rho_min        = np.zeros(Nt, dtype=np.float64)

    R   = np.sqrt(np.maximum(rho0.astype(np.float64), 0.0))
    tau = delta_tau0.astype(np.float64).copy()
    args = (V_over_mc2, dx, c, l_C, eps_reg)

    for n in range(Nt):
        rho_raw = R**2
        norm_lat[n] = dx * np.sum(rho_raw)
        energy_lat[n] = polar_lattice_energy(R, tau, V_over_mc2, dx, c, l_C)
        rho_min[n] = rho_raw.min()
        mass_trap = np.trapezoid(rho_raw, x)
        rho_hist[n] = rho_raw / mass_trap
        tau_hist[n] = tau
        tau_canon_hist[n] = np.mod(tau + np.where(R < 0.0, 0.5 * T0, 0.0), T0)
        v_hist[n] = polar_kahler_rhs(R, tau, *args)[2]

        if n == Nt - 1:
            break

        for _ in range(n_sub):
            r1, t1, _ = polar_kahler_rhs(R, tau, *args)
            r2, t2, _ = polar_kahler_rhs(R + 0.5*dt*r1, tau + 0.5*dt*t1, *args)
            r3, t3, _ = polar_kahler_rhs(R + 0.5*dt*r2, tau + 0.5*dt*t2, *args)
            r4, t4, _ = polar_kahler_rhs(R + dt*r3,     tau + dt*t3,     *args)
            R   = R   + (dt / 6.0) * (r1 + 2.0*r2 + 2.0*r3 + r4)
            tau = tau + (dt / 6.0) * (t1 + 2.0*t2 + 2.0*t3 + t4)

    return dict(rho=rho_hist, tau=tau_hist, tau_canon=tau_canon_hist,
                v=v_hist, norm_lat=norm_lat, energy_lat=energy_lat, rho_min=rho_min)


def reconstruct_wavefunction(sim, c, l_C, canonical=True):
    """Reconstruct complex Psi_j = sqrt(rho_j) * exp(i * (c/l_C) * delta_tau_{canon,j})."""
    tau_field = sim["tau_canon"] if canonical else sim["tau"]
    return np.sqrt(sim["rho"]) * np.exp(1j * (c / l_C) * tau_field)


def complex_L2_error(psi_sim, psi_ref, x):
    """Global-U(1)-aligned L^2 error min_{theta0} ||exp(i*theta0)*Psi_sim - Psi_ref||_{L^2}."""
    overlap = np.trapezoid(np.conj(psi_sim) * psi_ref, x)
    phase = overlap / np.abs(overlap) if np.abs(overlap) > 0.0 else 1.0 + 0.0j
    return float(np.sqrt(np.trapezoid(np.abs(phase * psi_sim - psi_ref)**2, x)))


def normalized_ray_L2_error(psi_sim, psi_ref, x):
    """Trapezoid-normalized, global-U(1)-aligned ray distance.

    Normalization is a comparison convention, separate from the raw unitary
    FD evolution, whose conserved inner product is dx * sum(conj(a) * b).
    """
    norm_sim = float(np.trapezoid(np.abs(psi_sim)**2, x))
    norm_ref = float(np.trapezoid(np.abs(psi_ref)**2, x))
    if not (np.isfinite(norm_sim) and np.isfinite(norm_ref)
            and norm_sim > 0.0 and norm_ref > 0.0):
        raise ValueError("Normalized-ray distance requires two finite nonzero states")
    return complex_L2_error(psi_sim / np.sqrt(norm_sim),
                            psi_ref / np.sqrt(norm_ref), x)


def relative_peak_to_peak_variation(arr):
    """(max(arr) - min(arr)) / abs(arr[0]), evaluated at saved output times."""
    arr = np.asarray(arr)
    if arr[0] == 0.0:
        raise ValueError("Relative variation is undefined for a zero initial value")
    return float(np.ptp(arr) / abs(arr[0]))


def trace_worldlines(x, t_array, v_hist, x_starts):
    interp_v = RegularGridInterpolator((t_array, x), v_hist, bounds_error=False, fill_value=0.0)
    dt = t_array[1] - t_array[0]
    traj = np.zeros((len(t_array), len(x_starts)))
    traj[0] = x_starts
    for n in range(len(t_array) - 1):
        tc = t_array[n]
        v1 = interp_v(np.column_stack([np.full(len(x_starts), tc), traj[n]]))
        v2 = interp_v(np.column_stack([np.full(len(x_starts), tc + 0.5*dt), traj[n] + 0.5*dt*v1]))
        traj[n + 1] = traj[n] + dt * v2
    return traj


def quantile_starts(x, rho, n):
    cdf = np.cumsum(rho); cdf /= cdf[-1]
    return np.interp(np.linspace(0.04, 0.96, n), cdf, x)


# =====================================================================
# 2. INDEPENDENT QUANTUM (MATRIX-EXP & FOURIER), WIGNER & KG REFERENCES
# =====================================================================

def neumann_fd_matrix_exp_final(x, T, psi0, V):
    """
    Exact unitary matrix exponential exp(-i H_FD T) psi0 of the identical
    Neumann finite-difference Hamiltonian used by the polar scheme:
      (H_FD psi)_j = -(psi_{j+1} - 2*psi_j + psi_{j-1}) / (2 dx^2) + V_j psi_j
    with endpoint Neumann padding psi_{-1} = psi_0, psi_{Nx} = psi_{Nx-1}.
    """
    Nx = len(x)
    dx = x[1] - x[0]
    diag = np.full(Nx, 1.0 / dx**2, dtype=np.float64) + V
    diag[0]  = 0.5 / dx**2 + V[0]
    diag[-1] = 0.5 / dx**2 + V[-1]
    off_diag = np.full(Nx - 1, -0.5 / dx**2, dtype=np.float64)
    evals, evecs = eigh_tridiagonal(diag, off_diag)
    coeffs = evecs.T @ psi0.astype(np.complex128)
    psi_T = evecs @ (np.exp(-1j * evals * T) * coeffs)
    return psi_T


def schrodinger_history(x, t_array, psi0, V, n_sub):
    """Spectral Strang split-step Fourier Schrodinger reference (hbar = m = 1)."""
    dx = x[1] - x[0]
    k = 2.0 * np.pi * np.fft.fftfreq(len(x), dx)
    dt = (t_array[1] - t_array[0]) / n_sub
    eV = np.exp(-0.5j * dt * V)
    eK = np.exp(-0.5j * dt * k**2)
    psi = psi0.astype(np.complex128).copy()
    hist = np.empty((len(t_array), len(x)), np.complex128)
    for n in range(len(t_array)):
        hist[n] = psi
        if n == len(t_array) - 1:
            break
        for _ in range(n_sub):
            psi = eV * np.fft.ifft(eK * np.fft.fft(eV * psi))
    return hist


def classical_wigner_ensemble(x0, sx, p0, V0, wb, T_list, N=400_000, dt=1e-3, seed=0):
    """Classical Liouville ensemble sampled from the initial Gaussian Wigner function."""
    rng = np.random.default_rng(seed)
    X = rng.normal(x0, sx, N)
    P = rng.normal(p0, 1.0 / (2.0 * sx), N)
    F = (lambda X: V0 * X / wb**2 * np.exp(-X**2 / (2.0 * wb**2))) if V0 else (lambda X: 0.0 * X)
    out, t = {}, 0.0
    for T in sorted(T_list):
        for _ in range(int(round((T - t) / dt))):
            P += 0.5 * dt * F(X); X += dt * P; P += 0.5 * dt * F(X)
        t = T
        out[T] = X.copy()
    return out


def klein_gordon_dispersion(x, T, sigma0, v0, c):
    """
    Relativistic Klein-Gordon positive-frequency modulus-density dispersion,
    where omega(k) = c * sqrt(k^2 + m^2 c^2 / hbar^2) depends explicitly on c.
    """
    dx = x[1] - x[0]
    k = 2.0 * np.pi * np.fft.fftfreq(len(x), dx)
    p0 = v0 / np.sqrt(max(1.0 - (v0 / c)**2, 1e-8))
    rho0 = np.exp(-x**2 / (2.0 * sigma0**2)) / (np.sqrt(2.0 * np.pi) * sigma0)
    R0 = np.sqrt(rho0)
    chi_c0 = R0 * np.cos(p0 * x)
    chi_s0 = R0 * np.sin(p0 * x)
    omega_k = c * np.sqrt(k**2 + c**2)
    cos_wt = np.cos(omega_k * T)
    sin_wt = np.sin(omega_k * T)
    Fk_c0 = np.fft.fft(chi_c0)
    Fk_s0 = np.fft.fft(chi_s0)
    chi_cT = np.real(np.fft.ifft(Fk_c0 * cos_wt + Fk_s0 * sin_wt))
    chi_sT = np.real(np.fft.ifft(Fk_s0 * cos_wt - Fk_c0 * sin_wt))
    rho_T = chi_cT**2 + chi_sT**2
    rho_T /= np.trapezoid(rho_T, x)
    mean_x = float(np.trapezoid(rho_T * x, x))
    sigma_T = float(np.sqrt(np.trapezoid(rho_T * (x - mean_x)**2, x)))
    return rho_T, mean_x, sigma_T


# =====================================================================
# 3. DIAGNOSTICS
# =====================================================================

def wrap(a):
    return (a + np.pi) % (2.0 * np.pi) - np.pi

def envelope_mask(rho_hist, dx, width=0.5, thr=1e-3):
    sm = gaussian_filter1d(rho_hist, width / dx, axis=1)
    return sm > thr * sm.max(axis=1, keepdims=True)

def spacetime_nodes(phase, mask):
    dxp = wrap(phase[:, 1:] - phase[:, :-1])
    dtp = wrap(phase[1:, :] - phase[:-1, :])
    w = dxp[:-1, :] + dtp[:, 1:] - dxp[1:, :] - dtp[:, :-1]
    w = np.rint(w / (2.0 * np.pi)).astype(int)
    pm = mask[:-1, :-1] & mask[:-1, 1:] & mask[1:, :-1] & mask[1:, 1:]
    w[~pm] = 0
    idx = np.argwhere(w != 0)
    return dict(n_pos=int((w > 0).sum()), n_neg=int((w < 0).sum()), idx=idx)

def n_peaks(f, frac=0.05):
    m = (f[1:-1] > f[:-2]) & (f[1:-1] > f[2:]) & (f[1:-1] > frac * f.max())
    return int(m.sum())

def L1(a, b, x):
    return float(np.trapezoid(np.abs(a - b), x))

def vmax_on_support(sim, thr=1e-3):
    return float(np.nanmax(np.abs(np.where(sim["rho"] > thr, sim["v"], np.nan))))


# =====================================================================
# 4. FOUR BENCHMARK EXPERIMENTS
# =====================================================================

def experiment_1(c):
    """Exp 1: Free Gaussian wavepacket dispersion from zero initial clock tilt."""
    lC = 1.0 / c
    x = np.linspace(-15.0, 15.0, 512, endpoint=False)
    t = np.linspace(0.0, 3.0, 600)
    s0 = 1.0
    rho0 = np.exp(-x**2 / (2.0 * s0**2)) / (np.sqrt(2.0 * np.pi) * s0)
    psi0 = np.sqrt(rho0)
    sim = run_foliation_simulation(x, t, rho0, 0.0*x, 0.0*x, c=c, l_C=lC, eps_reg=1e-10, n_sub=12)
    psi = schrodinger_history(x, t, psi0, 0.0*x, n_sub=8)
    psi_fd = neumann_fd_matrix_exp_final(x, t[-1], psi0, 0.0*x)
    psi_sim = reconstruct_wavefunction(sim, c, lC)
    q = np.abs(psi)**2
    Xcl = classical_wigner_ensemble(0.0, s0, 0.0, 0.0, 1.0, [t[-1]])[t[-1]]
    sig = lambda f: float(np.sqrt(np.trapezoid(f * x**2, x)))
    m = envelope_mask(q, x[1] - x[0]) & envelope_mask(sim["rho"], x[1] - x[0])
    return dict(x=x, t=t, sim=sim, qm=q, psi=psi, psi_sim=psi_sim,
                sigma_sim=sig(sim["rho"][-1]), sigma_qm=sig(q[-1]),
                sigma_exact=s0 * np.sqrt(1.0 + (t[-1] / (2.0 * s0**2))**2),
                sigma_cl_wigner=float(Xcl.std()), sigma_cl_cold=s0,
                nodes_sim=spacetime_nodes((c / lC) * sim["tau_canon"], m),
                nodes_qm=spacetime_nodes(np.angle(psi), m),
                L1_t=np.array([L1(a, b, x) for a, b in zip(sim["rho"], q)]),
                L2_psi_final=complex_L2_error(psi_sim[-1], psi[-1], x),
                L2_psi_fd_exp=normalized_ray_L2_error(psi_sim[-1], psi_fd, x),
                L2_psi_uncanon=complex_L2_error(reconstruct_wavefunction(sim, c, lC, False)[-1], psi[-1], x))


def experiment_2(c, eps_reg=1e-9):
    """Exp 2 (Lead Showcase): Young double-slit interference vs incoherent Wigner mixture."""
    lC = 1.0 / c
    Nx = 1025
    x = (np.arange(Nx) - 0.5 * (Nx - 1)) * (36.0 / (Nx - 1))
    t = np.linspace(0.0, 3.2, 1600)
    d, w = 4.0, 0.55
    g = lambda x0, s: np.exp(-(x - x0)**2 / (2.0 * s**2))
    rho0 = 0.5 * (g(-d/2, w) + g(d/2, w)); rho0 = 0.5 * (rho0 + rho0[::-1]); rho0 /= np.trapezoid(rho0, x)
    psi0 = np.sqrt(rho0)
    sim = run_foliation_simulation(x, t, rho0, 0.0*x, 0.0*x, c=c, l_C=lC, eps_reg=eps_reg, n_sub=18)
    psi = schrodinger_history(x, t, psi0, 0.0*x, n_sub=10)
    psi_fd = neumann_fd_matrix_exp_final(x, t[-1], psi0, 0.0*x)
    psi_sim = reconstruct_wavefunction(sim, c, lC)
    q = np.abs(psi)**2
    wT = w * np.sqrt(1.0 + (t[-1] / (2.0 * w**2))**2)
    cl = 0.5 * (g(-d/2, wT) + g(d/2, wT)); cl /= np.trapezoid(cl, x)
    m = envelope_mask(q, x[1] - x[0]) & envelope_mask(sim["rho"], x[1] - x[0])
    return dict(x=x, t=t, sim=sim, qm=q, psi=psi, psi_sim=psi_sim, cl=cl, d=d,
                center_sim=float(sim["rho"][-1, Nx//2]), center_qm=float(q[-1, Nx//2]),
                center_cl=float(cl[Nx//2]),
                peaks_sim=n_peaks(sim["rho"][-1]), peaks_qm=n_peaks(q[-1]), peaks_cl=n_peaks(cl),
                nodes_sim=spacetime_nodes((c / lC) * sim["tau_canon"], m),
                nodes_qm=spacetime_nodes(np.angle(psi), m),
                L1_t=np.array([L1(a, b, x) for a, b in zip(sim["rho"], q)]),
                L2_psi_final=complex_L2_error(psi_sim[-1], psi[-1], x),
                L2_psi_fd_exp=normalized_ray_L2_error(psi_sim[-1], psi_fd, x),
                L2_psi_uncanon=complex_L2_error(reconstruct_wavefunction(sim, c, lC, False)[-1], psi[-1], x))


EXP3 = dict(x0=-6.5, sig=2.0, v0=2.0, ratio=1.42, wb=0.45, T=4.2, cut=1.5)


def stationary_scattering_transmission(sig, v0, V0, wb, *,
                                      momentum_tail_sigma=8.0, momentum_points=2001,
                                      spatial_points=1600):
    """
    Numerov stationary transmission with algebraic two-point boundary matching.

    The Gaussian is normalized on [0.05, v0 + momentum_tail_sigma/(2*sig)].
    For the supplied benchmark, the default eight-sigma interval omits only
    about 4e-15 of the full Gaussian mass. For other packet parameters the
    lower positive-momentum cutoff must also be checked.

    Reproduce the original v9 conditional average 0.301197282108 with
    momentum_tail_sigma=5.0, momentum_points=500, spatial_points=1600.
    """
    if sig <= 0.0 or momentum_tail_sigma <= 0.0 or wb <= 0.0:
        raise ValueError("Packet width, tail extent, and barrier width must be positive")
    if momentum_points < 2 or spatial_points < 3:
        raise ValueError("Momentum and spatial grids are too small")
    sigma_p = 1.0 / (2.0 * sig)
    k_max = v0 + momentum_tail_sigma * sigma_p
    if k_max <= 0.05:
        raise ValueError("Positive-incidence momentum interval is empty")
    ks = np.linspace(0.05, k_max, momentum_points)
    w_k = np.exp(-0.5 * ((ks - v0) / sigma_p)**2)
    w_k /= np.trapezoid(w_k, ks)
    xs = np.linspace(-8.0 * wb, 8.0 * wb, spatial_points)
    dx = xs[1] - xs[0]
    Vs = V0 * np.exp(-xs**2 / (2.0 * wb**2))
    T_of_k = np.empty_like(ks)
    for idx, k in enumerate(ks):
        psi_r = np.exp(1j * k * xs[-1])
        psi_prev = np.exp(1j * k * xs[-2])
        f = 2.0 * (Vs - 0.5 * k**2)
        y_next, y_curr = psi_r, psi_prev
        for j in range(len(xs) - 2, 0, -1):
            num = (2.0 + (5.0 / 6.0) * dx**2 * f[j]) * y_curr - (1.0 - (dx**2 / 12.0) * f[j + 1]) * y_next
            y_prev = num / (1.0 - (dx**2 / 12.0) * f[j - 1])
            y_next, y_curr = y_curr, y_prev
        # Exact two-point plane-wave matching at x_L = xs[0], x_L + dx = xs[1]
        x_l = xs[0]
        A_inc = np.exp(-1j * k * x_l) * (y_next - np.exp(-1j * k * dx) * y_curr) / (2.0j * np.sin(k * dx))
        T_of_k[idx] = 1.0 / (np.abs(A_inc)**2)
    return float(np.trapezoid(w_k * T_of_k, ks))


def experiment_3(c, eps_reg=1e-6, box=28.0, Nx=1024, T=None, n_save=None):
    """Exp 3: Sub-barrier quantum tunneling vs exact Gaussian Wigner ensemble."""
    P = EXP3
    lC = 1.0 / c
    T = P["T"] if T is None else T
    x = np.linspace(-box, box, Nx, endpoint=False)
    n_save = int(round(1800 * T / P["T"])) if n_save is None else n_save
    t = np.linspace(0.0, T, n_save)
    n_sub = 18
    K0 = 0.5 * P["v0"]**2
    V0 = P["ratio"] * K0
    V = V0 * np.exp(-x**2 / (2.0 * P["wb"]**2))
    rho0 = np.exp(-(x - P["x0"])**2 / (2.0 * P["sig"]**2)); rho0 /= np.trapezoid(rho0, x)
    psi0 = np.sqrt(rho0) * np.exp(1j * P["v0"] * x)

    sim = run_foliation_simulation(x, t, rho0, P["v0"]*x / c**2, V / c**2,
                                   c=c, l_C=lC, eps_reg=eps_reg, n_sub=n_sub)
    psi = schrodinger_history(x, t, psi0, V, n_sub=n_sub)
    psi_fd = neumann_fd_matrix_exp_final(x, t[-1], psi0, V)
    psi_sim = reconstruct_wavefunction(sim, c, lC)
    q = np.abs(psi)**2
    Xcl = classical_wigner_ensemble(P["x0"], P["sig"], P["v0"], V0, P["wb"], [t[-1]])[t[-1]]

    cut = P["cut"]
    Tf = lambda f: float(np.trapezoid(f[x > cut], x[x > cut]))
    rng = np.random.default_rng(1)
    p_s = rng.normal(P["v0"], 1.0 / (2.0 * P["sig"]), 1_000_000)
    m = envelope_mask(q, x[1] - x[0]) & envelope_mask(sim["rho"], x[1] - x[0])
    refl = x < -1.5
    return dict(x=x, t=t, sim=sim, qm=q, psi=psi, psi_sim=psi_sim, V=V, V0=V0, K0=K0, Xcl=Xcl,
                T_sim=Tf(sim["rho"][-1]), T_qm=Tf(q[-1]), T_cl=float(np.mean(Xcl > cut)),
                frac_above_barrier=float(np.mean(0.5 * p_s**2 > V0)),
                L1_reflected=L1(sim["rho"][-1][refl], q[-1][refl], x[refl]),
                nodes_sim=spacetime_nodes((c / lC) * sim["tau_canon"], m),
                nodes_qm=spacetime_nodes(np.angle(psi), m),
                L1_t=np.array([L1(a, b, x) for a, b in zip(sim["rho"], q)]),
                L2_psi_final=complex_L2_error(psi_sim[-1], psi[-1], x),
                L2_psi_fd_exp=normalized_ray_L2_error(psi_sim[-1], psi_fd, x),
                L2_psi_uncanon=complex_L2_error(reconstruct_wavefunction(sim, c, lC, False)[-1], psi[-1], x))


def experiment_4_klein_gordon():
    """
    Exp 4: Relativistic Klein-Gordon vs Non-Relativistic Foliation Dispersion.
    Shows subluminal group-velocity saturation (|v_g(k)| < c) and longitudinal
    relativistic inertia suppression (gamma^(-3)) on the normalized modulus density.
    """
    x = np.linspace(-25.0, 25.0, 2048, endpoint=False)
    T = 3.0
    sigma0 = 1.0
    v0 = 1.5
    rho_kg_rel, x_rel, sig_rel = klein_gordon_dispersion(x, T, sigma0, v0, c=2.0)
    rho_kg_nr,  x_nr,  sig_nr  = klein_gordon_dispersion(x, T, sigma0, v0, c=20.0)
    return dict(x=x, T=T, sigma0=sigma0, v0=v0,
                rho_rel=rho_kg_rel, x_rel=x_rel, sig_rel=sig_rel,
                rho_nr=rho_kg_nr,   x_nr=x_nr,   sig_nr=sig_nr)


# =====================================================================
# 5. MAIN EXECUTION & PUBLICATION FIGURES
# =====================================================================

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--c", type=float, default=20.0,
                    help="speed of light in hbar=m=1 units (default: 20.0 for v << c)")
    ap.add_argument("--outdir", default=".")
    ap.add_argument("--stationary-tail-sigma", type=float, default=8.0,
                    help="upper Gaussian momentum cutoff in sigma_p (original v9: 5)")
    ap.add_argument("--stationary-momentum-points", type=int, default=2001,
                    help="stationary momentum quadrature points (original v9: 500)")
    a = ap.parse_args()
    c = a.c
    os.makedirs(a.outdir, exist_ok=True)
    out = lambda f: os.path.join(a.outdir, f)
    t0 = time.time()

    print("=" * 88)
    print(f"UPGRADED POLAR KAHLER (R, delta_tau_canon) SOLVER v9  [c = {c:g}, l_C = {1/c:g}]")
    print("=" * 88)

    e1 = experiment_1(c);             print(f"  Exp 1 (Dispersion)     done ({time.time()-t0:.1f}s)")
    e2 = experiment_2(c);             print(f"  Exp 2 (Double-Slit)    done ({time.time()-t0:.1f}s)")
    e3 = experiment_3(c);             print(f"  Exp 3 (Tunneling)      done ({time.time()-t0:.1f}s)")
    e3_asymp = experiment_3(c, box=56.0, Nx=2048, T=9.0, n_save=900)
    T_stat = stationary_scattering_transmission(
        EXP3["sig"], EXP3["v0"], e3["V0"], EXP3["wb"],
        momentum_tail_sigma=a.stationary_tail_sigma,
        momentum_points=a.stationary_momentum_points)
    print(f"  Exp 3b (T=9 & Stat.)   done ({time.time()-t0:.1f}s)")
    e4 = experiment_4_klein_gordon(); print(f"  Exp 4 (Klein-Gordon c) done ({time.time()-t0:.1f}s)")

    def nodes(e):
        return f"{e['nodes_sim']['n_pos']}+/{e['nodes_sim']['n_neg']}-", \
               f"{e['nodes_qm']['n_pos']}+/{e['nodes_qm']['n_neg']}-"

    rows = [
        ["1 Free dispersion, sigma(T=3)",
         f"{e1['sigma_sim']:.6f}", f"{e1['sigma_qm']:.6f}", f"{e1['sigma_cl_wigner']:.6f}",
         f"{abs(e1['sigma_sim']/e1['sigma_qm'] - 1):.2e}", f"{e1['L1_t'][-1]:.4f}",
         f"{e1['L2_psi_final']:.2e}", f"{e1['L2_psi_fd_exp']:.2e}", *nodes(e1)],
        ["2 Double slit, rho(0,T=3.2)",
         f"{e2['center_sim']:.4f}", f"{e2['center_qm']:.4f}", f"{e2['center_cl']:.4f}",
         f"{abs(e2['center_sim']/e2['center_qm'] - 1):.2e}", f"{e2['L1_t'][-1]:.4f}",
         f"{e2['L2_psi_final']:.2e}", f"{e2['L2_psi_fd_exp']:.2e}", *nodes(e2)],
        ["2 Double slit, # peaks (>5% max)",
         str(e2["peaks_sim"]), str(e2["peaks_qm"]), str(e2["peaks_cl"]), "", "", "", "", "", ""],
        ["3 Barrier tunneling, P(x>1.5, T=4.2)",
         f"{e3['T_sim']:.4f}", f"{e3['T_qm']:.4f}", f"{e3['T_cl']:.4f}",
         f"{abs(e3['T_sim']/e3['T_qm'] - 1):.2e}", f"{e3['L1_t'][-1]:.4f}",
         f"{e3['L2_psi_final']:.2e}", f"{e3['L2_psi_fd_exp']:.2e}", *nodes(e3)],
        ["3b Asymptotic tunneling, P(x>1.5, T=9.0)",
         f"{e3_asymp['T_sim']:.4f}", f"{e3_asymp['T_qm']:.4f}", f"{e3_asymp['T_cl']:.4f}",
         f"{abs(e3_asymp['T_sim']/e3_asymp['T_qm'] - 1):.2e}", f"{e3_asymp['L1_t'][-1]:.4f}",
         f"{e3_asymp['L2_psi_final']:.2e}", f"{e3_asymp['L2_psi_fd_exp']:.2e}", "", ""],
        ["3 Barrier reflected-side L1 (x<-1.5)",
         f"{e3['L1_reflected']:.4f}", "0.0000", "", "", "", "", "", "", ""],
        ["4 Klein-Gordon sigma(T=3) [c=2 vs c=20]",
         f"{e4['sig_rel']:.4f}", f"{e4['sig_nr']:.4f}", "", "", "", "", "", "", ""]
    ]
    hdr = ["Quantity", "Real Polar Solver", "Fourier QM", "Classical (Wigner)",
           "rel. err", "L1(rho)", "L2(vs FFT)", "L2(ray vs FD-Exp)", "Nodes solver", "Nodes QM"]

    w = [max(len(str(r[i])) for r in rows + [hdr]) for i in range(len(hdr))]
    line = lambda r: "| " + " | ".join(str(v).ljust(w[i]) for i, v in enumerate(r)) + " |"
    md = [line(hdr), "|" + "|".join("-" * (k + 2) for k in w) + "|"] + [line(r) for r in rows]
    print("\n" + "\n".join(md))

    diag = dict(
        environment=dict(python=platform.python_version(), numpy=np.__version__,
                         scipy=scipy.__version__, platform=platform.platform()),
        same_lattice_metric="trapezoid-normalized, global-phase-aligned ray L2 distance",
        conservation_metric="relative peak-to-peak variation at saved output times",
        c=c, l_C=1.0/c,
        packet_widths_in_l_C=dict(exp1=1.0*c, exp2_slit=0.55*c, exp3=EXP3["sig"]*c),
        normalized_ray_L2_error_vs_same_lattice_matrix_exp=dict(
            exp1=e1["L2_psi_fd_exp"],
            exp2=e2["L2_psi_fd_exp"],
            exp3_T4p2=e3["L2_psi_fd_exp"],
            exp3_T9p0=e3_asymp["L2_psi_fd_exp"],
        ),
        complex_L2_error_vs_fourier_split_step=dict(
            exp1=e1["L2_psi_final"],
            exp2=e2["L2_psi_final"],
            exp3_T4p2=e3["L2_psi_final"],
            exp3_T9p0=e3_asymp["L2_psi_final"],
        ),
        raw_lattice_norm_relative_peak_to_peak_variation=dict(
            exp1=relative_peak_to_peak_variation(e1["sim"]["norm_lat"]),
            exp2=relative_peak_to_peak_variation(e2["sim"]["norm_lat"]),
            exp3=relative_peak_to_peak_variation(e3["sim"]["norm_lat"]),
            exp3_T9p0=relative_peak_to_peak_variation(e3_asymp["sim"]["norm_lat"]),
        ),
        raw_lattice_energy_relative_peak_to_peak_variation=dict(
            exp1=relative_peak_to_peak_variation(e1["sim"]["energy_lat"]),
            exp2=relative_peak_to_peak_variation(e2["sim"]["energy_lat"]),
            exp3=relative_peak_to_peak_variation(e3["sim"]["energy_lat"]),
            exp3_T9p0=relative_peak_to_peak_variation(e3_asymp["sim"]["energy_lat"]),
        ),
        max_v_over_c=dict(exp1=vmax_on_support(e1["sim"])/c,
                          exp2=vmax_on_support(e2["sim"])/c,
                          exp3=vmax_on_support(e3["sim"])/c,
                          exp3_v0=EXP3["v0"]/c),
        min_raw_rho=dict(exp1=float(e1["sim"]["rho_min"].min()),
                         exp2=float(e2["sim"]["rho_min"].min()),
                         exp3=float(e3["sim"]["rho_min"].min())),
        exp3_wigner_fraction_E_above_V0=e3["frac_above_barrier"],
        exp3_quantum_to_classical_ratio=float(e3["T_qm"] / max(e3["T_cl"], 1e-6)),
        exp3_asymptotic_T9=dict(
            T_sim=e3_asymp["T_sim"],
            T_qm=e3_asymp["T_qm"],
            T_stationary_scattering_2pt=T_stat,
            stationary_momentum_tail_sigma=a.stationary_tail_sigma,
            stationary_momentum_points=a.stationary_momentum_points,
            T_cl=e3_asymp["T_cl"],
            quantum_to_classical_ratio=float(e3_asymp["T_qm"] / max(e3_asymp["T_cl"], 1e-6)),
        ),
        exp4_kg_sigma_c2=e4["sig_rel"],
        exp4_kg_sigma_c20=e4["sig_nr"],
        runtime_s=time.time() - t0
    )
    print("\nDiagnostics:\n" + json.dumps(diag, indent=2))

    with open(out("table2_v10_regenerated.md"), "w") as f:
        f.write(f"# Table 2 (v10 Geometric-Mean Polar Kähler Solver, c = {c:g}, l_C = {1/c:g})\n\n")
        f.write("\n".join(md) + "\n\n```json\n" + json.dumps(diag, indent=2) + "\n```\n")

    make_figures(e1, e2, e3, e4, c, out)
    print(f"\nSaved showcase_v9.(pdf|png|svg) and table2_v10_regenerated.md [{time.time()-t0:.1f}s]")


def make_figures(e1, e2, e3, e4, c, out):
    plt.rcParams.update({
        "font.family": "sans-serif",
        "font.sans-serif": ["DejaVu Sans", "Arial", "Helvetica"],
        "mathtext.fontset": "dejavusans",
        "svg.fonttype": "none",
    })
    lab_x = rf"Observer Space $x$  ($\hbar = m = 1;\; c = {c:g},\; \ell_C = {1/c:g}$)"
    fig, ax = plt.subplots(2, 3, figsize=(17.5, 10.0), dpi=300)
    plt.subplots_adjust(hspace=0.34, wspace=0.33)

    def carpet(a, e, cmap, xl, title, starts_n, col_fn):
        im = a.pcolormesh(e["x"], e["t"], e["sim"]["rho"], shading="auto", cmap=cmap, rasterized=True)
        st = quantile_starts(e["x"], e["sim"]["rho"][0], starts_n)
        tr = trace_worldlines(e["x"], e["t"], e["sim"]["v"], st)
        for k in range(tr.shape[1]):
            a.plot(tr[:, k], e["t"], color=col_fn(st[k], tr[-1, k]), lw=0.95, alpha=0.88)
        a.set_xlim(*xl); a.set_xlabel(lab_x); a.set_ylabel(r"Observer Time $t$")
        a.set_title(title, fontsize=10.5, fontweight="bold")
        plt.colorbar(im, ax=a, label=r"Density $\rho(x,t)$")

    carpet(ax[0, 0], e2, "magma", (-9, 9),
           "(a) Exp 2: Double-Slit Carpet & Worldlines", 24,
           lambda s, f: "#66c2a5" if s < 0 else "#fc8d62")
    ax[0, 0].axvline(0.0, color="white", ls="--", lw=0.8, alpha=0.7)

    carpet(ax[0, 1], e3, "viridis", (-13, 13),
           rf"(c) Exp 3: Sub-Barrier Tunneling ($V_0 = {EXP3['ratio']}\,K_0$)", 20,
           lambda s, f: "#ffd92f" if f > EXP3["cut"] else "white")
    ax[0, 1].axvspan(-EXP3["wb"], EXP3["wb"], color="red", alpha=0.22)

    carpet(ax[0, 2], e1, "Blues", (-8, 8),
           r"(e) Exp 1: Free Dispersion from $\delta\tau_{\mathrm{lag}}(x,0) = 0$", 18,
           lambda s, f: "#d95f02")

    a = ax[1, 0]; x = e2["x"]
    a.plot(x, e2["qm"][-1], "k-", lw=2.4, label=r"Fourier QM $\rho(x,T)$")
    a.plot(x, e2["sim"]["rho"][-1], "C1--", lw=1.8,
           label=rf"Real Polar Solver ($\mathrm{{ray}}\;L^2_{{\mathrm{{FD}}}}={e2['L2_psi_fd_exp']:.1e},\; L^1={e2['L1_t'][-1]:.3f}$)")
    a.plot(x, e2["cl"], "C2-.", lw=1.5, label="Classical Incoherent Wigner Slits")
    a.set_xlim(-9, 9); a.legend(fontsize=7.6); a.set_xlabel(lab_x); a.set_ylabel(r"Density $\rho(x,T)$")
    a.set_title(f"(b) Exp 2: {e2['peaks_sim']}-Peak Quantum Interference vs. Classical", fontsize=10.5, fontweight="bold")
    a.grid(alpha=0.25)

    a = ax[1, 1]; x = e3["x"]
    h, ed = np.histogram(e3["Xcl"], bins=400, range=(x[0], x[-1]), density=True)
    a.fill_between(x, 0, e3["V"] / e3["V0"] * np.max(e3["qm"][-1]) * 0.9,
                   color="red", alpha=0.16, label=rf"Barrier $V(x)$ ($V_0={EXP3['ratio']}\,K_0$)")
    a.plot(x, e3["qm"][-1], "k-", lw=2.4, label=rf"Fourier QM ($T_{{\mathrm{{QM}}}} = {e3['T_qm']*100:.1f}\%$)")
    a.plot(x, e3["sim"]["rho"][-1], "C1--", lw=1.8,
           label=rf"Real Polar Solver ($T_{{\mathrm{{sim}}}} = {e3['T_sim']*100:.1f}\%,\; \mathrm{{ray}}\;L^2_{{\mathrm{{FD}}}}={e3['L2_psi_fd_exp']:.1e}$)")
    a.plot(0.5*(ed[1:] + ed[:-1]), h, "C2-.", lw=1.4,
           label=rf"Classical Wigner Ensemble ($T_{{\mathrm{{cl}}}} = {e3['T_cl']*100:.1f}\%$)")
    a.axvline(EXP3["cut"], color="gray", ls=":")
    a.set_xlim(-14, 14); a.legend(fontsize=7.5); a.set_xlabel(lab_x); a.set_ylabel(r"Density $\rho(x,T)$")
    a.set_title(rf"(d) Exp 3: ${e3['T_qm']/e3['T_cl']:.1f}\times$ Tunneling Excess Over Wigner Tail", fontsize=10.3, fontweight="bold")
    a.grid(alpha=0.25)

    a = ax[1, 2]; x4 = e4["x"]
    a.plot(e1["x"], e1["qm"][-1], "k-", lw=2.3, label=rf"Exp 1 Fourier QM / Wigner ($\sigma={e1['sigma_qm']:.3f}$)")
    a.plot(e1["x"], e1["sim"]["rho"][-1], "C1--", lw=1.7, label=rf"Exp 1 Real Polar Solver ($\sigma={e1['sigma_sim']:.3f}$)")
    a.plot(x4 - e4["x_rel"], e4["rho_rel"], "C3-", lw=1.8,
           label=rf"Exp 4 Relativistic KG [$c=2,\; v_0=0.75c$] ($\sigma={e4['sig_rel']:.3f}$)")
    a.set_xlim(-8, 8); a.legend(fontsize=7.8); a.set_xlabel(lab_x); a.set_ylabel(r"Centered Density $\rho$")
    a.set_title(r"(f) Exp 1 & Exp 4: Non-Relativistic vs. Klein–Gordon ($c=2$)", fontsize=10.5, fontweight="bold")
    a.grid(alpha=0.25)

    fig.suptitle(
        rf"Geometric-Mean Polar Kähler ($\rho, \delta\tau_{{\mathrm{{canon}}}}$) Solver vs. Reference QM & Wigner Baselines [$c = {c:g},\; \ell_C = {1/c:g}$]",
        fontsize=12.8, fontweight="bold", y=0.98
    )
    fig.savefig(out("showcase_v9.pdf"), bbox_inches="tight", pad_inches=0.05)
    fig.savefig(out("showcase_v9.png"), dpi=300, bbox_inches="tight", pad_inches=0.05)
    fig.savefig(out("showcase_v9.svg"), bbox_inches="tight", pad_inches=0.05)
    plt.close(fig)


if __name__ == "__main__":
    np.seterr(over="raise", invalid="raise")
    main()